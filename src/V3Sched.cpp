// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3EmitV.h"
#include "V3Order.h"
#include "V3Sched.h"
#include "V3Stats.h"

#include "unordered_map"

namespace V3Sched {

LogicByScope LogicByScope::clone() const {
    LogicByScope result;
    for (const auto& pair : *this) {
        std::vector<AstActive*> clones;
        for (AstActive* const activep : pair.second) clones.push_back(activep->cloneTree(false));
        result.emplace_back(pair.first, std::move(clones));
    }
    return result;
}

static LogicClasses gatherLogicClasses(AstNetlist* netlistp) {
    LogicClasses result;

    const auto moveIfNotEmpty
        = [](LogicByScope& lbs, AstScope* scopep, std::vector<AstActive*>& vec) {
              if (!vec.empty()) lbs.emplace_back(scopep, std::move(vec));
          };

    netlistp->foreach<AstScope>([&](AstScope* scopep) {
        std::vector<AstActive*> statics;
        std::vector<AstActive*> initial;
        std::vector<AstActive*> settle;
        std::vector<AstActive*> final;
        std::vector<AstActive*> comb;
        std::vector<AstActive*> clocked;

        scopep->foreach<AstActive>([&](AstActive* activep) {
            AstSenTree* const senTreep = activep->sensesp();
            if (senTreep->hasStatic()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "static initializer with additional sensitivities");
                statics.push_back(activep);
            } else if (senTreep->hasInitial()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "'initial' logic with additional sensitivities");
                initial.push_back(activep);
            } else if (senTreep->hasSettle()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "settle logic with additional sensitivities");
                settle.push_back(activep);
            } else if (senTreep->hasFinal()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "'final' logic with additional sensitivities");
                final.push_back(activep);
            } else if (senTreep->hasCombo()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "combinational logic with additional sensitivities");
                comb.push_back(activep);
            } else {
                UASSERT_OBJ(senTreep->hasClocked(), activep, "What else could it be?");
                clocked.push_back(activep);
            }
        });

        moveIfNotEmpty(result.m_statics, scopep, statics);
        moveIfNotEmpty(result.m_initial, scopep, initial);
        moveIfNotEmpty(result.m_settle, scopep, settle);
        moveIfNotEmpty(result.m_final, scopep, final);
        moveIfNotEmpty(result.m_comb, scopep, comb);
        moveIfNotEmpty(result.m_clocked, scopep, clocked);
    });

    return result;
}

static AstCFunc* makeTopFunction(AstNetlist* netlistp, const string& name, bool slow,
                                 const string& returnType = "") {
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    AstCFunc* const funcp = new AstCFunc{netlistp->fileline(), name, scopeTopp, returnType};
    funcp->dontCombine(true);
    funcp->isStatic(false);
    funcp->isLoose(true);
    funcp->entryPoint(true);
    funcp->slow(slow);
    funcp->isConst(false);
    funcp->declPrivate(true);
    scopeTopp->addActivep(funcp);
    return funcp;
}

static AstEval* makeEval(AstNetlist* netlistp, VEvalKind kind) {
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    AstEval* const evalp = new AstEval{netlistp->fileline(), kind};
    scopeTopp->addActivep(evalp);
    return evalp;
}

static void orderSequentially(AstCFunc* funcp, const LogicByScope& logicByScope) {
    for (const auto& pair : logicByScope) {
        AstScope* const scopep = pair.first;
        // Create a sub-function per scope for combining
        const string subName{funcp->name() + "__" + scopep->nameDotless()};
        AstCFunc* const subFuncp = new AstCFunc{scopep->fileline(), subName, scopep};
        subFuncp->isLoose(true);
        subFuncp->isConst(false);
        subFuncp->declPrivate(true);
        subFuncp->slow(funcp->slow());
        scopep->addActivep(subFuncp);
        // Call it from the top function
        funcp->addStmtsp(new AstCCall{scopep->fileline(), subFuncp});
        // Add statements to sub-function
        for (AstActive* activep : pair.second) {
            for (AstNode *logicp = activep->stmtsp(), *nextp; logicp; logicp = nextp) {
                nextp = logicp->nextp();
                if (AstNodeProcedure* const procp = VN_CAST(logicp, NodeProcedure)) {
                    if (AstNode* const bodyp = procp->bodysp()) {
                        bodyp->unlinkFrBackWithNext();
                        subFuncp->addStmtsp(bodyp);
                    }
                } else {
                    logicp->unlinkFrBackWithNext();
                    subFuncp->addStmtsp(logicp);
                }
            }
            if (activep->backp()) activep->unlinkFrBack();
            activep->deleteTree();
        }
    }
}

static void createStatic(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_static", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_statics);
    splitCheck(funcp);
}

static void createInitial(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_initial", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_initial);
    // Not splitting yet as it is not final
    netlistp->initp(funcp);
}

static void createFinal(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_final", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_final);
    splitCheck(funcp);
}

static void createSettle(AstNetlist* netlistp, LogicClasses& logicClasses) {
    AstEval* const evalp = makeEval(netlistp, VEvalKind::SETTLE);

    // Clone, because ordering is destructive, but we still need them for "_eval"
    LogicByScope comb = logicClasses.m_comb.clone();

    // Order it (slow code, so always single threaded)
    const auto activeps = V3Order::orderST(netlistp, {&logicClasses.m_settle, &comb}, {},
                                           V3Order::OrderMode::Settle);

    // Move the logic under the function being built
    for (AstActive* const activep : activeps) evalp->addBodyp(activep);

    // Dispose of the remnants of the inputs
    logicClasses.m_settle.deleteActives();
    comb.deleteActives();
}

class SenExprBuilder final {
    // NODE STATE
    // AstVarScope::user1p()  -> AstVarScope* : prev value variables
    //    const VNUser1InUse user1InUse;

    // STATE
    AstCFunc* const m_initp;  // The initialization function
    AstScope* const m_scopeTopp;  // Top level scope
    std::vector<AstNodeStmt*> m_updates;  // Update assignments

    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_prev;

    // METHODS
    AstVarScope* getPrev(AstNode* currp) {
        auto it = m_prev.find(*currp);
        if (it != m_prev.end()) return it->second;

        // Create the variable
        const string name{"__Vtrigprev__" + cvtToStr(m_prev.size())};
        AstVarScope* const prevp = m_scopeTopp->createTemp(name, currp->dtypep());
        m_prev.emplace(*currp, prevp);

        FileLine* const flp = currp->fileline();
        const auto rdCurr = [=]() { return currp->cloneTree(false); };
        const auto wrPrev = [=]() { return new AstVarRef(flp, prevp, VAccess::WRITE); };

        // Add the initializer init
        AstNode* const initp = v3Global.opt.xInitialEdge() ? new AstNot{flp, rdCurr()} : rdCurr();
        m_initp->addStmtsp(new AstAssign{flp, wrPrev(), initp});

        // Add update >
        m_updates.push_back(new AstAssign{flp, wrPrev(), rdCurr()});

        //
        return prevp;
    }

    AstNode* createTerm(AstSenItem* senItemp) {
        if (senItemp->edgeType() == VEdgeType::ET_ILLEGAL) {
            senItemp->v3warn(
                E_UNSUPPORTED,
                "Unsupported: Complicated event expression in sensitive activity list");
            return nullptr;
        }

        FileLine* const flp = senItemp->fileline();
        AstNode* const senp = senItemp->sensp();

        const auto currp = [=]() { return senp->cloneTree(false); };
        const auto prevp = [=]() { return new AstVarRef{flp, getPrev(senp), VAccess::READ}; };
        const auto lsb = [=](AstNodeMath* opp) { return new AstSel{flp, opp, 0, 1}; };

        // All event signals should be 1-bit at this point
        switch (senItemp->edgeType()) {
        case VEdgeType::ET_CHANGED:
        case VEdgeType::ET_HYBRID: return new AstNeq(flp, currp(), prevp());
        case VEdgeType::ET_BOTHEDGE: return lsb(new AstXor{flp, currp(), prevp()});
        case VEdgeType::ET_POSEDGE: return lsb(new AstAnd{flp, currp(), new AstNot{flp, prevp()}});
        case VEdgeType::ET_NEGEDGE: return lsb(new AstAnd{flp, new AstNot{flp, currp()}, prevp()});
        case VEdgeType::ET_HIGHEDGE: return currp();
        case VEdgeType::ET_LOWEDGE: return new AstNot{flp, currp()};
        case VEdgeType::ET_EVENT: {
            UASSERT_OBJ(v3Global.hasEvents(), senItemp, "Inconsistent");

            {
                // If the event is fired, set up the clearing process
                AstCMethodHard* const callp = new AstCMethodHard{flp, currp(), "isFired"};
                callp->dtypeSetBit();
                AstIf* const ifp = new AstIf{flp, callp};
                m_updates.push_back(ifp);

                // Clear 'fired' state when done
                AstCMethodHard* const clearp = new AstCMethodHard{flp, currp(), "clearFired"};
                ifp->addIfsp(clearp);
                clearp->dtypeSetVoid();
                clearp->statement(true);

                // Enqueue for clearing 'triggered' state on next eval
                AstTextBlock* const blockp = new AstTextBlock{flp};
                ifp->addIfsp(blockp);
                const auto add = [&](const string& text) { blockp->addText(flp, text, true); };
                add("vlSymsp->enqueueTriggeredEventForClearing(");
                blockp->addNodep(currp());
                add(");\n");
            }

            // Get 'fired' state
            AstCMethodHard* const callp = new AstCMethodHard{flp, currp(), "isFired"};
            callp->dtypeSetBit();
            return callp;
        }
        default: senItemp->v3fatalSrc("Unknown edge type"); return nullptr;  // LCOV_EXCL_LINE
        }
    }

public:
    AstNode* build(const AstSenTree* senTreep) {
        FileLine* const flp = senTreep->fileline();
        AstNode* resultp = nullptr;
        for (AstSenItem* senItemp = senTreep->sensesp(); senItemp;
             senItemp = VN_AS(senItemp->nextp(), SenItem)) {
            if (AstNode* const termp = createTerm(senItemp)) {
                resultp = resultp ? new AstOr{flp, resultp, termp} : termp;
            }
        }
        return resultp;
    }

    std::vector<AstNodeStmt*> updates() { return std::move(m_updates); }

    // CONSTRUCTOR
    explicit SenExprBuilder(AstNetlist* netlistp)
        : m_initp{netlistp->initp()}
        , m_scopeTopp{netlistp->topScopep()->scopep()} {
        // If there is a DPI export trigger, always clear it after trigger computation
        if (AstVarScope* const vscp = netlistp->dpiExportTriggerp()) {
            FileLine* const flp = vscp->fileline();
            AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::WRITE};
            m_updates.push_back(new AstAssign{flp, refp, new AstConst{flp, AstConst::BitFalse{}}});
        }
    }
};

struct Triggers final {
    std::unordered_map<const AstSenTree*, AstSenTree*> preTrigSenTree;
    std::unordered_map<const AstSenTree*, AstSenTree*> actTrigSenTree;
    std::unordered_map<const AstSenTree*, AstSenTree*> nbaTrigSenTree;
};

static Triggers createTriggers(AstNetlist* netlistp) {
    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();
    FileLine* const flp = scopeTopp->fileline();

    Triggers triggers;

    // Count the number of unique triggers, and also associate each unique AstSenTree with its
    // trigger number.

    // Create the iteration counters
    AstNodeDType* const cDtypep = netlistp->findUInt32DType();
    AstVarScope* const actCountp = scopeTopp->createTemp("__VactIterCount", cDtypep);
    AstVarScope* const nbaCountp = scopeTopp->createTemp("__VnbaIterCount", cDtypep);
    netlistp->actCountp(actCountp);
    netlistp->nbaCountp(nbaCountp);

    uint32_t uniqueTriggers = 0;
    topScopep->senTreesp()->foreachAndNext<AstSenTree>([&](const AstSenTree* senTreep) {
        if (!senTreep->hasClocked() && !senTreep->hasHybrid()) return;
        uniqueTriggers++;
    });

    // Create the triggered flags
    AstBasicDType* const tDtypep = new AstBasicDType(
        flp, VBasicDTypeKwd::TRIGGERVEC, VSigning::UNSIGNED, uniqueTriggers, uniqueTriggers);
    UASSERT_OBJ(netlistp->findInsertSameDType(tDtypep) == tDtypep, tDtypep, "Already exists?");
    netlistp->typeTablep()->addTypesp(tDtypep);
    AstVarScope* const preTrigsp = scopeTopp->createTemp("__VpreTriggered", tDtypep);
    AstVarScope* const actTrigsp = scopeTopp->createTemp("__VactTriggered", tDtypep);
    AstVarScope* const nbaTrigsp = scopeTopp->createTemp("__VnbaTriggered", tDtypep);
    preTrigsp->varp()->noReset(true);
    actTrigsp->varp()->noReset(true);
    nbaTrigsp->varp()->noReset(true);
    netlistp->preTrigsp(preTrigsp);
    netlistp->actTrigsp(actTrigsp);
    netlistp->nbaTrigsp(nbaTrigsp);

    // Create a reference to a trigger flag
    const auto getTrigRef = [&](AstVarScope* vscp, uint32_t index, VAccess access) {
        AstVarRef* const vrefp = new AstVarRef{flp, vscp, access};
        AstConst* const idxp = new AstConst{flp, index};
        AstCMethodHard* callp = new AstCMethodHard{flp, vrefp, "at", idxp};
        callp->dtypeSetBit();
        callp->pure(true);
        return callp;
    };

    // Create trigger AstSenTrees. Defer adding the new AstSenTrees to topScopep as we are
    // iterating the same list of nodes below.
    std::vector<AstSenTree*> newSenTreeps;
    const auto getSenTrue = [&](AstVarScope* vscp, uint32_t index) {  //
        AstCMethodHard* const senp = getTrigRef(vscp, index, VAccess::READ);
        AstSenItem* const senItemp = new AstSenItem{flp, VEdgeType::ET_TRUE, senp};
        AstSenTree* const senTreep = new AstSenTree{flp, senItemp};
        newSenTreeps.push_back(senTreep);
        return senTreep;
    };

    // The trigger check function
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_triggers", false);
    netlistp->compTrigsp(funcp);

    // Populate
    uint32_t triggerNumber = 0;
    SenExprBuilder senExprBuilder{netlistp};
    AstNode* debugp = nullptr;
    topScopep->senTreesp()->foreachAndNext<AstSenTree>([&](const AstSenTree* senTreep) {  //
        if (!senTreep->hasClocked() && !senTreep->hasHybrid()) return;

        // Create the trigger AstSenTrees
        triggers.preTrigSenTree[senTreep] = getSenTrue(preTrigsp, triggerNumber);
        triggers.actTrigSenTree[senTreep] = getSenTrue(actTrigsp, triggerNumber);
        triggers.nbaTrigSenTree[senTreep] = getSenTrue(nbaTrigsp, triggerNumber);

        // Add the trigger computation
        funcp->addStmtsp(new AstAssign{flp, getTrigRef(actTrigsp, triggerNumber, VAccess::WRITE),
                                       senExprBuilder.build(senTreep)});

        // Add a debug dumping statement for this trigger
        {
            std::stringstream ss;
            ss << "VL_DBG_MSGF(\"         Triggered: ";
            V3EmitV::verilogForTree(senTreep, ss);
            ss << "\\n\");\n";
            const string message{ss.str()};

            AstIf* const ifp = new AstIf{flp, getTrigRef(actTrigsp, triggerNumber, VAccess::READ)};
            debugp = AstNode::addNext(debugp, ifp);
            ifp->addIfsp(new AstText{flp, message, true});
        }

        //
        ++triggerNumber;
    });
    for (AstNodeStmt* const nodep : senExprBuilder.updates()) funcp->addStmtsp(nodep);

    // Add debug dumping section
    {
        AstTextBlock* const blockp = new AstTextBlock{flp};
        funcp->addStmtsp(blockp);
        const auto add = [&](const string& text) { blockp->addText(flp, text, true); };
        add("#ifdef VL_DEBUG\n");
        add("if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {\n");
        AstCMethodHard* const callp
            = new AstCMethodHard{flp, new AstVarRef{flp, actTrigsp, VAccess::READ}, "any"};
        callp->dtypeSetBit();
        AstIf* const ifp = new AstIf{flp, callp};
        blockp->addNodep(ifp);
        ifp->addElsesp(
            new AstText{flp, "VL_DBG_MSGF(\"         No triggers active\\n\");\n", true});
        if (debugp) blockp->addNodep(debugp);
        add("}\n");
        add("#endif\n");
    }

    // Add new AstSenTrees under the netlist
    for (AstSenTree* const senTreep : newSenTreeps) topScopep->addSenTreep(senTreep);

    return triggers;
}

static const std::unordered_set<const AstVarScope*>
gatherWritten(const std::vector<const V3Sched::LogicByScope*>& coll) {
    std::unordered_set<const AstVarScope*> result;
    for (const auto& lbs : coll) {
        lbs->foreach ([&](AstScope*, AstActive* activep) {
            activep->foreach<AstVarRef>([&](const AstVarRef* refp) {
                if (refp->access().isReadOnly()) return;
                result.insert(refp->varScopep());
            });
        });
    }
    return result;
}

static void clearTrigger(AstNetlist* netlistp, AstEval* evalp, AstVarScope* trigp) {
    FileLine* const flp = evalp->fileline();

    // Clear triggers at the end
    AstVarRef* const refp = new AstVarRef{flp, trigp, VAccess::WRITE};
    AstCMethodHard* const callp = new AstCMethodHard{flp, refp, "clear"};
    callp->statement(true);
    callp->dtypeSetVoid();
    evalp->addFinalp(callp);
}

static void createActive(AstNetlist* netlistp, LogicRegions& logicRegions,
                         const std::unordered_set<const AstVarScope*>& writtenExternally,
                         const Triggers& triggers) {
    AstEval* const evalp = makeEval(netlistp, VEvalKind::ACTIVE);

    clearTrigger(netlistp, evalp, netlistp->preTrigsp());
    clearTrigger(netlistp, evalp, netlistp->actTrigsp());

    // Update sensitivity lists, but remember original triggers
    logicRegions.m_pre.foreach ([&](AstScope*, AstActive* activep) {
        AstSenTree* const senTreep = activep->sensesp();
        if (senTreep->hasCombo()) return;
        activep->sensesp(triggers.preTrigSenTree.at(senTreep));
        activep->triggerp(senTreep);
    });

    logicRegions.m_active.foreach ([&](AstScope*, AstActive* activep) {
        AstSenTree* const senTreep = activep->sensesp();
        if (senTreep->hasCombo()) return;
        activep->sensesp(triggers.actTrigSenTree.at(senTreep));
        activep->triggerp(senTreep);
    });

    // Order it TODO: there can only be a single ExecGraph right now, use it for the NBA
    //    if (v3Global.opt.mtasks()) {
    //        AstExecGraph* const execGraphp = orderMT(netlistp, coll);
    //        evalp->addBodyp(execGraphp);
    //    } else {
    const auto activeps = V3Order::orderST(netlistp, {&logicRegions.m_pre, &logicRegions.m_active},
                                           writtenExternally, V3Order::OrderMode::ActiveRegion);
    for (AstActive* const activep : activeps) evalp->addBodyp(activep);
    //    }

    // Dispose of the remnants of the inputs
    logicRegions.m_pre.deleteActives();
    logicRegions.m_active.deleteActives();
}

static void createNBA(AstNetlist* netlistp, LogicRegions& logicRegions,
                      const std::unordered_set<const AstVarScope*>& writtenExternally,
                      const Triggers& triggers) {
    AstEval* const evalp = makeEval(netlistp, VEvalKind::NBA);

    clearTrigger(netlistp, evalp, netlistp->nbaTrigsp());

    // Update sensitivity lists
    logicRegions.m_nba.foreach ([&](AstScope*, AstActive* activep) {
        AstSenTree* const senTreep = activep->sensesp();
        if (senTreep->hasCombo()) return;
        activep->sensesp(triggers.nbaTrigSenTree.at(senTreep));
        activep->triggerp(senTreep);
    });

    // Order it
    if (v3Global.opt.mtasks()) {
        AstExecGraph* const execGraphp = V3Order::orderMT(
            netlistp, {&logicRegions.m_nba}, writtenExternally, V3Order::OrderMode::NBARegion);
        evalp->addBodyp(execGraphp);
    } else {
        const auto activeps = V3Order::orderST(netlistp, {&logicRegions.m_nba}, writtenExternally,
                                               V3Order::OrderMode::NBARegion);
        for (AstActive* const activep : activeps) evalp->addBodyp(activep);
    }

    // Dispose of the remnants of the inputs
    logicRegions.m_nba.deleteActives();
}

static void addRegionStats(const string name, const LogicByScope& lbs) {
    uint64_t size = 0;
    lbs.foreach ([&](AstScope*, AstActive* activep) {
        for (AstNode* nodep = activep->stmtsp(); nodep; nodep = nodep->nextp()) {
            size += nodep->nodeCount();
        }
    });
    V3Stats::addStat("Scheduling, " + name, size);
}

void schedule(AstNetlist* netlistp) {
    LogicClasses logicClasses = gatherLogicClasses(netlistp);

    if (v3Global.opt.stats()) {
        addRegionStats("size of class: static", logicClasses.m_statics);
        addRegionStats("size of class: initial", logicClasses.m_initial);
        addRegionStats("size of class: settle", logicClasses.m_settle);
        addRegionStats("size of class: final", logicClasses.m_final);
    }

    createStatic(netlistp, logicClasses);
    createInitial(netlistp, logicClasses);
    createFinal(netlistp, logicClasses);
    V3Global::dumpCheckGlobalTree("sched-simple", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);

    createSettle(netlistp, logicClasses);
    V3Global::dumpCheckGlobalTree("sched-settle", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);

    // Note: breakCycles also removes corresponding logic from logicClasses.m_comb;
    logicClasses.m_hybrid = breakCycles(netlistp, logicClasses.m_comb);

    if (v3Global.opt.stats()) {
        addRegionStats("size of class: clocked", logicClasses.m_clocked);
        addRegionStats("size of class: combinational", logicClasses.m_comb);
        addRegionStats("size of class: hybrid", logicClasses.m_hybrid);
    }

    LogicRegions logicRegions
        = partition(logicClasses.m_clocked, logicClasses.m_comb, logicClasses.m_hybrid);

    if (v3Global.opt.stats()) {
        addRegionStats("size of region: Active Pre", logicRegions.m_pre);
        addRegionStats("size of region: Active", logicRegions.m_active);
        addRegionStats("size of region: NBA", logicRegions.m_nba);
    }

    Triggers triggers = createTriggers(netlistp);

    const auto writtenExtToAct = gatherWritten({&logicRegions.m_nba});
    const auto writtenExtToNBA = gatherWritten({&logicRegions.m_pre, &logicRegions.m_active});
    createActive(netlistp, logicRegions, writtenExtToAct, triggers);
    createNBA(netlistp, logicRegions, writtenExtToNBA, triggers);
    V3Global::dumpCheckGlobalTree("sched-eval", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void splitCheck(AstCFunc* ofuncp) {
    if (!v3Global.opt.outputSplitCFuncs() || !ofuncp->stmtsp()) return;
    if (ofuncp->nodeCount() < v3Global.opt.outputSplitCFuncs()) return;

    int funcnum = 0;
    int func_stmts = 0;
    AstCFunc* funcp = nullptr;

    // Unlink all statements, then add item by item to new sub-functions
    AstBegin* const tempp = new AstBegin{ofuncp->fileline(), "[EditWrapper]",
                                         ofuncp->stmtsp()->unlinkFrBackWithNext()};
    if (ofuncp->finalsp()) tempp->addStmtsp(ofuncp->finalsp()->unlinkFrBackWithNext());
    while (tempp->stmtsp()) {
        AstNode* const itemp = tempp->stmtsp()->unlinkFrBack();
        const int stmts = itemp->nodeCount();
        if (!funcp || (func_stmts + stmts) > v3Global.opt.outputSplitCFuncs()) {
            // Make a new function
            funcp = new AstCFunc{ofuncp->fileline(), ofuncp->name() + "__" + cvtToStr(funcnum++),
                                 ofuncp->scopep()};
            funcp->dontCombine(true);
            funcp->isStatic(false);
            funcp->isLoose(true);
            funcp->slow(ofuncp->slow());
            ofuncp->scopep()->addActivep(funcp);
            //
            AstCCall* const callp = new AstCCall{funcp->fileline(), funcp};
            ofuncp->addStmtsp(callp);
            func_stmts = 0;
        }
        funcp->addStmtsp(itemp);
        func_stmts += stmts;
    }
    VL_DO_DANGLING(tempp->deleteTree(), tempp);
}

}  // namespace V3Sched
