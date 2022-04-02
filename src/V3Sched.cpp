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

namespace {

LogicClasses gatherLogicClasses(AstNetlist* netlistp) {
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

AstCFunc* makeTopFunction(AstNetlist* netlistp, const string& name, bool slow,
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

AstEval* makeEval(AstNetlist* netlistp, VEvalKind kind) {
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    AstEval* const evalp = new AstEval{netlistp->fileline(), kind};
    scopeTopp->addActivep(evalp);
    return evalp;
}

void orderSequentially(AstCFunc* funcp, const LogicByScope& logicByScope) {
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

void createStatic(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_static", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_statics);
    splitCheck(funcp);
}

AstCFunc* createInitial(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_initial", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_initial);
    return funcp;  // Not splitting yet as it is not final
}

void createFinal(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_final", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_final);
    splitCheck(funcp);
}

void createSettle(AstNetlist* netlistp, LogicClasses& logicClasses) {
    AstEval* const evalp = makeEval(netlistp, VEvalKind::SETTLE);

    // Clone, because ordering is destructive, but we still need them for "_eval"
    LogicByScope comb = logicClasses.m_comb.clone();

    // Order it (slow code, so always single threaded)
    const auto activeps
        = V3Order::orderST(netlistp, {&logicClasses.m_settle, &comb}, V3Order::OrderMode::Settle);

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
    const string m_suffix;  // Name suffix to add to creaed variables
    std::vector<AstNodeStmt*> m_updates;  // Update assignments

    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_prev;

    // METHODS
    AstVarScope* getPrev(AstNode* currp) {
        auto it = m_prev.find(*currp);
        if (it != m_prev.end()) return it->second;

        // Create the variable
        const string name{"__Vtrigprev__" + m_suffix + "__" + cvtToStr(m_prev.size())};
        AstVarScope* const prevp = m_scopeTopp->createTemp(name, currp->dtypep());
        m_prev.emplace(*currp, prevp);

        FileLine* const flp = currp->fileline();
        const auto rdCurr = [=]() { return currp->cloneTree(false); };
        const auto wrPrev = [=]() { return new AstVarRef(flp, prevp, VAccess::WRITE); };

        // Add the initializer init
        AstNode* const initp = v3Global.opt.xInitialEdge() ? new AstNot{flp, rdCurr()} : rdCurr();
        m_initp->addStmtsp(new AstAssign{flp, wrPrev(), initp});

        // Add update
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
    SenExprBuilder(AstNetlist* netlistp, AstCFunc* initp, const string& suffix)
        : m_initp{initp}
        , m_scopeTopp{netlistp->topScopep()->scopep()}
        , m_suffix{suffix} {
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

Triggers createTriggers(AstNetlist* netlistp, AstCFunc* initp) {
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
    if (topScopep->senTreesp()) {
        // TODO: don't generate empty trigger vectors
        topScopep->senTreesp()->foreachAndNext<AstSenTree>([&](const AstSenTree* senTreep) {
            if (!senTreep->hasClocked() && !senTreep->hasHybrid()) return;
            uniqueTriggers++;
        });
    }

    // Create the triggered flags
    AstBasicDType* const tDtypep = new AstBasicDType(
        flp, VBasicDTypeKwd::TRIGGERVEC, VSigning::UNSIGNED, uniqueTriggers, uniqueTriggers);
    netlistp->typeTablep()->addTypesp(tDtypep);
    AstVarScope* const preTrigsp = scopeTopp->createTemp("__VpreTriggered", tDtypep);
    AstVarScope* const actTrigsp = scopeTopp->createTemp("__VactTriggered", tDtypep);
    AstVarScope* const nbaTrigsp = scopeTopp->createTemp("__VnbaTriggered", tDtypep);
    netlistp->preTrigsp(preTrigsp);
    netlistp->actTrigsp(actTrigsp);
    netlistp->nbaTrigsp(nbaTrigsp);

    // The trigger check function
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_triggers", false);
    netlistp->compTrigsp(funcp);

    if (!topScopep->senTreesp()) return triggers;

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

    // Populate
    uint32_t triggerNumber = 0;
    SenExprBuilder senExprBuilder{netlistp, initp, "act"};
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

void clearTrigger(AstNetlist* netlistp, AstEval* evalp, AstVarScope* trigp) {
    FileLine* const flp = evalp->fileline();

    // Clear triggers at the end
    AstVarRef* const refp = new AstVarRef{flp, trigp, VAccess::WRITE};
    AstCMethodHard* const callp = new AstCMethodHard{flp, refp, "clear"};
    callp->statement(true);
    callp->dtypeSetVoid();
    evalp->addBodyp(callp);
}

void remapSensitivities(LogicByScope& lbs,
                        std::unordered_map<const AstSenTree*, AstSenTree*> senTreeMap) {
    // Update sensitivity lists, but remember original triggers
    lbs.foreach ([&](AstScope*, AstActive* activep) {
        AstSenTree* const senTreep = activep->sensesp();
        if (senTreep->hasCombo()) return;
        activep->sensesp(senTreeMap.at(senTreep));
        activep->triggerp(senTreep);
    });
}

void createActive(AstNetlist* netlistp, LogicRegions& logicRegions, LogicByScope& replicas,
                  const Triggers& triggers) {
    AstEval* const evalp = makeEval(netlistp, VEvalKind::ACTIVE);

    remapSensitivities(logicRegions.m_pre, triggers.preTrigSenTree);
    remapSensitivities(logicRegions.m_active, triggers.actTrigSenTree);
    remapSensitivities(replicas, triggers.actTrigSenTree);

    // TODO: there can only be a single ExecGraph right now, use it for the NBA
    const auto activeps
        = V3Order::orderST(netlistp, {&logicRegions.m_pre, &logicRegions.m_active, &replicas},
                           V3Order::OrderMode::ActiveRegion);
    for (AstActive* const activep : activeps) evalp->addBodyp(activep);

    clearTrigger(netlistp, evalp, netlistp->preTrigsp());
    clearTrigger(netlistp, evalp, netlistp->actTrigsp());

    // Dispose of the remnants of the inputs
    logicRegions.m_pre.deleteActives();
    logicRegions.m_active.deleteActives();
    replicas.deleteActives();
}

void createNBA(AstNetlist* netlistp, LogicRegions& logicRegions, LogicByScope& replicas,
               const Triggers& triggers) {
    AstEval* const evalp = makeEval(netlistp, VEvalKind::NBA);

    remapSensitivities(logicRegions.m_nba, triggers.nbaTrigSenTree);
    remapSensitivities(replicas, triggers.nbaTrigSenTree);

    // Order it
    if (v3Global.opt.mtasks()) {
        AstExecGraph* const execGraphp = V3Order::orderMT(
            netlistp, {&logicRegions.m_nba, &replicas}, V3Order::OrderMode::NBARegion);
        evalp->addBodyp(execGraphp);
    } else {
        const auto activeps = V3Order::orderST(netlistp, {&logicRegions.m_nba, &replicas},
                                               V3Order::OrderMode::NBARegion);
        for (AstActive* const activep : activeps) evalp->addBodyp(activep);
    }

    clearTrigger(netlistp, evalp, netlistp->nbaTrigsp());

    // Dispose of the remnants of the inputs
    logicRegions.m_nba.deleteActives();
    replicas.deleteActives();
}

void createInputComb(AstNetlist* netlistp, AstCFunc* initp, LogicByScope& logic) {
    // Nothing to do if no combinational logic is sensitive to top level inputs
    if (logic.empty()) return;

    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();
    FileLine* const flp = scopeTopp->fileline();

    // Gather the unique senTrees used by the logic
    std::vector<const AstSenTree*> triggers;
    {
        const VNUser1InUse user1InUse;
        logic.foreach ([&](AstScope*, AstActive* activep) {
            AstSenTree* const senTreep = activep->sensesp();
            if (senTreep->user1SetOnce() || !senTreep->hasHybrid()) return;
            triggers.push_back(senTreep);
        });
    }

    // Create the triggered flags
    const size_t nTriggers = triggers.size() + 1;  // First one is always for pure comb logic
    AstBasicDType* const tDtypep = new AstBasicDType(flp, VBasicDTypeKwd::TRIGGERVEC,
                                                     VSigning::UNSIGNED, nTriggers, nTriggers);
    netlistp->typeTablep()->addTypesp(tDtypep);
    AstVarScope* const trigsp = scopeTopp->createTemp("__VicoTriggered", tDtypep);
    trigsp->varp()->noReset(true);

    // Create a reference to a trigger flag
    const auto getTrigRef = [&](uint32_t index, VAccess access) {
        AstVarRef* const vrefp = new AstVarRef{flp, trigsp, access};
        AstConst* const idxp = new AstConst{flp, index};
        AstCMethodHard* callp = new AstCMethodHard{flp, vrefp, "at", idxp};
        callp->dtypeSetBit();
        callp->pure(true);
        return callp;
    };

    // Create trigger AstSenTrees. Defer adding the new AstSenTrees to topScopep as we are
    // iterating the same list of nodes below.
    std::vector<AstSenTree*> newSenTreeps;
    const auto getSenTrue = [&](uint32_t index) {
        AstCMethodHard* const senp = getTrigRef(index, VAccess::READ);
        AstSenItem* const senItemp = new AstSenItem{flp, VEdgeType::ET_TRUE, senp};
        AstSenTree* const senTreep = new AstSenTree{flp, senItemp};
        newSenTreeps.push_back(senTreep);
        return senTreep;
    };

    // Create the function
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_comb_inputs", false);
    netlistp->evalIncombp(funcp);

    const auto setVar = [&](AstVarScope* cntp, uint32_t val) {
        AstVarRef* const refp = new AstVarRef{flp, cntp, VAccess::WRITE};
        AstConst* const zerop = new AstConst{flp, AstConst::DtypedValue{}, cntp->dtypep(), val};
        return new AstAssign{flp, refp, zerop};
    };

    const auto testZero = [&](AstVarScope* cntp) -> AstNodeMath* {
        AstVarRef* const refp = new AstVarRef{flp, cntp, VAccess::READ};
        AstConst* const zerop = new AstConst{flp, AstConst::DtypedValue{}, cntp->dtypep(), 0};
        return new AstEq{flp, refp, zerop};
    };

    // Create and initialize the iteration counter
    AstVarScope* const counterp = scopeTopp->createTemp("__VicoIterCount", 32);
    funcp->addStmtsp(setVar(counterp, 0));

    // Create the loop condition variable
    AstVarScope* const condp = scopeTopp->createTemp("__VicoContinue", 1);
    funcp->addStmtsp(setVar(condp, 1));
    // Add the loop
    AstWhile* const loopp = new AstWhile{flp, new AstVarRef{flp, condp, VAccess::READ}};
    funcp->addStmtsp(loopp);
    // Clear the loop condition variable in the loop
    loopp->addBodysp(setVar(condp, 0));

    // Compute trigger expressions
    // First is for pure combinational triggers
    AstSenTree* const inputChanged = getSenTrue(0);
    loopp->addBodysp(new AstAssign{flp, getTrigRef(0, VAccess::WRITE), testZero(counterp)});
    // Rest are for hybrid logic
    uint32_t triggerNumber = 1;
    std::unordered_map<const AstSenTree*, AstSenTree*> trigSenTree;
    SenExprBuilder senExprBuilder{netlistp, initp, "ico"};
    for (const AstSenTree* const senTreep : triggers) {
        // Create the trigger AstSenTrees
        trigSenTree[senTreep] = getSenTrue(triggerNumber);

        // Add the trigger computation
        loopp->addBodysp(new AstAssign{flp, getTrigRef(triggerNumber, VAccess::WRITE),
                                       senExprBuilder.build(senTreep)});

        //
        ++triggerNumber;
    }
    for (AstNodeStmt* const nodep : senExprBuilder.updates()) loopp->addBodysp(nodep);
    // Add new AstSenTrees under the netlist
    for (AstSenTree* const senTreep : newSenTreeps) topScopep->addSenTreep(senTreep);

    // Create if
    AstCMethodHard* const callp
        = new AstCMethodHard{flp, new AstVarRef{flp, trigsp, VAccess::READ}, "any"};
    callp->dtypeSetBit();

    AstIf* const ifp = new AstIf{flp, callp};
    loopp->addBodysp(ifp);
    ifp->addIfsp(setVar(condp, 1));
    ifp->addIfsp(new AstAssign{
        flp, new AstVarRef{flp, counterp, VAccess::WRITE},
        new AstAdd{flp, new AstVarRef{flp, counterp, VAccess::READ}, new AstConst{flp, 1}}});

    remapSensitivities(logic, trigSenTree);

    // Order and add to loop body via sub-function
    {
        AstCFunc* const bodyp = makeTopFunction(netlistp, "_eval_ico", false);
        bodyp->entryPoint(false);
        ifp->addIfsp(new AstCCall{flp, bodyp});
        const auto activeps
            = V3Order::orderST(netlistp, {&logic}, V3Order::OrderMode::InputComb, inputChanged);
        for (AstActive* const activep : activeps) bodyp->addStmtsp(activep);
    }

    logic.deleteActives();
}

}  // namespace

void schedule(AstNetlist* netlistp) {
    const auto addSizeStat = [](const string name, const LogicByScope& lbs) {
        uint64_t size = 0;
        lbs.foreachLogic([&](AstNode* nodep) { size += nodep->nodeCount(); });
        V3Stats::addStat("Scheduling, " + name, size);
    };

    LogicClasses logicClasses = gatherLogicClasses(netlistp);

    if (v3Global.opt.stats()) {
        V3Stats::statsStage("sched-gather");
        addSizeStat("size of class: static", logicClasses.m_statics);
        addSizeStat("size of class: initial", logicClasses.m_initial);
        addSizeStat("size of class: settle", logicClasses.m_settle);
        addSizeStat("size of class: final", logicClasses.m_final);
    }

    createStatic(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-static");

    AstCFunc* const initp = createInitial(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-initial");

    createFinal(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-final");

    createSettle(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-settle");

    // Note: breakCycles also removes corresponding logic from logicClasses.m_comb;
    logicClasses.m_hybrid = breakCycles(netlistp, logicClasses.m_comb);
    if (v3Global.opt.stats()) {
        addSizeStat("size of class: clocked", logicClasses.m_clocked);
        addSizeStat("size of class: combinational", logicClasses.m_comb);
        addSizeStat("size of class: hybrid", logicClasses.m_hybrid);
        V3Stats::statsStage("sched-break-cycles");
    }

    LogicRegions logicRegions
        = partition(logicClasses.m_clocked, logicClasses.m_comb, logicClasses.m_hybrid);
    if (v3Global.opt.stats()) {
        addSizeStat("size of region: Active Pre", logicRegions.m_pre);
        addSizeStat("size of region: Active", logicRegions.m_active);
        addSizeStat("size of region: NBA", logicRegions.m_nba);
        V3Stats::statsStage("sched-partition");
    }

    LogicReplicas logicReplicas = replicateLogic(logicRegions);
    if (v3Global.opt.stats()) {
        addSizeStat("size of replicated logic: Input", logicReplicas.m_input);
        addSizeStat("size of replicated logic: Active", logicReplicas.m_active);
        addSizeStat("size of replicated logic: NBA", logicReplicas.m_nba);
        V3Stats::statsStage("sched-replicate");
    }

    const Triggers triggers = createTriggers(netlistp, initp);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-triggers");

    createInputComb(netlistp, initp, logicReplicas.m_input);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-ico");

    createActive(netlistp, logicRegions, logicReplicas.m_active, triggers);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-act");

    createNBA(netlistp, logicRegions, logicReplicas.m_nba, triggers);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-nba");

    splitCheck(initp);

    V3Global::dumpCheckGlobalTree("sched", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
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
