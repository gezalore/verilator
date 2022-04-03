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
        moveIfNotEmpty(result.m_final, scopep, final);
        moveIfNotEmpty(result.m_comb, scopep, comb);
        moveIfNotEmpty(result.m_clocked, scopep, clocked);
    });

    return result;
}

AstCFunc* makeSubFunction(AstNetlist* netlistp, const string& name, bool slow) {
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    AstCFunc* const funcp = new AstCFunc{netlistp->fileline(), name, scopeTopp, ""};
    funcp->dontCombine(true);
    funcp->isStatic(false);
    funcp->isLoose(true);
    funcp->slow(slow);
    funcp->isConst(false);
    funcp->declPrivate(true);
    scopeTopp->addActivep(funcp);
    return funcp;
}

AstCFunc* makeTopFunction(AstNetlist* netlistp, const string& name, bool slow) {
    AstCFunc* const funcp = makeSubFunction(netlistp, name, slow);
    funcp->entryPoint(true);
    return funcp;
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
        AstNode* const initp = rdCurr();
        m_initp->addStmtsp(new AstAssign{flp, wrPrev(), initp});

        // Add update
        m_updates.push_back(new AstAssign{flp, wrPrev(), rdCurr()});

        //
        return prevp;
    }

    std::pair<AstNode*, bool> createTerm(AstSenItem* senItemp) {
        if (senItemp->edgeType() == VEdgeType::ET_ILLEGAL) {
            senItemp->v3warn(
                E_UNSUPPORTED,
                "Unsupported: Complicated event expression in sensitive activity list");
            return {nullptr, false};
        }

        FileLine* const flp = senItemp->fileline();
        AstNode* const senp = senItemp->sensp();

        const auto currp = [=]() { return senp->cloneTree(false); };
        const auto prevp = [=]() { return new AstVarRef{flp, getPrev(senp), VAccess::READ}; };
        const auto lsb = [=](AstNodeMath* opp) { return new AstSel{flp, opp, 0, 1}; };

        // All event signals should be 1-bit at this point
        switch (senItemp->edgeType()) {
        case VEdgeType::ET_CHANGED:
        case VEdgeType::ET_HYBRID:  //
            return {new AstNeq(flp, currp(), prevp()), true};
        case VEdgeType::ET_BOTHEDGE:  //
            return {lsb(new AstXor{flp, currp(), prevp()}), false};
        case VEdgeType::ET_POSEDGE:  //
            return {lsb(new AstAnd{flp, currp(), new AstNot{flp, prevp()}}), false};
        case VEdgeType::ET_NEGEDGE:  //
            return {lsb(new AstAnd{flp, new AstNot{flp, currp()}, prevp()}), false};
        case VEdgeType::ET_HIGHEDGE:  //
            return {currp(), false};
        case VEdgeType::ET_LOWEDGE:  //
            return {new AstNot{flp, currp()}, false};
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
            return {callp, false};
        }
        default:
            senItemp->v3fatalSrc("Unknown edge type");
            return {nullptr, false};  // LCOV_EXCL_LINE
        }
    }

public:
    // Returns the expression computing the trigger, and a bool indicating that
    // this trigger should be fired on the first evaluation (at initialization)
    std::pair<AstNode*, bool> build(const AstSenTree* senTreep) {
        FileLine* const flp = senTreep->fileline();
        AstNode* resultp = nullptr;
        bool firedAtInitialization = false;
        for (AstSenItem* senItemp = senTreep->sensesp(); senItemp;
             senItemp = VN_AS(senItemp->nextp(), SenItem)) {
            const auto& pair = createTerm(senItemp);
            if (AstNode* const termp = pair.first) {
                resultp = resultp ? new AstOr{flp, resultp, termp} : termp;
                firedAtInitialization |= pair.second;
            }
        }
        return {resultp, firedAtInitialization};
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

std::vector<const AstSenTree*> getSenTreesUsedBy(std::vector<const LogicByScope*> lbsps) {
    const VNUser1InUse user1InUse;
    std::vector<const AstSenTree*> result;
    for (const LogicByScope* const lbsp : lbsps) {
        lbsp->foreach ([&](AstScope*, AstActive* activep) {
            AstSenTree* const senTreep = activep->sensesp();
            if (senTreep->user1SetOnce()) return;
            if (senTreep->hasClocked() || senTreep->hasHybrid()) result.push_back(senTreep);
        });
    }
    return result;
}

AstAssign* setVar(AstVarScope* vscp, uint32_t val) {
    FileLine* const flp = vscp->fileline();
    AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::WRITE};
    AstConst* const zerop = new AstConst{flp, AstConst::DtypedValue{}, vscp->dtypep(), val};
    return new AstAssign{flp, refp, zerop};
};

struct TriggerKit {
    // The TRIGGERVEC AstVarScope representing these trigger flags
    AstVarScope* const m_vscp;
    // The AstCFunc that computes the current active triggers
    AstCFunc* const m_funcp;
    // The map from input sensitivity list to trigger sensitivitylist
    const std::unordered_map<const AstSenTree*, AstSenTree*> m_map;

    VL_UNCOPYABLE(TriggerKit);
    TriggerKit(TriggerKit&& other) = default;
    TriggerKit& operator=(TriggerKit&&) = default;

    // Create an AstSenTree that is sensitive to trigger 0. Must not exist yet!
    AstSenTree* createFirstTriggerRef(AstNetlist* netlistp) const {
        AstTopScope* const topScopep = netlistp->topScopep();
        FileLine* const flp = topScopep->fileline();
        AstVarRef* const vrefp = new AstVarRef{flp, m_vscp, VAccess::READ};
        AstCMethodHard* callp = new AstCMethodHard{flp, vrefp, "at", new AstConst{flp, 0}};
        callp->dtypeSetBit();
        callp->pure(true);
        AstSenItem* const senItemp = new AstSenItem{flp, VEdgeType::ET_TRUE, callp};
        AstSenTree* const resultp = new AstSenTree{flp, senItemp};
        topScopep->addSenTreep(resultp);
        return resultp;
    }

    // Utility that assigns the 0 index trigger to fire when the given variable is zero
    void addFirstIterationTriggerAssignment(AstVarScope* counterp) const {
        FileLine* const flp = counterp->fileline();
        AstVarRef* const vrefp = new AstVarRef{flp, m_vscp, VAccess::WRITE};
        AstCMethodHard* callp = new AstCMethodHard{flp, vrefp, "at", new AstConst{flp, 0}};
        callp->dtypeSetBit();
        callp->pure(true);
        m_funcp->stmtsp()->addHereThisAsNext(new AstAssign{
            flp, callp,
            new AstEq{flp, new AstVarRef{flp, counterp, VAccess::READ}, new AstConst{flp, 0}}});
    }
};

const TriggerKit createTriggers(AstNetlist* netlistp, AstCFunc* initp,
                                std::vector<const AstSenTree*> senTreeps, const string& name,
                                unsigned extra, bool slow = false) {
    // TODO: don't generate empty trigger vectors

    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();
    FileLine* const flp = scopeTopp->fileline();

    std::unordered_map<const AstSenTree*, AstSenTree*> map;

    const uint32_t nTriggers = senTreeps.size() + extra;

    // Create the TRIGGERVEC variable
    AstBasicDType* const tDtypep = new AstBasicDType(flp, VBasicDTypeKwd::TRIGGERVEC,
                                                     VSigning::UNSIGNED, nTriggers, nTriggers);
    netlistp->typeTablep()->addTypesp(tDtypep);
    AstVarScope* const vscp = scopeTopp->createTemp("__V" + name + "Triggered", tDtypep);

    // Create the trigger computation function TODO: this should be sub-function
    AstCFunc* const funcp = makeSubFunction(netlistp, "_eval_triggers__" + name, slow);

    // Create a reference to a trigger flag
    const auto getTrigRef = [&](uint32_t index, VAccess access) {
        AstVarRef* const vrefp = new AstVarRef{flp, vscp, access};
        AstConst* const idxp = new AstConst{flp, index};
        AstCMethodHard* callp = new AstCMethodHard{flp, vrefp, "at", idxp};
        callp->dtypeSetBit();
        callp->pure(true);
        return callp;
    };

    // Add a debug dumping statement for this trigger
    AstNode* debugp = nullptr;
    const auto addDebug = [&](uint32_t index, const string& text = "") {
        std::stringstream ss;
        ss << "VL_DBG_MSGF(\"         Triggered " << name << " index " << cvtToStr(index);
        if (!text.empty()) ss << ": " << text;
        ss << "\\n\");\n";
        const string message{ss.str()};

        AstIf* const ifp = new AstIf{flp, getTrigRef(index, VAccess::READ)};
        debugp = AstNode::addNext(debugp, ifp);
        ifp->addIfsp(new AstText{flp, message, true});
    };

    // Populate
    for (unsigned i = 0; i < extra; ++i) addDebug(i);
    uint32_t triggerNumber = extra;
    SenExprBuilder senExprBuilder{netlistp, initp, name};
    AstNode* initialTrigsp = nullptr;
    for (const AstSenTree* const senTreep : senTreeps) {
        UASSERT_OBJ(senTreep->hasClocked() || senTreep->hasHybrid(), senTreep,
                    "Cannot create trigger expression for non-clocked sensitivity");

        // Create the trigger AstSenTrees and associate it with the original AstSenTree
        AstCMethodHard* const senp = getTrigRef(triggerNumber, VAccess::READ);
        AstSenItem* const senItemp = new AstSenItem{flp, VEdgeType::ET_TRUE, senp};
        AstSenTree* const trigpSenp = new AstSenTree{flp, senItemp};
        topScopep->addSenTreep(trigpSenp);
        map[senTreep] = trigpSenp;

        // Add the trigger computation
        const auto& pair = senExprBuilder.build(senTreep);
        funcp->addStmtsp(
            new AstAssign{flp, getTrigRef(triggerNumber, VAccess::WRITE), pair.first});

        // Add initialization time trigger
        if (pair.second || v3Global.opt.xInitialEdge()) {
            AstNode* const assignp = new AstAssign{flp, getTrigRef(triggerNumber, VAccess::WRITE),
                                                   new AstConst{flp, 1}};
            initialTrigsp = AstNode::addNext(initialTrigsp, assignp);
        }

        // Add a debug statement for this trigger
        std::stringstream ss;
        V3EmitV::verilogForTree(senTreep, ss);
        addDebug(triggerNumber, ss.str());

        //
        ++triggerNumber;
    }
    // Add the update statements
    for (AstNodeStmt* const nodep : senExprBuilder.updates()) funcp->addStmtsp(nodep);

    // Add the initialization statements
    if (initialTrigsp) {
        AstVarScope* const vscp = scopeTopp->createTemp("__V" + name + "DidInit", 1);
        AstVarRef* const condp = new AstVarRef{flp, vscp, VAccess::READ};
        AstIf* const ifp = new AstIf{flp, new AstNot{flp, condp}};
        funcp->addStmtsp(ifp);
        ifp->branchPred(VBranchPred::BP_UNLIKELY);
        ifp->addIfsp(setVar(vscp, 1));
        ifp->addIfsp(initialTrigsp);
    }

    // Add the debug dumping section
    {
        AstTextBlock* const blockp = new AstTextBlock{flp};
        funcp->addStmtsp(blockp);
        const auto add = [&](const string& text) { blockp->addText(flp, text, true); };
        add("#ifdef VL_DEBUG\n");
        add("if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {\n");
        AstCMethodHard* const callp
            = new AstCMethodHard{flp, new AstVarRef{flp, vscp, VAccess::READ}, "any"};
        callp->dtypeSetBit();
        AstIf* const ifp = new AstIf{flp, callp};
        blockp->addNodep(ifp);
        ifp->addElsesp(
            new AstText{flp, "VL_DBG_MSGF(\"         No triggers active\\n\");\n", true});
        if (debugp) blockp->addNodep(debugp);
        add("}\n");
        add("#endif\n");
    }

    return {vscp, funcp, map};
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

AstNode* buildLoop(AstNetlist* netlistp, const string& name,
                   std::function<void(AstVarScope*, AstWhile*)> build)  //
{
    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();
    FileLine* const flp = scopeTopp->fileline();
    // Create the loop condition variable
    AstVarScope* const condp = scopeTopp->createTemp("__V" + name + "Continue", 1);
    // Initialize the loop condition variable to true
    AstNode* const resp = setVar(condp, 1);
    // Add the loop
    AstWhile* const loopp = new AstWhile{flp, new AstVarRef{flp, condp, VAccess::READ}};
    resp->addNext(loopp);
    // Clear the loop condition variable in the loop
    loopp->addBodysp(setVar(condp, 0));
    // Build the body
    build(condp, loopp);
    // Done
    return resp;
};

AstNode* incrementIterationCount(AstNetlist* netlistp, AstVarScope* cntp, const string& name) {
    FileLine* const flp = cntp->fileline();

    AstNode* resp = nullptr;

    // If we exceeded the iteration limit, die
    {
        AstTextBlock* const blockp = new AstTextBlock{flp};
        const uint32_t limit = v3Global.opt.convergeLimit();
        AstVarRef* const refp = new AstVarRef{flp, cntp, VAccess::READ};
        AstConst* const constp = new AstConst{flp, AstConst::DtypedValue{}, cntp->dtypep(), limit};
        AstNodeMath* const condp = new AstGt{flp, refp, constp};
        AstIf* const ifp = new AstIf{flp, condp, blockp};
        FileLine* const locp = netlistp->topModulep()->fileline();
        const string& file = EmitCBaseVisitor::protect(locp->filename());
        const string& line = cvtToStr(locp->lineno());
        const auto add = [&](const string& text) { blockp->addText(flp, text, true); };
        add("VL_FATAL_MT(\"" + file + "\", " + line + ", \"\", ");
        add("\"" + name + " region did not converge.\");\n");
        resp = ifp;
    }

    // Increment iteration count
    {
        AstVarRef* const wrefp = new AstVarRef{flp, cntp, VAccess::WRITE};
        AstVarRef* const rrefp = new AstVarRef{flp, cntp, VAccess::READ};
        AstConst* const onep = new AstConst{flp, AstConst::DtypedValue{}, cntp->dtypep(), 1};
        resp->addNext(new AstAssign{flp, wrefp, new AstAdd{flp, rrefp, onep}});
    }

    return resp;
};

std::pair<AstVarScope*, AstNode*> makeEvalLoop(AstNetlist* netlistp, const string& tag,
                                               const string& name, AstVarScope* trigVscp,
                                               std::function<AstNode*()> computeTriggers,
                                               std::function<AstNode*()> makeBody) {
    UASSERT_OBJ(trigVscp->dtypep()->basicp()->isTriggerVec(), trigVscp, "Not TRIGGERVEC");
    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();
    FileLine* const flp = scopeTopp->fileline();

    AstVarScope* const counterp = scopeTopp->createTemp("__V" + tag + "IterCount", 32);

    AstNode* nodep = setVar(counterp, 0);
    nodep->addNext(buildLoop(netlistp, tag, [&](AstVarScope* condp, AstWhile* loopp) {
        // Compute triggers
        loopp->addBodysp(computeTriggers());
        // Invoke body if triggered
        {
            AstVarRef* const refp = new AstVarRef{flp, trigVscp, VAccess::READ};
            AstCMethodHard* const callp = new AstCMethodHard{flp, refp, "any"};
            callp->dtypeSetBit();
            AstIf* const ifp = new AstIf{flp, callp};
            loopp->addBodysp(ifp);
            ifp->addIfsp(setVar(condp, 1));
            ifp->addIfsp(incrementIterationCount(netlistp, counterp, name));
            ifp->addIfsp(makeBody());
        }
    }));

    return {counterp, nodep};
}

void createSettle(AstNetlist* netlistp, AstCFunc* initp, LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_settle", true);

    // Clone, because ordering is destructive, but we still need them for "_eval"
    LogicByScope comb = logicClasses.m_comb.clone();
    LogicByScope hybrid = logicClasses.m_hybrid.clone();

    // Nothing to do if there is no logic.
    // While this is rare in real designs, it reduces noise in small tests.
    if (comb.empty() && hybrid.empty()) return;

    // Gather the relevant sensitivity expressions and create the trigger kit
    const auto& senTreeps = getSenTreesUsedBy({&comb, &hybrid});
    const TriggerKit& trig = createTriggers(netlistp, initp, senTreeps, "stl", 1, true);

    // Remap sensitivities (comb has none, so only do the hybrid)
    remapSensitivities(hybrid, trig.m_map);

    // First trigger is for pure combinational triggers (first iteration)
    AstSenTree* const inputChanged = trig.createFirstTriggerRef(netlistp);

    // Create and Order the body function
    AstCFunc* const stlFuncp = makeSubFunction(netlistp, "_eval_stl", true);
    const auto activeps
        = V3Order::orderST(netlistp, {&comb, &hybrid}, V3Order::OrderMode::Settle, inputChanged);
    for (AstActive* const activep : activeps) stlFuncp->addStmtsp(activep);

    // Dispose of the remnants of the inputs
    comb.deleteActives();
    hybrid.deleteActives();

    // Create the eval loop
    const auto& pair = makeEvalLoop(
        netlistp, "stl", "Settle", trig.m_vscp,
        [&]() {  // Trigger
            return new AstCCall{stlFuncp->fileline(), trig.m_funcp};
        },
        [&]() {  // Body
            return new AstCCall{stlFuncp->fileline(), stlFuncp};
        });

    // Add the first iteration trigger to the trigger computation function
    trig.addFirstIterationTriggerAssignment(pair.first);

    // Add the eval loop to the top function
    funcp->addStmtsp(pair.second);
}

AstNode* createInputCombLoop(AstNetlist* netlistp, AstCFunc* initp, LogicByScope& logic) {
    // Nothing to do if no combinational logic is sensitive to top level inputs
    if (logic.empty()) return nullptr;

    // Gather the relevant sensitivity expressions and create the trigger kit
    const auto& senTreeps = getSenTreesUsedBy({&logic});
    const TriggerKit& trig = createTriggers(netlistp, initp, senTreeps, "ico", 1);

    // Remap sensitivities
    remapSensitivities(logic, trig.m_map);

    // First trigger is for pure combinational triggers (first iteration)
    AstSenTree* const inputChanged = trig.createFirstTriggerRef(netlistp);

    // Create and Order the body function
    AstCFunc* const icoFuncp = makeSubFunction(netlistp, "_eval_ico", false);
    const auto activeps
        = V3Order::orderST(netlistp, {&logic}, V3Order::OrderMode::InputComb, inputChanged);
    for (AstActive* const activep : activeps) icoFuncp->addStmtsp(activep);

    // Dispose of the remnants of the inputs
    logic.deleteActives();

    // Create the eval loop
    const auto& pair = makeEvalLoop(
        netlistp, "ico", "Input combinational", trig.m_vscp,
        [&]() {  // Trigger
            return new AstCCall{icoFuncp->fileline(), trig.m_funcp};
        },
        [&]() {  // Body
            return new AstCCall{icoFuncp->fileline(), icoFuncp};
        });

    // Add the first iteration trigger to the trigger computation function
    trig.addFirstIterationTriggerAssignment(pair.first);

    // Return the eval loop itself
    return pair.second;
}

AstCFunc* createActive(AstNetlist* netlistp, LogicRegions& logicRegions, LogicByScope& replicas,
                       const std::unordered_map<const AstSenTree*, AstSenTree*>& preTrigMap,
                       const std::unordered_map<const AstSenTree*, AstSenTree*>& actTrigMap) {
    AstCFunc* const funcp = makeSubFunction(netlistp, "_eval_act", false);

    remapSensitivities(logicRegions.m_pre, preTrigMap);
    remapSensitivities(logicRegions.m_active, actTrigMap);
    remapSensitivities(replicas, actTrigMap);

    // TODO: there can only be a single ExecGraph right now, use it for the NBA
    const auto activeps
        = V3Order::orderST(netlistp, {&logicRegions.m_pre, &logicRegions.m_active, &replicas},
                           V3Order::OrderMode::ActiveRegion);
    for (AstActive* const activep : activeps) funcp->addStmtsp(activep);

    // Dispose of the remnants of the inputs
    logicRegions.m_pre.deleteActives();
    logicRegions.m_active.deleteActives();
    replicas.deleteActives();

    return funcp;
}

AstCFunc* createNBA(AstNetlist* netlistp, LogicRegions& logicRegions, LogicByScope& replicas,
                    const std::unordered_map<const AstSenTree*, AstSenTree*>& nbaTrigMap) {
    AstCFunc* const funcp = makeSubFunction(netlistp, "_eval_nba", false);

    remapSensitivities(logicRegions.m_nba, nbaTrigMap);
    remapSensitivities(replicas, nbaTrigMap);

    // Order it
    if (v3Global.opt.mtasks()) {
        AstExecGraph* const execGraphp = V3Order::orderMT(
            netlistp, {&logicRegions.m_nba, &replicas}, V3Order::OrderMode::NBARegion);
        funcp->addStmtsp(execGraphp);
    } else {
        const auto activeps = V3Order::orderST(netlistp, {&logicRegions.m_nba, &replicas},
                                               V3Order::OrderMode::NBARegion);
        for (AstActive* const activep : activeps) funcp->addStmtsp(activep);
    }

    // Dispose of the remnants of the inputs
    logicRegions.m_nba.deleteActives();
    replicas.deleteActives();

    return funcp;
}

void createEval(AstNetlist* netlistp,  //
                AstNode* icoLoop,  //
                const TriggerKit& actTrig,  //
                AstVarScope* preTrigsp,  //
                AstVarScope* nbaTrigsp,  //
                AstCFunc* actFuncp,  //
                AstCFunc* nbaFuncp  //
) {
    FileLine* const flp = netlistp->fileline();
    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();

    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval", false);
    netlistp->evalp(funcp);

    // Start with the ico loop, if any
    if (icoLoop) funcp->addStmtsp(icoLoop);

    // Create the active eval loop
    AstNode* const activeEvalLoopp
        = makeEvalLoop(
              netlistp, "act", "Active", actTrig.m_vscp,
              [&]() {  // Trigger
                  return new AstCCall{flp, actTrig.m_funcp};
              },
              [&]() {  // Body
                  AstNode* resultp = nullptr;

                  // Compute the pre triggers
                  {
                      AstVarRef* const lhsp = new AstVarRef{flp, preTrigsp, VAccess::WRITE};
                      AstVarRef* const opap = new AstVarRef{flp, actTrig.m_vscp, VAccess::READ};
                      AstVarRef* const opbp = new AstVarRef{flp, nbaTrigsp, VAccess::READ};
                      opap->addNext(opbp);
                      AstCMethodHard* const callp = new AstCMethodHard{flp, lhsp, "andNot", opap};
                      callp->statement(true);
                      callp->dtypeSetVoid();
                      resultp = AstNode::addNext(resultp, callp);
                  }

                  // Latch the active trigger flags under the NBA trigger flags
                  {
                      AstVarRef* const lhsp = new AstVarRef{flp, nbaTrigsp, VAccess::WRITE};
                      AstVarRef* const argp = new AstVarRef{flp, actTrig.m_vscp, VAccess::READ};
                      AstCMethodHard* const callp = new AstCMethodHard{flp, lhsp, "set", argp};
                      callp->statement(true);
                      callp->dtypeSetVoid();
                      resultp = AstNode::addNext(resultp, callp);
                  }

                  // Invoke body function
                  return AstNode::addNext(resultp, new AstCCall{flp, actFuncp});
              })
              .second;

    // Create the NBA eval loop. This uses the Active eval loop in the trigger section.
    AstNode* const nbaEvalLoopp
        = makeEvalLoop(
              netlistp, "nba", "NBA", nbaTrigsp,
              [&]() {  // Trigger
                  AstNode* resultp = nullptr;

                  // Reset NBA triggers
                  {
                      AstVarRef* const refp = new AstVarRef{flp, nbaTrigsp, VAccess::WRITE};
                      AstCMethodHard* const callp = new AstCMethodHard{flp, refp, "clear"};
                      callp->statement(true);
                      callp->dtypeSetVoid();
                      resultp = AstNode::addNext(resultp, callp);
                  }

                  // Run the Active eval loop
                  return AstNode::addNext(resultp, activeEvalLoopp);
              },
              [&]() {  // Body
                  return new AstCCall{flp, nbaFuncp};
              })
              .second;

    // Add the NBA eval loop
    funcp->addStmtsp(nbaEvalLoopp);
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
        addSizeStat("size of class: final", logicClasses.m_final);
    }

    createStatic(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-static");

    AstCFunc* const initp = createInitial(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-initial");

    createFinal(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-final");

    // Note: breakCycles also removes corresponding logic from logicClasses.m_comb;
    logicClasses.m_hybrid = breakCycles(netlistp, logicClasses.m_comb);
    if (v3Global.opt.stats()) {
        addSizeStat("size of class: clocked", logicClasses.m_clocked);
        addSizeStat("size of class: combinational", logicClasses.m_comb);
        addSizeStat("size of class: hybrid", logicClasses.m_hybrid);
        V3Stats::statsStage("sched-break-cycles");
    }

    createSettle(netlistp, initp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-settle");

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

    AstNode* const icoLoopp = createInputCombLoop(netlistp, initp, logicReplicas.m_input);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-ico");

    const auto& senTreeps = getSenTreesUsedBy({&logicRegions.m_pre,  //
                                               &logicRegions.m_active,  //
                                               &logicRegions.m_nba});
    const auto& actTrig = createTriggers(netlistp, initp, senTreeps, "act", 0);

    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();

    AstVarScope* const actTrigVscp = actTrig.m_vscp;
    AstVarScope* const preTrigVscp = scopeTopp->createTempLike("__VpreTriggered", actTrigVscp);
    AstVarScope* const nbaTrigVscp = scopeTopp->createTempLike("__VnbaTriggered", actTrigVscp);

    const auto cloneMapWithNewTriggerReferences
        = [=](std::unordered_map<const AstSenTree*, AstSenTree*> map, AstVarScope* vscp) {
              // Copy map
              auto newMap{map};
              VNDeleter deleter;
              // Replace references in each mapped value with a reference to the given vscp
              for (auto& pair : newMap) {
                  pair.second = pair.second->cloneTree(false);
                  pair.second->foreach<AstVarRef>([&](AstVarRef* refp) {
                      UASSERT_OBJ(refp->varScopep() == actTrigVscp, refp, "Unexpected reference");
                      UASSERT_OBJ(refp->access() == VAccess::READ, refp, "Should be read ref");
                      refp->replaceWith(new AstVarRef{refp->fileline(), vscp, VAccess::READ});
                      deleter.pushDeletep(refp);
                  });
                  topScopep->addSenTreep(pair.second);
              }
              return newMap;
          };

    const auto& actTrigMap = actTrig.m_map;
    const auto preTrigMap = cloneMapWithNewTriggerReferences(actTrigMap, preTrigVscp);
    const auto nbaTrigMap = cloneMapWithNewTriggerReferences(actTrigMap, nbaTrigVscp);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-triggers");

    AstCFunc* const actFuncp
        = createActive(netlistp, logicRegions, logicReplicas.m_active, preTrigMap, actTrigMap);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-act");

    AstCFunc* const nbaFuncp = createNBA(netlistp, logicRegions, logicReplicas.m_nba, nbaTrigMap);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-nba");

    createEval(netlistp, icoLoopp, actTrig, preTrigVscp, nbaTrigVscp, actFuncp, nbaFuncp);

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
