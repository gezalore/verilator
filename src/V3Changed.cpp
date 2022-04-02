// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for changed nodes
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
// V3Changed's Transformations:
//
// Each module:
//      Each combo block
//          For each variable that comes from combo block and is generated AFTER a usage
//              Add __Vlast_{var} to local section, init to current value (just use array?)
//              Change = if any var != last.
//          If a signal is used as a clock in this module or any
//          module *below*, and it isn't a input to this module,
//          we need to indicate a new clock has been created.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Ast.h"
#include "V3Changed.h"
#include "V3EmitCBase.h"
#include "V3Sched.h"

#include <algorithm>

//######################################################################

class ChangedState final {
public:
    // STATE
    AstScope* const m_scopetopp;  // The top level AstScope
    AstEval* m_evalp;  // The AstEval being converted
    AstCFunc* m_snapFuncp = nullptr;  // Change detect snapshot function
    AstCFunc* m_tlSnapFuncp = nullptr;  // Top level change detect snapshot function
    AstCFunc* m_checkFuncp = nullptr;  // Change detect check function
    AstCFunc* m_tlCheckFuncp = nullptr;  // Top level change detect check function
    int m_numStmts = 0;  // Number of statements added to the sub-functions
    int m_funcNum = 0;  // Number of change functions emitted

    ChangedState(AstNetlist* netlistp, AstEval* evalp)
        : m_scopetopp{netlistp->topScopep()->scopep()}
        , m_evalp{evalp} {}

    void maybeCreateChgFuncp() {
        maybeCreateTopChg();
        maybeCreateMidChg();
    }

private:
    AstCFunc* newFunction(const string& name, const string& returnType) {
        FileLine* const flp = m_scopetopp->fileline();
        AstCFunc* const cfuncp = new AstCFunc{flp, name, m_scopetopp, returnType};
        cfuncp->isStatic(false);
        cfuncp->isLoose(true);
        cfuncp->slow(m_evalp->isSlow());
        cfuncp->declPrivate(true);
        m_scopetopp->addActivep(cfuncp);
        return cfuncp;
    };

    void maybeCreateTopChg() {
        UASSERT(!!m_tlSnapFuncp == !!m_tlCheckFuncp, "Inconsistent");
        if (m_tlSnapFuncp) return;

        // Create the main change detection functions
        m_tlSnapFuncp = newFunction(m_evalp->name() + "__change_snapshot", "");
        m_tlCheckFuncp = newFunction(m_evalp->name() + "__change_check", "QData");

        // TODO: really???
        // Each change detection function needs at least one AstChangeDet
        // to ensure that V3EmitC outputs the necessary code.
        maybeCreateMidChg();
        m_checkFuncp->addStmtsp(new AstChangeDet{m_scopetopp->fileline(), nullptr, nullptr});
    }
    void maybeCreateMidChg() {
        // Don't create an extra function call if splitting is disabled
        if (!v3Global.opt.outputSplitCFuncs()) {
            m_snapFuncp = m_tlSnapFuncp;
            m_checkFuncp = m_tlCheckFuncp;
            return;
        }

        if (!m_checkFuncp || v3Global.opt.outputSplitCFuncs() < m_numStmts) {
            m_numStmts = 0;

            FileLine* const flp = m_scopetopp->fileline();

            // Create the sub-functions
            const string suffix{"__" + cvtToStr(m_funcNum)};
            m_snapFuncp = newFunction(m_evalp->name() + "__change_snapshot" + suffix, "");
            m_checkFuncp = newFunction(m_evalp->name() + "__change_check" + suffix, "QData");
            ++m_funcNum;

            // Add a calls from the top functions
            AstCCall* const initCallp = new AstCCall{flp, m_snapFuncp};
            AstCCall* const cdetCallp = new AstCCall{flp, m_checkFuncp};

            m_tlSnapFuncp->addStmtsp(initCallp);

            if (AstCReturn* const returnp = VN_AS(m_tlCheckFuncp->stmtsp(), CReturn)) {
                // This is currently using AstLogOr which will shortcut the evaluation if any
                // function returns true. This is likely what we want and is similar to the logic
                // already in use inside V3EmitC, however, it also means that verbose logging may
                // not print change detect variables.
                returnp->lhsp(new AstLogOr{flp, returnp->lhsp()->unlinkFrBack(), cdetCallp});
            } else {
                m_tlCheckFuncp->addStmtsp(new AstCReturn{flp, cdetCallp});
            }
        }
    }
};

//######################################################################
// Utility visitor to find elements to be compared

class ChangedInsertVisitor final : public VNVisitor {
    // NODE STATE
    // AstVarScope::user2p()    -> New (change detect) AstVarScope*

    // STATE
    ChangedState& m_state;  // Shared state across visitors
    AstVarScope* const m_vscp;  // Original (non-change) variable we're change-detecting
    AstVarScope* const m_newvscp;  // New (change detect) variable we're change-detecting
    AstNode* m_varEqnp = nullptr;  // Original var's equation to get var value
    AstNode* m_newLvEqnp = nullptr;  // New var's equation to read value
    AstNode* m_newRvEqnp = nullptr;  // New var's equation to set value
    uint32_t m_detects = 0;  // # detects created

    // CONSTANTS
    // How many indexes before error. Ok to increase this, but may result in much slower model
    static constexpr uint32_t DETECTARRAY_MAX_INDEXES = 256;

    void newChangeDet() {
        if (++m_detects > DETECTARRAY_MAX_INDEXES) {
            m_vscp->v3warn(E_DETECTARRAY,
                           "Unsupported: Can't detect more than "
                               << DETECTARRAY_MAX_INDEXES
                               << " array indexes (probably with UNOPTFLAT warning suppressed): "
                               << m_vscp->prettyName() << '\n'
                               << m_vscp->warnMore()
                               << "... Could recompile with DETECTARRAY_MAX_INDEXES increased");
            return;
        }
        m_state.maybeCreateChgFuncp();

        AstChangeDet* const changep = new AstChangeDet{
            m_vscp->fileline(), m_varEqnp->cloneTree(true), m_newRvEqnp->cloneTree(true)};
        m_state.m_checkFuncp->addStmtsp(changep);
        AstAssign* const initp = new AstAssign{m_vscp->fileline(), m_newLvEqnp->cloneTree(true),
                                               m_varEqnp->cloneTree(true)};
        m_state.m_snapFuncp->addFinalsp(initp);

        // Later code will expand words which adds to GCC compile time,
        // so add penalty based on word width also
        m_state.m_numStmts += initp->nodeCount() + m_varEqnp->widthWords();
    }

    static AstVarScope* getLastVarScope(AstScope* scopep, AstVarScope* vscp) {
        if (!vscp->user2p()) {
            AstVar* const varp = vscp->varp();
            const string newvarname{"__Vchglast__" + vscp->scopep()->nameDotless() + "__"
                                    + varp->shortName()};
            AstVar* const newvarp
                = new AstVar{varp->fileline(), VVarType::MODULETEMP, newvarname, varp};
            scopep->modp()->addStmtp(newvarp);
            AstVarScope* const newVscp = new AstVarScope{vscp->fileline(), scopep, newvarp};
            scopep->addVarp(newVscp);
            vscp->user2p(newVscp);
        }
        return VN_AS(vscp->user2p(), VarScope);
    }

    virtual void visit(AstBasicDType*) override {  //
        newChangeDet();
    }
    virtual void visit(AstPackArrayDType*) override {  //
        newChangeDet();
    }
    virtual void visit(AstUnpackArrayDType* nodep) override {
        for (int index = 0; index < nodep->elementsConst(); ++index) {
            VL_RESTORER(m_varEqnp);
            VL_RESTORER(m_newLvEqnp);
            VL_RESTORER(m_newRvEqnp);
            {
                m_varEqnp = new AstArraySel{nodep->fileline(), m_varEqnp->cloneTree(true), index};
                m_newLvEqnp
                    = new AstArraySel{nodep->fileline(), m_newLvEqnp->cloneTree(true), index};
                m_newRvEqnp
                    = new AstArraySel{nodep->fileline(), m_newRvEqnp->cloneTree(true), index};

                iterate(nodep->subDTypep()->skipRefp());

                m_varEqnp->deleteTree();
                m_newLvEqnp->deleteTree();
                m_newRvEqnp->deleteTree();
            }
        }
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        if (nodep->packedUnsup()) {
            newChangeDet();
        } else {
            if (debug()) nodep->dumpTree(cout, "-DETECTARRAY-class-");
            m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable"
                                          " (probably with UNOPTFLAT warning suppressed): "
                                              << m_vscp->varp()->prettyNameQ());
        }
    }
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        if (debug()) nodep->dumpTree(cout, "-DETECTARRAY-general-");
        m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable"
                                      " (probably with UNOPTFLAT warning suppressed): "
                                          << m_vscp->varp()->prettyNameQ());
    }

public:
    // CONSTRUCTORS
    ChangedInsertVisitor(AstVarScope* vscp, ChangedState& state)
        : m_state{state}
        , m_vscp{vscp}
        , m_newvscp(getLastVarScope(state.m_scopetopp, vscp)) {
        // DPI export trigger should never need change detect. See similar assertions in V3Order
        // (OrderVisitor::nodeMarkCircular), and V3GenClk (GenClkRenameVisitor::genInpClk).
        UASSERT_OBJ(vscp != v3Global.rootp()->dpiExportTriggerp(), vscp,
                    "DPI export trigger should not need change detect");
        m_varEqnp = new AstVarRef{m_vscp->fileline(), m_vscp, VAccess::READ};
        m_newLvEqnp = new AstVarRef{m_vscp->fileline(), m_newvscp, VAccess::WRITE};
        m_newRvEqnp = new AstVarRef{m_vscp->fileline(), m_newvscp, VAccess::READ};
        iterate(vscp->dtypep()->skipRefp());
        m_varEqnp->deleteTree();
        m_newLvEqnp->deleteTree();
        m_newRvEqnp->deleteTree();
    }
    virtual ~ChangedInsertVisitor() override = default;
    VL_UNCOPYABLE(ChangedInsertVisitor);
};

class ChangedConsVisitor final : public VNVisitor {
    // NOTE STATE:
    //   AstVarScope::user1() -> bool: already processed
    const VNUser1InUse user1InUse;

    // STATE
    ChangedState m_state;  // Shared state across visitors

    // VISIT methods
    virtual void visit(AstVarRef* nodep) override {
        AstVarScope* const vscp = nodep->varScopep();
        if (vscp->isCircular() && !vscp->user1SetOnce()) {
            vscp->v3warn(IMPERFECTSCH,
                         "Imperfect scheduling of variable: " << vscp->prettyNameQ());
            ChangedInsertVisitor{vscp, m_state};
        }
    }

    virtual void visit(AstCCall* nodep) override {
        iterateChildren(nodep);
        iterate(nodep->funcp());
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTOR
    explicit ChangedConsVisitor(AstNetlist* netlistp, AstEval* evalp)
        : m_state{netlistp, evalp} {
        iterate(evalp);
    }

public:
    static std::pair<AstCFunc*, AstCFunc*> main(AstNetlist* netlistp, AstEval* evalp) {
        ChangedConsVisitor visitor{netlistp, evalp};
        return {visitor.m_state.m_tlSnapFuncp, visitor.m_state.m_tlCheckFuncp};
    }
};

static AstVarScope* createVar(AstScope* scopep, const string& name, unsigned width) {
    FileLine* const flp = scopep->fileline();
    AstVar* const newvarp
        = new AstVar{flp, VVarType::MODULETEMP, name, VFlagBitPacked{}, static_cast<int>(width)};
    scopep->modp()->addStmtp(newvarp);
    AstVarScope* const newvscp = new AstVarScope{flp, scopep, newvarp};
    scopep->addVarp(newvscp);
    return newvscp;
}

//######################################################################
// Changed class functions

void V3Changed::changedAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    const VNUser2InUse user2InUse;  // Used by ChangedInsertVisitor

    AstScope* const scopeTopp = netlistp->topScopep()->scopep();

    const auto makeFuncp = [&](const string& name, bool slow) {
        AstCFunc* const funcp = new AstCFunc{netlistp->fileline(), name, scopeTopp};
        scopeTopp->addActivep(funcp);
        funcp->dontCombine(true);
        funcp->isLoose(true);
        funcp->slow(slow);
        funcp->isConst(false);
        funcp->declPrivate(true);
        return funcp;
    };

    AstCFunc* actFuncp = nullptr;
    AstCFunc* nbaFuncp = nullptr;

    // All AstEval are under the top level AstScope
    for (AstNode *nodep = scopeTopp->blocksp(), *nextp; nodep; nodep = nextp) {
        nextp = nodep->nextp();
        if (AstEval* const evalp = VN_CAST(nodep, Eval)) {
            // Construct change detect functions for this eval
            AstCFunc* cdSnapFuncp = nullptr;
            AstCFunc* cdCheckFuncp = nullptr;
            if (evalp->kind() == VEvalKind::SETTLE) {
                const auto& pair = ChangedConsVisitor::main(netlistp, evalp);
                cdSnapFuncp = pair.first;
                cdCheckFuncp = pair.second;
            }
            UASSERT_OBJ(!!cdSnapFuncp == !!cdCheckFuncp, evalp, "Inconsistent");

            FileLine* const flp = evalp->fileline();

            // Create the top level function
            AstCFunc* const topFuncp = makeFuncp(evalp->name(), evalp->isSlow());

            switch (evalp->kind().m_e) {
            case VEvalKind::ACTIVE: actFuncp = topFuncp; break;
            case VEvalKind::NBA: nbaFuncp = topFuncp; break;
            default: topFuncp->entryPoint(true); break;
            }

            if (evalp->initp()) topFuncp->addStmtsp(evalp->initp()->unlinkFrBackWithNext());

            if (cdSnapFuncp) {
                // A change detect loop is required. Create a sub-function for the body
                AstCFunc* const subFuncp = makeFuncp(evalp->name() + "__body", evalp->isSlow());

                // Move the body under the sub-function
                if (evalp->bodyp()) subFuncp->addStmtsp(evalp->bodyp()->unlinkFrBackWithNext());
                if (evalp->finalp()) subFuncp->addStmtsp(evalp->finalp()->unlinkFrBackWithNext());

                // Split it if needed
                V3Sched::splitCheck(subFuncp);

                // Create the change detect loop
                {
                    // Create the iteration count variable, and initialize it to zero
                    AstVarScope* const loopCntVscp
                        = createVar(scopeTopp, "__ViterationCount__" + evalp->name(), 32);
                    topFuncp->addStmtsp(
                        new AstAssign{flp, new AstVarRef{flp, loopCntVscp, VAccess::WRITE},
                                      new AstConst{flp, AstConst::WidthedValue{}, 32, 0}});

                    // Create the change variable, and initialize it to non-zero
                    AstVarScope* const changeVscp
                        = createVar(scopeTopp, "__Vchange__" + evalp->name(), 64);
                    topFuncp->addStmtsp(
                        new AstAssign{flp, new AstVarRef{flp, changeVscp, VAccess::WRITE},
                                      new AstConst{flp, AstConst::WidthedValue{}, 64, 1}});

                    // Create the loop
                    AstWhile* const whilep = new AstWhile{
                        flp, new AstVarRef{flp, changeVscp, VAccess::READ}, nullptr};
                    topFuncp->addStmtsp(whilep);

                    // If we exceeded the iteration limit, die

                    {
                        AstTextBlock* const blockp = new AstTextBlock{flp};
                        AstIf* const ifp = new AstIf{
                            flp,
                            new AstGt{
                                flp, new AstVarRef{flp, loopCntVscp, VAccess::READ},
                                new AstConst{flp, AstConst::WidthedValue{}, 32,
                                             static_cast<uint32_t>(v3Global.opt.convergeLimit())}},
                            blockp};
                        whilep->addBodysp(ifp);
                        const auto add
                            = [&](const string& text) { blockp->addText(flp, text, true); };
                        FileLine* const locp = netlistp->topModulep()->fileline();
                        add("VL_FATAL_MT(\"");
                        add(EmitCBaseVisitor::protect(locp->filename()));
                        add("\", ");
                        add(cvtToStr(locp->lineno()));
                        add(", \"\",\n");
                        add("\"Verilated model didn't converge (" + evalp->name() + ")\\n\"\n");
                        add("\"- See https://verilator.org/warn/DIDNOTCONVERGE\");\n");
                    }

                    // Increment iteration count
                    whilep->addBodysp(new AstAssign{
                        flp, new AstVarRef{flp, loopCntVscp, VAccess::WRITE},
                        new AstAdd{flp, new AstVarRef{flp, loopCntVscp, VAccess::READ},
                                   new AstConst{flp, AstConst::WidthedValue{}, 32, 1}}});

                    // Call the change detect snapshot function
                    whilep->addBodysp(new AstCCall{flp, cdSnapFuncp});

                    // Call the body function
                    whilep->addBodysp(new AstCCall{flp, subFuncp});

                    // Call the change detect check
                    whilep->addBodysp(new AstAssign{flp,
                                                    new AstVarRef{flp, changeVscp, VAccess::WRITE},
                                                    new AstCCall{flp, cdCheckFuncp}});
                }
            } else {
                // No change detect needed. Simply use the top function as the body.
                if (evalp->bodyp()) topFuncp->addStmtsp(evalp->bodyp()->unlinkFrBackWithNext());
                if (evalp->finalp()) topFuncp->addStmtsp(evalp->finalp()->unlinkFrBackWithNext());

                // Split it if needed
                V3Sched::splitCheck(topFuncp);
            }

            evalp->unlinkFrBack();
            evalp->deleteTree();
        }
    }

    FileLine* const flp = netlistp->fileline();

    AstCFunc* const funcp = makeFuncp("_eval", false);
    funcp->entryPoint(true);
    netlistp->evalp(funcp);

    if (AstCFunc* const evalIncombp = netlistp->evalIncombp()) {
        funcp->addStmtsp(new AstCCall{flp, evalIncombp});
    }

    const auto setVar = [&](AstVarScope* cntp, uint32_t val) {
        AstVarRef* const refp = new AstVarRef{flp, cntp, VAccess::WRITE};
        AstConst* const zerop = new AstConst{flp, AstConst::DtypedValue{}, cntp->dtypep(), val};
        return new AstAssign{flp, refp, zerop};
    };

    const auto buildLoop
        = [&](const string& name, std::function<void(AstVarScope*, AstWhile*)> build)  //
    {
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

    const auto makeRegionIf = [&](AstVarScope* cntp, AstVarScope* trigsp) {
        AstVarRef* const refp = new AstVarRef{flp, trigsp, VAccess::READ};
        AstCMethodHard* const callp = new AstCMethodHard{flp, refp, "any"};
        callp->dtypeSetBit();
        return new AstIf{flp, callp};
    };

    const auto incrementIterationCount = [&](AstVarScope* cntp, const string& name) {
        AstNode* resp = nullptr;

        // If we exceeded the iteration limit, die
        {
            AstTextBlock* const blockp = new AstTextBlock{flp};
            const uint32_t limit = v3Global.opt.convergeLimit();
            AstVarRef* const refp = new AstVarRef{flp, cntp, VAccess::READ};
            AstConst* const constp
                = new AstConst{flp, AstConst::DtypedValue{}, cntp->dtypep(), limit};
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

    AstVarScope* const preTrigsp = netlistp->preTrigsp();
    AstVarScope* const actTrigsp = netlistp->actTrigsp();
    AstVarScope* const nbaTrigsp = netlistp->nbaTrigsp();
    AstVarScope* const actCountp = netlistp->actCountp();
    AstVarScope* const nbaCountp = netlistp->nbaCountp();

    // Reset nbaCount
    funcp->addStmtsp(setVar(nbaCountp, 0));

    // Add NBA Region loop
    funcp->addStmtsp(buildLoop("nba", [&](AstVarScope* nbaCondp, AstWhile* nbaLoopp) {  //
        // Reset actCount
        nbaLoopp->addBodysp(setVar(actCountp, 0));
        // Add Active Region
        nbaLoopp->addBodysp(buildLoop("act", [&](AstVarScope* actCondp, AstWhile* actLoopp) {  //
            // Compute triggers
            actLoopp->addBodysp(new AstCCall{flp, netlistp->compTrigsp()});
            // Invoke Active region eval if triggered
            {
                AstIf* const ifp = makeRegionIf(actCountp, actTrigsp);
                actLoopp->addBodysp(ifp);
                ifp->addIfsp(setVar(actCondp, 1));
                ifp->addIfsp(incrementIterationCount(actCountp, "Active"));

                // Compute the pre triggers
                {
                    AstVarRef* const lhsp = new AstVarRef{flp, preTrigsp, VAccess::WRITE};
                    AstVarRef* const opap = new AstVarRef{flp, actTrigsp, VAccess::READ};
                    AstVarRef* const opbp = new AstVarRef{flp, nbaTrigsp, VAccess::READ};
                    opap->addNext(opbp);
                    AstCMethodHard* const callp = new AstCMethodHard{flp, lhsp, "andNot", opap};
                    callp->statement(true);
                    callp->dtypeSetVoid();
                    ifp->addIfsp(callp);
                }

                // Latch the active trigger flags under the NBA trigger flags
                {
                    AstVarRef* const lhsp = new AstVarRef{flp, nbaTrigsp, VAccess::WRITE};
                    AstVarRef* const argp = new AstVarRef{flp, actTrigsp, VAccess::READ};
                    AstCMethodHard* const callp = new AstCMethodHard{flp, lhsp, "set", argp};
                    callp->statement(true);
                    callp->dtypeSetVoid();
                    ifp->addIfsp(callp);
                }

                ifp->addIfsp(new AstCCall{flp, actFuncp});
            }
        }));
        // Invoke NBA region eval if triggered
        {
            AstIf* const ifp = makeRegionIf(nbaCountp, nbaTrigsp);
            nbaLoopp->addBodysp(ifp);
            ifp->addIfsp(incrementIterationCount(nbaCountp, "NBA"));
            ifp->addIfsp(setVar(nbaCondp, 1));
            ifp->addIfsp(new AstCCall{flp, nbaFuncp});
        }
    }));

    netlistp->preTrigsp(nullptr);
    netlistp->actTrigsp(nullptr);
    netlistp->nbaTrigsp(nullptr);
    netlistp->actCountp(nullptr);
    netlistp->nbaCountp(nullptr);

    V3Global::dumpCheckGlobalTree("changed", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
