// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generated Clock repairs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// GENCLK TRANSFORMATIONS:
//
// Follow code execution path. Any clock (variable referenced in a
// sensitivity list) that is assigned after it's used as a clock will
// be replaced with a delayed signal and a change detect added (by marking
// circular).
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3GenClk.h"
#include "V3Ast.h"

//######################################################################
// GenClk state, as a visitor of each AstNode

class GenClkBaseVisitor VL_NOT_FINAL : public AstNVisitor {
protected:
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// GenClk Read

class GenClkRenameVisitor final : public GenClkBaseVisitor {
    // NODE STATE
    // AstVarScope::user2p() -> AstVarScope*. Replacement clock signal to be used in
    //                          sensitivity lists.
    // AstStenTree::user3()  -> Flag indicating already processed.
    AstUser2InUse m_user2InUse;

    // STATE
    AstNodeModule* const m_topModp;  // Top module
    AstScope* m_scopetopp = nullptr;  // AstScope under AstTopScope
    bool m_inSenTree = false;  // Walking an AstSenTree

    // METHODS
    AstVarScope* genInpClk(AstVarScope* vscp) {
        if (!vscp->user2p()) {
            // In order to create a __VinpClk* for a signal, it needs to be marked circular.
            // The DPI export trigger is never marked circular by V3Order (see comments in
            // OrderVisitor::nodeMarkCircular). The only other place where one might mark
            // a node circular is in this pass (V3GenClk), if the signal is assigned but was
            // previously used as a clock. The DPI export trigger is only ever assigned in
            // a DPI export called from outside eval, or from a DPI import, which are not
            // discovered by GenClkReadVisitor (note that impure tasks - i.e.: those setting
            // non-local variables - cannot be no-inline, see V3Task), hence the DPI export
            // trigger should never be marked circular. Note that ordering should still be
            // correct as there will be a change detect on any signals set from a DPI export
            // that might have dependents scheduled earlier.
            UASSERT_OBJ(vscp != v3Global.rootp()->dpiExportTriggerp(), vscp,
                        "DPI export trigger should not need __VinpClk");

            AstVar* const varp = vscp->varp();
            const string newvarname
                = "__VinpClk__" + vscp->scopep()->nameDotless() + "__" + varp->name();
            AstVar* const newvarp
                = new AstVar(varp->fileline(), AstVarType::MODULETEMP, newvarname, varp);
            m_topModp->addStmtp(newvarp);
            AstVarScope* const newvscp = new AstVarScope(vscp->fileline(), m_scopetopp, newvarp);
            m_scopetopp->addVarp(newvscp);
            AstAssign* const assignp = new AstAssign(
                vscp->fileline(), new AstVarRef(vscp->fileline(), newvscp, VAccess::WRITE),
                new AstVarRef(vscp->fileline(), vscp, VAccess::READ));
            m_scopetopp->addFinalClkp(assignp);
            vscp->user2p(newvscp);
        }
        return vscp->user2u().to<AstVarScope*>();
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep) override {
        m_scopetopp = nodep->scopep();
        UASSERT_OBJ(m_scopetopp, nodep, "No scope found on top level");
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstActive* nodep) override {}  // Accelerate
    virtual void visit(AstNodeAssign* nodep) override {}  // Accelerate

    //----
    virtual void visit(AstSenTree* nodep) override {
        m_inSenTree = true;
        iterateChildren(nodep);
        m_inSenTree = false;
    }

    virtual void visit(AstVarRef* nodep) override {
        AstVarScope* const vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");
        if (m_inSenTree && vscp->isCircular()) {
            // Replace with the new variableS
            AstVarScope* const newvscp = genInpClk(vscp);
            AstVarRef* const newrefp = new AstVarRef(nodep->fileline(), newvscp, nodep->access());
            nodep->replaceWith(newrefp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    //-----

public:
    // CONSTRUCTORS
    GenClkRenameVisitor(AstNetlist* nodep)
        : m_topModp{nodep->topModulep()} {
        iterate(nodep);
    }
    virtual ~GenClkRenameVisitor() override = default;
};

//######################################################################
// GenClk Read

class GenClkReadVisitor final : public GenClkBaseVisitor {
    // NODE STATE
    // AstVarScope::user() -> bool. Set on variables read in a sensitivity list (i.e.: on clocks)
    AstUser1InUse m_user1InUse;

    // STATE
    bool m_inSenseList = false;  // Walking the sensitivity list of an AstActive
    bool m_inAssign = false;  // Walking under an AstNodeAssign

    // VISITORS

    // Trace execution path
    virtual void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(nodep->isTop(), nodep, "Only the top module should be visited");
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);
        // Analyse the body of the callee
        if (!nodep->funcp()->entryPoint()) iterateChildrenConst(nodep->funcp());
    }
    virtual void visit(AstCFunc* nodep) override {
        // We are trying to trace execution order, so only start from functions
        // that are entry points. Other function bodies will be visited when called.
        if (nodep->entryPoint()) iterateChildrenConst(nodep);
    }
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
    virtual void visit(AstSenTree* nodep) override {}  // Accelerate (we want them in code order)

    // Mark variables that were previously used as clock, but written later
    virtual void visit(AstVarRef* nodep) override {
        AstVarScope* const vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");

        if (m_inSenseList) {
            // Variable reference in a sensitivity list. Mark as clock.
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Sensitivity list writes clock");
            vscp->user1(true);
            return;
        }

        if (m_inAssign && nodep->access().isWriteOrRW() && vscp->user1()) {
            // TODO: why do we check only under assignments?
            // Variable was previously used as a clock, and is now being set,
            // thus it is an unordered generated clock...
            UINFO(8, "  VarSetAct " << nodep << endl);
            vscp->circular(true);
        }
    }
    virtual void visit(AstActive* nodep) override {
        m_inSenseList = true;
        iterateChildrenConst(nodep->sensesp());
        m_inSenseList = false;
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstNodeAssign* nodep) override {
        m_inAssign = true;
        iterateChildrenConst(nodep);
        m_inAssign = false;
    }

public:
    // CONSTRUCTORS
    explicit GenClkReadVisitor(AstNetlist* nodep) {
        // Trace execution and mark problematic clock
        iterate(nodep->topModulep());
        // Create the new clock signals and replace any references in sensitivity lists
        GenClkRenameVisitor visitor{nodep};
    }
    virtual ~GenClkReadVisitor() override = default;
};

//######################################################################
// GenClk class functions

void V3GenClk::genClkAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { GenClkReadVisitor visitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("genclk", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
