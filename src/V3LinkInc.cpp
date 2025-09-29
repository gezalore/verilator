// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replace increments/decrements with new variables
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3LinkInc's Transformations:
//
//      prepost_expr_visit
//        PREADD/PRESUB
//          Create a temporary __VIncrementX variable, assign the value of
//          the current variable value to it, substitute the current
//          variable with the temporary one in the statement.
//          Increment/decrement the original variable with by the given
//          value.
//        POSTADD/POSTSUB
//          Increment/decrement the current variable by the given value.
//          Create a temporary __VIncrementX variable, assign the value of
//          of the current variable (after the operation) to it. Substitute
//          The original variable with the temporary one in the statement.
//
//      prepost_stmt_visit
//        PREADD/PRESUB/POSTADD/POSTSUB
//          Increment/decrement the current variable by the given value.
//          The order (pre/post) doesn't matter outside statements thus
//          the pre/post operations are treated equally and there is no
//          need for a temporary variable.
//
//      prepost_stmt_sel_visit
//        For e.g. 'array[something_with_side_eff]++', common in UVM etc
//        PREADD/PRESUB/POSTADD/POSTSUB
//          Create temporary with array index.
//          Increment/decrement using index of the temporary.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LinkInc.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class LinkIncVisitor final : public VNVisitor {
    // STATE
    AstNodeFTask* m_ftaskp = nullptr;  // Function or task we're inside
    AstNodeModule* m_modp = nullptr;  // Module we're inside
    size_t m_tmpNameCnt = 0;  // Var name counter
    AstNode* m_insStmtp = nullptr;  // Where to insert statement
    bool m_unsupportedHere = false;  // Used to detect where it's not supported yet

    // METHODS
    void insertOnTop(AstVar* newp) {
        // Add the thing directly under the current TFunc/Module
        if (m_ftaskp) {
            m_ftaskp->stmtsp()->addHereThisAsNext(newp);
            return;
        }
        if (m_modp) {
            m_modp->stmtsp()->addHereThisAsNext(newp);
            return;
        }
        newp->v3fatalSrc("Variable not under FTASK/MODULE");
    }
    void insertBeforeStmt(AstNode* nodep, AstNode* newp) {
        // Return node that must be visited, if any
        UINFOTREE(9, newp, "", "newstmt");
        UASSERT_OBJ(m_insStmtp, nodep, "Expression not underneath a statement");
        m_insStmtp->addHereThisAsNext(newp);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        if (nodep->dead()) return;
        VL_RESTORER(m_modp);
        VL_RESTORER(m_tmpNameCnt);
        m_modp = nodep;
        m_tmpNameCnt = 0;
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNodeCoverOrAssert* nodep) override {
        VL_RESTORER(m_insStmtp);
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->propp());
        m_insStmtp = nullptr;
        // Note: no iterating over sentreep here as they will be ignored anyway
        if (AstAssert* const assertp = VN_CAST(nodep, Assert)) {
            iterateAndNextNull(assertp->failsp());
        } else if (AstAssertIntrinsic* const intrinsicp = VN_CAST(nodep, AssertIntrinsic)) {
            iterateAndNextNull(intrinsicp->failsp());
        }
        iterateAndNextNull(nodep->passsp());
    }
    void visit(AstLoop* nodep) override {
        UASSERT_OBJ(!nodep->contsp(), nodep, "'contsp' only used before LinkJump");
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateAndNextNull(nodep->stmtsp());
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstNodeForeach* nodep) override {
        // Special, as statements need to be put in different places
        // Body insert just before themselves
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateChildren(nodep);
        // Done the loop
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstJumpBlock* nodep) override {
        // Special, as statements need to be put in different places
        // Body insert just before themselves
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateChildren(nodep);
        // Done the loop
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstNodeIf* nodep) override {
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->condp());
        m_insStmtp = nullptr;
        iterateAndNextNull(nodep->thensp());
        iterateAndNextNull(nodep->elsesp());
        m_insStmtp = nullptr;
    }
    void visit(AstCaseItem* nodep) override {
        {
            VL_RESTORER(m_unsupportedHere);
            m_unsupportedHere = true;
            iterateAndNextNull(nodep->condsp());
        }
        m_insStmtp = nullptr;  // Next thing should be new statement
        iterateAndNextNull(nodep->stmtsp());
    }
    void visit(AstDelay* nodep) override {
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->lhsp());
        m_insStmtp = nullptr;
        iterateAndNextNull(nodep->stmtsp());
        m_insStmtp = nullptr;
    }
    void visit(AstEventControl* nodep) override {
        m_insStmtp = nullptr;
        iterateAndNextNull(nodep->stmtsp());
        m_insStmtp = nullptr;
    }
    void visit(AstWait* nodep) override {
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->condp());
        m_insStmtp = nullptr;
        iterateAndNextNull(nodep->stmtsp());
        m_insStmtp = nullptr;
    }
    void visit(AstBegin* nodep) override {
        m_insStmtp = nullptr;  // Pretend not a statement TODO: parse ++/-- as ExprStmt
        iterateChildren(nodep);
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstStmtExpr* nodep) override {
        AstNodeExpr* const exprp = nodep->exprp();
        m_insStmtp = nodep;
        iterateChildren(nodep);
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstNodeStmt* nodep) override {
        m_insStmtp = nodep;
        iterateChildren(nodep);
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void unsupported_visit(AstNode* nodep) {
        VL_RESTORER(m_unsupportedHere);
        m_unsupportedHere = true;
        UINFO(9, "Marking unsupported " << nodep);
        iterateChildren(nodep);
    }
    void visit(AstLogAnd* nodep) override { unsupported_visit(nodep); }
    void visit(AstLogOr* nodep) override { unsupported_visit(nodep); }
    void visit(AstLogEq* nodep) override { unsupported_visit(nodep); }
    void visit(AstLogIf* nodep) override { unsupported_visit(nodep); }
    void visit(AstCond* nodep) override { unsupported_visit(nodep); }
    void visit(AstPropSpec* nodep) override { unsupported_visit(nodep); }
    void prepost_visit(AstNodeTriop* nodep) {
        UASSERT_OBJ(m_insStmtp, nodep, "Should always be under statement");
        prepost_expr_visit(nodep);
    }
    void prepost_stmt_sel_visit(AstNodeTriop* nodep) {
        // Special case array[something]++, see comments at file top
        // UINFOTREE(9, nodep, "", "pp-stmt-sel-in");
        iterateChildren(nodep);
        AstConst* const constp = VN_AS(nodep->lhsp(), Const);
        UASSERT_OBJ(nodep, constp, "Expecting CONST");
        AstConst* const newconstp = constp->cloneTree(true);

        AstSelBit* const rdSelbitp = VN_CAST(nodep->rhsp(), SelBit);
        AstNodeExpr* const rdFromp = rdSelbitp->fromp()->unlinkFrBack();
        AstNodeExpr* const rdBitp = rdSelbitp->bitp()->unlinkFrBack();
        AstSelBit* const wrSelbitp = VN_CAST(nodep->thsp(), SelBit);
        AstNodeExpr* const wrFromp = wrSelbitp->fromp()->unlinkFrBack();

        // Prepare a temporary variable
        FileLine* const fl = nodep->fileline();
        const string name = "__VincIndex"s + cvtToStr(++m_tmpNameCnt);
        AstVar* const varp = new AstVar{
            fl, VVarType::BLOCKTEMP, name, VFlagChildDType{},
            new AstRefDType{fl, AstRefDType::FlagTypeOfExpr{}, rdBitp->cloneTree(true)}};
        if (m_ftaskp) varp->funcLocal(true);

        // Declare the variable
        insertOnTop(varp);

        // Define what operation will we be doing
        AstAssign* const varAssignp
            = new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, rdBitp};
        AstNode* const newp = varAssignp;

        AstNodeExpr* const valuep
            = new AstSelBit{fl, rdFromp, new AstVarRef{fl, varp, VAccess::READ}};
        AstNodeExpr* const storeTop
            = new AstSelBit{fl, wrFromp, new AstVarRef{fl, varp, VAccess::READ}};

        AstAssign* assignp;
        if (VN_IS(nodep, PreSub) || VN_IS(nodep, PostSub)) {
            assignp = new AstAssign{nodep->fileline(), storeTop,
                                    new AstSub{nodep->fileline(), valuep, newconstp}};
        } else {
            assignp = new AstAssign{nodep->fileline(), storeTop,
                                    new AstAdd{nodep->fileline(), valuep, newconstp}};
        }
        newp->addNext(assignp);

        // if (debug() >= 9) newp->dumpTreeAndNext("-pp-stmt-sel-new: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void prepost_stmt_visit(AstNodeTriop* nodep) {
        iterateChildren(nodep);
        AstConst* const constp = VN_AS(nodep->lhsp(), Const);
        UASSERT_OBJ(nodep, constp, "Expecting CONST");
        AstConst* const newconstp = constp->cloneTree(true);

        AstNodeExpr* const storeTop = nodep->thsp()->unlinkFrBack();
        AstNodeExpr* const valuep = nodep->rhsp()->unlinkFrBack();

        AstAssign* assignp;
        if (VN_IS(nodep, PreSub) || VN_IS(nodep, PostSub)) {
            assignp = new AstAssign{nodep->fileline(), storeTop,
                                    new AstSub{nodep->fileline(), valuep, newconstp}};
        } else {
            assignp = new AstAssign{nodep->fileline(), storeTop,
                                    new AstAdd{nodep->fileline(), valuep, newconstp}};
        }
        nodep->replaceWith(assignp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void prepost_expr_visit(AstNodeTriop* nodep) {

        AstNodeExpr* const readp = nodep->rhsp();
        AstNodeExpr* const writep = nodep->thsp()->unlinkFrBack();

        AstConst* const constp = VN_AS(nodep->lhsp(), Const);
        UASSERT_OBJ(nodep, constp, "Expecting CONST");
        AstConst* const newconstp = constp->cloneTree(true);

        // Prepare a temporary variable
        FileLine* const fl = nodep->fileline();
        const string name = "__Vincrement"s + cvtToStr(++m_tmpNameCnt);
        AstVar* const varp = new AstVar{
            fl, VVarType::BLOCKTEMP, name, VFlagChildDType{},
            new AstRefDType{fl, AstRefDType::FlagTypeOfExpr{}, readp->cloneTree(true)}};
        if (m_ftaskp) varp->funcLocal(true);

        // Declare the variable
        insertOnTop(varp);

        // Define what operation will we be doing
        AstNodeExpr* operp;
        if (VN_IS(nodep, PostSub) || VN_IS(nodep, PreSub)) {
            operp = new AstSub{fl, readp->cloneTreePure(true), newconstp};
        } else {
            operp = new AstAdd{fl, readp->cloneTreePure(true), newconstp};
        }

        if (VN_IS(nodep, PreAdd) || VN_IS(nodep, PreSub)) {
            // PreAdd/PreSub operations
            // Immediately after declaration - increment it by one
            AstAssign* const assignp
                = new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, operp};
            // Immediately after incrementing - assign it to the original variable
            assignp->addNext(new AstAssign{fl, writep, new AstVarRef{fl, varp, VAccess::READ}});
            insertBeforeStmt(nodep, assignp);
        } else {
            // PostAdd/PostSub operations
            // Assign the original variable to the temporary one
            AstAssign* const assignp = new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE},
                                                     readp->cloneTreePure(true)};
            // Increment the original variable by one
            assignp->addNext(new AstAssign{fl, writep, operp});
            insertBeforeStmt(nodep, assignp);
        }

        // Replace the node with the temporary
        nodep->replaceWith(new AstVarRef{readp->fileline(), varp, VAccess::READ});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    // If 'rValp' is a consant return it if unlinked, or return a clone.
    // Otherwise return a read reference to a temporary that captures the value.
    AstNodeExpr* captureRValue(AstNodeExpr* rValp, const char* prefixp) {
        // No need to save it if constant
        if (VN_IS(rValp, Const)) return rValp->backp() ? rValp->cloneTree(false) : rValp;

        // Create a temporary variable
        FileLine* const flp = rValp->fileline();
        AstVar* const varp = new AstVar{
            flp, VVarType::BLOCKTEMP, prefixp + std::to_string(++m_tmpNameCnt), VFlagChildDType{},
            new AstRefDType{flp, AstRefDType::FlagTypeOfExpr{}, rValp->cloneTree(true)}};
        // Add it to the enclosing FTask/Module
        if (m_ftaskp) {
            m_ftaskp->stmtsp()->addHereThisAsNext(varp);
            varp->funcLocal(true);
        } else if (m_modp) {
            m_modp->stmtsp()->addHereThisAsNext(varp);
        } else {
            varp->v3fatalSrc("Variable not under FTASK/MODULE");
        }

        // Create an assignment to it, and insert it before the enclosing statement
        AstNodeExpr* const capp = rValp->backp() ? rValp->cloneTreePure(false) : rValp;
        AstAssign* const assp = new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, capp};
        m_insStmtp->addHereThisAsNext(assp);

        // Return a reference to it
        return new AstVarRef{flp, varp, VAccess::READ};
    }

    void captureReferencedRValues(AstNodeExpr* lValp) {
        // TODO: for now, we only support what we used to before, do more when
        // LinkInc moves after V3Width, otherwise it's a PITA to do it here
        if (AstSelBit* const nodep = VN_CAST(lValp, SelBit)) {
            nodep->bitp(captureRValue(nodep->bitp()->unlinkFrBack(), "__VIncDecIndex"));
            captureReferencedRValues(nodep->fromp());
            return;
        }
    }

    void visit(AstIncDec* nodep) override {
        {
            VL_RESTORER(m_insStmtp);  // In case there is an ExprStmt under ...
            iterateChildren(nodep);
        }
        if (m_unsupportedHere) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Incrementation in this context.");
            return;
        }
        UASSERT_OBJ(m_insStmtp, nodep, "Should always be under statement");

        // Capture any RValues referenced in the operand
        captureReferencedRValues(nodep->lvalp());

        // Get the value we should use to get the result
        AstNodeExpr* const resp = captureRValue(nodep, "__VIncDecPreValue");

        // Replace with the value
        nodep->replaceWith(resp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstGenFor* nodep) override { iterateChildren(nodep); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkIncVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~LinkIncVisitor() override = default;
};

//######################################################################
// Task class functions

void V3LinkInc::linkIncrements(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { LinkIncVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkinc", 0, dumpTreeEitherLevel() >= 3);
}
