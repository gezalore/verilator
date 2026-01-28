// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add Unknown assigns
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Unknown's Transformations:
//
// Each module:
//      TBD: Eliminate tristates by adding __in, __inen, __en wires in parallel
//          Need __en in changed list if a signal is on the LHS of a assign
//      Constants:
//          RHS, Replace 5'bx_1_x with a module global we init to a random value
//              CONST(5'bx_1_x) -> VARREF(_{numberedtemp})
//                              -> VAR(_{numberedtemp})
//                              -> INITIAL(VARREF(_{numberedtemp}),
//                                         OR(5'bx_1_x,AND(random,5'b0_1_x))
//              OPTIMIZE: Must not collapse this initial back into the equation.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "verilatedos.h"

#include "V3Unknown.h"

#include "V3Const.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class UnknownVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on Netlist
    //  AstSel::user1()         -> bool.  Set true if already processed
    //  AstArraySel::user1()    -> bool.  Set true if already processed
    //  AstNode::user2p()       -> AstIf* Inserted if assignment for conditional
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE - across all visitors
    VDouble0 m_statUnkVars;  // Statistic tracking
    VDouble0 m_statLvBoundVars;  // Statistic tracking
    V3UniqueNames m_lvboundNames{"__Vlvbound"};  // For generating unique temporary variable names
    V3UniqueNames m_xrandNames{"__Vxrand"};  // For generating unique temporary variable names

    // STATE - for current visit position (use VL_RESTORER)
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    // Current procedural statement. TODO: Make this an AstNodeStmt after #6280
    AstNode* m_stmtp = nullptr;

    bool m_constXCvt = false;  // Convert X's
    bool m_allowXUnique = v3Global.opt.xAssign() == "unique";  // Allow unique assignments

    // METHODS

    AstVar* newVar(FileLine* const flp, const std::string& name, AstNodeDType* dtypep) {
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, dtypep};
        if (m_ftaskp) {
            varp->funcLocal(true);
            varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            m_ftaskp->stmtsp()->addHereThisAsNext(varp);
        } else {
            m_modp->stmtsp()->addHereThisAsNext(varp);
        }
        return varp;
    }

    void replaceBoundLvalue(AstNodeExpr* nodep, AstNodeExpr* condp) {
        // Spec says a out-of-range LHS SEL results in a NOP.
        // This is a PITA.  We could:
        //  1. IF(...) around an ASSIGN,
        //     but that would break a "foo[TOO_BIG]=$fopen(...)".
        //  2. Hack to extend the size of the output structure
        //     by one bit, and write to that temporary, but never read it.
        //     That makes there be two widths() and is likely a bug farm.
        //  3. Make a special SEL to choose between the real lvalue
        //     and a temporary NOP register.
        //  4. Assign to a temp, then IF that assignment.
        //     This is suspected to be nicest to later optimizations.
        // 4 seems best but breaks later optimizations.  3 was tried,
        // but makes a mess in the emitter as lvalue switching is needed.  So 4.
        // SEL(...) -> temp
        //             if (COND(LTE(bit<=maxlsb))) ASSIGN(SEL(...)),temp)

        if (!m_stmtp) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Dynamic Lvalue expression not supported in this positin");
            VL_DO_DANGLING(condp->deleteTree(), condp);
            return;
        }
        if (VN_IS(m_stmtp, AssignForce) || VN_IS(m_stmtp, Release)) {
            // The conversion done in this function breaks force and release statements
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Force / release statement with Dynamic Lvalue expression");
            VL_DO_DANGLING(condp->deleteTree(), condp);
            return;
        }

        FileLine* const fl = nodep->fileline();
        VL_DANGLING(nodep);  // Zap it so we don't use it by mistake - use prep

        // Already exists; rather than IF(a,... IF(b... optimize to IF(a&&b,
        // Saves us teaching V3Const how to optimize, and it won't be needed again.
        if (const AstIf* const ifp = VN_AS(prep->user2p(), If)) {
            VNRelinker replaceHandle;
            AstNodeExpr* const earliercondp = ifp->condp()->unlinkFrBack(&replaceHandle);
            AstNodeExpr* const newp = new AstLogAnd{condp->fileline(), condp, earliercondp};
            UINFO(4, "Edit BOUNDLVALUE " << newp);
            replaceHandle.relink(newp);
        } else {
            AstVar* const varp = newVar(fl, m_lvboundNames.get(prep), prep->dtypep());
            ++m_statLvBoundVars;

            prep->replaceWith(new AstVarRef{fl, varp, VAccess::WRITE});
            AstIf* const newp
                = new AstIf{fl, condp,

                            new AstAssign{fl, prep, new AstVarRef{fl, varp, VAccess::READ}}};
            newp->branchPred(VBranchPred::BP_LIKELY);
            newp->isBoundsCheck(true);
            UINFOTREE(9, newp, "", "_new");
            m_stmtp->addNextHere(newp);
            prep->user2p(newp);  // Save so we may LogAnd it next time
        }
    }

    // Returns true if it 'val' is known to be >= than value of 'exprp'
    static bool isStaticlyGte(uint64_t val, const AstNodeExpr* const exprp) {
        // If the index is too wide, assume false, should never happen in real code
        if (exprp->width() > VL_QUADSIZE) return false;
        // Check special forms or 'expr' that can be proven easily
        if (const AstConst* const constp = VN_CAST(exprp, Const)) {
            // If a constant, compare the values
            return val >= constp->toUQuad();
        } else if (const AstModDiv* const modDivp = VN_CAST(exprp, ModDiv)) {
            // If a remainder with constant, check the divisor
            if (const AstConst* const divp = VN_CAST(modDivp->rhsp(), Const)) {
                return val >= divp->toUQuad() - 1;
            }
        } else if (const AstAnd* const andp = VN_CAST(exprp, And)) {
            // If an and with a constant, check the constant
            if (const AstConst* const maskp = VN_CAST(andp->lhsp(), Const)) {
                return val >= maskp->toUQuad();
            }
        }
        // Otherwise check the maximum possible value of 'exprp' based on width
        return val >= ((1ULL << exprp->width()) - 1);
    }

    // Returns true if 'nodep' is a write or read/write reference
    static bool isLValue(AstNode* const nodep) {
        // FIXME: just write a recursive version instead of using `baseFromp` here
        const AstNode* const basefromp = AstArraySel::baseFromp(nodep, true);
        if (const AstNodeVarRef* const varrefp = VN_CAST(basefromp, NodeVarRef)) {
            return varrefp->access().isWriteOrRW();
        }
        return false;
    }

    AstNodeExpr* cloneSafePure(AstNodeExpr* exprp) {
        // If it's pure, just clone it
        if (exprp->isPure()) return exprp->cloneTreePure(false);

        // Otherwise turn it into an ExprStmt to save the result in a temporary
        FileLine* const flp = exprp->fileline();
        const std::string name = m_xrandNames.get(exprp);
        AstVar* const varp = newVar(flp, name, exprp->dtypep());
        VNRelinker relinker;
        exprp->unlinkFrBack(&relinker);
        AstAssign* const assp
            = new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, exprp};
        relinker.relink(new AstExprStmt{flp, assp, new AstVarRef{flp, varp, VAccess::READ}});
        // Return read reference to the temporary
        return new AstVarRef{flp, varp, VAccess::READ};
    }

    void visitEqNeqCase(AstNodeBiop* nodep) {
        UINFO(4, " N/EQCASE->EQ " << nodep);
        V3Const::constifyEdit(nodep->lhsp());  // lhsp may change
        V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
        if (VN_IS(nodep->lhsp(), Const) && VN_IS(nodep->rhsp(), Const)) {
            // Both sides are constant, node can be constant
            VL_DO_DANGLING(V3Const::constifyEdit(nodep), nodep);
            return;
        } else {
            AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
            AstNodeExpr* newp;
            // If we got ==1'bx it can never be true (but 1'bx==1'bx can be!)
            if (((VN_IS(lhsp, Const) && VN_AS(lhsp, Const)->num().isFourState())
                 || (VN_IS(rhsp, Const) && VN_AS(rhsp, Const)->num().isFourState()))) {
                newp = new AstConst(nodep->fileline(), AstConst::WidthedValue{}, 1,
                                    (VN_IS(nodep, EqCase) ? 0 : 1));
                VL_DO_DANGLING(lhsp->deleteTree(), lhsp);
                VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
            } else {
                if (VN_IS(nodep, EqCase)) {
                    newp = new AstEq{nodep->fileline(), lhsp, rhsp};
                } else {
                    newp = new AstNeq{nodep->fileline(), lhsp, rhsp};
                }
            }
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            // Iterate tree now that we may have gotten rid of Xs
            iterateChildren(newp);
        }
    }

    void visitEqNeqWild(AstNodeBiop* nodep) {
        UINFO(4, " N/EQWILD->EQ " << nodep);
        V3Const::constifyEdit(nodep->lhsp());  // lhsp may change
        V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
        if (VN_IS(nodep->lhsp(), Const) && VN_IS(nodep->rhsp(), Const)) {
            // Both sides are constant, node can be constant
            VL_DO_DANGLING(V3Const::constifyEdit(nodep), nodep);
            return;
        } else {
            AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
            AstNodeExpr* newp;
            if (!VN_IS(rhsp, Const)) {
                if (rhsp->dtypep()->isFourstate()) {
                    nodep->v3warn(
                        E_UNSUPPORTED,
                        "Unsupported: RHS of ==? or !=? is fourstate but not a constant");
                }
                newp = new AstEq{nodep->fileline(), lhsp, rhsp};
            } else {
                // X or Z's become mask, ala case statements.
                V3Number nummask{rhsp, rhsp->width()};
                nummask.opBitsNonX(VN_AS(rhsp, Const)->num());
                V3Number numval{rhsp, rhsp->width()};
                numval.opBitsOne(VN_AS(rhsp, Const)->num());
                AstNodeExpr* const and1p = new AstAnd{nodep->fileline(), lhsp,
                                                      new AstConst{nodep->fileline(), nummask}};
                AstNodeExpr* const and2p = new AstConst{nodep->fileline(), numval};
                if (VN_IS(nodep, EqWild)) {
                    newp = new AstEq{nodep->fileline(), and1p, and2p};
                } else {
                    newp = new AstNeq{nodep->fileline(), and1p, and2p};
                }
                VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
            }
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            // Iterate tree now that we may have gotten rid of the compare
            iterateChildren(newp);
        }
    }

    // VISITORS - Non statment/non-expression - All must set m_stmtp to nullptr
    void visit(AstNode* nodep) override {
        VL_RESTORER(m_stmtp);
        // Conservatively assume not a statement. If it is (prior to #6280),
        // add explicit 'visit' in stmt section below
        m_stmtp = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        UINFO(4, " MOD   " << nodep);

        // Reset variable names only at a root modules
        if (!m_modp) {
            m_lvboundNames.reset();
            m_xrandNames.reset();
        }

        VL_RESTORER(m_modp);
        VL_RESTORER(m_stmtp);
        VL_RESTORER(m_constXCvt);
        VL_RESTORER(m_allowXUnique);
        m_modp = nodep;
        m_stmtp = nullptr;
        m_constXCvt = true;
        // Class X randomization causes Vxrand in strange places, so disable
        if (VN_IS(nodep, Class)) m_allowXUnique = false;
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        UASSERT_OBJ(m_modp, nodep, "FTask must be under a NodeModule");
        VL_RESTORER(m_ftaskp);
        VL_RESTORER(m_stmtp);
        m_ftaskp = nodep;
        m_stmtp = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstNodeDType* nodep) override {
        // FIXME: Why is this needed?
        VL_RESTORER(m_stmtp);
        VL_RESTORER(m_constXCvt);
        m_stmtp = nullptr;
        m_constXCvt = false;  // Avoid losing the X's in casex
        iterateChildren(nodep);
    }
    void visit(AstVar* nodep) override {
        VL_RESTORER(m_stmtp);
        VL_RESTORER(m_allowXUnique);
        m_stmtp = nullptr;
        if (nodep->isParam()) m_allowXUnique = false;
        iterateChildren(nodep);
    }
    void visit(AstCaseItem* nodep) override {
        VL_RESTORER(m_stmtp);
        VL_RESTORER(m_constXCvt);
        m_stmtp = nullptr;
        m_constXCvt = false;  // Avoid losing the X's in casex
        iterateAndNextNull(nodep->condsp());
        m_constXCvt = true;
        iterateAndNextNull(nodep->stmtsp());
    }

    // VISITORS - Statements - All must set m_stmtp to self
    void visit(AstNodeStmt* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateChildren(nodep);
    }

    // VISITORS - Expressions - All must not modify m_stmtp (except under AstExprStmt)
    void visit(AstNodeExpr* nodep) override { iterateChildren(nodep); }
    void visit(AstEqCase* nodep) override { visitEqNeqCase(nodep); }
    void visit(AstNeqCase* nodep) override { visitEqNeqCase(nodep); }
    void visit(AstEqWild* nodep) override { visitEqNeqWild(nodep); }
    void visit(AstNeqWild* nodep) override { visitEqNeqWild(nodep); }
    void visit(AstIsUnknown* nodep) override {
        iterateChildren(nodep);
        // Ahh, we're two state, so this is easy
        UINFO(4, " ISUNKNOWN->0 " << nodep);
        AstConst* const newp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstCountBits* nodep) override {
        // Ahh, we're two state, so this is easy
        std::array<bool, 3> dropop;
        dropop[0] = VN_IS(nodep->rhsp(), Const) && VN_AS(nodep->rhsp(), Const)->num().isAnyX();
        dropop[1] = VN_IS(nodep->thsp(), Const) && VN_AS(nodep->thsp(), Const)->num().isAnyX();
        dropop[2] = VN_IS(nodep->fhsp(), Const) && VN_AS(nodep->fhsp(), Const)->num().isAnyX();
        UINFO(4, " COUNTBITS(" << dropop[0] << dropop[1] << dropop[2] << " " << nodep);

        AstNodeExpr* nonXp = nullptr;
        if (!dropop[0]) {
            nonXp = nodep->rhsp();
        } else if (!dropop[1]) {
            nonXp = nodep->thsp();
        } else if (!dropop[2]) {
            nonXp = nodep->fhsp();
        } else {  // Was all X-s
            UINFO(4, " COUNTBITS('x)->0 " << nodep);
            AstConst* const newp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        if (dropop[0]) {
            nodep->rhsp()->unlinkFrBack()->deleteTree();
            nodep->rhsp(nonXp->cloneTreePure(true));
        }
        if (dropop[1]) {
            nodep->thsp()->unlinkFrBack()->deleteTree();
            nodep->thsp(nonXp->cloneTreePure(true));
        }
        if (dropop[2]) {
            nodep->fhsp()->unlinkFrBack()->deleteTree();
            nodep->fhsp(nonXp->cloneTreePure(true));
        }
        iterateChildren(nodep);
    }
    void visit(AstConst* nodep) override {
        if (!m_constXCvt) return;
        if (!nodep->num().isFourState()) return;

        UINFO(4, " CONST4 " << nodep);
        UINFOTREE(9, nodep, "", "Const_old");
        // CONST(num) -> VARREF(newvarp)
        //          -> VAR(newvarp)
        //          -> INITIAL(VARREF(newvarp, OR(num_No_Xs,AND(random,num_1s_Where_X))
        V3Number numb1{nodep, nodep->width()};
        numb1.opBitsOne(nodep->num());
        V3Number numbx{nodep, nodep->width()};
        numbx.opBitsXZ(nodep->num());
        if (!m_allowXUnique) {
            // All X bits just become 0; fastest simulation, but not nice
            V3Number numnew{nodep, numb1.width()};
            if (v3Global.opt.xAssign() == "1") {
                numnew.opOr(numb1, numbx);
            } else {
                numnew.opAssign(numb1);
            }
            AstConst* const newp = new AstConst{nodep->fileline(), numnew};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            UINFO(4, "   -> " << newp);
        } else {
            // Make a Vxrand variable
            // We use the special XTEMP type so it doesn't break pure functions
            UASSERT_OBJ(m_modp, nodep, "X number not under module");
            AstVar* const newvarp
                = new AstVar{nodep->fileline(), VVarType::XTEMP, m_xrandNames.get(nullptr),
                             VFlagLogicPacked{}, nodep->width()};
            newvarp->lifetime(VLifetime::STATIC_EXPLICIT);
            ++m_statUnkVars;
            VNRelinker replaceHandle;
            nodep->unlinkFrBack(&replaceHandle);
            AstNodeVarRef* const newref1p
                = new AstVarRef{nodep->fileline(), newvarp, VAccess::READ};
            replaceHandle.relink(newref1p);  // Replace const with varref
            AstInitial* const newinitp = new AstInitial{
                nodep->fileline(),
                new AstAssign{
                    nodep->fileline(), new AstVarRef{nodep->fileline(), newvarp, VAccess::WRITE},
                    new AstOr{
                        nodep->fileline(), new AstConst{nodep->fileline(), numb1},
                        new AstAnd{nodep->fileline(), new AstConst{nodep->fileline(), numbx},
                                   new AstVarRef{nodep->fileline(), newvarp, VAccess::READ}}}}};
            // Add inits in front of other statement.
            // In the future, we should stuff the initp into the module's constructor.
            AstNode* const afterp = m_modp->stmtsp()->unlinkFrBackWithNext();
            m_modp->addStmtsp(newvarp);
            m_modp->addStmtsp(newinitp);
            m_modp->addStmtsp(afterp);
            UINFOTREE(9, newref1p, "", "_newref");
            UINFOTREE(9, newvarp, "", "_newvar");
            UINFOTREE(9, newinitp, "", "_newini");
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    void visit(AstSel* nodep) override {
        iterateChildren(nodep);
        if (nodep->user1SetOnce()) return;

        // Simplify the index in case it becomes constant
        V3Const::constifyEdit(nodep->lsbp());

        // Find range of dtype we are selecting from
        const uint32_t limit = nodep->fromp()->dtypep()->width() - 1;

        // If statically in bounds, no need to do anything
        if (isStaticlyGte(limit, nodep->lsbp())) return;

        // Guard against out of bounds access
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const idxp = nodep->lsbp()->unlinkFrBack();
        // Condition for bounds check
        AstConst* const limitp = new AstConst{flp, AstConst::WidthedValue{}, idxp->width(), limit};
        AstGte* const condp = new AstGte{flp, limitp, idxp};
        // Add back actual index expression
        nodep->lsbp(cloneSafePure(idxp));

        if (isLValue(nodep)) {
            replaceBoundLvalue(nodep, condp);
            return;
        }

        // It's a read reference. Replace with a bounds checking conditional.
        VNRelinker replaceHandle;
        nodep->unlinkFrBack(&replaceHandle);
        V3Number xnum{nodep, nodep->width()};
        xnum.setAllBitsX();
        AstNodeExpr* const xexprp = new AstConst{nodep->fileline(), xnum};
        AstNodeExpr* const newp = new AstCond{nodep->fileline(), condp, nodep, xexprp};
        replaceHandle.relink(newp);

        // Added X's, process them too
        iterate(newp);
    }

    // visit(AstSliceSel) not needed as its bounds are constant and checked in V3Width.

    void visit(AstArraySel* nodep) override {
        iterateChildren(nodep);
        if (nodep->user1SetOnce()) return;

        // Simplify the index in case it becomes constant
        V3Const::constifyEdit(nodep->bitp());

        // Find range of dtype we are selecting from
        AstNodeDType* const dtypep = nodep->fromp()->dtypep()->skipRefp();
        const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType);
        UASSERT_OBJ(adtypep, nodep, "Array select from non-array type");
        const uint32_t limit = adtypep->elementsConst();

        // If statically in bounds, no need to do anything
        if (isStaticlyGte(limit - 1, nodep->bitp())) return;

        // Guard against out of bounds access
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const idxp = nodep->bitp()->unlinkFrBack();
        // Condition for bounds check
        AstConst* const limitp = new AstConst{flp, AstConst::WidthedValue{}, idxp->width(), limit};
        AstGte* const condp = new AstGte{flp, limitp, idxp};
        // Add back actual index expression
        nodep->bitp(cloneSafePure(idxp));

        if (isLValue(nodep)) {
            replaceBoundLvalue(nodep, condp);
            return;
        }

        const AstNodeDType* const nodeDtp = nodep->dtypep()->skipRefp();
        // Making a scalar would break if we're making an array
        if (VN_IS(nodeDtp, BasicDType)) {
            // ARRAYSEL(...) -> COND(LT(bit<maxbit), ARRAYSEL(...), {width{1'bx}})
            VNRelinker replaceHandle;
            nodep->unlinkFrBack(&replaceHandle);
            // TODO make a tieoff function that takes AstNode and returns typed value
            V3Number xnum{nodep, nodep->width()};
            if (nodeDtp->isDouble()) {
                xnum = V3Number{nodep, V3Number::Double{}, 0.0};
            } else if (nodeDtp->isString()) {
                xnum = V3Number{nodep, V3Number::String{}, ""};
            } else {
                xnum.setAllBitsX();
            }
            AstNode* const newp = new AstCond{nodep->fileline(), condp, nodep,
                                              new AstConst{nodep->fileline(), xnum}};
            // Link in conditional, can blow away temp xor
            replaceHandle.relink(newp);
            // Added X's, tristate them too
            iterate(newp);
        } else {  // Mid-multidimension read, just use zero
            // ARRAYSEL(...) -> ARRAYSEL(COND(LT(bit<maxbit), bit, 0))
            VNRelinker replaceHandle;
            AstNodeExpr* const asBitp = nodep->bitp()->unlinkFrBack(&replaceHandle);
            AstNodeExpr* const newp = new AstCond{
                asBitp->fileline(), condp, asBitp,
                new AstConst{asBitp->fileline(), AstConst::WidthedValue{}, asBitp->width(), 0}};
            // Added X's, tristate them too
            replaceHandle.relink(newp);
            iterate(newp);
        }
    }

public:
    // CONSTRUCTORS
    explicit UnknownVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~UnknownVisitor() override {
        V3Stats::addStat("Unknowns, variables created", m_statUnkVars);
        V3Stats::addStat("Unknowns, bound LValues", m_statLvBoundVars);
    }
};
//######################################################################
// Unknown class functions

void V3Unknown::unknownAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { UnknownVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("unknown", 0, dumpTreeEitherLevel() >= 3);
}
