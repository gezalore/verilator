// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add C++ casts across expression size changes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2004-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Cast's Transformations:
//
// Each module:
//      For each expression, if above expression requires 32 bits,
//      and this isn't, cast to 32 bits.
//      Likewise for 64 bit expressions.
//
// C++ rules:
//      Integral promotions allow conversion to larger int.  Unsigned is only
//      used if a int would not fit the value.
//
//      Bools converts to int, not unsigned.
//
//      Most operations return unsigned if either operand is unsigned.
//
//      Unsignedness can be lost on results of the below operations, as they
//      may need the sign bit for proper operation:
//              /, %, /=, %=, <, <=, >, or >=
//
//      Signed values are always sign extended on promotion or right shift,
//      even if assigning to a unsigned.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Cast.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Cast state, as a visitor of each AstNode

class CastVisitor final : public VNVisitor {
    // NODE STATE
    // Entire netlist:
    //   AstNode::user1()               // bool.  Node is of known size
    const VNUser1InUse m_inuser1;

    // STATE

    // METHODS

    void insertCast(AstNodeExpr* nodep, int needsize) {  // We'll insert ABOVE passed node
        VNRelinker relinkHandle;
        nodep->unlinkFrBack(&relinkHandle);
        //
        AstCCast* const castp
            = new AstCCast{nodep->fileline(), nodep, needsize, nodep->widthMin()};
        UINFO(4, "  MadeCast " << static_cast<void*>(castp) << " for " << nodep);
        relinkHandle.relink(castp);
        // UINFOTREE(9, castp, "", "castins");
        //
        ensureLower32Cast(castp);
        nodep->user1(1);  // Now must be of known size
    }
    static int castSize(const AstNode* nodep) {
        if (nodep->isQuad()) {
            return VL_QUADSIZE;
        } else if (nodep->width() <= 8) {
            return 8;
        } else if (nodep->width() <= 16) {
            return 16;
        } else {
            return VL_IDATASIZE;
        }
    }
    void ensureCast(AstNodeExpr* nodep) {
        if (castSize(nodep->backp()) != castSize(nodep) || !nodep->user1()) {
            if (!nodep->isNull() && !nodep->isString() && !nodep->isDouble())
                insertCast(nodep, castSize(nodep->backp()));
        }
    }
    // cppcheck-suppress constParameterPointer // lhsp might be changed
    void ensureLower32Cast(AstCCast* nodep) {
        // If we have uint64 = CAST(uint64(x)) then the upcasting
        // really needs to be CAST(uint64(CAST(uint32(x))).
        // Otherwise a (uint64)(a>b) would return wrong value, as
        // less than has nondeterministic signedness.
        if (nodep->isQuad() && !nodep->lhsp()->isQuad() && !VN_IS(nodep->lhsp(), CCast)) {
            insertCast(nodep->lhsp(), VL_IDATASIZE);
        }
    }
    void ensureNullChecked(AstNodeExpr* nodep) {
        // TODO optimize to track null checked values and avoid where possible
        if (!VN_IS(nodep->backp(), NullCheck)) {
            VNRelinker relinkHandle;
            nodep->unlinkFrBack(&relinkHandle);
            relinkHandle.relink(new AstNullCheck{nodep->fileline(), nodep});
        }
    }

    // Whether the node is emitted as a C++ operator yielding a bool, which promotes to
    // (signed) int, so it is not of a known size, e.g. '~(a < b) >> 1'
    static bool isCppBool(const AstNode* nodep) {
        return VN_IS(nodep, Eq) || VN_IS(nodep, EqCase) || VN_IS(nodep, EqWild)
               || VN_IS(nodep, Neq) || VN_IS(nodep, NeqCase) || VN_IS(nodep, NeqWild)
               || VN_IS(nodep, Lt) || VN_IS(nodep, LtS) || VN_IS(nodep, Lte) || VN_IS(nodep, LteS)
               || VN_IS(nodep, Gt) || VN_IS(nodep, GtS) || VN_IS(nodep, Gte) || VN_IS(nodep, GteS)
               || VN_IS(nodep, LogAnd) || VN_IS(nodep, LogOr) || VN_IS(nodep, LogEq)
               || VN_IS(nodep, LogIf) || VN_IS(nodep, LogNot) || VN_IS(nodep, RedOr)
               || VN_IS(nodep, RedAnd);
    }

    // VISITORS
    void visit(AstNodeUniop* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1() && !isCppBool(nodep));
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
    }
    void visit(AstNodeBiop* nodep) override {
        iterateChildren(nodep);
        // The type of a shift is the type of its LHS only
        const bool isShift = VN_IS(nodep, ShiftL) || VN_IS(nodep, ShiftR);
        nodep->user1((nodep->lhsp()->user1() | (!isShift && nodep->rhsp()->user1()))
                     && !isCppBool(nodep));
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        if (nodep->sizeMattersRhs()) ensureCast(nodep->rhsp());
    }
    void visit(AstCond* nodep) override {
        // All class types are castable to each other. If they are of different types,
        // a compilation error will be thrown, so an explicit cast is required. Types were
        // already checked by V3Width and dtypep of a condition operator is a type of their
        // common base class, so both classes can be safely casted.
        const AstClassRefDType* const thenClassDtypep
            = VN_CAST(nodep->thenp()->dtypep()->skipRefp(), ClassRefDType);
        const AstClassRefDType* const elseClassDtypep
            = VN_CAST(nodep->elsep()->dtypep()->skipRefp(), ClassRefDType);
        const bool castRequired = thenClassDtypep && elseClassDtypep
                                  && (thenClassDtypep->classp() != elseClassDtypep->classp());
        if (castRequired) {
            const AstClass* const commonBaseClassp
                = VN_AS(nodep->dtypep()->skipRefp(), ClassRefDType)->classp();
            if (thenClassDtypep->classp() != commonBaseClassp) {
                AstNodeExpr* thenp = nodep->thenp()->unlinkFrBack();
                nodep->thenp(new AstCCast{thenp->fileline(), thenp, nodep});
            }
            if (elseClassDtypep->classp() != commonBaseClassp) {
                AstNodeExpr* elsep = nodep->elsep()->unlinkFrBack();
                nodep->elsep(new AstCCast{elsep->fileline(), elsep, nodep});
            }
        }
        visit(static_cast<AstNodeTriop*>(nodep));
    }
    void visit(AstNodeTriop* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1() | nodep->rhsp()->user1() | nodep->thsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        if (nodep->sizeMattersRhs()) ensureCast(nodep->rhsp());
        if (nodep->sizeMattersThs()) ensureCast(nodep->thsp());
    }
    void visit(AstNodeQuadop* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1() | nodep->rhsp()->user1() | nodep->thsp()->user1()
                     | nodep->fhsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        if (nodep->sizeMattersRhs()) ensureCast(nodep->rhsp());
        if (nodep->sizeMattersThs()) ensureCast(nodep->thsp());
        if (nodep->sizeMattersFhs()) ensureCast(nodep->fhsp());
    }
    void visit(AstCCast* nodep) override {
        iterateChildren(nodep);
        ensureLower32Cast(nodep);
        nodep->user1(1);
    }
    void visit(AstConsPackMember* nodep) override {
        iterateChildren(nodep);
        if (VN_IS(nodep->rhsp()->dtypep()->skipRefp(), BasicDType)) ensureCast(nodep->rhsp());
        nodep->user1(1);
    }
    void visit(AstExprStmt* nodep) override {
        iterateChildren(nodep);
        nodep->user1(1);
    }
    void visit(AstNegate* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1());
        if (nodep->lhsp()->widthMin() == 1 && !nodep->lhsp()->isWide()) {
            // We want to avoid a GCC "converting of negative value" warning
            // from our expansion of
            //    out = {32{a<b}}  =>   out = - (a<b)
            insertCast(nodep->lhsp(), castSize(nodep));
        } else {
            if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        }
    }
    void visit(AstVarRef* nodep) override {
        const AstNode* const backp = nodep->backp();
        if (nodep->access().isReadOnly() && VN_IS(backp, NodeExpr) && !VN_IS(backp, CCast)
            && !VN_IS(backp, NodeCCall) && !VN_IS(backp, CMethodHard) && !VN_IS(backp, SFormatF)
            && !VN_IS(backp, ArraySel) && !VN_IS(backp, StructSel) && !VN_IS(backp, RedXor)
            && (nodep->varp()->basicp() && !nodep->varp()->basicp()->isForkSync()
                && !nodep->varp()->basicp()->isProcessRef() && !nodep->varp()->basicp()->isEvent())
            && backp->width() && castSize(nodep) != castSize(nodep->varp())) {
            // Cast vars to IData first, else below has upper bits wrongly set
            //  CData x=3; out = (QData)(x<<30);
            insertCast(nodep, castSize(nodep));
        }
        nodep->user1(1);
    }
    void visit(AstConst* nodep) override {
        // Constants are of unknown size if smaller than 33 bits, because
        // we're too lazy to wrap every constant in the universe in
        // ((IData)#).
        nodep->user1(nodep->isQuad() || nodep->isWide() || nodep->isNull());
    }

    // Null dereference protection
    void visit(AstNullCheck* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1());
    }
    void visit(AstCMethodCall* nodep) override {
        iterateChildren(nodep);
        ensureNullChecked(nodep->fromp());
        nodep->user1(true);
    }
    void visit(AstCMethodHard* nodep) override {
        iterateChildren(nodep);
        nodep->user1(true);
    }
    void visit(AstMemberSel* nodep) override {
        iterateChildren(nodep);
        ensureNullChecked(nodep->fromp());
        nodep->user1(true);
    }
    void visit(AstStructSel* nodep) override {
        iterateChildren(nodep);
        nodep->user1(true);
    }

    // NOPs
    void visit(AstVar*) override {}

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CastVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~CastVisitor() override = default;
};

//######################################################################
// Cast class functions

void V3Cast::castAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { CastVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("cast", 0, dumpTreeEitherLevel() >= 3);
}
