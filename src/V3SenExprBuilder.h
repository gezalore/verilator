// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Builder for sensitivity checking expressions.
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

#ifndef VERILATOR_V3SENEXPRBUILDER_H_
#define VERILATOR_V3SENEXPRBUILDER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3UniqueNames.h"

//######################################################################
// SenExprBuilder constructs the expressions used to compute if an
// AstSenTree have triggered

class SenExprBuilder final {
public:
    // TYPES
    struct Results final {
        std::vector<AstNodeStmt*> m_inits;  // Initialization statements for previous values
        std::vector<AstNodeStmt*> m_preUpdates;  // Pre update assignments
        std::vector<AstNodeStmt*> m_postUpdates;  // Post update assignments
    };

private:
    // STATE
    AstScope* const m_scopep;  // The scope

    Results m_results;  // The builder result

    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_prev;  // The 'previous value' signals
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_curr;  // The 'current value' signals
    std::unordered_set<VNRef<AstNode>> m_hasPreUpdate;  // Whether the given sen expression already
                                                        // has an update statement in m_preUpdates
    std::unordered_set<VNRef<AstNode>> m_hasPostUpdate;  // Likewise for m_postUpdates

    V3UniqueNames m_currNames{"__Vtrigcurrexpr"};  // For generating unique current value
                                                   // signal names
    V3UniqueNames m_prevNames{"__Vtrigprevexpr"};  // Likewise for previous values

    static bool isSupportedDType(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (VN_IS(dtypep, BasicDType)) return true;
        if (VN_IS(dtypep, PackArrayDType)) return true;
        if (VN_IS(dtypep, UnpackArrayDType)) return isSupportedDType(dtypep->subDTypep());
        if (VN_IS(dtypep, NodeUOrStructDType)) return true;  // All are packed at the moment
        return false;
    }

    static bool isSimpleExpr(const AstNode* const exprp) {
        return exprp->forall([](const AstNode* const nodep) {
            return VN_IS(nodep, Const) || VN_IS(nodep, NodeVarRef) || VN_IS(nodep, Sel)
                   || VN_IS(nodep, NodeSel) || VN_IS(nodep, MemberSel)
                   || VN_IS(nodep, CMethodHard);
        });
    }

    // METHODS
    AstVarScope* crateTemp(AstNodeExpr* exprp) {
        // For readability, use the scoped signal name if the trigger is a simple AstVarRef
        string name;
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
            AstVarScope* const vscp = refp->varScopep();
            name = "__" + vscp->scopep()->nameDotless() + "__" + vscp->varp()->name();
            name = m_prevNames.get(name);
        } else {
            name = m_prevNames.get(exprp);
        }
        AstVarScope* const vscp = m_scopep->createTemp(name, exprp->dtypep());
        vscp->varp()->isInternal(true);
        return vscp;
    }

    AstNodeExpr* getCurr(AstNodeExpr* exprp) {
        // For simple expressions like varrefs or selects, just use them directly
        if (isSimpleExpr(exprp)) return exprp->cloneTree(false);

        // Create the 'current value' variable
        FileLine* const flp = exprp->fileline();
        auto result = m_curr.emplace(*exprp, nullptr);
        if (result.second) result.first->second = crateTemp(exprp);
        AstVarScope* const currp = result.first->second;

        // Add pre update if it does not exist yet in this round
        if (m_hasPreUpdate.emplace(*currp).second) {
            m_results.m_preUpdates.push_back(new AstAssign{
                flp, new AstVarRef{flp, currp, VAccess::WRITE}, exprp->cloneTree(false)});
        }
        return new AstVarRef{flp, currp, VAccess::READ};
    }
    AstVarScope* getPrev(AstNodeExpr* exprp) {
        FileLine* const flp = exprp->fileline();
        const auto rdCurr = [this, exprp]() { return getCurr(exprp); };

        AstNode* scopeExprp = exprp;
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) scopeExprp = refp->varScopep();
        // Create the 'previous value' variable
        const auto pair = m_prev.emplace(*scopeExprp, nullptr);
        if (pair.second) {
            AstVarScope* const prevp = crateTemp(exprp);
            pair.first->second = prevp;
            // Add the initializer init
            AstAssign* const initp = new AstAssign{flp, new AstVarRef{flp, prevp, VAccess::WRITE},
                                                   exprp->cloneTree(false)};
            m_results.m_inits.push_back(initp);
        }

        AstVarScope* const prevp = pair.first->second;

        const auto wrPrev = [=]() { return new AstVarRef{flp, prevp, VAccess::WRITE}; };

        // Add post update if it does not exist yet
        if (m_hasPostUpdate.emplace(*exprp).second) {
            if (!isSupportedDType(exprp->dtypep())) {
                exprp->v3warn(E_UNSUPPORTED,
                              "Unsupported: Cannot detect changes on expression of complex type"
                              " (see combinational cycles reported by UNOPTFLAT)");
                return prevp;
            }

            if (VN_IS(exprp->dtypep()->skipRefp(), UnpackArrayDType)) {
                AstCMethodHard* const cmhp = new AstCMethodHard{flp, wrPrev(), "assign", rdCurr()};
                cmhp->dtypeSetVoid();
                m_results.m_postUpdates.push_back(cmhp->makeStmt());
            } else {
                m_results.m_postUpdates.push_back(new AstAssign{flp, wrPrev(), rdCurr()});
            }
        }

        return prevp;
    }

    std::pair<AstNodeExpr*, bool> createTerm(const AstSenItem* senItemp) {
        FileLine* const flp = senItemp->fileline();
        AstNodeExpr* const senp = senItemp->sensp();

        const auto currp = [this, senp]() { return getCurr(senp); };
        const auto prevp = [this, flp, senp]() {
            return new AstVarRef{flp, getPrev(senp), VAccess::READ};
        };
        const auto lsb = [=](AstNodeExpr* opp) { return new AstSel{flp, opp, 0, 1}; };

        // All event signals should be 1-bit at this point
        switch (senItemp->edgeType()) {
        case VEdgeType::ET_CHANGED:
        case VEdgeType::ET_HYBRID:  //
            if (VN_IS(senp->dtypep()->skipRefp(), UnpackArrayDType)) {
                // operand order reversed to avoid calling neq() method on non-VlUnpacked type, see
                // issue #5125
                AstCMethodHard* const resultp = new AstCMethodHard{flp, prevp(), "neq", currp()};
                resultp->dtypeSetBit();
                return {resultp, true};
            }
            return {new AstNeq{flp, currp(), prevp()}, true};
        case VEdgeType::ET_BOTHEDGE:  //
            return {lsb(new AstXor{flp, currp(), prevp()}), false};
        case VEdgeType::ET_POSEDGE:  //
            return {lsb(new AstAnd{flp, currp(), new AstNot{flp, prevp()}}), false};
        case VEdgeType::ET_NEGEDGE:  //
            return {lsb(new AstAnd{flp, new AstNot{flp, currp()}, prevp()}), false};
        case VEdgeType::ET_EVENT: {
            UASSERT_OBJ(v3Global.hasEvents(), senItemp, "Inconsistent");
            {
                // Clear 'fired' state when done
                // No need to check if the event was fired, we need the flag clear regardless
                AstCMethodHard* const clearp = new AstCMethodHard{flp, currp(), "clearFired"};
                clearp->dtypeSetVoid();
                m_results.m_postUpdates.push_back(clearp->makeStmt());
            }

            // Get 'fired' state
            AstCMethodHard* const callp = new AstCMethodHard{flp, currp(), "isFired"};
            callp->dtypeSetBit();
            return {callp, false};
        }
        case VEdgeType::ET_TRUE:  //
            return {currp(), false};
        default:  // LCOV_EXCL_START
            senItemp->v3fatalSrc("Unknown edge type");
            return {nullptr, false};
        }  // LCOV_EXCL_STOP
    }

public:
    // Returns the expression computing the trigger, and a bool indicating that
    // this trigger should be fired on the first evaluation (at initialization)
    std::pair<AstNodeExpr*, bool> build(const AstSenItem* senItemp) {
        auto term = createTerm(senItemp);
        if (AstNodeExpr* const condp = senItemp->condp()) {
            term.first = new AstAnd{senItemp->fileline(), condp->cloneTreePure(false), term.first};
        }
        return term;
    }

    // Like above, but for a whole SenTree
    std::pair<AstNodeExpr*, bool> build(const AstSenTree* senTreep) {
        FileLine* const flp = senTreep->fileline();
        AstNodeExpr* resultp = nullptr;
        bool firedAtInitialization = false;
        for (AstSenItem* senItemp = senTreep->sensesp(); senItemp;
             senItemp = VN_AS(senItemp->nextp(), SenItem)) {
            const auto& pair = createTerm(senItemp);
            if (AstNodeExpr* termp = pair.first) {
                resultp = resultp ? new AstOr{flp, resultp, termp} : termp;
                firedAtInitialization |= pair.second;
            }
        }
        return {resultp, firedAtInitialization};
    }

    Results getAndClearResults() {
        m_curr.clear();
        m_prev.clear();
        m_hasPreUpdate.clear();
        m_hasPostUpdate.clear();
        return std::move(m_results);
    }

    // CONSTRUCTOR
    explicit SenExprBuilder(AstScope* scopep)
        : m_scopep{scopep} {}
};

#endif  // Guard
