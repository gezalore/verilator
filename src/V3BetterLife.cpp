// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Remove assignments to dead variables
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3BetterLife.h"
#include "V3Ast.h"
#include "V3Error.h"
#include "V3FlowGraph.h"
#include "V3FlowAnalysis.h"

#include <unordered_set>

typedef std::unordered_set<const AstVarScope*> VarScopeSet;

class LivenessAnalysisLattice : public V3Semilattice<VarScopeSet> {
public:
    // The meet operator. Must be associative, commutative and idempotent.
    virtual VarScopeSet meet(const VarScopeSet& x, const VarScopeSet& y) const {
        // Noddy set union
        VarScopeSet result = x;
        for (auto e : y) { result.insert(e); }
        return result;
    }
    // The top element
    virtual VarScopeSet top() const {
        return VarScopeSet();  // Empty set
    }
    // The bottom element
    virtual VarScopeSet bottom() const {
        v3fatal("Please don't use bottom");
        return VarScopeSet();
    }
    virtual bool eq(const VarScopeSet& x, const VarScopeSet& y) const { return x == y; }
};

static LivenessAnalysisLattice g_lattice;

class LivenessAnalysisTransferFunctions : public V3TransferFunctions<VarScopeSet> {
public:
    LivenessAnalysisTransferFunctions()
        : V3TransferFunctions<VarScopeSet>(g_lattice) {}

    virtual VarScopeSet start() const override { return VarScopeSet(); }

    VarScopeSet m_use;
    VarScopeSet m_def;

    void pre() {
        m_use.clear();
        m_def.clear();
    }
    void post(AstNode*nodep) {
        // return use U (arg - def);
        m_ret = *m_argp;
        for (auto p : m_def) { m_ret.erase(p); }
        for (auto p : m_use) { m_ret.insert(p); }
    }

protected:
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        AstVarScope* const vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");
        if (nodep->lvalue()) {
            m_def.insert(vscp);
        } else {
            m_use.insert(vscp);
        }
    }

    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
        pre();
        iterate(nodep->rhsp());
        iterate(nodep->lhsp());
        post(nodep);
    }

    virtual void visit(AstIf* nodep) VL_OVERRIDE {
        pre();
        iterate(nodep->condp());
        post(nodep);
    }

    virtual void visit(AstDisplay* nodep) VL_OVERRIDE {
        pre();
        iterateChildrenConst(nodep);
        post(nodep);
    }
    virtual void visit(AstSFormatF* nodep) VL_OVERRIDE { iterateChildrenConst(nodep); }
    virtual void visit(AstCCall* nodep) VL_OVERRIDE { iterateChildrenConst(nodep); }
    virtual void visit(AstNodeMath* nodep) VL_OVERRIDE { iterateChildrenConst(nodep); }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        v3fatal(string("NO BOTTOM! ") + nodep->typeName());
    }
};

static LivenessAnalysisTransferFunctions g_tf;

class LivenessAnalysis : public V3FlowAnalysis<false, VarScopeSet> {
public:
    LivenessAnalysis()
        : V3FlowAnalysis(g_lattice, g_tf) {}
};

static LivenessAnalysis g_la;

//######################################################################
// Life class functions

void V3BetterLife::all(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    V3FlowGraph* const flowGraphp = V3FlowGraph::build(nodep->evalp());

    LivenessAnalysis::Solution liveVariables = g_la(*flowGraphp);

    for (auto pair : liveVariables) {
        UINFO(0, pair.first << " :: " << pair.second.size() << std::endl);
        for (auto v : pair.second) { UINFO(0, "    " << v << std::endl); }
    }

    delete flowGraphp;
    //    nodep->evalp()

    V3Global::dumpCheckGlobalTree("better-life", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
