// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generic data-flow analysis framework
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
//
//*************************************************************************

#ifndef VERILATOR_V3DATAFLOWANALYSIS_H_
#define VERILATOR_V3DATAFLOWANALYSIS_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <unordered_map>

// This class is an interface for the description of a meet (or lower) semilattice
// (https://en.wikipedia.org/wiki/Semilattice) used in a general data flow analysis framework.
// Briefly, the important properties are as follows:
//
// A meet semilattice is defined by a set 'S' and a binary operator '/\' pronounced 'meet'.
// For all values 'x', 'y', 'z' from 'S', the meet operator must have the following properties:
//      1. Associativity: x /\ (y /\ z) == (x /\ y) /\ z
//      2. Commutativity: x /\ y == y /\ x
//      3. Idempotency: x /\ x == x
//
// The meet operator induces a partial order '<=' over the set 'S', with the following properties
// of interest:
//      1. x /\ y <= x
//      2. x /\ y <= y
//      3. if z <= x and z <= y then z <= x /\ y
// The last point says that 'x /\ y' is the 'greatest lower bound' of 'x' and 'y'.
//
// For our purposes the semilattice also needs to be bounded, which means that an element 'T'
// (pronounced 'top') of 'S' exists such that for all 'x' in 'S':
//      T /\ x == x
// With respect to the partial order '<=', 'T' is the largest element.
//
// Albeit the above would be enough for the general data flow frameworks, for practical
// implementation reasons we will also require the existence of an element 'B' (pronounced
// 'bottom') of 'S' suc that for all 'x' in 'S':
//      B /\ x == B
// That is: 'B' is the smallest element with respect to '<='. In the data flow problem,
// 'B' is the most conservative solution, which we can use for nodes we cannot otherwise handle.
template <typename T_Elem>  // The type of the domain 'S'
class V3Semilattice VL_NOT_FINAL {
    static_assert(!std::is_const<T_Elem>::value,
                  "Type parameter 'T_Elem' should not be const qualified");

public:
    // The meet operator. Must be associative, commutative and idempotent.
    // TODO: universal short circuiting if a is b (idempotency)
    virtual T_Elem meet(const T_Elem& a, const T_Elem& b) const = 0;
    // The top element
    virtual T_Elem top() const = 0;
    // The bottom element
    virtual T_Elem bottom() const = 0;
    //    //
    //    virtual bool eq(const T_Elem& x, const T_Elem& y) const = 0;  // TODO: explain
};

// The transfer functions of a data flow analysis transform elements of the domain 'S'.
template <typename T_Elem>  // The type of the domain 'S'
class V3TransferFunctions VL_NOT_FINAL {
    static_assert(!std::is_const<T_Elem>::value,
                  "Type parameter 'T_Elem' should not be const qualified");

public:
    // The constant transfer function of the entry/exit node. Used to
    // initialize the boundary condition of the data flow problems.
    virtual T_Elem initial() const = 0;

    // The transfer functions of various nodes
    virtual T_Elem apply(const AstIf* nodep, const T_Elem& in) const = 0;
    virtual T_Elem apply(const AstWhile* nodep, const T_Elem& in) const = 0;
    virtual T_Elem apply(const AstNodeAssign* nodep, const T_Elem& in) const = 0;

    //    T_Elem apply(AstNode* nodep, const T_Elem&) const {
    //        nodep->v3fatalSrc("No transfer function for node type: " << nodep->typeName());
    //    }
};

// Data flow analysis direction
enum class V3DataFlowDirection : bool {  //
    Forward = false,
    Backward = true
};

// A data flow analysis is defined by:
//      1. A direction 'D' which is either 'forward' or 'backward'
//      2. A semilattice which includes the domain 'S' and a meet operator '/\'
//      3. A family of transfer functions 'F' from 'S' to 'S'
template <V3DataFlowDirection T_Direction,  // The data flow direction 'D'
          typename T_Elem>  // The type of the elements of domain 'S'
class V3DataFlowAnalysis final : VNVisitor {
    static_assert(!std::is_const<T_Elem>::value,
                  "Type parameter 'T_Elem' should not be const qualified");

    const V3Semilattice<T_Elem>& m_lattice;  // For completions
    const V3TransferFunctions<T_Elem>& m_tf;
    const T_Elem m_top = m_lattice.top();  // A canonical top instance for fast copying
    const T_Elem m_bottom = m_lattice.bottom();  // A canonical bottom instance for fast copying

    std::unordered_map<const AstNode*, T_Elem> m_before;  // Data flow values before the nodes
    std::unordered_map<const AstNode*, T_Elem> m_after;  // Data flow values after the nodes

    AstCFunc* m_funcp;  // Current function we are analysing, if known

public:
    V3DataFlowAnalysis(const V3Semilattice<T_Elem>& lattice, const V3TransferFunctions<T_Elem>& tf)
        : m_lattice{lattice}
        , m_tf{tf} {}

    // The flow analysis can be invoked on a statements, and returns a solution. The solution to
    // the data flow problem is a map from nodes to elements of the domain. This map holds the data
    // flow values outgoing from the node. That is, for a forward problem, the map holds the data
    // flow values after the node, and for a backward problem the map holds the data flow values
    // before the node. Note that the map might be sparse. In particular, nodes that are under
    // unhandled constructs might not be in the map. For such nodes, assume the bottom solution.

    // TODO: It would be nice if all statements were AstNodeStmt...
    std::unordered_map<const AstNode*, T_Elem> operator()(const AstNode* nodep) {
        UASSERT_OBJ(m_before.empty(), nodep, "Should be empty");
        UASSERT_OBJ(m_after.empty(), nodep, "Should be empty");
        if (T_Direction == V3DataFlowDirection::Backward) {
            // Set boundary condition
            m_after.emplace(nodep, m_tf.initial());
            // Solve
            iterate(const_cast<AstNode*>(nodep));
            // Clean up and return solution
            m_after.clear();
            return std::move(m_before);
        } else {
            // Set boundary condition
            m_before.emplace(nodep, m_tf.initial());
            // Solve
            iterate(const_cast<AstNode*>(nodep));
            // Clean up and return solution
            m_before.clear();
            return std::move(m_after);
        }
    }

private:
    T_Elem meet(const T_Elem& a, const T_Elem& b) const { return m_lattice.meet(a, b); }
    template <typename T_Node>  //
    T_Elem tf(const T_Node* nodep, const T_Elem& in) const {
        return m_tf.apply(nodep, in);
    }

    T_Elem& before(const AstNode* nodep) { return m_before.emplace(nodep, m_top).first->second; }
    T_Elem& after(const AstNode* nodep) { return m_after.emplace(nodep, m_top).first->second; }

    // The solution for the continuation (successors) of this node. This must exist.
    const T_Elem& solutionCont(const AstNode* nodep) const { return m_after.at(nodep); }

    const T_Elem& solve(const AstNode* headp, const T_Elem& solutionContinuation) {
        UASSERT_OBJ(T_Direction == V3DataFlowDirection::Backward, headp, "this  is for bwd");
        // Empty list is easy ...
        if (!headp) return solutionContinuation;
        // Set initial condition for list
        after(headp->tailp()) = solutionContinuation;
        // Iterate list backwards
        for (AstNode *nodep = headp->tailp(), *prevp; nodep; nodep = prevp) {
            prevp = nodep == headp ? nullptr : nodep->backp();
            // The 'visit' functions update the 'before' of the node.
            iterate(nodep);
            // The after of the predecessor node in the list is simply the before of this node
            if (prevp) after(prevp) = before(nodep);
        }
        // Done
        return before(headp);
    }

    // VISITORS

    void visit(AstIf* nodep) override {
        const T_Elem& solutionThen = solve(nodep->ifsp(), solutionCont(nodep));
        const T_Elem& solutionElse = solve(nodep->elsesp(), solutionCont(nodep));
        before(nodep) = tf(nodep, meet(solutionThen, solutionElse));
    }

    void visit(AstWhile* nodep) override {
        for (bool changed = true; changed;) {
            const T_Elem solutionBefore = before(nodep);
            const T_Elem& solutionInc = solve(nodep->incsp(), solutionBefore);
            const T_Elem& solutionBody = solve(nodep->bodysp(), solutionInc);
            const T_Elem& solutionCond = tf(nodep, meet(solutionBody, solutionCont(nodep)));
            before(nodep) = solve(nodep->precondsp(), solutionCond);
            changed = solutionBefore != before(nodep);
        };
    }

    void visit(AstNodeAssign* nodep) override { before(nodep) = tf(nodep, after(nodep)); }

    void visit(AstCCall* nodep) override {}

    void visit(AstCFunc* nodep) override {
        UASSERT_OBJ(T_Direction == V3DataFlowDirection::Backward, nodep, "");
        VL_RESTORER(m_funcp);
        m_funcp = nodep;
        const T_Elem& solutionFinals = solve(nodep->finalsp(), solutionCont(nodep));
        const T_Elem& solutionStmts = solve(nodep->stmtsp(), solutionFinals);
        before(nodep) = solve(nodep->initsp(), solutionFinals);
    }

    void visit(AstNode* nodep) override {
        nodep->v3fatalSrc(
            "Data flow analysis encountered unhandled node type: " << nodep->typeName());
    }
};

#endif