// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generic data flow analysis framework
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

#ifndef _V3FLOWANALYSIS_H_
#define _V3FLOWANALYSIS_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3FlowGraph.h"

#include VL_INCLUDE_UNORDERED_MAP

// This class is an interface for the description of a meet (or lower)
// semilattice (https://en.wikipedia.org/wiki/Semilattice) used in the general
// data flow analysis framework. We present the important properties briefly:
//
// A meet semilattice is defined by a set 'S' and and a binary operator '/\'
// pronounced 'meet'. For all values 'x', 'y', 'z' from 'S', the meet operator
// must have the following properties:
//      1. Associativity: x /\ (y /\ z) == (x /\ y) /\ z
//      2. Commutativity: x /\ y == y /\ x
//      3. Idempotency: x /\ x == x
// The meet operator induces a partial order '<=' over the set 'S', with the
// following properties of interest:
//      1. x /\ y <= x
//      2. x /\ y <= y
//      3. if z <= x and z <= y then z <= x /\ y
// The last point says that 'x /\ y' is the greatest lower bound of 'x' and 'y'.
// For our purposes the semilattice also needs to be bounded, which means that
// an element 'T' (pronounced 'top') of 'S' exists such that for all 'x' in 'S':
//      T /\ x == x
// With respect to the partial order '<=', 'T' is the largest element.
// Albeit the above would be enough for the general data flow frameworks, for
// practical implementation reasons we will also requires the existence of an
// element 'B' (pronounced 'bottom') of 'S' suc that for all 'x' in 'S':
//      B /\ x == B
// That is: 'B' is the smallest element with respect to '<='
template <typename T_Elem>  // The type of the domain 'S'
class V3Semilattice {
public:
    // The meet operator. Must be associative, commutative and idempotent.
    virtual T_Elem meet(const T_Elem& x, const T_Elem& y) const = 0;
    // The top element
    virtual T_Elem top() const = 0;
    // The bottom element
    virtual T_Elem bottom() const = 0;
    virtual bool eq(const T_Elem& x, const T_Elem& y) const = 0;  // TODO: explain
};

// The transfer functions of a data flow analysis transform elements of a set
// 'S'. Since transfer functions depend heavily on the type of nodes, we use a
// visitor to represent them to take advantage of dynamic type based dispatch.
template <typename T_Elem>  // The type of the domain 'S'
class V3TransferFunctions : public AstNVisitor {
protected:
    const V3Semilattice<T_Elem>& m_lattice;
    const T_Elem* m_argp;  // Argument of transfer function
    T_Elem m_ret;  // Return value of transfer function
public:
    V3TransferFunctions(const V3Semilattice<T_Elem>& lattice)
        : m_lattice(lattice) {}

    // Apply transfer function of given node to x
    T_Elem operator()(AstNode* nodep, const T_Elem& arg) {
        m_argp = &arg;  // Keep hold of argument
        iterate(nodep);  // Dispatch to visit to do the work
        return m_ret;  // Return the result
    }

    // The constant transfer function of the entry/exit node. Used to
    // initialize the boundary condition of the data flow problems.
    virtual T_Elem start() const = 0;

protected:
    // VISITORS
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        // The most conservative (i.e.: safest) solution to a data flow problem
        // is the bottom element of the lattice, as this contains the least
        // amount of information about the program. We return this by default.
        // Note: This is the only reason we need to have a bottom in the
        // lattice.
        m_ret = m_lattice.bottom();
    }
};

// A data flow analysis is defined by:
//      1. A direction D which is either 'forward' or 'backward'
//      2. A semilattice which includes the domain 'S' and a meet operator '/\'
//      3. A family of transfer functions 'F' from 'S' to 'S'
template <bool T_Forward,  // The data flow direction
          typename T_Elem>  // The type of the domain 'S'
class V3FlowAnalysis {
    const V3Semilattice<T_Elem>& m_lattice;
    V3TransferFunctions<T_Elem>& m_tf;

public:
    V3FlowAnalysis(const V3Semilattice<T_Elem>& lattice,
                   V3TransferFunctions<T_Elem>& transferFunctions)
        : m_lattice(lattice)
        , m_tf(transferFunctions) {}

    // The solution to a data flow problem is a map from nodes to elements of
    // the domain. This map holds the data flow values incoming to the node.
    // That is, for a forward problem, the map holds the data flow values
    // before the node, and for a backward problem the map holds the data flow
    // values after the node.
    typedef vl_unordered_map<const AstNode*, T_Elem> Solution;

    // The flow analysis can be invoked on a flow graph, returning the solution.
    Solution operator()(V3FlowGraph& flowGraph) const {
        return T_Forward ? fwd(flowGraph) : bwd(flowGraph);
    }

private:
    Solution fwd(V3FlowGraph& flowGraph) const {
        // Allocate data flow values
        flowGraph.allocateDataFlowValues<T_Elem>();
        // Set boundary condition
        flowGraph.m_entryp->dfvo<T_Elem>() = m_tf.start();
        // Set initial solutions
        flowGraph.iterateVerticesForward([&](V3FlowVertex& v) {  //
            v.dfvo<T_Elem>() = m_lattice.top();
        });
        // Iterate until the fixed point is reached.
        for (bool change = true; change;) {
            change = false;
            flowGraph.iterateVerticesForward([&](V3FlowVertex& v) {
                // Reduce incoming values using the meet operator
                T_Elem acc = m_lattice.top();
                v.foreachPredecessor([&](const V3FlowVertex& pred) {
                    acc = m_lattice.meet(acc, pred.dfvo<T_Elem>());
                });
                // Apply transfer function
                T_Elem o = v.m_nodep ? m_tf(v.m_nodep, acc) : acc;
                // Check for change
                if (!m_lattice.eq(o, v.dfvo<T_Elem>())) {  //
                    change = true;
                }
                // Store data flow values
                v.dfvi<T_Elem>() = std::move(acc);
                v.dfvo<T_Elem>() = std::move(o);
            });
        }
        // Build the solution map
        Solution s;
        flowGraph.foreachVertex([&](V3FlowVertex& v) {
            const AstNode* const nodep = v.m_nodep;
            if (!nodep) return;  // Skip empty nodes
            const auto& dfvi = v.dfvi<T_Elem>();
            const auto it = s.find(nodep);
            s[nodep] = it == s.end() ? dfvi : m_lattice.meet(it->second, dfvi);
        });
        // Free data flow values
        flowGraph.freeDataFlowValues<T_Elem>();
        // Done
        return s;
    }

    Solution bwd(V3FlowGraph& flowGraph) const {  // Allocate data flow values
        flowGraph.allocateDataFlowValues<T_Elem>();
        // Set boundary condition
        flowGraph.m_exitp->dfvi<T_Elem>() = m_tf.start();
        // Set initial solutions
        flowGraph.iterateVerticesBackward([&](V3FlowVertex& v) {  //
            v.dfvi<T_Elem>() = m_lattice.top();
        });
        // Iterate until the fixed point is reached.
        for (bool change = true; change;) {
            change = false;
            flowGraph.iterateVerticesBackward([&](V3FlowVertex& v) {
                // Reduce incoming values using the meet operator
                T_Elem acc = m_lattice.top();
                v.foreachSuccessor([&](const V3FlowVertex& pred) {
                    acc = m_lattice.meet(acc, pred.dfvi<T_Elem>());
                });
                // Apply transfer function
                T_Elem i = v.m_nodep ? m_tf(v.m_nodep, acc) : acc;
                // Check for change
                if (!m_lattice.eq(i, v.dfvi<T_Elem>())) {  //
                    change = true;
                }
                // Store data flow value
                v.dfvo<T_Elem>() = std::move(acc);
                v.dfvi<T_Elem>() = std::move(i);
            });
            UINFO(0, "CHANGE " << change << endl);
        }
        // Build the solution map
        Solution s;
        flowGraph.foreachVertex([&](V3FlowVertex& v) {
            const AstNode* const nodep = v.m_nodep;
            if (!nodep) return;  // Skip empty nodes
            const auto& dfvo = v.dfvo<T_Elem>();
            const auto it = s.find(nodep);
            s[nodep] = it == s.end() ? dfvo : m_lattice.meet(it->second, dfvo);
        });
        // Free data flow values
        flowGraph.freeDataFlowValues<T_Elem>();
        // Done
        return s;
    }
};

#endif  // Guard
