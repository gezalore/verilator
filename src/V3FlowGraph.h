// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Control Flow Graph
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

#ifndef _V3FLOWGRAPH_H_
#define _V3FLOWGRAPH_H_ 1

#include <functional>

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"

class V3FlowGraph;

class V3FlowVertex : public V3GraphVertex {
    friend class V3FlowGraph;

public:
    AstNode* const m_nodep;  // The statement in this node
private:
    void* m_dfvi;  // The incoming data flow value
    void* m_dfvo;  // The outgoing data flow value
protected:
    unsigned m_pon;  // Post order number (i.e.: position in post order
    // enumeration of vertices). '0' means unassigned.
    void assignPon(unsigned& next);  // Compute post order enumeration
public:
    V3FlowVertex(V3FlowGraph* graphp, AstNode* nodep);
    virtual ~V3FlowVertex() {}

    virtual int sortCmp(const V3GraphVertex* rhsp) const VL_OVERRIDE {
        // Sort in reverse post order (i.e.: depth first order)
        return reinterpret_cast<const V3FlowVertex*>(rhsp)->m_pon - m_pon;
    }

    // Allocate data flow values
    template <typename T> void allocDfvs() {
        UASSERT(!m_dfvi && !m_dfvi, "Already allocated");
        m_dfvi = new T;
        m_dfvo = new T;
    }
    // Free data flow values
    template <typename T> void freeDfvs() {
        UASSERT(m_dfvi && m_dfvi, "Not allocated");
        delete reinterpret_cast<T*>(m_dfvi);
        delete reinterpret_cast<T*>(m_dfvo);
    }
    // Get references to data flow values
    template <typename T> T& dfvi() const { return *reinterpret_cast<T*>(m_dfvi); }
    template <typename T> T& dfvo() const { return *reinterpret_cast<T*>(m_dfvo); }

    // Apply function to each predecessor of this vertex
    void foreachPredecessor(std::function<void(V3FlowVertex&)>&& f) {
        for (V3GraphEdge* ep = inBeginp(); ep; ep = ep->inNextp()) {
            f(*static_cast<V3FlowVertex*>(ep->fromp()));
        }
    }

    // Apply function to each successor of this vertex
    void foreachSuccessor(std::function<void(V3FlowVertex&)>&& f) {
        for (V3GraphEdge* ep = outBeginp(); ep; ep = ep->outNextp()) {
            f(*static_cast<V3FlowVertex*>(ep->top()));
        }
    }

    // Debug
    string name() const VL_OVERRIDE { return cvtToStr(m_nodep) + " :: " + cvtToStr(m_pon); }
    string dotShape() const VL_OVERRIDE { return "box"; }
};

class V3FlowGraph : public V3Graph {
public:
    V3FlowVertex* const m_entryp;  // Entry vertex of control flow graph
    V3FlowVertex* const m_exitp;  // Exit vertex of control flow graph

public:
    V3FlowGraph();
    virtual ~V3FlowGraph();

    // Apply function to each vertex except the entry vertex in depth first
    // order (for forward data flow analysis)
    void iterateVerticesForward(std::function<void(V3FlowVertex&)>&& f) {
        for (V3GraphVertex* vp = verticesBeginp(); vp; vp = vp->verticesNextp()) {
            if (vp == m_entryp) continue;
            f(*static_cast<V3FlowVertex*>(vp));
        }
    }

    // Apply function to each vertex except the exit vertex in reverse depth
    // first order (for backward data flow analysis)
    void iterateVerticesBackward(std::function<void(V3FlowVertex&)>&& f) {
        for (V3GraphVertex* vp = verticesLastp(); vp; vp = vp->verticesPrevp()) {
            if (vp == m_exitp) continue;
            f(*static_cast<V3FlowVertex*>(vp));
        }
    }

    // Apply function to each vertex in some arbitrary order
    void foreachVertex(std::function<void(V3FlowVertex&)>&& f) {
        for (V3GraphVertex* vp = verticesBeginp(); vp; vp = vp->verticesNextp()) {
            f(*static_cast<V3FlowVertex*>(vp));
        }
    }

    template <typename T> void allocateDataFlowValues() {
        foreachVertex([](V3FlowVertex& v) {  //
            v.allocDfvs<T>();
        });
    }
    template <typename T> void freeDataFlowValues() {
        foreachVertex([](V3FlowVertex& v) {  //
            v.freeDfvs<T>();
        });
    }

    static V3FlowGraph* build(AstCFunc* nodep);
};

#endif  // Guard
