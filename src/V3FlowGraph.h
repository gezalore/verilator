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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"

class V3FlowVertex;

class V3FlowGraph : public V3Graph {
public:
    V3FlowVertex* const m_entryp;  // Entry node of control flow graph
    V3FlowVertex* const m_exitp;  // Exit node of control flow graph

public:
    V3FlowGraph();
    virtual ~V3FlowGraph();

    static void build(AstCFunc* nodep);
};

class V3FlowVertex : public V3GraphVertex {
public:
    const AstNode* const m_nodep; // The statement in this node
    V3FlowVertex(V3FlowGraph* graphp, const AstNode* nodep)
        : V3GraphVertex(graphp)
        , m_nodep(nodep) {}
    virtual ~V3FlowVertex() {}

    string name() const VL_OVERRIDE { return cvtToStr(m_nodep); }
    string dotShape() const VL_OVERRIDE { return "box"; }
};

#endif  // Guard
