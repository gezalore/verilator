// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Passes over DfgGraph
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

#ifndef VERILATOR_V3DFGPASSES_H_
#define VERILATOR_V3DFGPASSES_H_

#include "config_build.h"

#include "V3DfgPeephole.h"

class DfgGraph;

struct V3DfgCseContext {
    VDouble0 m_eliminated;  // Number of common sub-expressions eliminated

    ~V3DfgCseContext();
};

struct V3DfgOptimizationContext {
    V3DfgCseContext m_cseContext;
    V3DfgPeepholeContext m_peepholeContext;
};

class V3DfgPasses final {
    static void inlineVars(DfgGraph&);
    static void cse(DfgGraph&, V3DfgCseContext&);
    static void peephole(DfgGraph&, V3DfgPeepholeContext&);

public:
    // Construct a DfGGraph representing the combinational logic in the given AstModule. Return the
    // constructed DfgGraph, and a vector of all AstNodes that are represented by the DfgGraph. The
    // returned DfgGraph represents exactly the same logic as the returned vector of AstNodes,
    // i.e.: the two are semantically interchangeable.
    static DfgGraph* astToDfg(AstModule&);

    // Optimize the given DfgGraph
    static void optimize(DfgGraph&, V3DfgOptimizationContext&);

    // Convert DfgGraph back into Ast, and insert converted graph back into it's parent module.
    // Returns the parent module.
    static AstModule* dfgToAst(DfgGraph&);
};

#endif
