// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementations of simple passes over DfgGraph
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

#include "config_build.h"

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Global.h"

V3DfgCseContext::~V3DfgCseContext() {
    V3Stats::addStat("Optimizations, DFG CSE, expressions eliminated", m_eliminated);
}

// 'Inline' DfgVar nodes with known drivers
void V3DfgPasses::inlineVars(DfgGraph& dfg) {
    dfg.forEachVertex([](DfgVertex& vtx) {
        // For each DfgVar that has a known driver
        if (DfgVar* const varVtxp = vtx.cast<DfgVar>()) {
            if (DfgVertex* const driverp = varVtxp->driverp()) {
                // Make consumers of the DfgVar consume the driver directly
                varVtxp->forEachSinkEdge([=](DfgEdge& edge) { edge.relinkSource(driverp); });
            }
        }
    });
}

// Common subexpression elimination
void V3DfgPasses::cse(DfgGraph& dfg, V3DfgCseContext& ctx) {
    DfgVertex::HashCache hashCache;
    DfgVertex::EqualsCache equalsCache;
    std::unordered_multimap<V3Hash, DfgVertex*> verticesWithEqualHashes;

    dfg.forEachVertex([&](DfgVertex& vtx) {
        // Don't merge constants
        if (vtx.is<DfgConst>()) return;
        // For everything else...
        const V3Hash hash = vtx.hash(hashCache);
        auto pair = verticesWithEqualHashes.equal_range(hash);
        for (auto it = pair.first, end = pair.second; it != end; ++it) {
            DfgVertex* const candidatep = it->second;
            if (candidatep->equals(vtx, equalsCache)) {
                ++ctx.m_eliminated;
                vtx.replaceWith(candidatep);
                vtx.unlinkDelete(dfg);
                return;
            }
        }
        verticesWithEqualHashes.emplace(hash, &vtx);
    });
}

void V3DfgPasses::optimize(DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
    const auto applyPass = [&](const string name, std::function<void()> pass) {
        pass();
        if (v3Global.opt.dumpDfg() >= 2) dfg.dumpDotFilePrefixed(dfg.name() + "-" + name);
    };

    applyPass("inline", [&]() { inlineVars(dfg); });
    applyPass("cse-0", [&]() { cse(dfg, ctx.m_cseContext); });
    applyPass("peephole", [&]() { peephole(dfg, ctx.m_peepholeContext); });
    applyPass("cse-1", [&]() { cse(dfg, ctx.m_cseContext); });
}