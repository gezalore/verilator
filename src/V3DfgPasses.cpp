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

#include "V3DfgPasses.h"

#include "V3Dfg.h"
#include "V3Global.h"
#include "V3String.h"

#include <algorithm>
#include <type_traits>

VL_DEFINE_DEBUG_FUNCTIONS;

V3DfgCseContext::~V3DfgCseContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " CSE, expressions eliminated",
                     m_eliminated);
}

DfgRemoveVarsContext::~DfgRemoveVarsContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " Remove vars, variables removed",
                     m_removed);
}

static std::string getPrefix(const std::string& label) {
    if (label.empty()) return "";
    std::string str = VString::removeWhitespace(label);
    std::transform(str.begin(), str.end(), str.begin(), [](unsigned char c) {  //
        return c == ' ' ? '-' : std::tolower(c);
    });
    str += "-";
    return str;
}

V3DfgOptimizationContext::V3DfgOptimizationContext(const std::string& label)
    : m_label{label}
    , m_prefix{getPrefix(label)} {}

V3DfgOptimizationContext::~V3DfgOptimizationContext() {
    const string prefix = "Optimizations, DFG " + m_label + " ";
    V3Stats::addStat(prefix + "General, modules", m_modules);
    V3Stats::addStat(prefix + "Ast2Dfg, coalesced assignments", m_coalescedAssignments);
    V3Stats::addStat(prefix + "Ast2Dfg, input equations", m_inputEquations);
    V3Stats::addStat(prefix + "Ast2Dfg, representable", m_representable);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (dtype)", m_nonRepDType);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (impure)", m_nonRepImpure);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (timing)", m_nonRepTiming);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (lhs)", m_nonRepLhs);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (node)", m_nonRepNode);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (unknown)", m_nonRepUnknown);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (var ref)", m_nonRepVarRef);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (width)", m_nonRepWidth);
    V3Stats::addStat(prefix + "Dfg2Ast, intermediate variables", m_intermediateVars);
    V3Stats::addStat(prefix + "Dfg2Ast, replaced variables", m_replacedVars);
    V3Stats::addStat(prefix + "Dfg2Ast, result equations", m_resultEquations);

    // Check the stats are consistent
    UASSERT(m_inputEquations
                == m_representable + m_nonRepDType + m_nonRepImpure + m_nonRepTiming + m_nonRepLhs
                       + m_nonRepNode + m_nonRepUnknown + m_nonRepVarRef + m_nonRepWidth,
            "Inconsistent statistics");
}

// Common subexpression elimination
void V3DfgPasses::cse(DfgGraph& dfg, V3DfgCseContext& ctx) {
    DfgVertex::HashCache hashCache;
    DfgVertex::EqualsCache equalsCache;
    std::unordered_multimap<V3Hash, DfgVertex*> verticesWithEqualHashes;

    // In reverse, as the graph is sometimes in reverse topological order already
    dfg.forEachVertexInReverse([&](DfgVertex& vtx) {
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

void V3DfgPasses::removeVars(DfgGraph& dfg, DfgRemoveVarsContext& ctx) {
    dfg.forEachVertex([&](DfgVertex& vtx) {
        // We can eliminate certain redundant DfgVarPacked vertices
        DfgVarPacked* const varp = vtx.cast<DfgVarPacked>();
        if (!varp) return;

        // Can't remove if it has consumers
        if (varp->hasSinks()) return;

        // Can't remove if read in the module and driven here (i.e.: it's an output of the DFG)
        if (varp->hasModRefs() && varp->isDrivenByDfg()) return;

        // Can't remove if only partially driven by the DFG
        if (varp->isDrivenByDfg() && !varp->isDrivenFullyByDfg()) return;

        // Can't remove if referenced externally, or other special reasons
        if (varp->keep()) return;

        // If the driver of this variable has multiple non-variable sinks, then we would need
        // a temporary when rendering the graph. Instead of introducing a temporary, keep the
        // first variable that is driven by that driver
        if (varp->isDrivenByDfg()) {
            DfgVertex* const driverp = varp->source(0);
            unsigned nonVarSinks = 0;
            const DfgVarPacked* firstSinkVarp = nullptr;
            const bool keepFirst = driverp->findSink<DfgVertex>([&](const DfgVertex& sink) {
                if (const DfgVarPacked* const sinkVarp = sink.cast<DfgVarPacked>()) {
                    if (!firstSinkVarp) firstSinkVarp = sinkVarp;
                } else {
                    ++nonVarSinks;
                }
                // We can stop as soon as we found the first var, and 2 non-var sinks
                return firstSinkVarp && nonVarSinks >= 2;
            });
            // Keep this DfgVarPacked if needed
            if (keepFirst && firstSinkVarp == varp) return;
        }

        // OK, we can delete this DfgVarPacked
        ++ctx.m_removed;

        // If not referenced outside the DFG, then also delete the referenced AstVar,
        // as it is now unused.
        if (!varp->hasRefs()) varp->varp()->unlinkFrBack()->deleteTree();

        // Unlink and delete vertex
        vtx.unlinkDelete(dfg);
    });
}

bool isRootOfRightLeaningBinaryTree(DfgVertexWithArity<2>* vtxp) {
    // If RHS is a different type of node, then the tree rooted here is a single op, ignore
    if (vtxp->rhsp()->type() != vtxp->type()) return false;
    // We can only balance trees, so the tree rooted here is a single op, ignore
    if (vtxp->rhsp()->hasMultipleSinks()) return false;
    // This needs a temporary, so root here
    if (vtxp->hasMultipleSinks()) return true;
    // Feeds a different type of vertex, so root here
    if (vtxp->sinkp()->type() != vtxp->type()) return true;
    // Feeds the same type of vertex, but on the lhs, root here
    if (vtxp == static_cast<DfgVertexWithArity<2>*>(vtxp->sinkp())->lhsp()) return true;
    // Not a root
    return false;
}

template <typename Vertex>
void balanceRightLeaningBinaryTreeRootedAt(DfgGraph& dfg, Vertex* vtxp) {
    DfgVertex* const rootp = vtxp;
    DfgVertex* lastp = vtxp->rhsp();
    std::vector<std::pair<DfgVertex*, FileLine*>> terms;

    // Gather all the terms
    terms.emplace_back(vtxp->lhsp(), vtxp->fileline());
    while (lastp->is<Vertex>() && !lastp->hasMultipleSinks()) {
        vtxp = lastp->as<Vertex>();
        terms.emplace_back(vtxp->lhsp(), vtxp->fileline());
        lastp = vtxp->rhsp();
    }
    terms.emplace_back(lastp, nullptr);

    const size_t nTerms = terms.size();

    // Recursively concatenate them pairwise
    for (size_t stride = 1; stride < nTerms; stride *= 2) {
        for (size_t i = 0; i + stride < nTerms; i += 2 * stride) {
            const size_t j = i + stride;
            DfgVertex* const lhsp = terms[i].first;
            DfgVertex* const rhsp = terms[j].first;
            // The FileLine is chosen such that e.g.: '(a | (b | (c | d))' maps to
            // '(a | b) | (c | d)' with the locations of the operators being unaltered
            FileLine* const flp = terms[j - 1].second;
            const auto dtypep = std::is_same<Vertex, DfgConcat>::value
                                    ? DfgVertex::dtypeForWidth(lhsp->width() + rhsp->width())
                                    : lhsp->dtypep();
            Vertex* const vtxp = new Vertex{dfg, flp, dtypep};
            vtxp->lhsp(lhsp);
            vtxp->rhsp(rhsp);
            terms[i].first = vtxp;
        }
    }

    // Replace the root node with the result
    rootp->replaceWith(terms[0].first);

    // Remove all the replaced terms
    for (DfgVertex *currp = rootp, *nextp; currp != lastp; currp = nextp) {
        nextp = currp->as<Vertex>()->rhsp();
        currp->unlinkDelete(dfg);
    }
}

// Convert right leaning binary expression trees (e.g.: 'a | (b | (c | d)') to balanced binary
// trees (e.g.: '(a | b) | (c | d)'). While the impact of this on the performance of the generated
// code is close to neutral, it has the following benefits:
// - Allows for further CSE opportunities in a later pass due to representational perturbations
// - Reduces peak memory consumption of Verilator in the later stages. Namely, a ~30% peak memory
//   consumption reduction was observed on OpenTitan in the V3Expand and V3Subst passes using
//   OpenTitan. The reason for this in relation to this balancing transformation is not clear,
//   but we will take the win.
// - DFG dumps are a lot clearer to look at when scouting for further opportunities.
void V3DfgPasses::balanceRightLeaningBinaryTrees(DfgGraph& dfg) {
    std::vector<DfgConcat*> rootConcatps;
    std::vector<DfgAnd*> rootAndps;
    std::vector<DfgOr*> rootOrps;
    std::vector<DfgXor*> rootXorps;
    std::vector<DfgAdd*> rootAddps;

    // Gather all the roots of non-trivial (has more than one vertex) right leaning binary trees.
    dfg.forEachVertex([&](DfgVertex& vtx) {
        // No point to optimize unused vertices. Note: We cannot remove vertices here as we rely on
        // the number of sinks to determine roots. If we remove vertices as we collect the roots,
        // we might add a root that due to a removal is no longer a root but is a part of a larger
        // tree, in which case we would invoke the balancing on two nodes within the same tree (one
        // non-root), which would end badly.
        if (!vtx.hasSinks()) return;

        if (DfgConcat* const p = vtx.cast<DfgConcat>()) {
            if (isRootOfRightLeaningBinaryTree(p)) rootConcatps.push_back(p);
        } else if (DfgAnd* const p = vtx.cast<DfgAnd>()) {
            if (isRootOfRightLeaningBinaryTree(p)) rootAndps.push_back(p);
        } else if (DfgOr* const p = vtx.cast<DfgOr>()) {
            if (isRootOfRightLeaningBinaryTree(p)) rootOrps.push_back(p);
        } else if (DfgXor* const p = vtx.cast<DfgXor>()) {
            if (isRootOfRightLeaningBinaryTree(p)) rootXorps.push_back(p);
        } else if (DfgAdd* const p = vtx.cast<DfgAdd>()) {
            if (isRootOfRightLeaningBinaryTree(p)) rootAddps.push_back(p);
        }
    });

    // Optimize each root
    for (const auto p : rootConcatps) balanceRightLeaningBinaryTreeRootedAt(dfg, p);
    for (const auto p : rootAndps) balanceRightLeaningBinaryTreeRootedAt(dfg, p);
    for (const auto p : rootOrps) balanceRightLeaningBinaryTreeRootedAt(dfg, p);
    for (const auto p : rootXorps) balanceRightLeaningBinaryTreeRootedAt(dfg, p);
    for (const auto p : rootAddps) balanceRightLeaningBinaryTreeRootedAt(dfg, p);
}

void V3DfgPasses::removeUnused(DfgGraph& dfg) {
    const auto processVertex = [&](DfgVertex& vtx) {
        // Keep variables
        if (vtx.is<DfgVarPacked>() || vtx.is<DfgVarArray>()) return false;
        // Keep if it has sinks
        if (vtx.hasSinks()) return false;
        // Unlink and delete vertex
        vtx.unlinkDelete(dfg);
        return true;
    };

    dfg.runToFixedPoint(processVertex);
}

void V3DfgPasses::optimize(DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
    // There is absolutely nothing useful we can do with a graph of size 2 or less
    if (dfg.size() <= 2) return;

    int passNumber = 0;

    const auto apply = [&](int dumpLevel, const string name, std::function<void()> pass) {
        pass();
        if (dumpDfg() >= dumpLevel) {
            const string strippedName = VString::removeWhitespace(name);
            const string label
                = ctx.prefix() + "pass-" + cvtToStr(passNumber) + "-" + strippedName;
            dfg.dumpDotFilePrefixed(label);
        }
        ++passNumber;
    };

    if (dumpDfg() >= 8) dfg.dumpDotAllVarConesPrefixed(ctx.prefix() + "input");
    apply(3, "input         ", [&]() {});
    apply(4, "cse           ", [&]() { cse(dfg, ctx.m_cseContext0); });
    if (v3Global.opt.fDfgPeephole()) {
        apply(4, "peephole      ", [&]() { peephole(dfg, ctx.m_peepholeContext); });
        // Without peephole no variables will be redundant, and we just did CSE, so skip these
        apply(4, "removeVars    ", [&]() { removeVars(dfg, ctx.m_removeVarsContext); });
        apply(4, "cse           ", [&]() { cse(dfg, ctx.m_cseContext1); });
    }
    apply(4, "balance       ", [&]() { balanceRightLeaningBinaryTrees(dfg); });
    apply(3, "optimized     ", [&]() { removeUnused(dfg); });
    if (dumpDfg() >= 8) dfg.dumpDotAllVarConesPrefixed(ctx.prefix() + "optimized");
}
