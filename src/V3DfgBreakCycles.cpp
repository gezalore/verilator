// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Converting cyclic DFGs into acyclic DFGs
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"

#include <limits>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

// Similar algorithm used in ExtractCyclicComponents
class ColorStronglyConnectedComponents final {
    static constexpr uint32_t UNASSIGNED = std::numeric_limits<uint32_t>::max();

    // TYPES
    struct VertexState final {
        uint32_t component = UNASSIGNED;  // Result component number (0 means not in SCC)
        uint32_t index = UNASSIGNED;  // Used by Pearce's algorithm for detecting SCCs
        VertexState() = default;
        VertexState(uint32_t i, uint32_t n)
            : component{n}
            , index{i} {}
    };

    // STATE
    DfgGraph& m_dfg;  // The input graph
    uint32_t m_nonTrivialSCCs = 0;  // Number of non-trivial SCCs in the graph
    uint32_t m_index = 0;  // Visitation index counter
    std::vector<DfgVertex*> m_stack;  // The stack used by the algorithm

    // METHODS
    void visitColorSCCs(DfgVertex& vtx, VertexState& vtxState) {
        UDEBUGONLY(UASSERT_OBJ(vtxState.index == UNASSIGNED, &vtx, "Already visited vertex"););

        // Visiting vertex
        const size_t rootIndex = vtxState.index = ++m_index;

        // Visit children
        vtx.forEachSink([&](DfgVertex& child) {
            VertexState& childSatate = child.user<VertexState>();
            // If the child has not yet been visited, then continue traversal
            if (childSatate.index == UNASSIGNED) visitColorSCCs(child, childSatate);
            // If the child is not in an SCC
            if (childSatate.component == UNASSIGNED) {
                if (vtxState.index > childSatate.index) vtxState.index = childSatate.index;
            }
        });

        if (vtxState.index == rootIndex) {
            // This is the 'root' of an SCC

            // A trivial SCC contains only a single vertex
            const bool isTrivial = m_stack.empty()  //
                                   || m_stack.back()->getUser<VertexState>().index < rootIndex;
            // We also need a separate component for vertices that drive themselves (which can
            // happen for input like 'assign a = a'), as we want to extract them (they are cyclic).
            const bool drivesSelf = vtx.findSink<DfgVertex>([&vtx](const DfgVertex& sink) {  //
                return &vtx == &sink;
            });

            if (!isTrivial || drivesSelf) {
                // Allocate new component
                ++m_nonTrivialSCCs;
                vtxState.component = m_nonTrivialSCCs;
                while (!m_stack.empty()) {
                    VertexState& topState = m_stack.back()->getUser<VertexState>();
                    // Only higher nodes belong to the same SCC
                    if (topState.index < rootIndex) break;
                    m_stack.pop_back();
                    topState.component = m_nonTrivialSCCs;
                }
            } else {
                // Trivial SCC (and does not drive itself), so acyclic. Keep it in original graph.
                vtxState.component = 0;
            }
        } else {
            // Not the root of an SCC
            m_stack.push_back(&vtx);
        }
    }

    void colorSCCs() {
        // Implements Pearce's algorithm to color the strongly connected components. For reference
        // see "An Improved Algorithm for Finding the Strongly Connected Components of a Directed
        // Graph", David J.Pearce, 2005.

        // We know constant nodes have no input edges, so they cannot be part
        // of a non-trivial SCC. Mark them as such without any real traversals.
        for (DfgConst& vtx : m_dfg.constVertices()) vtx.setUser(VertexState{0, 0});

        // Start traversals through variables
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            VertexState& vtxState = vtx.user<VertexState>();
            // If it has no input or no outputs, it cannot be part of a non-trivial SCC.
            if (vtx.arity() == 0 || !vtx.hasSinks()) {
                UDEBUGONLY(UASSERT_OBJ(vtxState.index == UNASSIGNED || vtxState.component == 0,
                                       &vtx, "Non circular variable must be in a trivial SCC"););
                vtxState.index = 0;
                vtxState.component = 0;
                continue;
            }
            // If not yet visited, start a traversal
            if (vtxState.index == UNASSIGNED) visitColorSCCs(vtx, vtxState);
        }

        // Start traversals through variables
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            VertexState& vtxState = vtx.user<VertexState>();
            // If not yet visited, start a traversal
            if (vtxState.index == UNASSIGNED) visitColorSCCs(vtx, vtxState);
        }
    }

    ColorStronglyConnectedComponents(DfgGraph& dfg)
        : m_dfg{dfg} {
        UASSERT_OBJ(dfg.size() < UNASSIGNED, dfg.modulep(), "Graph too big");
        // Yet another implementation of Pearce's algorithm.
        colorSCCs();
        // Re-assign user values
        m_dfg.forEachVertex([](DfgVertex& vtx) {
            const uint32_t component = vtx.getUser<VertexState>().component;
            vtx.setUser<uint32_t>(component);
        });
    }

public:
    // Sets DfgVertex::user<size_t>() for all vertext to:
    // - 0, if the vertex is not part of a non-trivial strongly connected component
    //   and is not part of a self-loop. That is the Vertex is not part of any cycle
    // - N, if the vertex is part of a non-trivial strongly conneced component or self-loop N.
    //   That is, each set of vertices that are reachable from each other will ahve the same
    //   non-zero value assigned.
    // Returns the number of non-trivial SCCs (distinct cycles)
    static uint32_t apply(DfgGraph& dfg) {
        return ColorStronglyConnectedComponents{dfg}.m_nonTrivialSCCs;
    }
};

class ChaseDriver final : public DfgVisitor {

    // TYPES
    struct HashforVisited final {
        size_t operator()(const std::pair<const DfgVertex*, uint32_t>& item) const {
            const size_t a = reinterpret_cast<std::uintptr_t>(item.first);
            constexpr size_t halfWidth = 8 * sizeof(size_t) / 2;
            return a ^ (static_cast<size_t>(item.second) << halfWidth);
        }
    };

    // SATE

    // Set of visited vertex/lsb pairs
    DfgGraph& m_dfg; // The graph being processed
    std::unordered_set<std::pair<const DfgVertex*, uint32_t>, HashforVisited> m_visited;
    DfgVertex* m_currp = nullptr;  // The currently found furthest driver
    uint32_t m_lsb = 0;  // LSB to extract from the current driver
    uint32_t m_msb = 0;  // MSB to extract from the current driver
    const uint32_t m_width;  // Driver width we are trying to find
    const uint32_t m_component;  // Component we are trying to escape

    // METHODS

    // Continue chasing drivers of the given vertex, at the given LSB. Every
    // visitor should call this to continue the traversal, then immediately
    // return after the call. 'visit' methods should not call 'iterate', call
    // this method instead, which checks for cycles.
    void chase(DfgVertex* vtxp, uint32_t lsb) {
        // Check for true cycle and bail if found. We should probably error here.
        if (!m_visited.emplace(vtxp, lsb).second) {
            m_currp = nullptr;
            return;
        }

        m_currp = vtxp;
        m_lsb = lsb;
        m_msb = lsb + m_width - 1;
        UASSERT_OBJ(m_currp->width() > m_msb, m_currp, "Chased driver too narrow");
        // UINFO(0, "Chasing " << vtxp->typeName() << " lsb: " << m_lsb << " msb: " << m_msb);
        // If we found a vertex in a different component which is exactly
        // the expression we need, then we can stop
        if (m_currp->user<uint32_t>() != m_component  //
            && m_lsb == 0  //
            && m_msb == vtxp->width() - 1) {
            return;
        }
        // Otherwise continue from m_currp (which is the passed 'vtxp')
        iterate(m_currp);
    }

    // VISITORS
    void visit(DfgVarPacked* vtxp) override {
        // Proceed with the driver that wholly covers the searched bits
        const auto pair = vtxp->sourceEdges();
        for (size_t i = 0; i < pair.second; ++i) {
            DfgVertex* const srcp = pair.first[i].sourcep();
            const uint32_t lsb = vtxp->driverLsb(i);
            const uint32_t msb = lsb + srcp->width() - 1;
            // If it does not cover the searched bit range, move on
            if (m_lsb < lsb || msb < m_msb) continue;
            // Chase this driver
            chase(srcp, m_lsb - lsb);
            return;
        }
    }

    void visit(DfgConcat* vtxp) override {
        DfgVertex* const rhsp = vtxp->rhsp();
        DfgVertex* const lhsp = vtxp->lhsp();
        if (rhsp->width() > m_msb) {
            chase(rhsp, m_lsb);
            return;
        }
        if (rhsp->width() >= m_lsb) {
            chase(lhsp, m_lsb - rhsp->width());
            return;
        }
    }

    void visit(DfgExtend* vtxp) override {
        DfgVertex* const srcp = vtxp->srcp();
        if (srcp->width() > m_msb) {
            chase(srcp, m_lsb);
            return;
        }
    }


    void visit (DfgConst* vtxp) override {
        DfgConst* const constp = new DfgConst{m_dfg, vtxp->fileline(), m_width};
        constp->num().opSelInto(vtxp->num(), m_lsb, m_width);
        chase(constp, 0);
    }


    void visit(DfgVertex* vtxp) override {
        // Base case: cannot continue ...
        // UINFO(0, "Cannot chase vertex type: " << vtxp->typeName());
        // ... but can check if a Sel would make this node OK
        if (vtxp->width() > m_msb && vtxp->user<uint32_t>() != m_component) {
            DfgSel* const selp = new DfgSel{m_dfg, vtxp->fileline(), DfgVertex::dtypeForWidth(m_width) };
            selp->fromp(vtxp);
            selp->lsb(m_lsb);
            chase(selp, 0);
            return;
        }
    }

    // CONSTRUCTOR

    ChaseDriver(DfgGraph& dfg, DfgVertex* vtxp, uint32_t lsb, uint32_t width)
        : m_dfg{dfg}
        , m_width{width}
        , m_component{vtxp->user<uint32_t>()} {
        chase(vtxp, lsb);
        // If we failed to find a suitable expression in a different component, reset the result
        if (m_currp->user<uint32_t>() == m_component  //
            || m_lsb != 0  //
            || m_currp->width() != m_width) {
            m_currp = nullptr;
            // UINFO(0, "Chase unsuccessful");
            return;
        }
        // UINFO(0, "Chase succesful");
    }

public:
    static DfgVertex* apply(DfgGraph& dfg, DfgVertex* vtxp, uint32_t lsb, uint32_t width) {
        return ChaseDriver{dfg, vtxp, lsb, width}.m_currp;
    }
};

std::unique_ptr<DfgGraph> V3DfgPasses::breakCycles(const DfgGraph& dfg,
                                                   V3DfgOptimizationContext& ctx) {
    // Can't do much with trivial things ('a = a' or 'a[1] = a[0]')
    if (dfg.size() <= 2) return nullptr;

    const std::string prefix = ctx.prefix() + "breakCycles-";
    dfg.dumpDotFilePrefixed(prefix + "input");

    // We might fail, so first of all, create a clone of the graph. This is what
    //  we will be working on, and return if successful. Do not touch the input.
    std::unique_ptr<DfgGraph> clonep = dfg.clone();
    clonep->dumpDotFilePrefixed(prefix + "clone");

    // Round 1. Attempt to push Var Sel drivers through to the driving expressions
    for (bool again = true; again;) {
        auto userDataInUse = clonep->userDataInUse();
        const uint32_t numNonTrivialSCCs = ColorStronglyConnectedComponents::apply(*clonep);
        // clonep->dumpDotFilePrefixed("colored");
        // Congrats, it has become acyclic
        if (!numNonTrivialSCCs) return clonep;

        again = false;

        UINFO(0, "Go for it");

        for (DfgVertexVar& vtx : clonep->varVertices()) {
            // Only handle DfgVarPacked at this point
            DfgVarPacked* const varp = vtx.cast<DfgVarPacked>();
            if (!varp) continue;
            // If Variable is not part of a cycle, move on
            const uint32_t component = varp->getUser<uint32_t>();
            if (!component) continue;

            UINFO(0, "Cyclic " << varp->varp()->name());

            varp->forEachSink([&](DfgVertex& sink) {
                // Ignore if sink is not part of cycle
                if (sink.getUser<uint32_t>() != component) return;
                // Only Handle Sels now
                DfgSel* const selp = sink.cast<DfgSel>();
                if (!selp) return;
                // Try to find the driver out of cycle
                DfgVertex* const fixp = ChaseDriver::apply(*clonep, varp, selp->lsb(), selp->width());
                if (!fixp) return;
                // We can replace this sink
                selp->replaceWith(fixp);
                selp->unlinkDelete(*clonep);
                again = true;
                clonep->dumpDotFilePrefixed(prefix + "fixChase");
            });
        }
    }

    UINFO(0, "Give up");

    return nullptr;
}
