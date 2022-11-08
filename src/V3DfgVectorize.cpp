// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: SLP Vectorizer for DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Inspired by LLVM -fslp-vectorize, and based on the paper
// "Exploiting Superword Level Parallelism with Multimedia Instruction Sets"
// by Samuel Larsen and Saman Amarasinghe
// This pass tries to combine DFG vertices to perform processing on wider
// vectors. E.g.:
//
//    assign a[0] = b[0] & c[0];
//    assign a[1] = b[1] & c[1];
//
// can be converted to:
//
//    assign a[1:0] = b[1:0] & c[1:0];
//
// Current implementation only handles bitwise operations, mainly due to
// lack of representation for wider operations
//
// The algorithm proceeds by forming 'packs'. Every DfgVertex can only
// be a member in exactly one 'pack'. In the above example, (a[1], a[0]),
// (b[1], b[0]), and (c[1], c[0]) would be the 3 initial packs. We would
// then combine the two DfgAnd vertices representing the two '&' operations,
// to construct a 4th pack. We keep combining sinks/sources of packs until
// we cannot construct any more new packs. Finally we convert all vertices
// that are part of a pack into a single wider (vectorized) operation that
// replaces the whole pack, and delete the original pack members.
//
//*************************************************************************

#include "config_build.h"

#include "V3Ast.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <algorithm>
#include <deque>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class V3DfgVectorize final {

    static constexpr uint32_t UNASSIGNED = std::numeric_limits<uint32_t>::max();

    // TYPES
    struct State final {  // Algorithm state associated with each relevant DfgVertex
        DfgVertex* lop = nullptr;  // Lower bit index neighbour
        DfgVertex* hip = nullptr;  // Higher bit index neighbour
        size_t rank = UNASSIGNED;  // Rank in graph
        State() = default;

    private:
        VL_UNCOPYABLE(State);
    };

    // STATE
    DfgGraph& m_dfg;  // The DfgGraph being processed
    V3DfgVectorizeContext& m_ctx;  // The optimization context for stats
    std::deque<State> m_sateAlloc;  // Allocator for State structures
    std::vector<DfgVertex*> m_packs;  // Vector of vertex packs to consider for vectorization
    // Map from vertex of pack to vectorized vertex, and lsb offset within vectorized vertex
    std::unordered_map<DfgVertex*, std::pair<DfgVertex*, uint32_t>> m_vtx2vec;

    // METHODS
    State& state(DfgVertex* vtxp) {
        State*& statep = vtxp->user<State*>();
        if (!statep) {
            m_sateAlloc.emplace_back();
            statep = &m_sateAlloc.back();
            if (vtxp->arity() == 0) {
                statep->rank = 0;
            } else {
                size_t max = 0;
                vtxp->forEachSource([&](DfgVertex& src) {  //
                    max = std::max(max, state(&src).rank);
                });
                statep->rank = max + 1;
            }
        }
        return *statep;
    }

    bool isPackStart(DfgVertex* vtxp) {
        State& n = state(vtxp);
        return n.hip && !n.lop;
    }

    bool isPackMember(DfgVertex* vtxp) {
        State& n = state(vtxp);
        return n.hip || n.lop;
    }

    bool canVectorize(DfgVertex* vtxp) {
        return vtxp->is<DfgAnd>() || vtxp->is<DfgOr>() || vtxp->is<DfgXor>() || vtxp->is<DfgNot>();
    }

    void constructInitalPacks() {
        // Map from vertex to all the DfgSel vertices that select from that vertex
        std::unordered_map<DfgVertex*, std::vector<DfgSel*>> frompToSelps;
        frompToSelps.reserve(m_dfg.size());
        // Keys of the above for deterministic enumeration
        std::vector<DfgVertex*> fromps;

        // Gather root candidates
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            // We only vectorize single use sub-expressions at the moment, to avoid lot of packing
            if (DfgVertex* const sinkp = vtx.singleSink()) {
                // Collect DfgSel vertices, groupped by what they select from
                if (DfgSel* const selp = vtx.cast<DfgSel>()) {
                    DfgVertex* const fromp = selp->fromp();
                    std::vector<DfgSel*>& vec = frompToSelps[fromp];
                    if (vec.empty()) fromps.push_back(fromp);
                    vec.emplace_back(selp);
                }
            }
        }

        // Construct initial packs
        for (DfgVertex* const fromp : fromps) {
            std::vector<DfgSel*>& vec = frompToSelps[fromp];
            UASSERT_OBJ(!vec.empty(), fromp, "Should not be in 'fromps' if no used by selects");
            if (vec.size() == 1) continue;

            // Sort by LSB index (note it might contain multiple selects with the same LSB)
            std::stable_sort(vec.begin(), vec.end(), [](const DfgSel* ap, const DfgSel* bp) {  //
                return ap->lsb() < bp->lsb();
            });

            // Link together consecutive selects to form 'packs'
            DfgSel* prevp = vec[0];
            for (size_t i = 1; i < vec.size(); ++i) {
                DfgSel* const currp = vec[i];
                State& prevState = state(prevp);
                // If consecutive, and not yet part of a pack, then pack these together
                if (!prevState.hip) {
                    if (currp->lsb() == prevp->msb() + 1) {
                        State& currState = state(currp);
                        UASSERT_OBJ(!currState.lop, currp, "Should not be a pack member yet");
                        prevState.hip = currp;
                        currState.lop = prevp;
                        // If the previous vertex is the rightmost, add to the pack list
                        if (!prevState.lop) {
                            ++m_ctx.m_initialPacks;
                            m_packs.push_back(prevp);
                        }
                    }
                }
                prevp = currp;
            }
        }
    }

    // Return true if a path exists between 'ap' and 'bp'
    bool pathExists(const DfgVertex* ap, const DfgVertex* bp) {
        if (ap == bp) return true;
        State& sa = state(const_cast<DfgVertex*>(ap));
        State& sb = state(const_cast<DfgVertex*>(bp));
        if (sa.rank == sb.rank) return false;
        if (sa.rank > sb.rank) std::swap(ap, bp);
        return ap->findSink<DfgVertex>([&](const DfgVertex& sink) {  //
            return pathExists(&sink, bp);
        });
    }

    // Return the index of the source edge in 'sinkp;' that is driven from 'sourcep'
    static size_t getSourceIndex(DfgVertex* sourcep, DfgVertex* sinkp) {
        size_t result = 0;
        sinkp->findSourceEdge([&](const DfgEdge& edge, size_t index) {
            result = index + 1;
            return edge.sourcep() == sourcep;
        });
        UASSERT_OBJ(result, sourcep, "Not an operand of it's sink?");
        return result - 1;
    }

    void extendPacksThroughSinks() {
        // Just use the packs vector as the work list
        std::vector<DfgVertex*> workList = std::move(m_packs);
        m_packs.reserve(workList.size());
        // Extend packs through sinks
        while (!workList.empty()) {
            // Pick up current work item (rightmost vertex in a pack)
            DfgVertex* const rightp = workList.back();
            workList.pop_back();

            UASSERT_OBJ(isPackStart(rightp), rightp, "Not a pack start");

            // Add pack to pack list
            m_packs.push_back(rightp);

            // Process whole pack from lsb to msb. If the sinks can form a pack, create it.
            // We only pack sinks together if they are the single sink, and they themselves
            // only have a single sink (otherwise we would need too much unpacking).
            for (DfgVertex *currp = rightp, *nextp; currp; currp = nextp) {
                nextp = state(currp).hip;
                if (!nextp) break;  // End of pack

                // Check sink of the currp can be packed
                DfgVertex* const sinkCurrp = currp->singleSink();
                if (!sinkCurrp) continue;
                if (!canVectorize(sinkCurrp)) continue;
                if (!sinkCurrp->singleSink()) continue;

                // Check sink of the nextp can be packed
                DfgVertex* const sinkNextp = nextp->singleSink();
                if (!sinkNextp) continue;
                if (sinkNextp->type() != sinkCurrp->type()) continue;
                if (!sinkNextp->singleSink()) continue;
                if (isPackMember(sinkNextp)) continue;

                // It's possible they might be the same, e.g. a[0] & a[1]
                if (sinkNextp == sinkCurrp) continue;

                // It's possible there is a path between the sinks, e.g.: (a[0] & _) & a[1]
                if (pathExists(sinkNextp, sinkCurrp)) continue;

                // Currently only vectorize those where the operands are in the same position.
                // E.g.: vectorize (a[0] & _, a[1] & _), but not (a[0] & _, _ & a[1]). Even
                // though it might be a commutative operation, current implementation of
                // 'convertPacks' can't handle that.
                const size_t indexCurr = getSourceIndex(currp, sinkCurrp);
                const size_t indexNext = getSourceIndex(nextp, sinkNextp);
                if (indexCurr != indexNext) continue;

                // Don't vectorize if the sinks are already part of a pack
                State& sinkCurrState = state(sinkCurrp);
                if (sinkCurrState.hip) continue;
                State& sinkNextState = state(sinkNextp);
                if (sinkNextState.lop) continue;

                // Otherwise we can pack the two sinks together
                sinkCurrState.hip = sinkNextp;
                sinkNextState.lop = sinkCurrp;

                // If this sink vertex is the rightmost in the pack, add to the pack list
                if (!sinkCurrState.lop) {
                    ++m_ctx.m_sinkPacks;
                    workList.push_back(sinkCurrp);
                }
            }
        }
    }

    size_t packWidth(DfgVertex* vtxp) {
        UASSERT_OBJ(isPackStart(vtxp), vtxp, "'vtxp' is not start of pack");
        uint32_t width = 0;
        for (DfgVertex *currp = vtxp, *nextp; currp; currp = nextp) {
            nextp = state(currp).hip;
            width += currp->width();
        }
        return width;
    }

    // Lazy construct if necessary and retrieve the vectorized vertex,
    // and the offset corresponding to the given pack member
    std::pair<DfgVertex*, uint32_t> vectorized(DfgVertex* vtxp) {
        UASSERT_OBJ(isPackMember(vtxp), vtxp, "'vtxp' is not a member of a pack");
        auto emplaced = m_vtx2vec.emplace(std::piecewise_construct,  //
                                          std::forward_as_tuple(vtxp),  //
                                          std::forward_as_tuple(nullptr, 0));
        auto& pair = emplaced.first->second;
        if (emplaced.second) {
            // Rewind to head of pack and compute LSB as we go
            uint32_t lsb = 0;
            DfgVertex* headp = vtxp;
            while (DfgVertex* const prevp = state(headp).lop) {
                lsb += prevp->width();
                headp = prevp;
            }
            pair.second = lsb;

            if (lsb != 0) {
                pair.first = vectorized(headp).first;
            } else {
                AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(packWidth(headp));
                if (headp->is<DfgSel>()) {
                    pair.first = new DfgSel{m_dfg, headp->fileline(), dtypep};
                } else if (headp->is<DfgAnd>()) {
                    pair.first = new DfgAnd{m_dfg, headp->fileline(), dtypep};
                } else if (headp->is<DfgOr>()) {
                    pair.first = new DfgOr{m_dfg, headp->fileline(), dtypep};
                } else if (headp->is<DfgXor>()) {
                    pair.first = new DfgXor{m_dfg, headp->fileline(), dtypep};
                } else if (headp->is<DfgNot>()) {
                    pair.first = new DfgNot{m_dfg, headp->fileline(), dtypep};
                } else {  // LCOV_EXCL_START
                    headp->v3fatalSrc("Non-vectorizable DfgVertex: " << headp->type().ascii());
                }
            }
        }
        return pair;
    }

    // Given a pack start vertex, return the 'Idx' operand of the equivalent
    // vectorized vertex, by packing source nodes into a concatenation.
    template <size_t Idx, size_t Arity>
    DfgVertex* getInputPack(DfgVertexWithArity<Arity>* vtxp) {
        UASSERT_OBJ(isPackStart(vtxp), vtxp, "'vtxp' is not start of pack");

        // The terms we gather for concatenating together
        std::vector<DfgVertex*> terms;
        uint32_t width = packWidth(vtxp);
        const auto addTerm = [&](DfgVertex* termp) {
            terms.push_back(termp);
            width -= termp->width();
        };

        do {
            DfgVertex* const srcp = vtxp->template source<Idx>();
            FileLine* const flp = srcp->fileline();
            uint32_t termWidth;
            if (isPackStart(srcp)) {
                // If the source itself is a pack start, use the related vectorized vertex
                const auto pair = vectorized(srcp);
                DfgVertex* const vecp = pair.first;
                UASSERT_OBJ(!pair.second, srcp, "Pack starting vertex should have offset 0");
                // It's possible the vectorized source is wider than the required number of bits
                if (vecp->width() > width) {
                    termWidth = width;
                    DfgSel* const selp = new DfgSel{m_dfg, flp, DfgVertex::dtypeForWidth(width)};
                    selp->fromp(vecp);
                    selp->lsb(0);
                    addTerm(selp);
                } else {
                    termWidth = vecp->width();
                    addTerm(vecp);
                }
            } else if (isPackMember(srcp)) {
                // If the source is a pack member, select out of the related vectorized vertex
                const auto pair = vectorized(srcp);
                DfgVertex* const vecp = pair.first;
                UASSERT_OBJ(pair.second, srcp, "Mid pack vertex should have offset > 0");
                const uint32_t lsb = pair.second;
                termWidth = std::min(vecp->width() - lsb, width);
                DfgSel* const selp = new DfgSel{m_dfg, flp, DfgVertex::dtypeForWidth(termWidth)};
                selp->fromp(vecp);
                selp->lsb(lsb);
                addTerm(selp);
            } else {
                // Otherwise just add the source term
                termWidth = srcp->width();
                addTerm(srcp);
            }
            // Skip over the pack members covered by the term we just added
            do {
                UASSERT_OBJ(termWidth >= vtxp->width(), vtxp, "Should be at least same size");
                termWidth -= vtxp->width();
                vtxp = reinterpret_cast<DfgVertexWithArity<Arity>*>(state(vtxp).hip);
            } while (termWidth);
        } while (width);

        // Concatenate all the terms.
        m_ctx.m_packingRequired += terms.size() - 1;
        DfgVertex* resultp = terms.back();
        terms.pop_back();
        while (!terms.empty()) {
            DfgVertex* const termp = terms.back();
            terms.pop_back();
            const uint32_t partialWidth = resultp->width() + termp->width();
            AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(partialWidth);
            DfgConcat* const catp = new DfgConcat{m_dfg, termp->fileline(), dtypep};
            catp->rhsp(termp);
            catp->lhsp(resultp);
            resultp = catp;
        }

        // Done
        return resultp;
    }

    void convertPacks() {
        m_vtx2vec.reserve(m_dfg.size());

        // Create and connect the vectorized vertices
        for (DfgVertex* const rightp : m_packs) {
            UASSERT_OBJ(isPackStart(rightp), rightp, "Not a pack start");
            ++m_ctx.m_convertedPacks;
            if (DfgSel* const vtxp = rightp->cast<DfgSel>()) {
                DfgSel* const vecp = vectorized(vtxp).first->as<DfgSel>();
                vecp->fromp(vtxp->fromp());
                vecp->lsb(vtxp->lsb());
            } else if (DfgVertexUnary* const vtxp = rightp->cast<DfgVertexUnary>()) {
                DfgVertexUnary* const vecp = vectorized(vtxp).first->as<DfgVertexUnary>();
                vecp->srcp(getInputPack<0, 1>(vtxp));
            } else if (DfgVertexBinary* const vtxp = rightp->cast<DfgVertexBinary>()) {
                DfgVertexBinary* const vecp = vectorized(vtxp).first->as<DfgVertexBinary>();
                vecp->lhsp(getInputPack<0, 2>(vtxp));
                vecp->rhsp(getInputPack<1, 2>(vtxp));
            } else {  // LCOV_EXCL_START
                rightp->v3fatalSrc("Non-vectorizable vertex: " << rightp->type().ascii());
            }  // LCOV_EXCL_STOP
        }

        dumpDot("combined");

        // Now add the necessary unpacking
        for (DfgVertex* const rightp : m_packs) {
            // Grab the vectorized vertex
            DfgVertex* const vecp = vectorized(rightp).first;
            // Extract and substitute each sink from the vector
            uint32_t lsb = 0;
            for (DfgVertex *currp = rightp, *nextp; currp; currp = nextp) {
                nextp = state(currp).hip;
                DfgSel* unpackp = nullptr;
                currp->forEachSinkEdge([&](DfgEdge& edge) {
                    // If the sink is a pack, it was converted above and needs no unpacking
                    if (isPackMember(edge.sinkp())) return;

                    // TODO: this is too much. Add variadic concatenations instead.
                    if (!unpackp) {
                        ++m_ctx.m_unpackingRequired;
                        unpackp = new DfgSel{m_dfg, currp->fileline(), currp->dtypep()};
                        unpackp->fromp(vecp);
                        unpackp->lsb(lsb);
                    }
                    edge.relinkSource(unpackp);
                });
                lsb += currp->width();
            }
        }

        dumpDot("unpacked");

        // Finally delete the vectorized vertices
        for (DfgVertex* const vtxp : m_packs) {
            for (DfgVertex *currp = vtxp, *nextp; currp; currp = nextp) {
                nextp = state(currp).hip;
                currp->unlinkDelete(m_dfg);
            }
        }
        m_packs.clear();
    }

    // Dump current graph, highlighting packs as clusters
    void dumpDot(const string& label) {
        if (dumpDfgLevel() < 6) return;

        std::string fileName = m_dfg.name() + "-vectorize";
        if (!label.empty()) fileName += "-" + label;
        fileName = v3Global.debugFilename(fileName) + ".dot";
        const std::unique_ptr<std::ofstream> osp{V3File::new_ofstream(fileName)};
        std::ofstream& os = *osp;
        if (os.fail()) v3fatal("Cannot write to file: " << fileName);

        // Header
        os << "digraph dfg {" << endl;
        os << "graph [label=\"" << m_dfg.name();
        if (!label.empty()) os << "-" << label;
        os << "\", labelloc=t, labeljust=l]" << endl;
        os << "graph [rankdir=LR]" << endl;

        // Emit all packs as clusters
        size_t i = 0;
        for (DfgVertex* const rightp : m_packs) {
            os << "subgraph cluster_" << i++ << " {" << endl;
            os << "label=\"" << i << "\"" << endl;
            os << "color=black" << endl;
            for (DfgVertex* currp = rightp; currp; currp = state(currp).hip) {
                os << currp->toDotId() << endl;
            }
            os << "}" << endl;
        }

        // Emit all vertices
        m_dfg.forEachVertex([&](const DfgVertex& vtx) { vtx.dumpDotVertexAndSourceEdges(os); });

        // Footer
        os << "}" << endl;

        os.close();
    }

    // CONSTRUCTOR
    V3DfgVectorize(DfgGraph& dfg, V3DfgVectorizeContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {
        // Stores pointer to State instance
        const auto userDataInUse = dfg.userDataInUse();

        constructInitalPacks();
        if (m_packs.empty()) return;
        dumpDot("initial");

        extendPacksThroughSinks();
        dumpDot("extended");

        convertPacks();
        dumpDot("converted");
    }

public:
    static void apply(DfgGraph& dfg, V3DfgVectorizeContext& ctx) { V3DfgVectorize{dfg, ctx}; }
};

void V3DfgPasses::vectorize(DfgGraph& dfg, V3DfgVectorizeContext& ctx) {
    V3DfgVectorize::apply(dfg, ctx);
}
