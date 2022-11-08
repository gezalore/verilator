// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Peephole optimizations over DfgGraph
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
// A pattern-matching based optimizer for DfgGraph. This is in some aspects similar to V3Const, but
// more powerful in that it does not care about ordering combinational statement. This is also less
// broadly applicable than V3Const, as it does not apply to procedural statements with sequential
// execution semantics.
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

class V3DfgSlpVectorize {

    static constexpr uint32_t UNASSIGNED = std::numeric_limits<uint32_t>::max();

    // TYPES
    struct State {
        DfgVertex* lop = nullptr;  // Lower bit index neighbour
        DfgVertex* hip = nullptr;  // Higher bit index neighbour
        size_t rank = UNASSIGNED;
        State() {}

    private:
        VL_UNCOPYABLE(State);
    };

    // STATE
    DfgGraph& m_dfg;  // The DfgGraph being visited
    std::deque<State> m_sateAlloc;  // Allocator for Neighbour structures
    std::vector<DfgVertex*> m_packs;  // Vector of vertex packs to consider for vectorization
    // Map from vertex of pack to vectorized vertex, and lsb offset
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

    bool canVectorize(DfgVertex* vtxp) {
        return  // vtxp->is<DfgConst>()  //
                //||
            vtxp->is<DfgAnd>() || vtxp->is<DfgOr>() || vtxp->is<DfgXor>()  //
            || vtxp->is<DfgNot>();
    }

    void constructRoots() {
        // Map from vertex to all the DfgSel vertices that select from that vertex
        std::unordered_map<DfgVertex*, std::vector<DfgSel*>> selects;
        selects.reserve(m_dfg.size());

        // Gather root candidates
        for (DfgVertex *vtxp = m_dfg.opVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            if (VL_LIKELY(nextp)) VL_PREFETCH_RW(nextp);
            // We only vectorize single use sub-expressions at the moment, to avoid lot of packing
            if (DfgVertex* const sinkp = vtxp->singleSink()) {
                // Collect DfgSel vertices
                if (DfgSel* const selp = vtxp->cast<DfgSel>()) {
                    selects[selp->fromp()].push_back(selp);
                }
            }
        }

        // Construct initial packs
        for (auto& pair : selects) {
            std::vector<DfgSel*>& vec = pair.second;
            if (vec.size() <= 1) continue;
            std::stable_sort(vec.begin(), vec.end(), [](const DfgSel* ap, const DfgSel* bp) {  //
                return ap->lsb() < bp->lsb();
            });

            DfgSel* prevp = vec[0];
            for (size_t i = 1; i < vec.size(); ++i) {
                DfgSel* const currp = vec[i];
                State& prevState = state(prevp);
                // If consecutive, and not yet part of a pack, then pack these together
                if (!prevState.hip) {
                    if (currp->lsb() == prevp->msb() + 1) {
                        State& currState = state(currp);
                        if (!currState.lop) {
                            prevState.hip = currp;
                            currState.lop = prevp;
                            // If the previous vertex is the rightmost, add to the pack list
                            if (!prevState.lop) m_packs.push_back(prevp);
                        }
                    }
                }
                prevp = currp;
            }
        }
    }

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

    bool extendPacksThroughSinks() {
        const size_t size = m_packs.size();
        // Just use the packs vector as the work list
        std::vector<DfgVertex*> workList = std::move(m_packs);
        m_packs.reserve(workList.size());
        // Extend packs through sinks
        while (!workList.empty()) {
            // Pick up current work item
            DfgVertex* const rightp = workList.back();
            workList.pop_back();

            UINFO(0, "Process: " << rightp << endl);
            UASSERT_OBJ(isPackStart(rightp), rightp,
                        "Not a pack start " << rightp << " hip: " << state(rightp).hip
                                            << " lop: " << state(rightp).lop);

            // Add pack to pack list
            m_packs.push_back(rightp);

            // Process whole pack from right to left
            for (DfgVertex* prevp = rightp; prevp;) {
                // Skip over any vertices that are not single sink
                if (!prevp->singleSink()) {
                    prevp = state(prevp).hip;
                    continue;
                }

                DfgVertex* currp = state(prevp).hip;
                if (!currp) break;
                // Try to form new packs of the sinks
                for (DfgVertex* nextp = nullptr; currp; currp = nextp) {
                    nextp = state(currp).hip;
                    DfgVertex* const currSinkp = currp->singleSink();
                    // If this a vertex we would like to vectorize
                    if (currSinkp && currSinkp->singleSink() && canVectorize(currSinkp)) {
                        DfgVertex* const prevSinkp = prevp->singleSink();
                        // If different, but isomorphic with the previous vertex
                        // TODO: isomorphism requires same operand position
                        if (currSinkp != prevSinkp && currSinkp->type() == prevSinkp->type()
                            && prevSinkp->singleSink() && !pathExists(currSinkp, prevSinkp)) {
                            State& prevSinkState = state(prevSinkp);
                            // If not yet part of a pack, then pack these together
                            if (!prevSinkState.hip) {
                                State& currSinkState = state(currSinkp);
                                if (!currSinkState.lop && !currSinkState.hip) {
                                    prevSinkState.hip = currSinkp;
                                    currSinkState.lop = prevSinkp;
                                    // If the previous sink is the rightmost, add to work list
                                    if (!prevSinkState.lop) {
                                        UINFO(0, "ADDING: " << prevSinkp
                                                            << " hip: " << state(prevSinkp).hip
                                                            << " lop: " << state(prevSinkp).lop
                                                            << endl);

                                        UASSERT_OBJ(isPackStart(prevSinkp), prevSinkp, "WHY?");
                                        workList.push_back(prevSinkp);
                                    }
                                }
                            }
                        }
                        prevp = currp;
                    } else {
                        // Current node is no good, so continue search from the next node
                        prevp = nextp;
                        break;
                    }
                }
            }
        }
        return m_packs.size() != size;
    }

    bool isPackStart(DfgVertex* vtxp) {
        State& n = state(vtxp);
        return n.hip && !n.lop;
    }

    bool isPackMember(DfgVertex* vtxp) {
        State& n = state(vtxp);
        return n.hip || n.lop;
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
            while (DfgVertex* prevp = state(headp).lop) {
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

    template <size_t Idx, size_t Arity>
    DfgVertex* getInputPack(DfgVertexWithArity<Arity>* vtxp) {
        UASSERT_OBJ(isPackStart(vtxp), vtxp, "'vtxp' is not start of pack");
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
                auto pair = vectorized(srcp);
                DfgVertex* const vecp = pair.first;
                UASSERT_OBJ(pair.second == 0, srcp, "Pack starting vertex should have offset 0");
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
                auto pair = vectorized(srcp);
                DfgVertex* const vecp = pair.first;
                UASSERT_OBJ(pair.second > 0, srcp, "Mid pack vertex should have offset > 0");
                const uint32_t lsb = pair.second;
                termWidth = std::min(vecp->width() - lsb, width);
                DfgSel* const selp = new DfgSel{m_dfg, flp, DfgVertex::dtypeForWidth(termWidth)};
                selp->fromp(vecp);
                selp->lsb(lsb);
                addTerm(selp);
            } else {
                termWidth = srcp->width();
                addTerm(srcp);
            }
            // Skip over the covered pack
            do {
                termWidth -= vtxp->width();
                vtxp = reinterpret_cast<DfgVertexWithArity<Arity>*>(state(vtxp).hip);
            } while (termWidth);
        } while (width);

        // Concatenate all the terms
        DfgVertex* resultp = terms.back();
        terms.pop_back();
        while (!terms.empty()) {
            DfgVertex* const termp = terms.back();
            terms.pop_back();
            const uint32_t partialWidth = resultp->width() + termp->width();
            AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(partialWidth);
            DfgConcat* const catp = new DfgConcat{m_dfg, termp->fileline(), dtypep};
            catp->rhsp(resultp);
            catp->lhsp(termp);
            resultp = catp;
        }

        // Done
        return resultp;
    }

    void convertPacks() {
        m_vtx2vec.reserve(m_dfg.size());

        // Create and connect the vectorized vertices
        for (DfgVertex* const rightp : m_packs) {
            UASSERT_OBJ(isPackStart(rightp), rightp, "E");
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
                    // Pack inputs are converted above
                    if (isPackMember(edge.sinkp())) {
                        UINFO(0, edge.sinkp() << " " << edge.sinkp()->type().ascii() << endl);
                        UINFO(0,
                              state(edge.sinkp()).hip << " " << state(edge.sinkp()).lop << endl);
                        return;
                    }
                    if (!unpackp) {
                        unpackp = new DfgSel{m_dfg, currp->fileline(), currp->dtypep()};
                        unpackp->fromp(vecp);
                        unpackp->lsb(lsb);
                    }
                    edge.relinkSource(unpackp);
                });
                lsb += currp->width();
            }
        }

        dumpDot("nonrem");

        // Finally delete the vectorized vertices
        for (DfgVertex* const vtxp : m_packs) {
            for (DfgVertex *currp = vtxp, *nextp; currp; currp = nextp) {
                nextp = state(currp).hip;
                currp->unlinkDelete(m_dfg);
            }
        }
        m_packs.clear();
    }

    void dumpDot(const string& label) {
        string fileName = m_dfg.name();
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
    V3DfgSlpVectorize(DfgGraph& dfg)
        : m_dfg{dfg} {

        {
            // Stores pointer to State instance
            const auto userDataInUse = dfg.userDataInUse();

            constructRoots();
            if (m_packs.empty()) return;
            dumpDot("roots");

            UINFO(0, "Root Packs: " << endl);
            for (DfgVertex* const p : m_packs) {
                for (DfgVertex* c = p; c; c = state(c).hip) cout << " " << c;
                cout << endl;
            }
            UINFO(0, "END" << endl);

            m_dfg.forEachVertex([&](DfgVertex& vtx) {
                if (isPackMember(&vtx))
                    UINFO(0, "Pack member: " << &vtx << " hi: " << state(&vtx).hip
                                             << " lo: " << state(&vtx).lop << endl);
            });

            while (extendPacksThroughSinks()) {}

            UINFO(0, "Extended Packs: " << endl);
            for (DfgVertex* const p : m_packs) {
                for (DfgVertex* c = p; c; c = state(c).hip) cout << " " << c;
                cout << endl;
            }
            UINFO(0, "END" << endl);

            m_dfg.forEachVertex([&](DfgVertex& vtx) {
                if (isPackMember(&vtx))
                    UINFO(0, "Pack member: " << &vtx << " hi: " << state(&vtx).hip
                                             << " lo: " << state(&vtx).lop << endl);
            });

            dumpDot("extended");

            convertPacks();
            dumpDot("converted");
        }

        V3DfgPeepholeContext ctx{"e"};
        V3DfgPasses::peephole(m_dfg, ctx);
        dumpDot("simplified");
    }

public:
    static void apply(DfgGraph& dfg) { V3DfgSlpVectorize{dfg}; }
};

void V3DfgPasses::slpVectorize(DfgGraph& dfg) { V3DfgSlpVectorize::apply(dfg); }
