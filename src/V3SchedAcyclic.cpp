// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling - break combinational cycles
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Combinational loops are broken by the introduction of instances of the
// 'hybrid' logic. Hybrid logic is like combinational logic, but also has
// explicit sensitivities. Any explicit sensitivity of hybrid logic suppresses
// the implicit sensitivity of the logic on the same variable. This enables us
// to cut combinational logic loops and perform ordering as if the logic is
// acyclic.  See the internals documentation for more details.
//
// To achieve this we build a dependency graph of all combinational logic in
// the design, and then compute a feedback vertex set of the variables: a set
// of variables that covers every dependency cycle. All combinational logic
// that consumes one of these 'cut' variables is converted into hybrid logic,
// with the cut variables it reads listed as explicit 'changed'
// sensitivities.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitV.h"
#include "V3File.h"
#include "V3Graph.h"
#include "V3InstrCount.h"
#include "V3Sched.h"
#include "V3SenTree.h"
#include "V3SplitVar.h"
#include "V3Stats.h"

#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

namespace {

// ##############################################################################
//  Data structures (graph types)

class SchedAcyclicLogicVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(SchedAcyclicLogicVertex, V3GraphVertex)
    AstNode* const m_logicp;  // The logic node this vertex represents
    AstScope* const m_scopep;  // The enclosing AstScope of the logic node

public:
    SchedAcyclicLogicVertex(V3Graph* graphp, AstNode* logicp, AstScope* scopep)
        : V3GraphVertex{graphp}
        , m_logicp{logicp}
        , m_scopep{scopep} {}
    V3GraphVertex* clone(V3Graph* graphp) const override {
        return new SchedAcyclicLogicVertex{graphp, logicp(), scopep()};
    }

    AstNode* logicp() const { return m_logicp; }
    AstScope* scopep() const { return m_scopep; }

    // LCOV_EXCL_START // Debug code
    string name() const override VL_MT_STABLE { return m_logicp->fileline()->ascii(); };
    string dotShape() const override { return "rectangle2"; }
    // LCOV_EXCL_STOP
};

class SchedAcyclicVarVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(SchedAcyclicVarVertex, V3GraphVertex)
    AstVarScope* const m_vscp;  // The AstVarScope this vertex represents

public:
    SchedAcyclicVarVertex(V3Graph* graphp, AstVarScope* vscp)
        : V3GraphVertex{graphp}
        , m_vscp{vscp} {}
    AstVarScope* vscp() const { return m_vscp; }
    AstVar* varp() const { return m_vscp->varp(); }
    V3GraphVertex* clone(V3Graph* graphp) const override {
        return new SchedAcyclicVarVertex{graphp, vscp()};
    }

    // LCOV_EXCL_START // Debug code
    string name() const override VL_MT_STABLE { return m_vscp->name(); }
    string dotShape() const override { return "ellipse"; }
    string dotColor() const override { return "blue"; }
    // LCOV_EXCL_STOP
};

class Graph final : public V3Graph {
    string loopsVertexCb(V3GraphVertex* vtxp) override {
        if (SchedAcyclicLogicVertex* const lvtxp = vtxp->cast<SchedAcyclicLogicVertex>()) {
            AstNode* const logicp = lvtxp->logicp();
            std::string logicName = logicp->prettyTypeName();
            if (const AstAlways* const alwaysp = VN_CAST(logicp, Always)) {
                if (alwaysp->keyword() == VAlwaysKwd::CONT_ASSIGN) {
                    logicName = "ASSIGNW";  // Keep using historiacl name until we have better
                }
            }
            return logicp->fileline()->warnOther() + "     Example path: " + logicName + "\n";
        } else {
            SchedAcyclicVarVertex* const vvtxp = vtxp->as<SchedAcyclicVarVertex>();
            AstVarScope* const vscp = vvtxp->vscp();
            return vscp->fileline()->warnOther() + "     Example path: " + vscp->prettyName()
                   + "\n";
        }
    }
};

//##############################################################################
// Algorithm implementation

std::unique_ptr<Graph> buildGraph(const LogicByScope& lbs) {
    std::unique_ptr<Graph> graphp{new Graph};

    // AstVarScope::user1() -> VarVertx
    const VNUser1InUse user1InUse;
    const auto getVarVertex = [&](AstVarScope* vscp) {
        if (!vscp->user1p()) vscp->user1p(new SchedAcyclicVarVertex{graphp.get(), vscp});
        return vscp->user1u().to<SchedAcyclicVarVertex*>();
    };

    const auto addEdge = [&](V3GraphVertex* fromp, V3GraphVertex* top) {
        new V3GraphEdge{graphp.get(), fromp, top, 1};
    };

    for (const auto& pair : lbs) {
        AstScope* const scopep = pair.first;
        AstActive* const activep = pair.second;
        UASSERT_OBJ(activep->hasCombo(), activep, "Not combinational logic");
        for (AstNode* nodep = activep->stmtsp(); nodep; nodep = nodep->nextp()) {
            // Can safely ignore Postponed as we generate them all
            if (VN_IS(nodep, AlwaysPostponed)) continue;

            SchedAcyclicLogicVertex* const lvtxp
                = new SchedAcyclicLogicVertex{graphp.get(), nodep, scopep};
            const VNUser2InUse user2InUse;
            const VNUser3InUse user3InUse;

            V3Sched::util::VarScopeSet forceReadEdgeIgnores;
            V3Sched::util::collectForceReadEdgeIgnores(nodep, forceReadEdgeIgnores);

            nodep->foreach([&](AstVarRef* refp) {
                AstVarScope* const vscp = refp->varScopep();
                SchedAcyclicVarVertex* const vvtxp = getVarVertex(vscp);
                // If written, add logic -> var edge
                if (refp->access().isWriteOrRW() && !refp->varp()->ignoreSchedWrite()
                    && !vscp->user2SetOnce())
                    addEdge(lvtxp, vvtxp);
                // If read, add var -> logic edge
                // Note: Use same heuristic as ordering does to ignore written variables
                // TODO: Use live variable analysis.
                if (refp->access().isReadOrRW() && !vscp->user3SetOnce() && !vscp->user2()
                    && !forceReadEdgeIgnores.count(vscp))
                    addEdge(vvtxp, lvtxp);
            });
        }
    }

    return graphp;
}

void removeNonCyclic(Graph* graphp) {
    // Work queue
    std::vector<V3GraphVertex*> queue;

    const auto enqueue = [&](V3GraphVertex* vtxp) {
        if (vtxp->user()) return;  // Already in queue
        vtxp->user(1);
        queue.push_back(vtxp);
    };

    // Start with vertices with no inputs or outputs
    for (V3GraphVertex& vtx : graphp->vertices()) {
        if (vtx.inEmpty() || vtx.outEmpty()) enqueue(&vtx);
    }

    // Iterate while we still have candidates
    while (!queue.empty()) {
        // Pop next candidate
        V3GraphVertex* const vtxp = queue.back();
        queue.pop_back();
        vtxp->user(0);  // No longer in queue

        if (vtxp->inEmpty()) {
            // Enqueue children for consideration, remove out edges, and delete this vertex
            for (V3GraphEdge* const edgep : vtxp->outEdges().unlinkable()) {
                enqueue(edgep->top());
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
            }
            VL_DO_DANGLING(vtxp->unlinkDelete(graphp), vtxp);
        } else if (vtxp->outEmpty()) {
            // Enqueue parents for consideration, remove in edges, and delete this vertex
            for (V3GraphEdge* const edgep : vtxp->inEdges().unlinkable()) {
                enqueue(edgep->fromp());
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
            }
            VL_DO_DANGLING(vtxp->unlinkDelete(graphp), vtxp);
        }
    }
}

// Greedily select a set of variables (a feedback vertex set) that covers every dependency
// cycle in the given graph. Cutting these will make the graph acyclic. Note that optimal
// feedback vertex set is NP-hard, so anything below is a heuristic.
//
// The caller will cut the returned variables (make all their readers hybrid logic), so
// prefer cutting the variables read by the most expensive logic: cutting a variable gives
// every reader of it an explicit 'changed' sensitivity, and that explicit sensitivity
// suppresses the reader's implicit sensitivity on the same variable. Where the reader is
// expensive, the cut gives it a value-change wakeup instead of the coarser sensitivity it would
// otherwise be left with (in the worst case a clock edge, which re-evaluates it every cycle
// regardless of its data). A reader is only fully gated once all of its inputs are cut, so each
// input is credited a share of the reader's cost rather than the whole of it, and logic already
// gated by earlier cuts attracts no further cuts.
std::vector<SchedAcyclicVarVertex*> feedbackVertexSet(Graph* graphp) {
    // Collect statistics
    if (v3Global.opt.stats()) {
        size_t nCyclicVtxs = 0;  // Number of vertices that are part of an SCC (cycle)
        size_t nCyclicVars = 0;  // Number of variables that are part of an SCC (cycle)
        std::unordered_set<uint32_t> sccs;  // Unique SCC colors
        for (V3GraphVertex& vtx : graphp->vertices()) {
            ++nCyclicVtxs;
            if (vtx.cast<SchedAcyclicVarVertex>()) ++nCyclicVars;
            sccs.insert(vtx.color());
        }
        V3Stats::addStat("Scheduling, Cycles, cyclic variables", nCyclicVars);
        V3Stats::addStat("Scheduling, Cycles, cyclic logic blocks", nCyclicVtxs - nCyclicVars);
        V3Stats::addStat("Scheduling, Cycles, unique SCCs", sccs.size());
    }

    // Vertex state for algorithm.
    struct VtxState final {
        size_t liveIns = 0;  // Number of in-edges from live vertices
        size_t liveOuts = 0;  // Number of out-edges to live vertices
        size_t cost = 0;  // Logic: evaluation cost of the block. Variable: score when queued
        // A vertex is dead when it has no live predecessor or successor
        bool isDead() const { return !liveIns || !liveOuts; }
    };

    // Number of live vertices remaining
    size_t nLive = graphp->vertices().size();

    // The vertex state records - sized up front, so pointers into it are stable
    std::vector<VtxState> states(nLive);

    // Initialize the vertex state records. Vertex userp() points to its record.
    size_t n = 0;
    for (V3GraphVertex& vtx : graphp->vertices()) {
        VtxState& state = states[n++];
        vtx.userp(&state);
        state.liveIns = vtx.inEdges().size();
        state.liveOuts = vtx.outEdges().size();
        UASSERT(state.liveIns && state.liveOuts, "SCC vertex should have edges within SCCs");
        if (const SchedAcyclicLogicVertex* const lvtxp = vtx.cast<SchedAcyclicLogicVertex>()) {
            state.cost = V3InstrCount::count(lvtxp->logicp(), false);
        }
    }

    const auto stateOf = [](const V3GraphVertex* vtxp) -> VtxState& {
        return *static_cast<VtxState*>(vtxp->userp());
    };

    // Score of cutting the given variable: its share of the evaluation cost of its live
    // readers. A reader is only fully change-gated once all of its inputs are cut, so each
    // live input is credited an equal share of the reader's cost. The share grows as the
    // reader's other inputs die - the remaining inputs carry the residual benefit.
    const auto scoreOf = [&](const SchedAcyclicVarVertex* vvtxp) {
        size_t score = 0;
        for (const V3GraphEdge& edge : vvtxp->outEdges()) {
            const VtxState& readerState = stateOf(edge.top());
            if (!readerState.isDead()) score += readerState.cost / readerState.liveIns;
        }
        return score;
    };

    // Orders variables
    struct VarCmp final {
        bool operator()(const SchedAcyclicVarVertex* ap, const SchedAcyclicVarVertex* bp) const {
            const VtxState& a = *static_cast<VtxState*>(ap->userp());
            const VtxState& b = *static_cast<VtxState*>(bp->userp());
            // First by cost, most expensive first
            if (a.cost != b.cost) return a.cost > b.cost;
            // Then by width, narrowest first
            const int aWidth = ap->varp()->width();
            const int bWidth = bp->varp()->width();
            if (aWidth != bWidth) return aWidth < bWidth;
            // Then by graph order (which the pointer comparison preserves here deterministically)
            return &a < &b;
        }
    };

    // Candidate variables to cut
    std::set<SchedAcyclicVarVertex*, VarCmp> candidates;
    for (V3GraphVertex& vtx : graphp->vertices()) {
        if (SchedAcyclicVarVertex* const vvtxp = vtx.cast<SchedAcyclicVarVertex>()) {
            stateOf(vvtxp).cost = scoreOf(vvtxp);
            candidates.insert(vvtxp);
        }
    }

    // Greedily pick the most expensive variable - the one whose live readers cost the most
    // to evaluate - as the next one to cut, kill it, then peel the rest of the graph that
    // becomes acyclic. Repeat until no cycles remain (and hence no live vertices) remain.
    // Note: as cuts fragment an SCC, a still-live variable may no longer be on a cycle,
    // so a pick is not guaranteed to break one - the greedy choice is a heuristic.
    std::vector<SchedAcyclicVarVertex*> result;
    std::vector<const V3GraphVertex*> queue;  // Work queue of dead vertices pending update
    while (nLive) {
        UASSERT(!candidates.empty(), "Live variables should have candidate entries");
        // Pick the most expensive variable
        const auto it = candidates.begin();
        SchedAcyclicVarVertex* const vvtxp = *it;
        VtxState& state = stateOf(vvtxp);
        candidates.erase(it);

        // If fixed by a cut since queued, discard
        if (state.isDead()) continue;

        // Queued scores never underestimate: increases (shares growing when a reader loses
        // another input) are applied eagerly below, decreases (readers dying) are handled
        // lazily here - when the best entry's score went stale, it is re-queued with its
        // current score instead of being picked.
        const size_t score = scoreOf(vvtxp);
        if (score != state.cost) {
            state.cost = score;
            candidates.insert(vvtxp);
            continue;
        }

        // Cutting this variable
        result.push_back(vvtxp);

        // Mark it dead: the cut vertex is live (has live neighbours on both sides), so zero both
        state.liveIns = 0;
        state.liveOuts = 0;

        // Peel off all vertices no longer part of a cycle
        // (those left without a live predecessor or successor)
        queue.push_back(vvtxp);
        while (!queue.empty()) {
            const V3GraphVertex* const deadp = queue.back();
            queue.pop_back();
            UASSERT(stateOf(deadp).isDead(), "Enqueued vertex should be dead");

            // This vertex is now dead
            --nLive;

            // Mark downstream vertices as dead
            for (const V3GraphEdge& edge : deadp->outEdges()) {
                V3GraphVertex* const top = edge.top();
                VtxState& toState = stateOf(top);

                // Reader already dead, ignore
                if (!toState.liveOuts) continue;

                // If reader dies here, enqueue it
                if (!--toState.liveIns) {
                    queue.push_back(top);
                    continue;
                }

                // Otherwise the reader had an input cut, but still lives:
                // requeue other input variables whose score have increased.
                if (deadp->is<SchedAcyclicVarVertex>()) {
                    for (const V3GraphEdge& inEdge : top->inEdges()) {
                        V3GraphVertex* const fromp = inEdge.fromp();
                        SchedAcyclicVarVertex* const inp = fromp->as<SchedAcyclicVarVertex>();
                        VtxState& inState = stateOf(inp);
                        if (inState.isDead()) continue;
                        candidates.erase(inp);
                        inState.cost = scoreOf(inp);
                        candidates.insert(inp);
                    }
                }
            }

            // Mark upstream vertices as dead
            for (const V3GraphEdge& edge : deadp->inEdges()) {
                V3GraphVertex* const fromp = edge.fromp();
                VtxState& fromState = stateOf(fromp);

                // Driver already dead, ignore
                if (!fromState.liveIns) continue;

                // Driver dies here, enqueue it
                if (!--fromState.liveOuts) queue.push_back(fromp);
            }
        }
    }

    // Statistics
    V3Stats::addStat("Scheduling, Cycles, cut variables", result.size());

    return result;
}

// A VarVertex together with its fanout
using Candidate = std::pair<SchedAcyclicVarVertex*, unsigned>;

// Gather all splitting candidates that are in the same SCC as the given vertex
void gatherSCCCandidates(V3GraphVertex* vtxp, std::vector<Candidate>& candidates) {
    if (vtxp->user()) return;  // Already done
    vtxp->user(true);

    if (SchedAcyclicVarVertex* const vvtxp = vtxp->cast<SchedAcyclicVarVertex>()) {
        AstVar* const varp = vvtxp->varp();
        const string name = varp->prettyName();
        if (!varp->user3SetOnce()  // Only consider each AstVar once
            && varp->width() != 1  // Ignore 1-bit signals (they cannot be split further)
            && name.find("__Vdly") == string::npos  // Ignore internal signals
            && name.find("__Vcell") == string::npos) {
            // Also compute the fanout of this vertex
            const unsigned fanout = vtxp->outEdges().size();
            candidates.emplace_back(vvtxp, fanout);
        }
    }

    // Iterate through all the vertices within the same strongly connected component (same color)
    for (V3GraphEdge& edge : vtxp->outEdges()) {
        V3GraphVertex* const top = edge.top();
        if (top->color() == vtxp->color()) gatherSCCCandidates(top, candidates);
    }
    for (V3GraphEdge& edge : vtxp->inEdges()) {
        V3GraphVertex* const fromp = edge.fromp();
        if (fromp->color() == vtxp->color()) gatherSCCCandidates(fromp, candidates);
    }
}

// Find all variables in a loop (SCC) that are candidates for splitting to break loops.
std::string reportLoopVars(FileLine* /*warnFl*/, Graph* graphp, SchedAcyclicVarVertex* vvtxp) {
    std::ostringstream ss;
    // Vector of variables in UNOPTFLAT loop that are candidates for splitting.
    std::vector<Candidate> candidates;
    {
        // AstNode::user3 is used to mark if we have done a particular variable.
        // V3GraphVertex::user is used to mark if we have seen this vertex before.
        const VNUser3InUse user3InUse;
        graphp->userClearVertices();
        gatherSCCCandidates(vvtxp, candidates);
        graphp->userClearVertices();
    }

    // Possible we only have candidates the user cannot do anything about, so don't bother them.
    if (candidates.empty()) return "";

    // There may be a very large number of candidates, so only report up to 10 of the "most
    // important" signals.
    unsigned splittable = 0;
    const auto reportFirst10
        = [&](std::function<bool(const Candidate&, const Candidate&)> less) -> string {
        std::stable_sort(candidates.begin(), candidates.end(), less);
        std::ostringstream ss2;
        for (size_t i = 0; i < 10; i++) {
            if (i == candidates.size()) break;
            const Candidate& candidate = candidates[i];
            AstVar* const varp = candidate.first->varp();

            ss2 << V3Error::warnMore() << "    " << varp->fileline() << ' ' << varp->prettyName()
                << ", width " << std::dec << varp->width() << ", circular fanout "
                << candidate.second;
            if (V3SplitVar::canSplitVar(varp)) {
                ss2 << ", can split_var";
                ++splittable;
            }
            ss2 << '\n';
        }
        return ss2.str();
    };

    // Widest variables
    ss << V3Error::warnMore() << "... Widest variables candidate to splitting:\n"
       << reportFirst10([](const Candidate& a, const Candidate& b) {
              return a.first->varp()->width() > b.first->varp()->width();
          });

    // Highest fanout
    ss << V3Error::warnMore() << "... Candidates with the highest fanout:\n"
       << reportFirst10([](const Candidate& a, const Candidate& b) {  //
              return a.second > b.second;
          });

    if (splittable) {
        ss << V3Error::warnMore()
           << "... Suggest add /*verilator split_var*/ to appropriate variables above.\n";
    }
    V3Stats::addStat("Scheduling, split_var, candidates", splittable);
    return ss.str();
}

void reportCycles(Graph* graphp, const std::vector<SchedAcyclicVarVertex*>& cutVertices) {
    for (SchedAcyclicVarVertex* vvtxp : cutVertices) {
        AstVarScope* const vscp = vvtxp->vscp();
        FileLine* const flp = vscp->fileline();

        // First v3warn not inside warnIsOff so we can see the suppressions with --debug
        if (flp->warnIsOff(V3ErrorCode::UNOPTFLAT)) {
            // First v3warn not inside warnIsOff so we can see the suppressions with --debug
            vscp->v3warn(UNOPTFLAT, "Signal unoptimizable: Circular combinational logic: "
                                        << vscp->prettyNameQ());
        } else {
            vscp->v3warn(UNOPTFLAT,
                         "Signal unoptimizable: Circular combinational logic: "
                             << vscp->prettyNameQ() << '\n'
                             << vscp->warnContextPrimary()
                             << V3Error::warnAdditionalInfo()
                             // Calls Graph::loopsVertexCb
                             << graphp->reportLoops(&V3GraphEdge::followAlwaysTrue, vvtxp)
                             // Report candidate variables for splitting
                             << (v3Global.opt.reportUnoptflat()
                                     ? reportLoopVars(vscp->fileline(), graphp, vvtxp)
                                     : ""));
            // Complain just once
            flp->modifyWarnOff(V3ErrorCode::UNOPTFLAT, true);
            // Create a subgraph for the UNOPTFLAT loop
            if (v3Global.opt.reportUnoptflat()) {
                V3Graph loopGraph;
                graphp->subtreeLoops(&V3GraphEdge::followAlwaysTrue, vvtxp, &loopGraph);
                loopGraph.dumpDotFilePrefixedAlways("unoptflat");
            }
        }
    }
}

void dumpSccs(V3Graph* graphp) {
    // Map from SCC color to vertices in that SCC
    std::map<uint32_t, std::vector<V3GraphVertex*>> scc2Vtxps;

    // Gather all vertices in each SCC
    for (V3GraphVertex& vtx : graphp->vertices()) {
        if (!vtx.color()) continue;
        scc2Vtxps[vtx.color()].push_back(&vtx);
    }

    // Dump Verilog for each SCC into separate files
    for (const auto& pair : scc2Vtxps) {
        const uint32_t color = pair.first;
        const std::vector<V3GraphVertex*>& vtxps = pair.second;

        // Open dump file
        const std::string fname
            = v3Global.debugFilename("sched_scc_" + std::to_string(color) + ".v");
        const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(fname)};
        if (ofp->fail()) v3fatal("Can't write file: " << fname);

        // Write header
        *ofp << "// SCC " << color << ", size: " << vtxps.size() << "\n\n";

        // Dump variables
        *ofp << "//////////////////////////////////////////////////////////////////////\n";
        *ofp << "// Variables\n";
        *ofp << "//////////////////////////////////////////////////////////////////////\n";
        *ofp << "\n";
        for (V3GraphVertex* vtxp : vtxps) {
            const SchedAcyclicVarVertex* const vvtxp = vtxp->cast<SchedAcyclicVarVertex>();
            if (!vvtxp) continue;
            AstVarScope* const vscp = vvtxp->vscp();
            *ofp << "// " << vscp->fileline()->ascii() << "\n";
            *ofp << "// " << vscp->prettyName() << "\n";
            V3EmitV::debugVerilogForTree(vscp->varp(), *ofp);
            *ofp << "\n";
        }

        // Dump logic
        *ofp << "\n";
        *ofp << "//////////////////////////////////////////////////////////////////////\n";
        *ofp << "// Logic\n";
        *ofp << "//////////////////////////////////////////////////////////////////////\n";
        *ofp << "\n";
        for (V3GraphVertex* vtxp : vtxps) {
            const SchedAcyclicLogicVertex* const lvtxp = vtxp->cast<SchedAcyclicLogicVertex>();
            if (!lvtxp) continue;
            *ofp << "// " << lvtxp->logicp()->fileline()->ascii() << "\n";
            V3EmitV::debugVerilogForTree(lvtxp->logicp(), *ofp);
            *ofp << "\n";
        }
    }
}

LogicByScope fixCuts(AstNetlist* netlistp,
                     const std::vector<SchedAcyclicVarVertex*>& cutVertices) {
    // For all logic that reads a cut vertex, build a map from logic -> list of cut AstVarScope
    // they read. Also build a vector of the involved logic for deterministic results.
    std::unordered_map<SchedAcyclicLogicVertex*, std::vector<AstVarScope*>> lvtx2Cuts;
    std::vector<SchedAcyclicLogicVertex*> lvtxps;
    {
        const VNUser1InUse user1InUse;  // bool: already added to 'lvtxps'
        for (SchedAcyclicVarVertex* const vvtxp : cutVertices) {
            for (V3GraphEdge& edge : vvtxp->outEdges()) {
                SchedAcyclicLogicVertex* const lvtxp
                    = static_cast<SchedAcyclicLogicVertex*>(edge.top());
                if (!lvtxp->logicp()->user1SetOnce()) lvtxps.push_back(lvtxp);
                lvtx2Cuts[lvtxp].push_back(vvtxp->vscp());
            }
        }
    }

    // Make the logic reading cut vertices use a hybrid sensitivity (combinational, but with some
    // explicit additional triggers on the cut variables)
    LogicByScope result;
    SenTreeFinder finder{netlistp};
    for (SchedAcyclicLogicVertex* const lvtxp : lvtxps) {
        AstNode* const logicp = lvtxp->logicp();
        logicp->unlinkFrBack();
        FileLine* const flp = logicp->fileline();
        // Build the hybrid sensitivity list
        AstSenItem* senItemsp = nullptr;
        for (AstVarScope* const vscp : lvtx2Cuts[lvtxp]) {
            AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::READ};
            AstSenItem* const nextp = new AstSenItem{flp, VEdgeType::ET_HYBRID, refp};
            senItemsp = AstNode::addNext(senItemsp, nextp);
        }
        AstSenTree* const senTree = new AstSenTree{flp, senItemsp};
        // Add logic to result with new sensitivity
        result.add(lvtxp->scopep(), finder.getSenTree(senTree), logicp);
        // SenTreeFinder::getSenTree clones, so clean up
        VL_DO_DANGLING(senTree->deleteTree(), senTree);
    }
    return result;
}

}  // namespace

LogicByScope breakCycles(AstNetlist* netlistp, const LogicByScope& combinationalLogic) {
    // Build the dataflow (dependency) graph
    const std::unique_ptr<Graph> graphp = buildGraph(combinationalLogic);

    // Remove nodes that don't form part of a cycle
    removeNonCyclic(graphp.get());

    // Nothing to do if no cycles, yay!
    if (graphp->empty()) return LogicByScope{};

    // Color strongly connected components. Delete every vertex not in an SCC.
    // (In case one cycle feeds into another cycle)
    graphp->stronglyConnected(&V3GraphEdge::followAlwaysTrue);
    for (V3GraphVertex* const vtxp : graphp->vertices().unlinkable()) {
        if (!vtxp->color()) VL_DO_DANGLING(vtxp->unlinkDelete(graphp.get()), vtxp);
    }

    // Dump for debug
    if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("sched-comb-cycles");

    // Select the set of variables to cut in order to make the graph acyclic
    const std::vector<SchedAcyclicVarVertex*> cutVertices = feedbackVertexSet(graphp.get());

    // Report warnings/diagnostics
    reportCycles(graphp.get(), cutVertices);

    // Debug dump
    if (dumpLevel() >= 6) dumpSccs(graphp.get());

    // Fix cuts by converting dependent logic to use hybrid sensitivities
    return fixCuts(netlistp, cutVertices);
}

}  // namespace V3Sched
