// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
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
// V3Trace's Transformations:
//
//  Examine whole design and build a graph describing which function call
//  may result in a write to a traced variable. This is done in 2 passes:
//
//  Pass 1:
//      Add vertices for the described signals, and for CFunc, CCall and
//      VarRef nodes, add edges from CCall -> CFunc, VarRef -> signal, also
//      add edges for public entry points to CFuncs (these are like a
//      spontaneous call)
//
//  Pass 2:
//      Add edges from CFunc -> VarRef being written
//
//  Finally:
//      Process graph to determine when traced variables can change, allocate
//      activity flags, insert nodes to set activity flags, and assign each
//      described signal its activity set.
//
//  The activity flags live in the symbol table, and are set via AstCStmt, as
//  only the runtime reads them.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Trace.h"

#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Stats.h"

#include <map>
#include <set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Graph vertexes

class TraceActivityVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(TraceActivityVertex, V3GraphVertex)
    AstNode* const m_insertp;
    int32_t m_activityCode;
    bool m_slow;  // If always slow, we can use the same code
public:
    enum { ACTIVITY_NEVER = ((1UL << 31) - 1) };
    enum { ACTIVITY_ALWAYS = ((1UL << 31) - 2) };
    // First flag after V3Trace::EVAL_FLAG
    enum { ACTIVITY_SLOW = V3Trace::EVAL_FLAG + 1 };
    TraceActivityVertex(V3Graph* graphp, AstNode* nodep, bool slow)
        : V3GraphVertex{graphp}
        , m_insertp{nodep} {
        m_activityCode = 0;
        m_slow = slow;
    }
    TraceActivityVertex(V3Graph* graphp, int32_t code)
        : V3GraphVertex{graphp}
        , m_insertp{nullptr} {
        m_activityCode = code;
        m_slow = false;
    }
    ~TraceActivityVertex() override = default;
    // ACCESSORS
    AstNode* insertp() const {
        UASSERT(m_insertp, "Null insertp; probably called on a special always/slow");
        return m_insertp;
    }
    std::string name() const override {
        if (activityAlways()) {
            return "*ALWAYS*";
        } else {
            return std::string{slow() ? "*SLOW* " : ""} + insertp()->name();
        }
    }
    std::string dotColor() const override { return slow() ? "yellowGreen" : "green"; }
    int32_t activityCode() const { return m_activityCode; }
    bool activityAlways() const { return activityCode() == ACTIVITY_ALWAYS; }
    bool activitySlow() const { return activityCode() == ACTIVITY_SLOW; }
    void activityCode(int32_t code) { m_activityCode = code; }
    bool slow() const { return m_slow; }
    void slow(bool flag) {
        if (!flag) m_slow = false;
    }
};

class TraceCFuncVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(TraceCFuncVertex, V3GraphVertex)
    AstCFunc* const m_nodep;

public:
    TraceCFuncVertex(V3Graph* graphp, AstCFunc* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    ~TraceCFuncVertex() override = default;
    // ACCESSORS
    AstCFunc* nodep() const { return m_nodep; }
    std::string name() const override { return nodep()->name(); }
    std::string dotColor() const override { return "yellow"; }
    FileLine* fileline() const override { return nodep()->fileline(); }
};

class TraceTraceVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(TraceTraceVertex, V3GraphVertex)
    AstRtmdSignal* const m_nodep;  // Described signal this represents

public:
    TraceTraceVertex(V3Graph* graphp, AstRtmdSignal* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    ~TraceTraceVertex() override = default;
    // ACCESSORS
    AstRtmdSignal* nodep() const { return m_nodep; }
    std::string name() const override { return nodep()->name(); }
    std::string dotColor() const override { return "red"; }
    FileLine* fileline() const override { return nodep()->fileline(); }
};

class TraceVarVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(TraceVarVertex, V3GraphVertex)
    AstVarScope* const m_nodep;

public:
    TraceVarVertex(V3Graph* graphp, AstVarScope* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    ~TraceVarVertex() override = default;
    // ACCESSORS
    AstVarScope* nodep() const { return m_nodep; }
    std::string name() const override { return nodep()->name(); }
    std::string dotColor() const override { return "skyblue"; }
    FileLine* fileline() const override { return nodep()->fileline(); }
};

//######################################################################
// Trace state, as a visitor of each AstNode

class TraceVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared entire netlist
    //  AstCFunc::user1()               // V3GraphVertex* for this node
    //  AstRtmdSignal::user1()  // V3GraphVertex* for this node
    //  AstVarScope::user1()            // V3GraphVertex* for this node
    //  AstStmtExpr::user2()            // bool; walked next list for other ccalls
    //  Ast*::user3()                   // TraceActivityVertex* for this node
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;

    // STATE
    AstCFunc* m_cfuncp = nullptr;  // C function adding to graph
    AstRtmdSignal* m_tracep = nullptr;  // Described signal adding to graph
    uint32_t m_activityNumber = 0;  // Count of fields in activity variable
    V3Graph m_graph;  // Var/CFunc tracking
    TraceActivityVertex* const m_alwaysVtxp;  // "Always trace" vertex
    bool m_finding = false;  // Pass one of algorithm?

    VDouble0 m_statSetters;  // Statistic tracking
    VDouble0 m_statSettersSlow;  // Statistic tracking
    VDouble0 m_statUniqSigs;  // Statistic tracking
    VDouble0 m_statSets;  // Statistic tracking
    VDouble0 m_statAlways;  // Statistic tracking
    VDouble0 m_statNever;  // Statistic tracking

    // All activity numbers applying to a given trace
    using ActCodeSet = std::set<uint32_t>;
    // For activity set, what traces apply
    using TraceVec = std::multimap<ActCodeSet, TraceTraceVertex*>;
    // Candidate interface-member VarScopes keyed by (interface type, member name)
    std::map<std::pair<const AstIface*, std::string>, std::vector<AstVarScope*>>
        m_ifaceMemberVscps;

    // METHODS

    void graphSimplify(bool initial) {
        if (initial) {
            // Remove all variable nodes
            for (V3GraphVertex* const vtxp : m_graph.vertices().unlinkable()) {
                if (TraceVarVertex* const vvertexp = vtxp->cast<TraceVarVertex>()) {
                    vvertexp->rerouteEdges(&m_graph);
                    vvertexp->unlinkDelete(&m_graph);
                }
            }
            // Remove multiple variables connecting funcs to traces
            // We do this twice, as then we have fewer edges to multiply out in the below
            // expansion.
            m_graph.removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);
            // Remove all Cfunc nodes
            for (V3GraphVertex* const vtxp : m_graph.vertices().unlinkable()) {
                if (TraceCFuncVertex* const vvertexp = vtxp->cast<TraceCFuncVertex>()) {
                    vvertexp->rerouteEdges(&m_graph);
                    vvertexp->unlinkDelete(&m_graph);
                }
            }
        }

        // Remove multiple variables connecting funcs to traces
        m_graph.removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);

        // If there are any edges from a always, keep only the always
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            if (TraceTraceVertex* const vvertexp = vtx.cast<TraceTraceVertex>()) {
                // Search for the incoming always edge
                const V3GraphEdge* alwaysEdgep = nullptr;
                for (const V3GraphEdge& edge : vvertexp->inEdges()) {
                    const TraceActivityVertex* const actVtxp
                        = edge.fromp()->as<const TraceActivityVertex>();
                    if (actVtxp->activityAlways()) {
                        alwaysEdgep = &edge;
                        break;
                    }
                }
                // If always edge exists, remove all other edges
                if (alwaysEdgep) {
                    for (V3GraphEdge* const edgep : vvertexp->inEdges().unlinkable()) {
                        if (edgep != alwaysEdgep) VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                    }
                }
            }
        }

        // Activity points with no outputs can be removed
        for (V3GraphVertex* const vtxp : m_graph.vertices().unlinkable()) {
            if (TraceActivityVertex* const aVtxp = vtxp->cast<TraceActivityVertex>()) {
                // Leave in the always vertex for later use.
                if (aVtxp != m_alwaysVtxp && aVtxp->outEmpty()) {
                    VL_DO_DANGLING(aVtxp->unlinkDelete(&m_graph), aVtxp);
                }
            }
        }
    }

    uint32_t assignactivityNumbers() {
        // Note TraceActivityVertex::ACTIVITY_SLOW indicates slow only
        uint32_t activityNumber = TraceActivityVertex::ACTIVITY_SLOW + 1;
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            if (TraceActivityVertex* const vvertexp = vtx.cast<TraceActivityVertex>()) {
                if (vvertexp != m_alwaysVtxp) {
                    if (vvertexp->slow()) {
                        vvertexp->activityCode(TraceActivityVertex::ACTIVITY_SLOW);
                    } else {
                        vvertexp->activityCode(activityNumber++);
                    }
                }
            }
        }
        return activityNumber;
    }
    void sortTraces(TraceVec& traces) {
        // Populate sort structure
        traces.clear();
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            if (TraceTraceVertex* const vtxp = vtx.cast<TraceTraceVertex>()) {
                ActCodeSet actSet;
                UINFO(9, "  Add to sort: " << vtxp);
                for (const V3GraphEdge& edge : vtxp->inEdges()) {
                    const TraceActivityVertex* const cfvertexp
                        = edge.fromp()->cast<const TraceActivityVertex>();
                    UASSERT_OBJ(cfvertexp, vtxp->nodep(),
                                "Should have been function pointing to this trace");
                    UINFO(9, "   Activity: " << cfvertexp);
                    if (cfvertexp->activityAlways()) {
                        // If code 0, we always trace; ignore other codes
                        actSet.insert(TraceActivityVertex::ACTIVITY_ALWAYS);
                    } else {
                        actSet.insert(cfvertexp->activityCode());
                    }
                }
                UASSERT_OBJ(actSet.count(TraceActivityVertex::ACTIVITY_ALWAYS) == 0
                                || actSet.size() == 1,
                            vtxp->nodep(), "Always active trace has further triggers");
                if (actSet.empty()) {
                    // If a trace doesn't have activity, it's constant, and we
                    // don't need to track changes on it.
                    actSet.insert(TraceActivityVertex::ACTIVITY_NEVER);
                } else if (actSet.count(TraceActivityVertex::ACTIVITY_SLOW) && actSet.size() > 1) {
                    // If a trace depends on the slow flag as well as other
                    // flags, remove the dependency on the slow flag. We will
                    // make slow routines set all activity flags.
                    actSet.erase(TraceActivityVertex::ACTIVITY_SLOW);
                }
                traces.emplace(actSet, vtxp);
            }
        }
    }

    AstNode* newActivitySetter(AstNode* insertp, uint32_t code) {
        ++m_statSetters;
        return new AstCStmt{insertp->fileline(),
                            "vlSymsp->__Vm_traceActivity[" + cvtToStr(code) + "] = 1;\n"};
    }

    AstNode* newActivityAll(AstNode* insertp) {
        ++m_statSettersSlow;
        // Just set all flags (including EVAL_FLAG) in slow code as it should be rare
        return new AstCStmt{insertp->fileline(),
                            "for (uint32_t vlAct = 0; vlAct < " + cvtToStr(m_activityNumber)
                                + "; ++vlAct) vlSymsp->__Vm_traceActivity[vlAct] = 1;\n"};
    }

    void createActivityFlags() {
        // Assign final activity numbers
        m_activityNumber = assignactivityNumbers();
        // The flags are bytes, not a bit vector, as they can be set atomically by mtasks, and
        // are cheaper to set (no need for read-modify-write on the C type), and the speed of the
        // tracing code is the same on largish designs.

        // Insert activity setters
        for (const V3GraphVertex& vtx : m_graph.vertices()) {
            if (const TraceActivityVertex* const vtxp = vtx.cast<const TraceActivityVertex>()) {
                AstNode* setterp = nullptr;
                if (vtxp->activitySlow()) {
                    setterp = newActivityAll(vtxp->insertp());
                } else if (!vtxp->activityAlways()) {
                    setterp = newActivitySetter(vtxp->insertp(), vtxp->activityCode());
                }
                if (setterp) {
                    AstNode* const insertp = vtxp->insertp();
                    if (AstStmtExpr* const stmtp = VN_CAST(insertp, StmtExpr)) {
                        stmtp->addNextHere(setterp);
                    } else if (AstCFunc* const funcp = VN_CAST(insertp, CFunc)) {
                        // If there are awaits, insert the setter after each await
                        if (funcp->isCoroutine() && funcp->stmtsp()) {
                            funcp->stmtsp()->foreachAndNext([setterp](AstCAwait* awaitp) {
                                awaitp->addNextHere(setterp->cloneTree(false));
                            });
                        }
                        funcp->addStmtsp(setterp);
                    } else {
                        insertp->v3fatalSrc("Bad trace activity vertex");
                    }
                }
            }
        }
    }

    // Assign the activity set of each signal. An empty set means the signal never changes.
    void createActivitySets(AstNetlist* netlistp, const TraceVec& traces) {
        FileLine* const flp = netlistp->fileline();
        AstRtmdActSets* const setsp = new AstRtmdActSets{flp, m_activityNumber};
        netlistp->rtmdActSetsp(setsp);
        for (auto it = traces.begin(); it != traces.end();) {
            const ActCodeSet& actSet = it->first;
            AstRtmdActSet* entryp = nullptr;
            if (!actSet.count(TraceActivityVertex::ACTIVITY_ALWAYS)) {
                std::vector<uint32_t> flags;
                if (!actSet.count(TraceActivityVertex::ACTIVITY_NEVER)) {
                    flags.insert(flags.end(), actSet.begin(), actSet.end());
                }
                // Traces are grouped by activity set, so a set is only seen once
                entryp = new AstRtmdActSet{flp, std::move(flags)};
                setsp->addEntriesp(entryp);
                ++m_statSets;
            }
            for (; it != traces.end() && it->first == actSet; ++it) {
                if (!entryp) {
                    ++m_statAlways;
                } else if (entryp->flags().empty()) {
                    ++m_statNever;
                }
                it->second->nodep()->actSetp(entryp);
            }
        }
    }

    TraceCFuncVertex* getCFuncVertexp(AstCFunc* nodep) {
        V3GraphVertex* const vtxp = nodep->user1u().toGraphVertex();
        TraceCFuncVertex* vertexp = vtxp ? vtxp->cast<TraceCFuncVertex>() : nullptr;
        if (!vertexp) {
            vertexp = new TraceCFuncVertex{&m_graph, nodep};
            nodep->user1p(vertexp);
        }
        return vertexp;
    }
    TraceActivityVertex* getActivityVertexp(AstNode* nodep, bool slow) {
        V3GraphVertex* const vtxp = nodep->user3u().toGraphVertex();
        TraceActivityVertex* vertexp = vtxp ? vtxp->cast<TraceActivityVertex>() : nullptr;
        if (!vertexp) {
            vertexp = new TraceActivityVertex{&m_graph, nodep, slow};
            nodep->user3p(vertexp);
        }
        vertexp->slow(slow);
        return vertexp;
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // Add vertexes for all described signals, and edges from VARs each trace looks at
        m_finding = false;
        iterateChildren(nodep);

        // Add vertexes for all CFUNCs, and edges to VARs the func sets
        m_finding = true;
        iterateChildren(nodep);

        // Simplify the graph
        if (dumpGraphLevel() >= 6) m_graph.dumpDotFilePrefixed("trace_pre");
        graphSimplify(true);
        graphSimplify(false);
        if (dumpGraphLevel() >= 6) m_graph.dumpDotFilePrefixed("trace_simplified");

        // Create the fine grained activity flags
        createActivityFlags();

        // Assign activity sets
        TraceVec traces;
        sortTraces(traces);
        createActivitySets(nodep, traces);
    }

    void visit(AstVarScope* nodep) override {
        if (!m_finding) {
            if (const AstIface* const ifacep = nodep->varp()->sensIfacep()) {
                m_ifaceMemberVscps[{ifacep, nodep->varp()->name()}].push_back(nodep);
            }
        }
    }
    void visit(AstStmtExpr* nodep) override {
        if (!m_finding && !nodep->user2()) {
            if (AstCCall* const callp = VN_CAST(nodep->exprp(), CCall)) {
                UINFO(8, "   CCALL " << callp);
                // See if there are other calls in same statement list;
                // If so, all funcs might share the same activity code
                TraceActivityVertex* const activityVtxp
                    = getActivityVertexp(nodep, callp->funcp()->slow());
                for (AstNode* nextp = nodep; nextp; nextp = nextp->nextp()) {
                    if (AstStmtExpr* const stmtp = VN_CAST(nextp, StmtExpr)) {
                        if (AstCCall* const ccallp = VN_CAST(stmtp->exprp(), CCall)) {
                            stmtp->user2(true);  // Processed
                            UINFO(8, "     SubCCALL " << ccallp);
                            V3GraphVertex* const ccallFuncVtxp = getCFuncVertexp(ccallp->funcp());
                            activityVtxp->slow(ccallp->funcp()->slow());
                            new V3GraphEdge{&m_graph, activityVtxp, ccallFuncVtxp, 1};
                        }
                    }
                }
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstCFunc* nodep) override {
        UINFO(8, "   CFUNC " << nodep);
        V3GraphVertex* const funcVtxp = getCFuncVertexp(nodep);
        if (!m_finding) {  // If public, we need a unique activity code to allow for sets
                           // directly in this func
            if (nodep->funcPublic() || nodep->dpiExportImpl() || nodep->entryPoint()
                || nodep->isCoroutine()) {
                // Cannot treat a coroutine as slow, it may be resumed later
                const bool slow = nodep->slow() && !nodep->isCoroutine();
                TraceActivityVertex* const activityVtxp = getActivityVertexp(nodep, slow);
                new V3GraphEdge{&m_graph, activityVtxp, funcVtxp, 1};
            }
        }
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstRtmdSignal* nodep) override {
        UINFO(8, "   TRACE " << nodep);
        // Parameters are constant, so have no activity
        if (!m_finding && !nodep->varp()->isParam()) {
            ++m_statUniqSigs;
            V3GraphVertex* const vertexp = new TraceTraceVertex{&m_graph, nodep};
            nodep->user1p(vertexp);
            VL_RESTORER(m_tracep);
            m_tracep = nodep;
            iterateChildren(nodep);
        }
    }
    void visit(AstNodeRtmdItem* nodep) override {
        // Other entries have no value to trace
    }

    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(nodep->varScopep(), nodep, "No var scope?");
        AstVarScope* const varscopep = nodep->varScopep();
        V3GraphVertex* varVtxp = varscopep->user1u().toGraphVertex();
        if (m_tracep) {
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Lvalue in trace?  Should be const.");
            if (!varVtxp) {
                varVtxp = new TraceVarVertex{&m_graph, nodep->varScopep()};
                nodep->varScopep()->user1p(varVtxp);
            }
            V3GraphVertex* const traceVtxp = m_tracep->user1u().toGraphVertex();
            new V3GraphEdge{&m_graph, varVtxp, traceVtxp, 1};
            if (nodep->varp()->isPrimaryInish()  // Always need to trace primary inputs
                || nodep->varp()->isSigPublic()) {  // Or ones user can change
                new V3GraphEdge{&m_graph, m_alwaysVtxp, traceVtxp, 1};
            }
        } else if (m_cfuncp && m_finding && nodep->access().isWriteOrRW()) {
            V3GraphVertex* const funcVtxp = getCFuncVertexp(m_cfuncp);
            if (varVtxp) {  // else we're not tracing this signal
                new V3GraphEdge{&m_graph, funcVtxp, varVtxp, 1};
            }
        }
    }

    void visit(AstMemberSel* nodep) override {
        if (m_cfuncp && m_finding && nodep->access().isWriteOrRW()) {
            AstIfaceRefDType* const dtypep
                = VN_CAST(nodep->fromp()->dtypep()->skipRefp(), IfaceRefDType);
            if (dtypep && dtypep->isVirtual()) {
                const auto it = m_ifaceMemberVscps.find({dtypep->ifacep(), nodep->varp()->name()});
                if (it != m_ifaceMemberVscps.end()) {
                    V3GraphVertex* const funcVtxp = getCFuncVertexp(m_cfuncp);
                    for (AstVarScope* const vscp : it->second) {
                        V3GraphVertex* varVtxp = vscp->user1u().toGraphVertex();
                        if (!varVtxp) {
                            varVtxp = new TraceVarVertex{&m_graph, vscp};
                            vscp->user1p(varVtxp);
                        }
                        new V3GraphEdge{&m_graph, funcVtxp, varVtxp, 1};
                    }
                }
            }
        }
        iterateChildren(nodep);
    }
    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TraceVisitor(AstNetlist* nodep)
        : m_alwaysVtxp{new TraceActivityVertex{&m_graph, TraceActivityVertex::ACTIVITY_ALWAYS}} {
        nodep->user2ClearTree();  // AstStmtExpr walked flag
        nodep->user3ClearTree();  // TraceActivityVertex (assumes we start at nullptr)
        iterate(nodep);
    }
    ~TraceVisitor() override {
        V3Stats::addStat("Tracing, Activity setters", m_statSetters);
        V3Stats::addStat("Tracing, Activity slow blocks", m_statSettersSlow);
        V3Stats::addStat("Tracing, Activity flags", m_activityNumber);
        V3Stats::addStat("Tracing, Activity sets", m_statSets);
        V3Stats::addStat("Tracing, Always traced signals", m_statAlways);
        V3Stats::addStat("Tracing, Never changing signals", m_statNever);
        V3Stats::addStat("Tracing, Unique traced signals", m_statUniqSigs);
    }
};

//######################################################################
// Trace class functions

void V3Trace::traceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { TraceVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("trace", 0, dumpTreeEitherLevel() >= 3);
}
