// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Flag the logic only needed by the run time model descriptors
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
// V3RtmdLogic's Transformations:
//
// Builds a bipartite graph of the always blocks and the variables: always block -> the
// variables it writes -> the always blocks reading them. The 'pre' and 'post' blocks of
// non-blocking assignments (from V3Delayed) are always blocks here too, so registers are seen
// through their commits. Always blocks with side effects other than writing variables are
// needed, so are variables read by anything other than an always block, or visible outside the
// model, and so is the logic they depend on. Always blocks that are not needed, but compute
// values read by the descriptors, are moved under AstActives of their own, flagged with
// AstActive::rtmdOnly, and their bodies only run when tracing might be used. Those
// that are combinational, and only feed the descriptors via combinational logic, hold no state,
// so their AstActives are also flagged with AstActive::rtmdOnlyComb, to only run when the
// descriptors are read.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Graph.h"
#include "V3Rtmd.h"
#include "V3Stats.h"

#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Flags the logic only computing values read by the descriptors

class RtmdLogicVarVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(RtmdLogicVarVertex, V3GraphVertex)
    AstVarScope* const m_vscp;  // The variable

public:
    RtmdLogicVarVertex(V3Graph* graphp, AstVarScope* vscp)
        : V3GraphVertex{graphp}
        , m_vscp{vscp} {}
    std::string name() const override VL_MT_STABLE { return m_vscp->name(); }
};

class RtmdLogicVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(RtmdLogicVertex, V3GraphVertex)
    AstNodeProcedure* const m_procp;  // The logic
    AstActive* const m_activep;  // The AstActive holding the logic

public:
    RtmdLogicVertex(V3Graph* graphp, AstNodeProcedure* procp, AstActive* activep)
        : V3GraphVertex{graphp}
        , m_procp{procp}
        , m_activep{activep} {}
    std::string name() const override VL_MT_STABLE { return cvtToHex(m_procp); }
    AstNodeProcedure* procp() const { return m_procp; }
    AstActive* activep() const { return m_activep; }
};

class RtmdLogic final : public VNVisitorConst {
    // NODE STATE
    //  AstVarScope::user1p()  -> RtmdLogicVarVertex*, vertex of the variable
    const VNUser1InUse m_user1InUse;

    // Vertex flags, in V3GraphVertex::user()
    enum : uint32_t {
        NEEDED = 1 << 0,  // Needed other than for the descriptors
        FOR_RTMD = 1 << 1,  // Needed for the descriptors
        FEEDS_STATE = 1 << 2,  // Feeds logic holding state
    };

    // STATE
    // Bipartite graph: always blocks -> variables they write -> always blocks reading them
    V3Graph m_graph;
    RtmdLogicVertex* m_logicVtxp = nullptr;  // Vertex of the always block being visited
    VDouble0 m_statRtmdOnly;  // Statistic tracking
    VDouble0 m_statRtmdOnlyComb;  // Statistic tracking

    // METHODS
    RtmdLogicVarVertex* varVertex(AstVarScope* vscp) {
        if (!vscp->user1p()) {
            RtmdLogicVarVertex* const vtxp = new RtmdLogicVarVertex{&m_graph, vscp};
            // Variables visible outside the model are always needed
            const AstVar* const varp = vscp->varp();
            if ((varp->isIO() && vscp->scopep()->isTop()) || varp->isSigPublic()
                || varp->sensIfacep() || varp->isVirtIface()) {
                vtxp->user(NEEDED);
            }
            vscp->user1p(vtxp);
        }
        return vscp->user1u().to<RtmdLogicVarVertex*>();
    }

    // Whether the always block has side effects other than writing variables
    static bool isImpure(AstNodeProcedure* procp) {
        if (procp->isSuspendable() || procp->needProcess()) return true;
        return procp->exists([](AstNode* nodep) {  //
            return !nodep->isPure() || nodep->isOutputter();
        });
    }

    // Whether the logic vertex reads a variable it also writes
    static bool readsOwnWrite(const V3GraphVertex& logicVtx) {
        for (const V3GraphEdge& writeEdge : logicVtx.outEdges()) {
            for (const V3GraphEdge& readEdge : writeEdge.top()->outEdges()) {
                if (readEdge.top() == &logicVtx) return true;
            }
        }
        return false;
    }

    // Set 'flag' on every vertex a vertex with it depends on
    void propagate(uint32_t flag) {
        std::vector<V3GraphVertex*> stack;
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            if (vtx.user() & flag) stack.push_back(&vtx);
        }
        while (!stack.empty()) {
            V3GraphVertex* const vtxp = stack.back();
            stack.pop_back();
            for (V3GraphEdge& edge : vtxp->inEdges()) {
                V3GraphVertex* const fromp = edge.fromp();
                if (fromp->user() & flag) continue;
                fromp->user(fromp->user() | flag);
                stack.push_back(fromp);
            }
        }
    }

    // VISITORS
    void visit(AstActive* nodep) override {
        for (AstNode* logicp = nodep->stmtsp(); logicp; logicp = logicp->nextp()) {
            VL_RESTORER(m_logicVtxp);
            if (VN_IS(logicp, Always) || VN_IS(logicp, AlwaysPre) || VN_IS(logicp, AlwaysPost)) {
                AstNodeProcedure* const procp = VN_AS(logicp, NodeProcedure);
                m_logicVtxp = new RtmdLogicVertex{&m_graph, procp, nodep};
                if (isImpure(procp)) m_logicVtxp->user(NEEDED);
                // Only purely combinational logic holds no state between evaluations
                const AstAlways* const alwaysp = VN_CAST(procp, Always);
                if (!nodep->sentreep()->hasCombo()
                    || (alwaysp && alwaysp->keyword() == VAlwaysKwd::ALWAYS_LATCH)) {
                    m_logicVtxp->user(m_logicVtxp->user() | FEEDS_STATE);
                }
            }
            iterateConst(logicp);
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        AstVarScope* const vscp = nodep->varScopep();
        if (!vscp) return;  // Function local
        RtmdLogicVarVertex* const varVtxp = varVertex(vscp);
        if (m_logicVtxp) {
            if (nodep->access().isWriteOrRW()) new V3GraphEdge{&m_graph, m_logicVtxp, varVtxp, 1};
            if (nodep->access().isReadOrRW()) new V3GraphEdge{&m_graph, varVtxp, m_logicVtxp, 1};
        } else if (nodep->access().isReadOrRW()) {
            // Read by something other than an always block
            varVtxp->user(varVtxp->user() | NEEDED);
        }
    }
    void visit(AstRtmdSignal* nodep) override {
        if (AstVarRef* const refp = nodep->refp()) {
            RtmdLogicVarVertex* const varVtxp = varVertex(refp->varScopep());
            varVtxp->user(varVtxp->user() | FOR_RTMD);
        }
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTORS
    explicit RtmdLogic(AstNetlist* netlistp) {
        iterateConst(netlistp);
        // Logic reading a variable it also writes might hold state in it, e.g. a counter
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            if (!vtx.is<RtmdLogicVertex>() || !readsOwnWrite(vtx)) continue;
            vtx.user(vtx.user() | FEEDS_STATE);
        }
        propagate(NEEDED);
        propagate(FOR_RTMD);
        propagate(FEEDS_STATE);
        // The AstActives of their own holding the logic only for the RTMD of each AstActive,
        // the 'rtmdOnlyComb' one first
        std::unordered_map<AstActive*, std::pair<AstActive*, AstActive*>> rtmdActives;
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            RtmdLogicVertex* const logicVtxp = vtx.cast<RtmdLogicVertex>();
            if (!logicVtxp || (vtx.user() & (NEEDED | FOR_RTMD)) != FOR_RTMD) continue;
            const bool comb = !(vtx.user() & FEEDS_STATE);
            ++m_statRtmdOnly;
            if (comb) ++m_statRtmdOnlyComb;
            // Move it under an AstActive of its own, so it can be scheduled separately
            AstActive* const activep = logicVtxp->activep();
            std::pair<AstActive*, AstActive*>& pair = rtmdActives[activep];
            AstActive*& rtmdActivep = comb ? pair.first : pair.second;
            if (!rtmdActivep) {
                rtmdActivep
                    = new AstActive{activep->fileline(), activep->name(), activep->sentreep()};
                rtmdActivep->rtmdOnly(true);
                rtmdActivep->rtmdOnlyComb(comb);
                activep->addNextHere(rtmdActivep);
            }
            AstNodeProcedure* const procp = logicVtxp->procp();
            rtmdActivep->addStmtsp(procp->unlinkFrBack());
            // The state it holds only needs updating if tracing might be used
            if (!comb && procp->stmtsp()) {
                FileLine* const flp = procp->fileline();
                AstCExpr* const condp = new AstCExpr{
                    flp, AstCExpr::Pure{}, "vlSymsp->_vm_contextp__->calcUnusedSigs()", 1};
                procp->addStmtsp(new AstIf{flp, condp, procp->stmtsp()->unlinkFrBackWithNext()});
            }
        }
        // Delete the AstActives left empty
        for (const auto& pair : rtmdActives) {
            AstActive* const activep = pair.first;
            if (!activep->stmtsp()) VL_DO_DANGLING(activep->unlinkFrBack()->deleteTree(), activep);
        }
        if (dumpGraphLevel() >= 6) m_graph.dumpDotFilePrefixed("rtmd_logic");
    }
    ~RtmdLogic() override {
        V3Stats::addStat("Rtmd, logic only for descriptors", m_statRtmdOnly);
        V3Stats::addStat("Rtmd, logic only for descriptors, combinational", m_statRtmdOnlyComb);
    }

public:
    static void apply(AstNetlist* netlistp) { RtmdLogic{netlistp}; }
};

void V3Rtmd::logicAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    RtmdLogic::apply(nodep);
    V3Global::dumpCheckGlobalTree("rtmdlogic", 0, dumpTreeEitherLevel() >= 3);
}
