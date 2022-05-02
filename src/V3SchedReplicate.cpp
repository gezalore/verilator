// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling - replicate combinational logic
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
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3Global.h"
#include "V3SenTree.h"
#include "V3Sched.h"
#include "V3SplitVar.h"
#include "V3Stats.h"
#include "V3Graph.h"

#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

namespace V3Sched {

namespace {

// Driving region flags
enum RegionFlags : uint8_t { NONE = 0x0, INPUT = 0x1, ACTIVE = 0x2, NBA = 0x4 };

//##############################################################################
// Data structures (graph types)

class Vertex VL_NOT_FINAL : public V3GraphVertex {
    RegionFlags m_drivingRegions{NONE};  // The regions driving this vertex

public:
    Vertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    uint8_t drivingRegions() const { return m_drivingRegions; }
    void addDrivingRegions(uint8_t regions) {
        m_drivingRegions = static_cast<RegionFlags>(m_drivingRegions | regions);
    }

    // For graph dumping
    string dotColor() const override {
        switch (static_cast<unsigned>(m_drivingRegions)) {
        case NONE: return "black";
        case INPUT: return "red";
        case ACTIVE: return "green";
        case NBA: return "blue";
        case INPUT | ACTIVE: return "yellow";
        case INPUT | NBA: return "magenta";
        case ACTIVE | NBA: return "cyan";
        case INPUT | ACTIVE | NBA: return "gray80";  // don't want white on white background
        default: v3fatal("There are only 3 region bits"); return "";  // LCOV_EXCL_LINE
        }
    }
};

class LogicVertex final : public Vertex {
    AstScope* const m_scopep;  // The enclosing AstScope of the logic node
    AstSenTree* const m_senTreep;  // The sensitivity of the logic node
    AstNode* const m_logicp;  // The logic node this vertex represents
    RegionFlags const m_assignedRegion;  // The region this logic is originally assigned to

public:
    LogicVertex(V3Graph* graphp, AstScope* scopep, AstSenTree* senTreep, AstNode* logicp,
                RegionFlags assignedRegion)
        : Vertex{graphp}
        , m_scopep{scopep}
        , m_senTreep{senTreep}
        , m_logicp{logicp}
        , m_assignedRegion{assignedRegion} {
        addDrivingRegions(assignedRegion);
    }
    AstScope* scopep() const { return m_scopep; }
    AstSenTree* senTreep() const { return m_senTreep; }
    AstNode* logicp() const { return m_logicp; }
    RegionFlags assignedRegion() const { return m_assignedRegion; }

    // For graph dumping
    string name() const override { return m_logicp->fileline()->ascii(); };
    string dotShape() const override { return "rectangle"; }
};

class VarVertex final : public Vertex {
    AstVarScope* const m_vscp;  // The AstVarScope this vertex represents

public:
    VarVertex(V3Graph* graphp, AstVarScope* vscp)
        : Vertex{graphp}
        , m_vscp{vscp} {
        if (isTopInput()) addDrivingRegions(INPUT);
    }
    AstVarScope* vscp() const { return m_vscp; }
    AstVar* varp() const { return m_vscp->varp(); }
    AstScope* scopep() const { return m_vscp->scopep(); }
    bool isTopInput() const { return scopep()->isTop() && varp()->isNonOutput(); }

    // For graph dumping
    string name() const override { return m_vscp->name(); }
    string dotShape() const override { return isTopInput() ? "invhouse" : "ellipse"; }
};

class Graph final : public V3Graph {};

//##############################################################################
// Algorithm implementation

std::unique_ptr<Graph> buildGraph(const LogicRegions& logicRegions) {
    std::unique_ptr<Graph> graphp{new Graph};

    // AstVarScope::user1() -> VarVertx
    const VNUser1InUse user1InUse;
    const auto getVarVertex = [&](AstVarScope* vscp) {
        if (!vscp->user1p()) vscp->user1p(new VarVertex{graphp.get(), vscp});
        return vscp->user1u().to<VarVertex*>();
    };

    const auto addEdge = [&](Vertex* fromp, Vertex* top) {
        new V3GraphEdge{graphp.get(), fromp, top, 1};
    };

    const auto addLogic = [&](RegionFlags region, AstScope* scopep, AstActive* activep) {
        AstSenTree* const senTreep = activep->sensesp();

        // Predicate for whether a read of the given variable triggers this block
        std::function<bool(AstVarScope*)> readTriggersThisLogic;

        const VNUser4InUse user4InUse;  // bool: Explicit sensitivity of hybrid logic just below

        if (senTreep->hasClocked()) {
            // Clocked logic is never triggered by reads
            readTriggersThisLogic = [](AstVarScope*) { return false; };
        } else if (senTreep->hasCombo()) {
            // Combinational logic is always triggered by reads
            readTriggersThisLogic = [](AstVarScope*) { return true; };
        } else {
            UASSERT_OBJ(senTreep->hasHybrid(), activep, "unexpected");
            // Hybrid logic is triggered by all reads, except for reads of the explicit
            // sensitivities
            readTriggersThisLogic = [](AstVarScope* vscp) { return !vscp->user4(); };
            senTreep->foreach<AstVarRef>([](const AstVarRef* refp) {  //
                refp->varScopep()->user4(true);
            });
        }

        for (AstNode* nodep = activep->stmtsp(); nodep; nodep = nodep->nextp()) {
            LogicVertex* const lvtxp
                = new LogicVertex{graphp.get(), scopep, senTreep, nodep, region};
            const VNUser2InUse user2InUse;
            const VNUser3InUse user3InUse;

            nodep->foreach<AstVarRef>([&](AstVarRef* refp) {
                AstVarScope* const vscp = refp->varScopep();
                VarVertex* const vvtxp = getVarVertex(vscp);

                // If read, add var -> logic edge FIXMEV5: explain the third term in the condition
                if (refp->access().isReadOrRW() && !vscp->user3SetOnce()
                    && readTriggersThisLogic(vscp) && !vscp->user2()) {  //
                    addEdge(vvtxp, lvtxp);
                }
                // If written, add logic -> var edge
                if (refp->access().isWriteOrRW() && !vscp->user2SetOnce()) {  //
                    addEdge(lvtxp, vvtxp);
                }
            });
        }
    };

    for (const auto& pair : logicRegions.m_pre) addLogic(ACTIVE, pair.first, pair.second);
    for (const auto& pair : logicRegions.m_active) addLogic(ACTIVE, pair.first, pair.second);
    for (const auto& pair : logicRegions.m_nba) addLogic(NBA, pair.first, pair.second);

    return graphp;
}

void propagateDrivingRegions(Graph* graphp) {
    // FIXMEV5: better algorithm (the graph is guaranteed to be acyclic at this point,
    // so iterate in breadth first (rank) order

    bool changed;
    do {
        changed = false;
        // For each vertex
        for (V3GraphVertex* gvtxp = graphp->verticesBeginp(); gvtxp;
             gvtxp = gvtxp->verticesNextp()) {
            Vertex* const vtxp = static_cast<Vertex*>(gvtxp);
            // Based on inputs, compute union of all driving regions
            uint8_t drivingRegions = 0;
            for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                const Vertex* const srcp = static_cast<Vertex*>(edgep->fromp());
                drivingRegions |= srcp->drivingRegions();
            }
            // If any new driving regions discovered, update this vertex
            if (drivingRegions & ~vtxp->drivingRegions()) {
                changed = true;
                vtxp->addDrivingRegions(drivingRegions);
            }
        }
    } while (changed);
}

LogicReplicas replicate(Graph* graphp) {
    LogicReplicas result;
    for (V3GraphVertex* vtxp = graphp->verticesBeginp(); vtxp; vtxp = vtxp->verticesNextp()) {
        if (LogicVertex* const lvtxp = dynamic_cast<LogicVertex*>(vtxp)) {
            const auto replicateTo = [&](LogicByScope& lbs) {
                lbs.add(lvtxp->scopep(), lvtxp->senTreep(), lvtxp->logicp()->cloneTree(false));
            };
            const uint8_t targetRegions = lvtxp->drivingRegions() & ~lvtxp->assignedRegion();
            UASSERT(!lvtxp->senTreep()->hasClocked() || targetRegions == 0,
                    "replicating clocked logic");
            if (targetRegions & INPUT) replicateTo(result.m_input);
            if (targetRegions & ACTIVE) replicateTo(result.m_active);
            if (targetRegions & NBA) replicateTo(result.m_nba);
        }
    }
    return result;
}

}  // namespace

LogicReplicas replicateLogic(LogicRegions& logicRegionsRegions) {
    // Build the dataflow (dependency) graph
    const std::unique_ptr<Graph> graphp = buildGraph(logicRegionsRegions);
    // Dump for debug
    graphp->dumpDotFilePrefixed("sched-replicate");
    // Propagate driving region flags
    propagateDrivingRegions(graphp.get());
    // Dump for debug
    graphp->dumpDotFilePrefixed("sched-replicate-propagated");
    // Replicate the necessary logic
    return replicate(graphp.get());
}

}  // namespace V3Sched
