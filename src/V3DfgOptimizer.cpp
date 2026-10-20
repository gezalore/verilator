// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow based optimization of combinational logic
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
// High level entry points from Ast world to the DFG optimizer.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3DfgOptimizer.h"

#include "V3Const.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"

#include <algorithm>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class DataflowOptimize final {
    // NODE STATE
    // AstVar::user1, AstVarScope::user1 -> uint64_t, used as a bit-field
    // - bit0: Read via AstVarXRef (hierarchical reference)
    // - bit1: Written via AstVarXRef (hierarchical reference)
    // - bit2: Read by logic in same module/netlist not represented in DFG
    // - bit3: Written by logic in same module/netlist not represented in DFG
    // - bit4: Has READWRITE references
    // - bit5: Only read externally by run time model descriptors (bit0 also set unless hidden)
    // - bit31-6: How many DfgPrev represent this variable
    // - bit63-32: Reference count, how many DfgVertexVar represent this variable
    //
    // AstNode::user2/user3/user4 can be used by various DFG algorithms
    const VNUser1InUse m_user1InUse;

    // STATE
    V3DfgContext m_ctx;  // The context holding values that need to persist across multiple graphs

    void endOfStage(const std::string& name) {
        if (VL_UNLIKELY(v3Global.opt.stats())) V3Stats::statsStage("dfg-" + name);
    }

    void endOfStage(const std::string& name, const DfgGraph& dfg,
                    const std::vector<std::unique_ptr<DfgGraph>>& componentps) {
        // Dump the graphs for debugging
        if (VL_UNLIKELY(dumpDfgLevel() >= 5)) {
            if (dfg.size() > 0) dfg.dumpDotFilePrefixed(name);
            for (const std::unique_ptr<DfgGraph>& componentp : componentps) {
                if (componentp->size() > 0) componentp->dumpDotFilePrefixed(name);
            }
        }
        // Type check the graphs
        if (VL_UNLIKELY(v3Global.opt.debugCheck())) {
            V3DfgPasses::typeCheck(dfg);
            for (const std::unique_ptr<DfgGraph>& componentp : componentps) {
                V3DfgPasses::typeCheck(*componentp);
            }
        }
        // Dump stage stats
        endOfStage(name);
    }

    // Mark variables with external references
    void markExternallyReferencedVariables(AstNetlist* netlistp) {
        std::vector<AstVarScope*> rtmdReadps;
        netlistp->foreach([&](AstNode* nodep) {
            // Check variable flags
            if (AstVarScope* const vscp = VN_CAST(nodep, VarScope)) {
                const AstVar* const varp = vscp->varp();
                // Force and trace have already been processed
                const bool hasExtRd =  //
                    varp->isPrimaryIO()  // Top level port - readable
                    || varp->isSigUserRdPublic()  // Readable by user
                    || varp->constPoolEntry()  // Held in V3ConstPool lookup cache, keep
                    ;
                const bool hasExtWr =  //
                    (varp->isPrimaryIO() && varp->isNonOutput())  // Top level port - writable
                    || varp->isSigUserRWPublic()  // Writable by user
                    ;
                if (hasExtRd) DfgVertexVar::setHasExtRdRefs(vscp);
                if (hasExtWr) DfgVertexVar::setHasExtWrRefs(vscp);
                return;
            }
            if (const AstRtmdSignal* const sigp = VN_CAST(nodep, RtmdSignal)) {
                if (sigp->refp()) rtmdReadps.push_back(sigp->vscp());
                return;
            }
            // Check references
            if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
                if (refp->access().isRW()) DfgVertexVar::setHasRWRefs(refp->varScopep());
                UASSERT_OBJ(!refp->classOrPackagep(), refp, "V3Scope should have removed");
                return;
            }
            UASSERT_OBJ(!VN_IS(nodep, VarXRef), nodep, "V3Scope should have removed");
            // Check cell ports
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                // Why does this not hold?
                UASSERT_OBJ(true || !cellp->pinsp(), cellp, "Pins should have been lowered");
                return;
            }
        });
        // Variables read by descriptors are read externally
        for (AstVarScope* const vscp : rtmdReadps) {
            if (DfgVertexVar::hasExtRdRefs(vscp)) continue;
            DfgVertexVar::setHasExtRdRefs(vscp);
            DfgVertexVar::setHasRtmdOnlyRdRefs(vscp);
        }
    }

    // Remove or restore the variable references held by the vertices of the given graph.
    // While removed, the graph does not affect the optimization of other graphs.
    static void hideRefs(DfgGraph& dfg, bool hide) {
        const auto adjust = [hide](AstVarScope* vscp, uint64_t one) {
            vscp->user1(hide ? vscp->user1() - one : vscp->user1() + one);
        };
        for (DfgVertexVar& vtx : dfg.varVertices()) {
            adjust(vtx.vscp(), DfgVertexVar::VAR_COUNT_ONE);
        }
        for (DfgVertex& vtx : dfg.opVertices()) {
            if (DfgPrev* const prevp = vtx.cast<DfgPrev>()) {
                adjust(prevp->vscp(), DfgVertexVar::PREV_COUNT_ONE);
            }
        }
    }

    // Reconstruct, from the unoptimized clones, the variables only read by descriptors
    // that the optimized graph no longer computes
    void reconstructRtmdOnly(DfgGraph& dfg, std::vector<std::unique_ptr<DfgGraph>>&& clonesp) {
        if (clonesp.empty()) return;

        // Merge the clones into one graph
        std::unique_ptr<DfgGraph> rtmdp{new DfgGraph{m_ctx, "rtmdOnly"}};
        for (const std::unique_ptr<DfgGraph>& clonep : clonesp) hideRefs(*clonep, false);
        rtmdp->mergeGraphs(std::move(clonesp));

        // Reads by descriptors are observable again
        for (DfgVertexVar& vtx : dfg.varVertices()) vtx.hideRtmdOnlyRdRefs(false);
        for (DfgVertexVar& vtx : rtmdp->varVertices()) vtx.hideRtmdOnlyRdRefs(false);

        // Ast references are updated by the optimized graph
        for (DfgVertexAst* const vtxp : rtmdp->astVertices().unlinkable()) {
            VL_DO_DANGLING(vtxp->unlinkDelete(*rtmdp), vtxp);
        }

        // Read the variables the optimized graph still computes instead of recomputing them
        {
            const VNUser2InUse user2InUse;
            for (DfgVertexVar& vtx : dfg.varVertices()) {
                if (vtx.srcp()) vtx.vscp()->user2(1);
            }
            for (DfgVertexVar& vtx : rtmdp->varVertices()) {
                if (!vtx.vscp()->user2()) continue;
                vtx.srcp(nullptr);
                vtx.defaultp(nullptr);
            }
        }
        V3DfgPasses::removeUnused(*rtmdp);

        // The optimized graph might have deleted variables written here, keep them
        {
            const VNUser2InUse user2InUse;
            for (DfgVertexVar& vtx : rtmdp->varVertices()) vtx.vscp()->user2(1);
            std::vector<AstNode*>& deleteps = m_ctx.m_peepholeContext.m_deleteps;
            deleteps.erase(std::remove_if(deleteps.begin(), deleteps.end(),
                                          [](const AstNode* nodep) { return nodep->user2(); }),
                           deleteps.end());
        }

        // Optimize what is left
        V3DfgPasses::inlineVars(*rtmdp);
        V3DfgPasses::cse(*rtmdp, m_ctx.m_cseContext1);
        V3DfgPasses::peephole(*rtmdp, m_ctx.m_peepholeContext);

        // Add to the optimized graph
        std::vector<std::unique_ptr<DfgGraph>> rtmdps;
        rtmdps.emplace_back(std::move(rtmdp));
        dfg.mergeGraphs(std::move(rtmdps));
    }

    void optimize(DfgGraph& dfg) {
        // Remove unobservable variabels and logic that drives only such variables
        V3DfgPasses::removeUnobservable(dfg, m_ctx);
        endOfStage("removeUnobservable", dfg, {});

        // Synthesize DfgLogic vertices
        V3DfgPasses::synthesize(dfg, m_ctx);
        endOfStage("synthesize", dfg, {});

        // Extract the cyclic sub-graphs, so breakCycles can operate on small graphs,
        // make all of them acyclic, then merge them back to the main graph
        {
            std::vector<std::unique_ptr<DfgGraph>> comps = dfg.extractCyclicComponents("cyclic");
            for (const auto& cp : comps) V3DfgPasses::breakCycles(*cp, m_ctx);
            dfg.mergeGraphs(std::move(comps));
            endOfStage("breakCycles", dfg, {});
        }

        // Split the now entirely acyclic DFG into [weakly] connected components
        std::vector<std::unique_ptr<DfgGraph>> comps = dfg.splitIntoComponents("acyclic");
        UASSERT(dfg.size() == 0, "DfgGraph should have become empty");
        endOfStage("splitAcyclic", dfg, comps);

        // Optimize the components as if variables only read by descriptors were not read,
        // keeping an unoptimized clone to reconstruct them from if needed. The clones must
        // not affect the optimization of the components, so hide them.
        std::vector<std::unique_ptr<DfgGraph>> clonesp;
        for (const auto& cp : comps) {
            bool drivesRtmdOnly = false;
            for (DfgVertexVar& vtx : cp->varVertices()) {
                if (!vtx.srcp() || !vtx.hasRtmdOnlyRdRefs()) continue;
                vtx.hideRtmdOnlyRdRefs(true);
                drivesRtmdOnly = true;
            }
            if (!drivesRtmdOnly) continue;
            clonesp.emplace_back(cp->clone());
            hideRefs(*clonesp.back(), true);
        }

        // Main pass pipeline - optimize each acyclic component
        {
            for (auto& cp : comps) V3DfgPasses::removeSelects(*cp, m_ctx.m_removeSelectsContext);
            endOfStage("removeSelects", dfg, comps);
            for (const auto& cp : comps) V3DfgPasses::inlineVars(*cp);
            endOfStage("inlineVars", dfg, comps);
            for (auto& cp : comps) V3DfgPasses::cse(*cp, m_ctx.m_cseContext0);
            endOfStage("cse0", dfg, comps);
            for (auto& cp : comps) V3DfgPasses::binToOneHot(*cp, m_ctx.m_binToOneHotContext);
            endOfStage("binToOneHot", dfg, comps);
            for (auto& cp : comps) V3DfgPasses::peephole(*cp, m_ctx.m_peepholeContext);
            endOfStage("peephole", dfg, comps);

            // Accumulate patterns for reporting
            if (v3Global.opt.dumpDfgPatterns()) V3DfgPasses::dumpPatterns(comps);

            for (auto& cp : comps) V3DfgPasses::pushDownSels(*cp, m_ctx.m_pushDownSelsContext);
            endOfStage("pushDownSels", dfg, comps);
            for (auto& cp : comps) V3DfgPasses::cse(*cp, m_ctx.m_cseContext1);
            endOfStage("cse1", dfg, comps);
        }

        // Merge everything back under the main graph
        dfg.mergeGraphs(std::move(comps));
        endOfStage("optimized", dfg, {});

        reconstructRtmdOnly(dfg, std::move(clonesp));
        endOfStage("reconstructRtmdOnly", dfg, {});

        // Regularize the graph after merging it all back together so all
        // references are known and we only need to iterate the Ast once
        // to replace redundant variables.
        V3DfgPasses::regularize(dfg, m_ctx.m_regularizeContext);
        endOfStage("regularize", dfg, {});
    }

    void removeNeverActives(AstNetlist* netlistp) {
        std::vector<AstActive*> neverActiveps;
        netlistp->foreach([&](AstActive* activep) {
            AstSenTree* const senTreep = activep->sentreep();
            if (!senTreep) return;
            const AstNode* const nodep = V3Const::constifyEdit(senTreep);
            UASSERT_OBJ(nodep == senTreep, nodep, "Should not have been repalced");
            if (senTreep->sensesp()->isNever()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), nodep,
                            "Never senitem should be alone, else the never should be eliminated.");
                neverActiveps.emplace_back(activep);
            }
        });
        for (AstActive* const activep : neverActiveps) {
            VL_DO_DANGLING(activep->unlinkFrBack()->deleteTree(), activep);
        }
    }

    DataflowOptimize(AstNetlist* netlistp) {
        // Mark variables with external references
        markExternallyReferencedVariables(netlistp);
        // Dump stage stats
        endOfStage("init");
        // Post V3Scope application. Run on whole netlist.
        UINFO(4, "Applying DFG optimization to entire netlist");
        // Build the DFG of the entire netlist
        const std::unique_ptr<DfgGraph> dfgp = V3DfgPasses::astToDfg(*netlistp, m_ctx);
        endOfStage("astToDfg", *dfgp, {});
        // Actually process the graph
        optimize(*dfgp);
        // Convert back to Ast
        V3DfgPasses::dfgToAst(*dfgp, m_ctx);
        endOfStage("dfgToAst", *dfgp, {});
        // Some sentrees might have become constant, remove them
        removeNeverActives(netlistp);
        // Reset interned types so the corresponding Ast types can be garbage collected
        DfgDataType::reset();
        // Dump stage stats
        endOfStage("fini");
    }

public:
    static void apply(AstNetlist* netlistp) { DataflowOptimize{netlistp}; }
};

void V3DfgOptimizer::optimize(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");
    DataflowOptimize::apply(netlistp);
    V3Global::dumpCheckGlobalTree("dfg-optimize", 0, dumpTreeEitherLevel() >= 3);
}
