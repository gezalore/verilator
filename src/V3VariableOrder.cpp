// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Variable ordering
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
// V3VariableOrder's Transformations:
//
// Each module:
//   Order module variables
//
// With multithreading, variables accessed by MTasks are grouped by the exact
// set of MTasks writing them (variables MTasks only read form one group), and
// the first instance field of each group is aligned to a cache line. Variables
// no MTask accesses follow, unaligned.
//
// Separating writers is enough to avoid false sharing. Every MTask accessing a
// variable is ordered relative to the variable's writers by the MTask graph, so
// a cache line holding one group is never written while another thread is using
// it, however the MTasks are packed onto threads. Grouping by readers as well
// would only add padding.
//
// Variables only used by the 'rtmd_comb' region, which only runs when the run
// time model descriptors are read, are placed after the others of the same kind,
// so they do not dilute the variables used on every evaluation.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3VariableOrder.h"

#include "V3AstUserAllocator.h"
#include "V3ExecGraph.h"
#include "V3Stats.h"

#include <algorithm>
#include <cstdint>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

using MTaskIdVec = std::vector<bool>;  // Used as a bit-set indexed by MTask ID
// Writing MTasks of each variable accessed by any MTask
using MTaskWritersMap = std::unordered_map<const AstVar*, MTaskIdVec>;

// Trace through code reachable from an MTask and record the writers of referenced variables
class GatherMTaskWriters final : VNVisitorConst {
    // NODE STATE
    //  AstCFunc::user1()  // bool: Already traced this function
    //  AstVar::user1()  // bool: Already traced this variable
    const VNUser1InUse m_user1InUse;

    // STATE
    MTaskWritersMap& m_results;  // The result map being built;
    const uint32_t m_id;  // Id of mtask being analysed
    const size_t m_usedIds = ExecMTask::numUsedIds();  // Value of max id + 1

    // CONSTRUCTOR
    GatherMTaskWriters(const ExecMTask* mTaskp, MTaskWritersMap& results)
        : m_results{results}
        , m_id{mTaskp->id()} {
        iterateConst(mTaskp->funcp());
    }
    ~GatherMTaskWriters() = default;
    VL_UNMOVABLE(GatherMTaskWriters);

    // VISIT
    void visit(AstNodeVarRef* nodep) override {
        // Cheaper than relying on emplace().second
        if (nodep->user1SetOnce()) return;
        AstVar* const varp = nodep->varp();
        // Record the access, and the writer bit if written
        MTaskIdVec& writers = m_results
                                  .emplace(std::piecewise_construct,  //
                                           std::forward_as_tuple(varp),  //
                                           std::forward_as_tuple(m_usedIds))
                                  .first->second;
        if (nodep->access().isWriteOrRW()) writers[m_id] = true;
    }

    void visit(AstCFunc* nodep) override {
        if (nodep->user1SetOnce()) return;  // Prevent repeat traversals/recursion
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);  // Arguments
        iterateConst(nodep->funcp());  // Callee
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    static void apply(const ExecMTask* mTaskp, MTaskWritersMap& results) {
        GatherMTaskWriters{mTaskp, results};
    }
};

// Variables only referenced by the code of the 'rtmd_comb' region
using RtmdCombVars = std::unordered_set<const AstVar*>;

class GatherRtmdCombVars final : VNVisitorConst {
    // NODE STATE
    //  AstCFunc::user1()  // bool: Function of the 'rtmd_comb' region
    //  AstCFunc::user2()  // bool: Already traced this function from other code
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

    // STATE
    std::unordered_set<const AstVar*> m_otherVarps;  // Variables referenced by other code

    // VISITORS - Gather the variables referenced by code other than the region's
    void visit(AstNodeVarRef* nodep) override { m_otherVarps.insert(nodep->varp()); }
    void visit(AstCFunc* nodep) override {
        // The functions of the region are traced only if called from other code
        if (nodep->user1() || nodep->user2SetOnce()) return;
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);  // Arguments
        AstCFunc* const funcp = nodep->funcp();
        if (!funcp->user2SetOnce()) iterateChildrenConst(funcp);  // Callee, even in the region
    }
    void visit(AstNodeAssign* nodep) override {
        // Resetting a variable at construction is not a use
        const AstCReset* const resetp = VN_CAST(nodep->rhsp(), CReset);
        if (resetp && resetp->constructing()) return;
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeRtmdItem*) override {}  // Descriptors are not code
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTOR
    GatherRtmdCombVars(AstNetlist* netlistp, RtmdCombVars& results) {
        // The functions of the region, reachable from its entry points
        std::vector<AstCFunc*> funcps;
        for (AstCFunc* const funcp : {netlistp->evalFuncp(VEval::RTMD_COMB),
                                      netlistp->dumpTriggersFuncp(VEval::RTMD_COMB)}) {
            if (!funcp->user1SetOnce()) funcps.push_back(funcp);
        }
        for (size_t i = 0; i < funcps.size(); ++i) {
            funcps[i]->foreach([&](const AstNodeCCall* callp) {
                if (!callp->funcp()->user1SetOnce()) funcps.push_back(callp->funcp());
            });
        }
        // Everything else
        iterateConst(netlistp);
        // The variables the region references, and nothing else does
        for (AstCFunc* const funcp : funcps) {
            funcp->foreach([&](const AstNodeVarRef* refp) {
                if (!m_otherVarps.count(refp->varp())) results.insert(refp->varp());
            });
        }
    }
    ~GatherRtmdCombVars() = default;
    VL_UNMOVABLE(GatherRtmdCombVars);

public:
    static void apply(AstNetlist* netlistp, RtmdCombVars& results) {
        GatherRtmdCombVars{netlistp, results};
    }
};

class VariableOrder final {
    // NODE STATE
    //  AstVar::user1()   ->   uint64_t: Stratum, roughly equivalent to alignment
    //                                   requirement, to avoid padding
    const VNUser1InUse m_user1InUse;

    const MTaskWritersMap& m_mTaskWriters;
    const RtmdCombVars& m_rtmdCombVars;

    VariableOrder(AstNodeModule* modp, const MTaskWritersMap& mTaskWriters,
                  const RtmdCombVars& rtmdCombVars)
        : m_mTaskWriters{mTaskWriters}
        , m_rtmdCombVars{rtmdCombVars} {
        orderModuleVars(modp);
    }
    ~VariableOrder() = default;
    VL_UNCOPYABLE(VariableOrder);

    //######################################################################

    // Simple sort by stratum
    void simpleSortVars(std::vector<AstVar*>& varps) {
        stable_sort(varps.begin(), varps.end(), [](const AstVar* ap, const AstVar* bp) -> bool {
            return ap->user1() < bp->user1();
        });
    }

    // Sort by writing MTasks first, then the same as simpleSortVars
    void mtaskSortVars(std::vector<AstVar*>& varps) {
        // Map from "writing MTasks" -> "variable list", for variables accessed by MTasks
        std::map<MTaskIdVec, std::vector<AstVar*>> m2v;
        // Variables not accessed by any MTask
        std::vector<AstVar*> noAffinityVarps;
        for (AstVar* const varp : varps) {
            const auto it = m_mTaskWriters.find(varp);
            if (it == m_mTaskWriters.end()) {
                noAffinityVarps.push_back(varp);
            } else {
                m2v[it->second].push_back(varp);
            }
        }

        varps.clear();

        // Helper function to sort given vector, then append to 'varps'
        const auto sortAndAppend
            = [this, &varps](std::vector<AstVar*>& subVarps, bool alignFirst) {
                  simpleSortVars(subVarps);
                  bool aligned = !alignFirst;
                  for (AstVar* const varp : subVarps) {
                      // Align the first variable with instance storage
                      if (!aligned && varp->isModelState()) {
                          varp->mtaskCacheLineAlign(true);
                          V3Stats::addStatSum("VariableOrder, MTask aligned group starts", 1);
                          aligned = true;
                      }
                      varps.push_back(varp);
                  }
              };

        // Add the groups in the map's deterministic key order
        for (auto& pair : m2v) sortAndAppend(pair.second, true);

        // Finally add the variables with no known MTask affinity
        sortAndAppend(noAffinityVarps, false);

        V3Stats::addStatSum("VariableOrder, MTask affinity groups", m2v.size());
        V3Stats::addStatSum("VariableOrder, no-affinity variables", noAffinityVarps.size());
    }

    // cppcheck-suppress constParameterPointer
    void orderModuleVars(AstNodeModule* modp) {
        // Top level ports stay first, in source order (--lib-create wrapper must match original)
        std::vector<AstVar*> portps;
        // Followed by trivially constructible variables, those only used by 'rtmd_comb' last
        std::vector<AstVar*> trivps;
        std::vector<AstVar*> rtmdTrivps;
        // Followed by not trivially constructible variables, likewise
        std::vector<AstVar*> nontps;
        std::vector<AstVar*> rtmdNontps;
        // Followed by variables that are not model state, in source order
        std::vector<AstVar*> restps;

        // Gather variables, compute stratum
        for (AstNode *nodep = modp->stmtsp(), *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isPrimaryIO()) {
                    portps.push_back(varp);
                    continue;
                }
                if (!varp->isModelState()) {
                    restps.push_back(varp);
                    continue;
                }

                const bool rtmdComb = m_rtmdCombVars.count(varp);
                if (varp->isTriviallyConstructible()) {
                    (rtmdComb ? rtmdTrivps : trivps).push_back(varp);
                } else {
                    (rtmdComb ? rtmdNontps : nontps).push_back(varp);
                }

                AstNodeDType* const dtypep = varp->dtypeSkipRefp();
                const int sigbytes = dtypep->widthAlignBytes();
                const uint64_t stratum = VN_IS(dtypep, UnpackArrayDType)                  ? 9
                                         : (varp->basicp() && varp->basicp()->isString()) ? 4
                                         : (varp->basicp() && varp->basicp()->isOpaque()) ? 8
                                         : (sigbytes == 8)                                ? 3
                                         : (sigbytes == 4)                                ? 2
                                         : (sigbytes == 2)                                ? 1
                                         : (sigbytes == 1)                                ? 0
                                                                                          : 10;
                varp->user1(stratum);
            }
        }

        // Sort them
        for (std::vector<AstVar*>* const varpsp : {&trivps, &rtmdTrivps, &nontps, &rtmdNontps}) {
            if (varpsp->empty()) continue;
            if (!v3Global.opt.mtasks()) {
                simpleSortVars(*varpsp);
            } else {
                mtaskSortVars(*varpsp);
            }
        }

        // Insert them back under the module, in the new order, but at
        // the front of the list so they come out first in dumps/JSON.
        AstNode* nodesp = nullptr;
        for (const std::vector<AstVar*>* const varpsp :
             {&portps, &trivps, &rtmdTrivps, &nontps, &rtmdNontps, &restps}) {
            for (AstVar* const varp : *varpsp) {
                nodesp = AstNode::addNextNull(nodesp, varp->unlinkFrBack());
            }
        }
        modp->prependStmtsp(nodesp);
    }

public:
    static void apply(AstNodeModule* modp, const MTaskWritersMap& mTaskWriters,
                      const RtmdCombVars& rtmdCombVars) {
        VariableOrder{modp, mTaskWriters, rtmdCombVars};
    }
};

//######################################################################
// V3VariableOrder static functions

void V3VariableOrder::orderAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");

    MTaskWritersMap mTaskWriters;

    // Gather writing MTasks
    if (v3Global.opt.mtasks()) {
        netlistp->topModulep()->foreach([&](AstExecGraph* execGraphp) {
            for (const V3GraphVertex& vtx : execGraphp->depGraphp()->vertices()) {
                GatherMTaskWriters::apply(vtx.as<const ExecMTask>(), mTaskWriters);
            }
        });
    }

    // Gather the variables only used by the 'rtmd_comb' region
    RtmdCombVars rtmdCombVars;
    if (v3Global.opt.rtmd()) GatherRtmdCombVars::apply(netlistp, rtmdCombVars);
    V3Stats::addStat("VariableOrder, rtmd_comb only variables", rtmdCombVars.size());

    // Sort variables of each module
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        if (modp->isConstPool()) continue;
        VariableOrder::apply(modp, mTaskWriters, rtmdCombVars);
    }

    V3Global::dumpCheckGlobalTree("variableorder", 0, dumpTreeEitherLevel() >= 3);
}
