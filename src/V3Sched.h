// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling
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

#ifndef VERILATOR_V3SCHED_H_
#define VERILATOR_V3SCHED_H_

#include "config_build.h"
#include "verilatedos.h"
#include "V3Ast.h"

#include <functional>
#include <utility>
#include <vector>

//============================================================================

namespace V3Sched {

struct LogicByScope final : public std::vector<std::pair<AstScope*, AstActive*>> {
    // Add logic
    void add(AstScope* scopep, AstSenTree* senTreep, AstNode* logicp) {
        UASSERT_OBJ(!logicp->backp(), logicp, "Already linked");
        if (empty() || back().first != scopep || back().second->sensesp() != senTreep) {
            emplace_back(scopep, new AstActive{logicp->fileline(), "", senTreep});
        }
        back().second->addStmtsp(logicp);
    };

    // Create copy, with the AstActives cloned
    LogicByScope clone() const {
        LogicByScope result;
        for (const auto& pair : *this) {
            result.emplace_back(pair.first, pair.second->cloneTree(false));
        }
        return result;
    }

    // Delete actives (they should all be empty)
    void deleteActives() {
        for (const auto& pair : *this) {
            AstActive* const activep = pair.second;
            UASSERT_OBJ(!activep->stmtsp(), activep, "Leftover logic");
            if (activep->backp()) activep->unlinkFrBack();
            activep->deleteTree();
        }
        clear();
    };

    void foreach (std::function<void(AstActive*)> f) const {
        for (const auto& pair : *this) f(pair.second);
    }

    void foreachLogic(std::function<void(AstNode*)> f) const {
        for (const auto& pair : *this) {
            for (AstNode* nodep = pair.second->stmtsp(); nodep; nodep = nodep->nextp()) f(nodep);
        }
    }
};

struct LogicClasses final {
    // Types of AstActives under .
    LogicByScope m_static;
    LogicByScope m_initial;
    LogicByScope m_final;
    LogicByScope m_comb;
    LogicByScope m_clocked;
    LogicByScope m_hybrid;

    LogicClasses() = default;
    VL_UNCOPYABLE(LogicClasses);
    LogicClasses(LogicClasses&&) = default;
    LogicClasses& operator=(LogicClasses&&) = default;
};

struct LogicRegions final {
    LogicByScope m_pre;
    LogicByScope m_active;
    LogicByScope m_nba;

    LogicRegions() = default;
    VL_UNCOPYABLE(LogicRegions);
    LogicRegions(LogicRegions&&) = default;
    LogicRegions& operator=(LogicRegions&&) = default;
};

struct LogicReplicas final {
    LogicByScope m_input;
    LogicByScope m_active;
    LogicByScope m_nba;

    LogicReplicas() = default;
    VL_UNCOPYABLE(LogicReplicas);
    LogicReplicas(LogicReplicas&&) = default;
    LogicReplicas& operator=(LogicReplicas&&) = default;
};

void schedule(AstNetlist*);

void splitCheck(AstCFunc* funcp);

LogicByScope breakCycles(AstNetlist* netlistp, LogicByScope& combinationalLogic);
LogicRegions partition(LogicByScope& clockedLogic, LogicByScope& combinationalLogic,
                       LogicByScope& hybridLogic);
LogicReplicas replicateLogic(LogicRegions&);

}  // namespace V3Sched

#endif  // Guard
