// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
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

#ifndef VERILATOR_V3ORDER_H_
#define VERILATOR_V3ORDER_H_

#include "config_build.h"
#include "verilatedos.h"

#include <unordered_set>
#include <vector>

class AstActive;
class AstExecGraph;
class AstNetlist;
class AstVarScope;

namespace V3Sched {
struct LogicByScope;
};

//============================================================================

namespace V3Order {
enum class OrderMode { Settle, Eval, ActiveRegion, NBARegion };

std::vector<AstActive*> orderST(  //
    AstNetlist*, const std::vector<const V3Sched::LogicByScope*>&,
    const std::unordered_set<const AstVarScope*>& writtenExternally, OrderMode);
AstExecGraph* orderMT(  //
    AstNetlist*, const std::vector<const V3Sched::LogicByScope*>&,
    const std::unordered_set<const AstVarScope*>& writtenExternally, OrderMode);
};  // namespace V3Order

#endif  // Guard
