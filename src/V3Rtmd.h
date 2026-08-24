// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Build the run time model descriptors (RTMD)
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

#ifndef VERILATOR_V3RTMD_H_
#define VERILATOR_V3RTMD_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3Rtmd final {
public:
    // Build the descriptors
    static void rtmdAll(AstNetlist* nodep) VL_MT_DISABLED;
    // Remove unreachable descriptors, and signals disabled per instance. Must run after
    // V3Scope, and before the passes that pin the described state.
    static void pruneAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
