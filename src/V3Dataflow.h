// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow optimization
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

#ifndef VERILATOR_V3DATAFLOW_H_
#define VERILATOR_V3DATAFLOW_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

//============================================================================

class V3Dataflow final {
public:
    static void all(AstNetlist*);
};

#endif  // Guard
