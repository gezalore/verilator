// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Preprocessing wrapper program
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3PRESHELL_H_
#define VERILATOR_V3PRESHELL_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"

#include <memory>

class V3ParseImp;
class VInFilter;
class VSpellCheck;
class V3PreShellImp;

//============================================================================

class V3PreShell final {

    std::unique_ptr<V3PreShellImp> m_implp;  // Pointer to implementation

public:
    V3PreShell();
    ~V3PreShell();

    void boot();
    bool preproc(FileLine* fl, const string& modname, VInFilter* filterp, V3ParseImp* parsep,
                 const string& errmsg);
    void preprocInclude(FileLine* fl, const string& modname);
    void defineCmdLine(const string& name, const string& value);
    void undef(const string& name);
    void dumpDefines(std::ostream& os);
    void candidateDefines(VSpellCheck* spellerp);
};

extern V3PreShell v3PreShell;

#endif  // Guard
