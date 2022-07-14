// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Preprocessing wrapper
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3PreShell.h"
#include "V3PreProc.h"
#include "V3File.h"
#include "V3Parse.h"
#include "V3Os.h"

#include <algorithm>
#include <iostream>

//######################################################################

class V3PreShellImp final {
protected:
    friend class V3PreShell;

    static V3PreShellImp s_preImp;
    std::unique_ptr<V3PreProc> m_preprocp;
    std::unique_ptr<VInFilter> m_filterp;

    //---------------------------------------
    // METHODS

    static int debug(bool reset = false) {
        static int level = -1;
        if (VL_UNLIKELY(level < 0) || reset) level = v3Global.opt.debugSrcLevel(__FILE__);
        return level;
    }

    void boot() {
        // Create the implementation pointer
        if (!m_preprocp) {
            FileLine* const cmdfl = new FileLine(FileLine::commandLineFilename());
            m_preprocp.reset(V3PreProc::createPreProc(cmdfl));
            m_preprocp->debug(debug());
            // Default defines
            FileLine* const prefl = new FileLine(FileLine::builtInFilename());
            m_preprocp->defineCmdLine(prefl, "VERILATOR", "1");  // LEAK_OK
            m_preprocp->defineCmdLine(prefl, "verilator", "1");  // LEAK_OK
            m_preprocp->defineCmdLine(prefl, "verilator3", "1");  // LEAK_OK
            m_preprocp->defineCmdLine(prefl, "coverage_block_off",
                                      "/*verilator coverage_block_off*/");  // LEAK_OK
            if (prefl->language().systemVerilog()) {
                // Synthesis compatibility
                m_preprocp->defineCmdLine(prefl, "SYSTEMVERILOG", "1");  // LEAK_OK
                // IEEE predefined
                m_preprocp->defineCmdLine(prefl, "SV_COV_START", "0");
                m_preprocp->defineCmdLine(prefl, "SV_COV_STOP", "1");
                m_preprocp->defineCmdLine(prefl, "SV_COV_RESET", "2");
                m_preprocp->defineCmdLine(prefl, "SV_COV_CHECK", "3");
                m_preprocp->defineCmdLine(prefl, "SV_COV_MODULE", "10");
                m_preprocp->defineCmdLine(prefl, "SV_COV_HIER", "11");
                m_preprocp->defineCmdLine(prefl, "SV_COV_ASSERTION", "20");
                m_preprocp->defineCmdLine(prefl, "SV_COV_FSM_STATE", "21");
                m_preprocp->defineCmdLine(prefl, "SV_COV_STATEMENT", "22");
                m_preprocp->defineCmdLine(prefl, "SV_COV_TOGGLE", "23");
                m_preprocp->defineCmdLine(prefl, "SV_COV_OVERFLOW", "-2");
                m_preprocp->defineCmdLine(prefl, "SV_COV_ERROR", "-1");
                m_preprocp->defineCmdLine(prefl, "SV_COV_NOCOV", "0");
                m_preprocp->defineCmdLine(prefl, "SV_COV_OK", "1");
                m_preprocp->defineCmdLine(prefl, "SV_COV_PARTIAL", "2");
            }
        }
    }

    bool preproc(FileLine* fl, const string& modname, VInFilter* filterp, V3ParseImp* parsep,
                 const string& errmsg) {  // "" for no error
        debug(true);  // Recheck if debug on - first check was before command line passed

        // Preprocess the given module, putting output in vppFilename
        UINFONL(1, "  Preprocessing " << modname << endl);

        // Preprocess
        m_filterp.reset(filterp);
        const string modfilename = preprocOpen(fl, m_filterp.get(), modname, "", errmsg);
        if (modfilename.empty()) return false;

        // Set language standard up front
        if (!v3Global.opt.preprocOnly()) {
            // Letting lex parse this saves us from having to specially en/decode
            // from the V3LangCode to the various Lex BEGIN states. The language
            // of this source file is updated here, in case there have been any
            // intervening +<lang>ext+ options since it was first encountered.
            FileLine* const modfileline = new FileLine(modfilename);
            modfileline->language(v3Global.opt.fileLanguage(modfilename));
            V3Parse::ppPushText(
                parsep, (string("`begin_keywords \"") + modfileline->language().ascii() + "\"\n"));
            // FileLine tracks and frees modfileline
        }

        while (!m_preprocp->isEof()) {
            const string line = m_preprocp->getline();
            V3Parse::ppPushText(parsep, line);
        }
        return true;
    }

    void preprocInclude(FileLine* fl, const string& modname) {
        if (modname[0] == '/' || modname[0] == '\\') {
            fl->v3warn(INCABSPATH,
                       "Suggest `include with absolute path be made relative, and use +include: "
                           << modname);
        }
        preprocOpen(fl, m_filterp.get(), modname, V3Os::filenameDir(fl->filename()),
                    "Cannot find include file: ");
    }

private:
    string preprocOpen(FileLine* fl, VInFilter* filterp, const string& modname,
                       const string& lastpath,
                       const string& errmsg) {  // Error message or "" to suppress
        // Returns filename if successful
        // Try a pure name in case user has a bogus `filename they don't expect
        string filename = v3Global.opt.filePath(fl, modname, lastpath, errmsg);
        if (filename == "") {
            // Allow user to put `defined names on the command line instead of filenames,
            // then convert them properly.
            const string ppmodname = m_preprocp->removeDefines(modname);

            filename = v3Global.opt.filePath(fl, ppmodname, lastpath, errmsg);
        }
        if (filename == "") return "";  // Not found

        UINFO(2, "    Reading " << filename << endl);
        m_preprocp->openFile(fl, filterp, filename);
        return filename;
    }

public:
    // CONSTRUCTORS
    V3PreShellImp() = default;
    ~V3PreShellImp() = default;
};

//######################################################################
// V3PreShell

V3PreShell::V3PreShell()
    : m_implp{new V3PreShellImp} {}

V3PreShell::~V3PreShell() = default;

void V3PreShell::boot() { m_implp->boot(); }

bool V3PreShell::preproc(FileLine* fl, const string& modname, VInFilter* filterp,
                         V3ParseImp* parsep, const string& errmsg) {
    return m_implp->preproc(fl, modname, filterp, parsep, errmsg);
}

void V3PreShell::preprocInclude(FileLine* fl, const string& modname) {
    m_implp->preprocInclude(fl, modname);
}

void V3PreShell::defineCmdLine(const string& name, const string& value) {
    FileLine* const prefl = new FileLine(FileLine::commandLineFilename());
    m_implp->m_preprocp->defineCmdLine(prefl, name, value);
}

void V3PreShell::undef(const string& name) { m_implp->m_preprocp->undef(name); }

void V3PreShell::dumpDefines(std::ostream& os) { m_implp->m_preprocp->dumpDefines(os); }

void V3PreShell::candidateDefines(VSpellCheck* spellerp) {
    m_implp->m_preprocp->candidateDefines(spellerp);
}
