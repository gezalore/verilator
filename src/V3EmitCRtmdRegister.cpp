// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for the run time model descriptor registration
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
// Emits the constant pool, and the function that registers the model's descriptor tables with
// the tracer.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3File.h"

#include <cstdio>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Rtmd registration function emitter

class EmitCRtmdRegister final : public EmitCBaseVisitorConst {
    // STATE
    const V3EmitC::RtmdDataTypes& m_dataTypes;  // Data type table
    const V3EmitC::RtmdSignalTypes& m_signalTypes;  // Signal type table
    const V3EmitC::RtmdActSets& m_actSets;  // Activity set tables
    const V3EmitC::RtmdScopes& m_scopes;  // Scope tables and constant pool

    // VISITORS
    // Not a visitor pass
    void visit(AstNode*) override {}  // LCOV_EXCL_LINE

    // METHODS

    // Name of the constant pool, which is static
    static std::string constsSymbol() { return "VlRtmdConsts"; }

    // offsetof on the non-standard-layout generated classes works but warns, so suppress it
    void putOffsetofPragmaPush() {
        puts("\n#if defined(__GNUC__)\n");
        puts("# pragma GCC diagnostic push\n");
        puts("# pragma GCC diagnostic ignored \"-Winvalid-offsetof\"\n");
        puts("#endif\n");
    }
    void putOffsetofPragmaPop() {
        puts("\n#if defined(__GNUC__)\n");
        puts("# pragma GCC diagnostic pop\n");
        puts("#endif\n");
    }

    // Declare the tables emitted in other files
    void emitExterns() {
        puts("\n// Tables emitted in other files\n");
        puts("extern const VlRtmdTypeRow " + m_dataTypes.m_symbol + "[];\n");
        puts("extern const VlRtmdSignalType " + m_signalTypes.m_symbol + "[];\n");
        puts("extern const VlRtmdScopeRow* const " + m_scopes.m_tablesSymbol + "[];\n");
        puts("extern const uint32_t " + m_scopes.m_tableRowsSymbol + "[];\n");
        puts("extern const VlRtmdActSetRow " + m_actSets.m_symbol + "[];\n");
    }

    void emitConstPool() {
        const std::vector<uint32_t>& words = m_scopes.m_constWords;
        if (words.empty()) return;
        puts("\n// Constant pool\n");
        puts("alignas(8) static const uint32_t " + constsSymbol() + "[] VL_ATTR_UNUSED = {\n   ");
        for (size_t i = 0; i < words.size(); ++i) {
            if (i && i % 8 == 0) puts("\n   ");
            char buf[16];
            VL_SNPRINTF(buf, sizeof(buf), " 0x%08x,", words[i]);
            puts(buf);
        }
        puts("\n};\n");
    }

    void emitRegister() {
        const std::string symsClass = EmitCUtil::symClassName();
        puts("\n// Registration\n");
        puts("VL_ATTR_COLD void " + EmitCUtil::topClassName() + "__"
             + VIdProtect::protect("rtmd_register") + "(" + symsClass
             + "* vlSymsp, VerilatedTraceBaseC* tracep) {\n");
        puts("    tracep->modelConnected(true);\n");
        puts("    VlRtmdTables tables;\n");
        puts("    tables.m_symsp = vlSymsp;\n");
        puts("    tables.m_namep = vlSymsp->name();\n");
        puts("    tables.m_isLibInstance = "s
             + (v3Global.opt.libCreate().empty() ? "false" : "true") + ";\n");
        puts("    tables.m_typesp = " + m_dataTypes.m_symbol + ";\n");
        puts("    tables.m_nTypes = " + cvtToStr(m_dataTypes.m_rowOf.size()) + ";\n");
        puts("    tables.m_signalsp = " + m_signalTypes.m_symbol + ";\n");
        puts("    tables.m_nSignals = " + cvtToStr(m_signalTypes.m_rowOf.size()) + ";\n");
        puts("    tables.m_tablesp = " + m_scopes.m_tablesSymbol + ";\n");
        puts("    tables.m_tableRowsp = " + m_scopes.m_tableRowsSymbol + ";\n");
        puts("    tables.m_nTables = " + cvtToStr(m_scopes.m_nTables) + ";\n");
        puts("    tables.m_rootTable = " + cvtToStr(m_scopes.m_rootTable) + ";\n");
        if (!m_scopes.m_constWords.empty()) {
            puts("    tables.m_constsp = " + constsSymbol() + ";\n");
        }
        if (m_actSets.m_nFlags) {
            puts("    tables.m_activityFlagsp = vlSymsp->__Vm_traceActivity;\n");
            puts("    tables.m_nActivityFlags = " + cvtToStr(m_actSets.m_nFlags) + ";\n");
        }
        puts("    tables.m_actSetsp = " + m_actSets.m_symbol + ";\n");
        puts("    tracep->addRtmdTables(tables);\n");
        puts("}\n");
    }

    // CONSTRUCTORS
    EmitCRtmdRegister(AstNetlist* netlistp, const V3EmitC::RtmdDataTypes& dataTypes,
                      const V3EmitC::RtmdSignalTypes& signalTypes,
                      const V3EmitC::RtmdActSets& actSets, const V3EmitC::RtmdScopes& scopes)
        : m_dataTypes{dataTypes}
        , m_signalTypes{signalTypes}
        , m_actSets{actSets}
        , m_scopes{scopes} {
        openNewOutputSourceFile(EmitCUtil::topClassName() + "__Rtmd", /* slow: */ true,
                                /* support: */ true, "Run time model descriptors");
        puts("\n#include \"" + EmitCUtil::symClassName() + ".h\"\n");
        puts("#include \"verilated_trace.h\"\n");
        puts("\n#include <cstddef>\n");
        emitExterns();
        putOffsetofPragmaPush();
        emitConstPool();
        emitRegister();
        putOffsetofPragmaPop();
        closeOutputFile();
        for (AstCFile* const cfilep : getAndClearCfileps()) netlistp->addFilesp(cfilep);
    }

public:
    static void apply(AstNetlist* netlistp, const V3EmitC::RtmdDataTypes& dataTypes,
                      const V3EmitC::RtmdSignalTypes& signalTypes,
                      const V3EmitC::RtmdActSets& actSets, const V3EmitC::RtmdScopes& scopes) {
        EmitCRtmdRegister{netlistp, dataTypes, signalTypes, actSets, scopes};
    }
};

//######################################################################
// Rtmd registration emit

void V3EmitC::emitcRtmdRegister(const RtmdDataTypes& dataTypes, const RtmdSignalTypes& signalTypes,
                                const RtmdActSets& actSets, const RtmdScopes& scopes) {
    UINFO(2, __FUNCTION__ << ":");
    EmitCRtmdRegister::apply(v3Global.rootp(), dataTypes, signalTypes, actSets, scopes);
}
