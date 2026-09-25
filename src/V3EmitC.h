// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ code for module tree
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

#ifndef VERILATOR_V3EMITC_H_
#define VERILATOR_V3EMITC_H_

#include "config_build.h"
#include "verilatedos.h"

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

class AstNodeRtmdDataType;
class AstRtmdActSet;
class AstRtmdSignalType;

//============================================================================

class V3EmitC final {
public:
    static void emitcConstPool() VL_MT_DISABLED;
    static void emitcFiles() VL_MT_DISABLED;
    static void emitcHeaders() VL_MT_DISABLED;
    static void emitcImp();
    static void emitcInlines() VL_MT_DISABLED;
    static void emitcModel() VL_MT_DISABLED;
    static void emitcPch() VL_MT_DISABLED;
    static void emitcSyms(bool dpiHdrOnly = false) VL_MT_DISABLED;

    // Run time model descriptor emitters. Each returns what later emitters need.
    struct RtmdDataTypes final {
        std::unordered_map<const AstNodeRtmdDataType*, uint32_t> m_rowOf;  // Row of each type
        std::string m_symbol;  // The data type table
    };
    struct RtmdSignalTypes final {
        std::unordered_map<const AstRtmdSignalType*, uint32_t> m_rowOf;  // Row of each signal
        std::string m_symbol;  // The signal type table
    };
    struct RtmdActSets final {
        std::unordered_map<const AstRtmdActSet*, uint32_t> m_rowOf;  // Row of each set
        std::string m_symbol;  // The activity set table
        uint32_t m_nFlags = 0;  // Number of activity flags
    };
    struct RtmdScopes final {
        std::string m_tablesSymbol;  // The table of tables
        std::string m_tableRowsSymbol;  // The row count of each table
        std::vector<uint32_t> m_constWords;  // Constant pool
        uint32_t m_nTables = 0;  // Number of tables
        uint32_t m_rootTable = 0;  // Table of the model itself
    };
    static RtmdDataTypes emitcRtmdDataTypes() VL_MT_DISABLED;
    static RtmdSignalTypes emitcRtmdSignalTypes(const RtmdDataTypes&) VL_MT_DISABLED;
    static RtmdActSets emitcRtmdActSets() VL_MT_DISABLED;
    static RtmdScopes emitcRtmdScopes(const RtmdSignalTypes&, const RtmdActSets&) VL_MT_DISABLED;
    static void emitcRtmdRegister(const RtmdDataTypes&, const RtmdSignalTypes&, const RtmdActSets&,
                                  const RtmdScopes&) VL_MT_DISABLED;
    // Emit all descriptor tables and the registration function
    static void emitcRtmd() {
        const RtmdDataTypes dataTypes = emitcRtmdDataTypes();
        const RtmdSignalTypes signalTypes = emitcRtmdSignalTypes(dataTypes);
        const RtmdActSets actSets = emitcRtmdActSets();
        const RtmdScopes scopes = emitcRtmdScopes(signalTypes, actSets);
        emitcRtmdRegister(dataTypes, signalTypes, actSets, scopes);
    }
};

#endif  // Guard
