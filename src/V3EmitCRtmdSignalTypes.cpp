// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for the run time model descriptor signal types
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
// Emits the signal type table (VlRtmdSignalType), one row per signal type descriptor.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3File.h"
#include "V3Stats.h"

#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Rtmd signal type table emitter

class EmitCRtmdSignalTypes final : public EmitCBaseVisitorConst {
    // STATE
    const V3EmitC::RtmdDataTypes& m_dataTypes;  // Data type table, already laid out
    V3EmitC::RtmdSignalTypes m_result;  // Result
    std::vector<const AstRtmdSignalType*> m_signals;  // Signal type table rows
    std::unordered_map<const AstRtmdSignalType*, uint32_t> m_signalIdx;  // Row of each signal
    VDouble0 m_statSignalRows;  // Statistic tracking

    // VISITORS
    // Not a visitor pass; the descriptors are walked directly
    void visit(AstNode*) override {}  // LCOV_EXCL_LINE

    // METHODS

    // Assign a row to each signal type descriptor
    void layoutSignals(AstNetlist* netlistp) {
        for (AstRtmdSignalType* sigp = netlistp->typeTablep()->rtmdSignalTypesp(); sigp;
             sigp = VN_AS(sigp->nextp(), RtmdSignalType)) {
            m_signalIdx.emplace(sigp, static_cast<uint32_t>(m_signals.size()));
            m_signals.push_back(sigp);
        }
    }

    // Name of the signal type table, unique per model
    static std::string signalTypesSymbol() {
        return EmitCUtil::topClassName() + "__RtmdSignalTypes";
    }

    void emitSignalTypeTable() {
        const auto& dataTypeRowOf = m_dataTypes.m_rowOf;
        puts("\n// Signal type table\n");
        puts("VL_CONSTINIT_CXX20 extern const VlRtmdSignalType " + signalTypesSymbol()
             + "[] = {\n");
        for (size_t idx = 0; idx < m_signals.size(); ++idx) {
            const AstRtmdSignalType* const sigp = m_signals[idx];
            ++m_statSignalRows;
            std::string comment = sigp->varKind().ascii();
            if (sigp->direction() != VDirection::NONE) {
                comment += " "s + sigp->direction().ascii();
            }
            puts("    /*" + cvtToStr(idx) + "*/ {" + cvtToStr(dataTypeRowOf.at(sigp->rtmddtp()))
                 + ", VlRtmdVarKind::" + sigp->varKind().ascii()
                 + ", VlRtmdDirection::" + sigp->direction().rtmdDirection() + "},  // " + comment
                 + " of #" + cvtToStr(dataTypeRowOf.at(sigp->rtmddtp())) + "\n");
        }
        puts("};\n");
    }

    // CONSTRUCTORS
    EmitCRtmdSignalTypes(AstNetlist* netlistp, const V3EmitC::RtmdDataTypes& dataTypes)
        : m_dataTypes{dataTypes} {
        layoutSignals(netlistp);
        openNewOutputSourceFile(signalTypesSymbol(), /* slow: */ true, /* support: */ true,
                                "Run time model descriptor signal types");
        puts("\n#include \"verilated_rtmd.h\"\n");
        emitSignalTypeTable();
        closeOutputFile();
        m_result = {std::move(m_signalIdx), signalTypesSymbol()};
        for (AstCFile* const cfilep : getAndClearCfileps()) netlistp->addFilesp(cfilep);
    }
    ~EmitCRtmdSignalTypes() override {
        V3Stats::addStatSum("Tracing, Rtmd signal rows", m_statSignalRows);
    }

public:
    static V3EmitC::RtmdSignalTypes apply(AstNetlist* netlistp,
                                          const V3EmitC::RtmdDataTypes& dataTypes) {
        return std::move(EmitCRtmdSignalTypes{netlistp, dataTypes}.m_result);
    }
};

//######################################################################
// Rtmd signal types emit

V3EmitC::RtmdSignalTypes V3EmitC::emitcRtmdSignalTypes(const RtmdDataTypes& dataTypes) {
    UINFO(2, __FUNCTION__ << ":");
    return EmitCRtmdSignalTypes::apply(v3Global.rootp(), dataTypes);
}
