// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for the run time model descriptor activity sets
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
// Emits the activity set table (VlRtmdActSetRow), each row a range in the activity flag number
// table. Set 0 holds only the flag set on every eval, and is used by signals with no activity set
// of their own. An empty set means the signal never changes.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3File.h"
#include "V3Stats.h"
#include "V3Trace.h"

#include <unordered_map>
#include <utility>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Rtmd activity set table emitter

class EmitCRtmdActSets final : public EmitCBaseVisitorConst {
    // STATE
    V3EmitC::RtmdActSets m_result;  // Result
    std::vector<uint32_t> m_actSetFlags;  // Activity flag numbers of all sets
    std::vector<std::pair<uint32_t, uint32_t>> m_actSetRows;  // Flag range of each set
    std::unordered_map<const AstRtmdActSet*, uint32_t> m_actSetIds;  // Table index of each set
    VDouble0 m_statActSets;  // Statistic tracking

    // VISITORS
    // Not a visitor pass; the descriptors are walked directly
    void visit(AstNode*) override {}  // LCOV_EXCL_LINE

    // METHODS

    void layoutActSets(const AstRtmdActSets* setsp) {
        // Set 0
        m_actSetFlags = {V3Trace::EVAL_FLAG};
        m_actSetRows = {{0, 1}};
        if (setsp) {
            for (AstRtmdActSet* entryp = setsp->entriesp(); entryp;
                 entryp = VN_AS(entryp->nextp(), RtmdActSet)) {
                m_actSetIds.emplace(entryp, static_cast<uint32_t>(m_actSetRows.size()));
                ++m_statActSets;
                const uint32_t first = static_cast<uint32_t>(m_actSetFlags.size());
                const std::vector<uint32_t>& flags = entryp->flags();
                m_actSetFlags.insert(m_actSetFlags.end(), flags.begin(), flags.end());
                m_actSetRows.emplace_back(first, static_cast<uint32_t>(m_actSetFlags.size()));
            }
        }
    }

    // Name of the activity set table, unique per model
    static std::string actSetsSymbol() { return EmitCUtil::topClassName() + "__RtmdActSets"; }
    // Name of the flag number table, which is static
    static std::string actSetFlagsSymbol() { return "VlRtmdActSetFlags"; }

    void emitActSetTables() {
        puts("\n// Activity flag numbers of each set\n");
        puts("static const uint32_t " + actSetFlagsSymbol() + "[] VL_ATTR_UNUSED = {\n");
        for (size_t id = 0; id < m_actSetRows.size(); ++id) {
            const uint32_t first = m_actSetRows[id].first;
            const uint32_t last = m_actSetRows[id].second;
            if (first == last) {
                puts("    /* Set " + cvtToStr(id) + " is empty */\n");
                continue;
            }
            puts("    /* Set " + cvtToStr(id) + " */ ");
            for (uint32_t i = first; i < last; ++i) puts(" " + cvtToStr(m_actSetFlags[i]) + ",");
            puts("\n");
        }
        puts("};\n");

        puts("\n// Activity sets\n");
        puts("extern const VlRtmdActSetRow " + actSetsSymbol() + "[] = {\n");
        for (size_t id = 0; id < m_actSetRows.size(); ++id) {
            std::string comment;
            for (uint32_t i = m_actSetRows[id].first; i < m_actSetRows[id].second; ++i) {
                comment += (comment.empty() ? "flags " : ", ") + cvtToStr(m_actSetFlags[i]);
            }
            if (comment.empty()) comment = "no flags, so never changes";
            puts("    /*" + cvtToStr(id) + "*/ {" + actSetFlagsSymbol() + " + "
                 + cvtToStr(m_actSetRows[id].first) + ", " + actSetFlagsSymbol() + " + "
                 + cvtToStr(m_actSetRows[id].second) + "},  // " + comment + "\n");
        }
        puts("};\n");
    }

    // CONSTRUCTORS
    explicit EmitCRtmdActSets(AstNetlist* netlistp) {
        const AstRtmdActSets* const setsp = netlistp->rtmdActSetsp();
        layoutActSets(setsp);
        openNewOutputSourceFile(actSetsSymbol(), /* slow: */ true, /* support: */ true,
                                "Run time model descriptor activity sets");
        puts("\n#include \"verilated_rtmd.h\"\n");
        emitActSetTables();
        closeOutputFile();
        m_result = {std::move(m_actSetIds), actSetsSymbol(), setsp ? setsp->nFlags() : 0};
        for (AstCFile* const cfilep : getAndClearCfileps()) netlistp->addFilesp(cfilep);
    }
    ~EmitCRtmdActSets() override {
        V3Stats::addStatSum("Tracing, Rtmd activity sets", m_statActSets);
    }

public:
    static V3EmitC::RtmdActSets apply(AstNetlist* netlistp) {
        return std::move(EmitCRtmdActSets{netlistp}.m_result);
    }
};

//######################################################################
// Rtmd activity sets emit

V3EmitC::RtmdActSets V3EmitC::emitcRtmdActSets() {
    UINFO(2, __FUNCTION__ << ":");
    return EmitCRtmdActSets::apply(v3Global.rootp());
}
