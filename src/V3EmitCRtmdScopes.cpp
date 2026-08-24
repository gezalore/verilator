// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for the run time model descriptor scopes
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
// Emits one table (of VlRtmdScopeRow) per scope descriptor, with one row per descriptor entry,
// plus the table of tables that INSTANCE rows index. Values are located by offset from the symbol
// table. Constant values are collected into the constant pool.
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
// Rtmd scope table emitter

class EmitCRtmdScopes final : public EmitCBaseVisitorConst {
    // STATE
    const V3EmitC::RtmdSignalTypes& m_signalTypes;  // Signal type table, already laid out
    const V3EmitC::RtmdActSets& m_actSets;  // Activity set table, already laid out
    V3EmitC::RtmdScopes m_result;  // Result
    // One emitted table
    struct Table final {
        const AstRtmdScope* m_descp;  // The descriptor
        std::string m_path;  // Trace path of the instance
        uint32_t m_rows = 0;  // Number of rows
    };
    std::vector<Table> m_tables;
    std::vector<uint32_t> m_constWords;  // Constant pool
    std::unordered_map<std::string, uint32_t> m_constOfs;  // Word index of each constant
    uint32_t m_rootTable = 0;  // Scope table of the model itself
    VDouble0 m_statScopeRows;  // Statistic tracking

    // VISITORS
    // Not a visitor pass; the descriptors are walked directly
    void visit(AstNode*) override {}  // LCOV_EXCL_LINE

    // METHODS

    // Return a name as a C string literal
    static std::string nameLiteral(const std::string& name, bool protect) {
        return '"' + V3OutFormatter::quoteNameControls(VIdProtect::protectWordsIf(name, protect))
               + '"';
    }

    // The descriptors of all instances are inlined into the one of the top scope, so there is
    // a single table
    void layoutScopes(AstNetlist* netlistp) {
        const AstTopScope* const topScopep = netlistp->topScopep();
        // prettyName drops the leading 'TOP.'
        m_tables.push_back(
            {topScopep->rtmdsp(), AstNode::prettyName(topScopep->scopep()->name() + "->"), 0});
        m_rootTable = 0;
    }

    // Return the Pop closing the naming level the given Push opens
    static const AstRtmdPop* matchingPop(const AstRtmdPush* pushp) {
        int depth = 0;
        for (const AstNode* itemp = pushp->nextp(); itemp; itemp = itemp->nextp()) {
            if (VN_IS(itemp, RtmdPush)) {
                ++depth;
            } else if (const AstRtmdPop* const popp = VN_CAST(itemp, RtmdPop)) {
                if (!depth) return popp;
                --depth;
            }
        }
        pushp->v3fatalSrc("Unbalanced naming levels in descriptor");
        return nullptr;  // LCOV_EXCL_LINE
    }

    // Add a constant to the pool (at an even index, for 64-bit alignment), and return its index
    uint32_t poolConst(const AstConst* constp) {
        const uint32_t words = (static_cast<uint32_t>(constp->width()) + 31) / 32;
        std::string key = cvtToStr(words);
        std::vector<uint32_t> vals;
        for (uint32_t i = 0; i < words; ++i) {
            const uint32_t val = constp->num().edataWord(i);
            vals.push_back(val);
            key += "_" + cvtToStr(val);
        }
        const auto pair = m_constOfs.emplace(key, static_cast<uint32_t>(m_constWords.size()));
        if (!pair.second) return pair.first->second;
        if (m_constWords.size() & 1) {  // Pad to even word
            m_constWords.push_back(0);
            pair.first->second = static_cast<uint32_t>(m_constWords.size());
        }
        for (const uint32_t val : vals) m_constWords.push_back(val);
        return pair.first->second;
    }

    static std::string scopeKind(VRtmdScopeKind kind) { return kind.ascii(); }

    // Return the offset of an instance from the symbol table
    static std::string scopeOffset(const AstScope* scopep) {
        return "offsetof(" + EmitCUtil::symClassName() + ", "
               + VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + ")";
    }

    // Return the offset of a value from the symbol table. This is not relative to the described
    // scope, as the variable might live in a different scope (e.g. V3Inst port aliasing).
    static std::string valueOffset(const AstRtmdSignal* ep) {
        const AstScope* const scopep = ep->refScopep();
        UASSERT_OBJ(scopep, ep, "Described value without a scope, V3Descope should have linked");
        return scopeOffset(scopep) + " + offsetof(" + EmitCUtil::prefixNameProtect(scopep->modp())
               + ", " + ep->varp()->nameProtect() + ")";
    }

    // Activity set table index of the given set, 0 if none
    uint32_t actSetId(const AstRtmdActSet* entryp) const {
        const auto it = m_actSets.m_rowOf.find(entryp);
        return it == m_actSets.m_rowOf.end() ? 0 : it->second;
    }

    // Names of the tables, unique per model
    static std::string tablesSymbol() { return EmitCUtil::topClassName() + "__RtmdTables"; }
    static std::string tableRowsSymbol() { return EmitCUtil::topClassName() + "__RtmdTableRows"; }

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

    void emitPushRow(const std::string& name, VRtmdScopeKind kind) {
        puts("    {VlRtmdScopeOp::PUSH, VlRtmdScopeKind::" + scopeKind(kind) + ", "
             + nameLiteral(name, false) + ", \"\", 0, 0, 0, 0},\n");
    }
    void emitPopRow() {
        puts("    {VlRtmdScopeOp::POP, VlRtmdScopeKind::MODULE, \"\", \"\", 0, 0, 0, 0},\n");
    }

    // Emit the rows of the items from 'firstp' up to, but not including, 'endp', and return the
    // number of rows emitted. 'paths' is the stack of instance paths of the open naming levels.
    uint32_t emitRows(const AstNode* firstp, const AstNode* endp,
                      std::vector<std::string>& paths) {
        uint32_t rows = 0;
        for (const AstNode* entryp = firstp; entryp != endp; entryp = entryp->nextp()) {
            if (VN_IS(entryp, RtmdInstance)) {
                // The inlined naming level that follows opens the instance
                continue;
            }
            ++m_statScopeRows;
            ++rows;
            if (const AstRtmdPush* const ep = VN_CAST(entryp, RtmdPush)) {
                emitPushRow(ep->name(), ep->kind());
                // Only instance levels are part of the instance path
                const bool instance = ep->kind() == VRtmdScopeKind::MODULE
                                      || ep->kind() == VRtmdScopeKind::INTERFACE;
                paths.push_back(instance ? paths.back() + ep->name() + "." : paths.back());
            } else if (VN_IS(entryp, RtmdPop)) {
                emitPopRow();
                paths.pop_back();
            } else if (const AstRtmdIfaceRef* const ep = VN_CAST(entryp, RtmdIfaceRef)) {
                // Show the contents of the referenced interface under the name of the reference.
                // Values at the same address share trace codes at run time.
                const AstRtmdPush* const targetp = ep->ifaceRtmdp();
                UASSERT_OBJ(targetp, ep, "Interface reference not linked");
                emitPushRow(ep->name(), VRtmdScopeKind::INTERFACE);
                paths.push_back(paths.back() + ep->name() + ".");
                rows += emitRows(targetp->nextp(), matchingPop(targetp), paths);
                paths.pop_back();
                emitPopRow();
                ++m_statScopeRows;
                ++rows;
            } else if (const AstRtmdSignal* const ep = VN_CAST(entryp, RtmdSignal)) {
                // A parameter is emitted as its value, held in the constant pool
                const AstVar* const varp = ep->varp();
                const AstConst* const constp
                    = varp->isParam() ? VN_CAST(varp->valuep(), Const) : nullptr;
                UASSERT_OBJ(constp || !varp->isParam(), ep, "Parameter without a constant value");
                const bool isConst = constp;
                const std::string dataOfs
                    = constp ? cvtToStr(poolConst(constp)) : valueOffset(ep);
                puts("    {VlRtmdScopeOp::"s + (isConst ? "SIGNAL_CONST" : "SIGNAL")
                     + ", VlRtmdScopeKind::MODULE, " + nameLiteral(ep->name(), false) + ", \"\", "
                     + cvtToStr(m_signalTypes.m_rowOf.at(ep->typeDescp())) + ", " + dataOfs + ", "
                     + "0, " + cvtToStr(actSetId(ep->actSetp())) + "},\n");
            } else if (const AstRtmdPartition* const ep = VN_CAST(entryp, RtmdPartition)) {
                // The library registers under its instance path, so emit that for matching
                const std::string path = paths.back() + ep->name();
                puts("    {VlRtmdScopeOp::PARTITION"
                     ", VlRtmdScopeKind::MODULE, "
                     + nameLiteral(ep->name(), false) + ", " + nameLiteral(path, false)
                     + ", 0, 0, 0, 0},\n");
            }
        }
        return rows;
    }

    // Emit the table of one scope, and return the rows it holds
    uint32_t emitScopeTable(const Table& table, uint32_t idx) {
        const AstRtmdScope* const descp = table.m_descp;
        puts("\n// " + descp->name() + "\n");
        puts("static const VlRtmdScopeRow VlRtmdScope" + cvtToStr(idx)
             + "[] VL_ATTR_UNUSED = {\n");
        std::vector<std::string> paths{table.m_path};
        const uint32_t rows = emitRows(descp->itemsp(), nullptr, paths);
        UASSERT_OBJ(paths.size() == 1, descp, "Unbalanced naming levels in descriptor");
        puts("};\n");
        return rows;
    }

    void emitTables() {
        puts("\n// Table of tables\n");
        puts("extern const VlRtmdScopeRow* const " + tablesSymbol() + "[] = {\n");
        for (size_t idx = 0; idx < m_tables.size(); ++idx) {
            puts("    VlRtmdScope" + cvtToStr(idx) + ",\n");
        }
        puts("};\n");
        puts("\n// Rows in each table above\n");
        puts("extern const uint32_t " + tableRowsSymbol() + "[] = {\n");
        for (const Table& table : m_tables) puts("    " + cvtToStr(table.m_rows) + ",\n");
        puts("};\n");
    }

    // CONSTRUCTORS
    EmitCRtmdScopes(AstNetlist* netlistp, const V3EmitC::RtmdSignalTypes& signalTypes,
                    const V3EmitC::RtmdActSets& actSets)
        : m_signalTypes{signalTypes}
        , m_actSets{actSets} {
        layoutScopes(netlistp);
        openNewOutputSourceFile(EmitCUtil::topClassName() + "__RtmdScopes", /* slow: */ true,
                                /* support: */ true, "Run time model descriptor scopes");
        // Needed for offsetof
        puts("\n#include \"" + EmitCUtil::symClassName() + ".h\"\n");
        puts("#include \"verilated_rtmd.h\"\n");
        puts("\n#include <cstddef>\n");
        putOffsetofPragmaPush();
        for (size_t idx = 0; idx < m_tables.size(); ++idx) {
            m_tables[idx].m_rows = emitScopeTable(m_tables[idx], static_cast<uint32_t>(idx));
        }
        emitTables();
        putOffsetofPragmaPop();
        closeOutputFile();
        m_result = {tablesSymbol(), tableRowsSymbol(), std::move(m_constWords),
                    static_cast<uint32_t>(m_tables.size()), m_rootTable};
        for (AstCFile* const cfilep : getAndClearCfileps()) netlistp->addFilesp(cfilep);
    }
    ~EmitCRtmdScopes() override {
        V3Stats::addStatSum("Tracing, Rtmd scope rows", m_statScopeRows);
    }

public:
    static V3EmitC::RtmdScopes apply(AstNetlist* netlistp,
                                     const V3EmitC::RtmdSignalTypes& signalTypes,
                                     const V3EmitC::RtmdActSets& actSets) {
        return std::move(EmitCRtmdScopes{netlistp, signalTypes, actSets}.m_result);
    }
};

//######################################################################
// Rtmd scopes emit

V3EmitC::RtmdScopes V3EmitC::emitcRtmdScopes(const RtmdSignalTypes& signalTypes,
                                             const RtmdActSets& actSets) {
    UINFO(2, __FUNCTION__ << ":");
    return EmitCRtmdScopes::apply(v3Global.rootp(), signalTypes, actSets);
}
