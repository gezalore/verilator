// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for the run time model descriptors
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
// Emits the descriptor tables of the model, each in its own file. The model's rtmd()
// method, which hands them to the runtime, is emitted by V3EmitCModel:
//
// - Data type table (VlRtmdDataTypeRow), one row per type descriptor, each holding the
//   descriptor itself. The members of a struct or union, and the items of an enum, are the rows
//   following it.
// - Global table (VlRtmdGlobalSymRow), the global variables of GLOBAL rows, which are
//   constant pool entries. Index 0 is not used, and is nullptr.
// - Signal type table (VlRtmdSignalTypeRow), one row per signal type descriptor.
// - Activity set table (VlRtmdActSetRow). The first rows are the row range of each set, by set
//   index, so a signal's set index is its row. The rest are the flag numbers of all sets, each
//   set's following the previous. An empty set means the signal never changes.
// - Hierarchy table (VlRtmdHierRow), one row per descriptor entry, ending with the Pop of the
//   root level. Values are located by offset from the symbol table, or, for constant pool
//   entries, via the global table.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3File.h"
#include "V3Stats.h"

#include <string>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Base of the emitters of a run time model descriptor table: an array of rows, each commented
// with its index

class EmitCRtmdTableBase VL_NOT_FINAL : public EmitCBaseVisitorConst {
    // STATE
    const std::string m_rowType;  // Type of the rows of the table
    uint32_t m_nRows = 0;  // Number of rows so far
    bool m_needComma = false;  // Row has an argument already. Cleared by beginRow, set by putArg
    bool m_needBrace = false;  // Row needs a closing brace. Set by beginRow

protected:
    // VISITORS
    void visit(AstNode* nodep) override { nodep->v3fatalSrc("Unexpected node"); }

    // METHODS

    // Return as a C string literal
    static std::string stringLiteral(const std::string& str) {
        return '"' + V3OutFormatter::quoteNameControls(str) + '"';
    }
    // Return the name of the node as a C string literal
    static std::string nameLiteral(const AstNode* nodep) { return stringLiteral(nodep->name()); }

    // Number of rows so far, which is the index of the next row
    uint32_t nRows() const { return m_nRows; }

    // Begin the definition of table 'symbol'
    void beginTable(const std::string& symbol) {
        puts("\nVL_CONSTINIT_CXX20 extern const " + m_rowType + " " + symbol + "[] = {\n");
    }
    void endTable() { puts("};\n"); }

    // A row of the table. 'kind' is the type nested in the row type to construct the row from,
    // from the arguments. If empty, the row is the single argument itself.
    void beginRow(const std::string& kind = "") {
        puts("/*" + std::to_string(m_nRows++) + "*/ ");
        m_needBrace = !kind.empty();
        if (m_needBrace) puts(m_rowType + "::" + kind + "{");
        m_needComma = false;
    }
    void putArg(const std::string& arg) {
        if (m_needComma) puts(", ");
        puts(arg);
        m_needComma = true;
    }
    void endRow(const std::string& comment = "") {
        if (m_needBrace) puts("}");
        puts(comment.empty() ? ",\n" : ", // " + comment + "\n");
    }

    // CONSTRUCTORS
    explicit EmitCRtmdTableBase(const std::string& rowType)
        : m_rowType{rowType} {}
};

//######################################################################
// Rtmd activity set table emitter

class EmitCRtmdActSets final : public EmitCRtmdTableBase {
    // CONSTRUCTORS
    explicit EmitCRtmdActSets(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdActSetRow"} {
        const std::string symbol = EmitCUtil::rtmdActSetTableName();

        // Open output file
        openNewOutputSourceFile(symbol, true, true, "RTMD activity flag sets");

        // Header
        puts("\n#include \"verilated_rtmd.h\"\n");

        // Table
        const std::vector<std::vector<uint32_t>>& sets = netlistp->actSets();
        beginTable(symbol);
        // The row range of each set, the flags starting after these rows
        size_t begin = sets.size();
        for (const std::vector<uint32_t>& set : sets) {
            const size_t end = begin + set.size();
            const std::string comment = [&]() -> std::string {
                if (set.empty()) return "empty";
                std::string str = "flags";
                for (const uint32_t flag : set) str += " " + std::to_string(flag);
                return str;
            }();
            beginRow("Range");
            putArg(std::to_string(begin));
            putArg(std::to_string(end));
            endRow(comment);
            begin = end;
        }
        // The flags of each set
        for (size_t id = 0; id < sets.size(); ++id) {
            for (const uint32_t flag : sets[id]) {
                beginRow("Flag");
                putArg(std::to_string(flag) + "U");
                endRow("In set " + std::to_string(id));
            }
        }
        endTable();
        V3Stats::addStat("Emit, Rtmd activity set table rows", nRows());

        // Close output file
        closeOutputFile();
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdActSets{netlistp}; }
};

//######################################################################
// Rtmd data type table emitter

class EmitCRtmdDataTypes final : public EmitCRtmdTableBase {
    // METHODS

    // Number of nodes in a list
    static uint32_t countOf(const AstNode* nodep) {
        uint32_t count = 0;
        for (; nodep; nodep = nodep->nextp()) ++count;
        return count;
    }

    // VISITORS - Each type puts its row, then the rows of its members or items
    void visit(AstRtmdDTAtom* nodep) override {
        beginRow("Atom");
        putArg("VlRtmdDataTypeRow::Atom::Kind::"s + nodep->keyword().rtmdAtomKind());
        putArg(nodep->isSigned() ? "true" : "false");
        putArg(std::to_string(nodep->bits()));
        endRow(nodep->keyword().ascii() + (nodep->isSigned() ? " signed"s : ""s));
    }

    void visit(AstRtmdDTEnum* nodep) override {
        const std::string baseIdx = std::to_string(nodep->rtmddtp()->user2());
        beginRow("Enum");
        putArg(nameLiteral(nodep));
        putArg(baseIdx);
        putArg(std::to_string(countOf(nodep->itemsp())));
        endRow("enum " + nodep->name() + " of #" + baseIdx);
        for (const AstRtmdEnumItem* ip = nodep->itemsp(); ip;
             ip = VN_AS(ip->nextp(), RtmdEnumItem)) {
            beginRow("EnumItem");
            putArg(nameLiteral(ip));
            putArg(stringLiteral(ip->value()));
            endRow("item " + ip->name());
        }
    }

    void visit(AstRtmdDTPackedArray* nodep) override {
        const std::string lStr = std::to_string(nodep->left());
        const std::string rStr = std::to_string(nodep->right());
        const std::string elemIdx = std::to_string(nodep->elemRtmddtp()->user2());
        beginRow("PackedArray");
        putArg(lStr);
        putArg(rStr);
        putArg(elemIdx);
        putArg(nodep->isSigned() ? "true" : "false");
        endRow((nodep->isSigned() ? "signed "s : ""s) + "[" + lStr + ":" + rStr + "] of #"
               + elemIdx);
    }

    void visit(AstRtmdDTPackedStruct* nodep) override {
        beginRow("PackedStruct");
        putArg(std::to_string(countOf(nodep->membersp())));
        putArg(nodep->isSigned() ? "true" : "false");
        endRow("struct packed"s + (nodep->isSigned() ? " signed" : ""));
        for (const AstRtmdMember* mp = nodep->membersp(); mp;
             mp = VN_AS(mp->nextp(), RtmdMember)) {
            const std::string memberIdx = std::to_string(mp->rtmddtp()->user2());
            beginRow("Member");
            putArg(nameLiteral(mp));
            putArg(memberIdx);
            putArg(std::to_string(mp->lsb()));
            endRow("member " + mp->name() + " of #" + memberIdx);
        }
    }

    void visit(AstRtmdDTPackedUnion* nodep) override {
        beginRow("PackedUnion");
        putArg(std::to_string(countOf(nodep->membersp())));
        putArg(nodep->isSigned() ? "true" : "false");
        endRow("union packed"s + (nodep->isSigned() ? " signed" : ""));
        // The members, with the bit offset of their LSB
        for (const AstRtmdMember* mp = nodep->membersp(); mp;
             mp = VN_AS(mp->nextp(), RtmdMember)) {
            const std::string memberIdx = std::to_string(mp->rtmddtp()->user2());
            beginRow("Member");
            putArg(nameLiteral(mp));
            putArg(memberIdx);
            putArg(std::to_string(mp->lsb()));
            endRow("member " + mp->name() + " of #" + memberIdx);
        }
    }

    void visit(AstRtmdDTUnpackedArray* nodep) override {
        const std::string lStr = std::to_string(nodep->left());
        const std::string rStr = std::to_string(nodep->right());
        const std::string elemIdx = std::to_string(nodep->elemRtmddtp()->user2());
        const std::string elemType
            = VN_AS(nodep->dtypep(), UnpackArrayDType)->subDTypep()->cType("", false, false);
        beginRow("UnpackedArray");
        putArg(lStr);
        putArg(rStr);
        putArg(elemIdx);
        putArg("sizeof(" + elemType + ")");
        endRow("[" + lStr + ":" + rStr + "] of #" + elemIdx);
    }

    void visit(AstRtmdDTUnpackedStruct* nodep) override {
        beginRow("UnpackedStruct");
        putArg(std::to_string(countOf(nodep->membersp())));
        endRow("struct");
        const std::string structType = EmitCUtil::prefixNameProtect(nodep->dtypep());
        const AstMemberDType* dtMemberp = VN_AS(nodep->dtypep(), StructDType)->membersp();
        for (const AstRtmdMember* mp = nodep->membersp(); mp;
             mp = VN_AS(mp->nextp(), RtmdMember)) {
            UASSERT_OBJ(dtMemberp, mp, "Member without a data type");
            const std::string memberIdx = std::to_string(mp->rtmddtp()->user2());
            beginRow("Member");
            putArg(nameLiteral(mp));
            putArg(memberIdx);
            putArg("offsetof(" + structType + ", " + dtMemberp->nameProtect() + ")");
            endRow("member " + mp->name() + " of #" + memberIdx);
            dtMemberp = VN_AS(dtMemberp->nextp(), MemberDType);
        }
    }

    // CONSTRUCTORS
    explicit EmitCRtmdDataTypes(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdDataTypeRow"} {
        const std::string symbol = EmitCUtil::rtmdDataTypeTableName();

        // Open output file
        openNewOutputSourceFile(symbol, true, true, "RTMD data type table");

        // Header
        puts("\n#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        puts("\n#include \"verilated_rtmd.h\"\n");
        putOffsetofPragmaPush();

        // Table
        beginTable(symbol);
        for (AstNodeRtmdDataType* typep = netlistp->typeTablep()->rtmdDataTypesp(); typep;
             typep = VN_AS(typep->nextp(), NodeRtmdDataType)) {
            // Record the row index of this type
            typep->user2(nRows());
            // Emit it
            iterateConst(typep);
        }
        beginRow("End");
        endRow("end of table");
        endTable();
        V3Stats::addStat("Emit, Rtmd data type table rows", nRows());

        // Footer
        putOffsetofPragmaPop();

        // Close output file
        closeOutputFile();
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdDataTypes{netlistp}; }
};

//######################################################################
// Rtmd global symbol table emitter

class EmitCRtmdGlobalSyms final : public EmitCRtmdTableBase {
    // CONSTRUCTORS
    explicit EmitCRtmdGlobalSyms(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdGlobalSymRow"} {
        const std::string symbol = EmitCUtil::rtmdGlobalTableName();

        // Open output file
        openNewOutputSourceFile(symbol, true, true, "RTMD global symbol table");

        // Header
        puts("\n#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        puts("\n#include \"verilated_rtmd.h\"\n");

        // Gather the globals, recording the index of each
        std::vector<AstVar*> varps;
        netlistp->topScopep()->rtmdp()->foreach([&](AstRtmdSignal* ep) {
            if (!ep->refp()) return;
            AstVar* const varp = ep->varp();
            if (!varp->constPoolEntry() || varp->user2()) return;
            varps.push_back(varp);
            varp->user2(varps.size());
        });

        // Declarations of the globals - these will need relocations in the table
        if (!varps.empty()) puts("\n");
        for (const AstVar* const varp : varps) {
            const std::string name = EmitCUtil::constPoolName(varp);
            putns(varp, "extern const " + varp->dtypep()->cType(name, false, false) + ";\n");
        }

        // Table
        beginTable(symbol);
        beginRow("Const");
        putArg("nullptr");
        endRow("not used");
        for (const AstVar* const varp : varps) {
            beginRow("Const");
            putArg("&" + EmitCUtil::constPoolName(varp));
            endRow(varp->name());
        }
        endTable();

        // Close output file
        closeOutputFile();

        V3Stats::addStat("Emit, Rtmd global symbol table rows", nRows());
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdGlobalSyms{netlistp}; }
};

//######################################################################
// Rtmd signal type table emitter

class EmitCRtmdSignalTypes final : public EmitCRtmdTableBase {
    // CONSTRUCTORS
    explicit EmitCRtmdSignalTypes(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdSignalTypeRow"} {
        const std::string symbol = EmitCUtil::rtmdSignalTypeTableName();

        // Open output file
        openNewOutputSourceFile(symbol, true, true, "RTMD signal type table");

        // Header
        puts("\n#include \"verilated_rtmd.h\"\n\n");

        // Table
        beginTable(symbol);
        for (AstRtmdSignalType* sigp = netlistp->typeTablep()->rtmdSignalTypesp(); sigp;
             sigp = VN_AS(sigp->nextp(), RtmdSignalType)) {
            sigp->user2(nRows());
            beginRow("Signal");
            putArg("VlRtmdSignalTypeRow::Signal::Kind::"s + sigp->kind().ascii());
            putArg("VlRtmdSignalTypeRow::Signal::Direction::"s + sigp->direction().ascii());
            putArg(std::to_string(sigp->rtmddtp()->user2()));
            endRow();
        }
        endTable();
        V3Stats::addStat("Emit, Rtmd signal type table rows", nRows());

        // Close output file
        closeOutputFile();
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdSignalTypes{netlistp}; }
};

//######################################################################
// Rtmd hierarchy table emitter

class EmitCRtmdHier final : public EmitCRtmdTableBase {
    // NODE STATE
    //  AstRtmdLevel::user3()  // int; 0: unknown, 1: has no signals, 2: has signals
    const VNUser3InUse m_user3InUse;

    // METHODS

    // Computes the offset of a signal's storage from the model symbol table
    static std::string valueOffset(const AstRtmdSignal* ep) {
        const AstScope* const scopep = ep->refScopep();
        return "VL_RTMD_OFFSETOF(" + EmitCUtil::prefixNameProtect(scopep->modp()) + ", "
               + VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + ", "
               + ep->varp()->nameProtect() + ")";
    }

    // Whether a signal is present under levelp
    static bool hasSignals(AstRtmdLevel* levelp) {
        if (levelp->user3()) return levelp->user3() == 2;

        bool found = false;
        for (AstNode* itemp = levelp->itemsp(); itemp; itemp = itemp->nextp()) {
            if (AstRtmdLevel* const subp = VN_CAST(itemp, RtmdLevel)) {
                found = hasSignals(subp);
            } else if (AstRtmdIfaceRef* const refp = VN_CAST(itemp, RtmdIfaceRef)) {
                found = hasSignals(refp->ifaceRtmdp());
            } else if (VN_IS(itemp, RtmdPartition)) {
                found = true;  // Assume partitions are not empty
            } else if (VN_IS(itemp, RtmdSignal)) {
                found = true;
            }
            if (found) break;
        }
        levelp->user3(found ? 2 : 1);
        return found;
    }

    // Number the Push row of each level, from 'row', returns the row after the level
    static uint32_t numberRows(AstRtmdLevel* levelp, uint32_t row) {
        levelp->user2(row++);  // Push
        for (AstNode* itemp = levelp->itemsp(); itemp; itemp = itemp->nextp()) {
            if (AstRtmdLevel* const subp = VN_CAST(itemp, RtmdLevel)) {
                row = numberRows(subp, row);
            } else {
                ++row;
            }
        }
        return ++row;  // Pop
    }

    // VISITORS - Each item puts its rows
    void visit(AstRtmdLevel* nodep) override {
        // The rows of a hierarchy level, bracketed by a Push and a Pop
        const uint32_t pushRow = nRows();
        UASSERT_OBJ(nodep->user2() == pushRow, nodep, "Push row numbered wrong");
        beginRow("Push");
        putArg(nameLiteral(nodep));
        putArg("VlRtmdHierRow::Push::Kind::"s + nodep->kind().ascii());
        putArg(hasSignals(nodep) ? "true" : "false");
        endRow("push");
        iterateAndNextConstNull(nodep->itemsp());
        beginRow("Pop");
        endRow("pop #" + std::to_string(pushRow));
    }

    void visit(AstRtmdIfaceRef* nodep) override {
        beginRow("IfaceRef");
        putArg(nameLiteral(nodep));
        putArg(std::to_string(nodep->ifaceRtmdp()->user2()));
        endRow();
    }

    void visit(AstRtmdInstance* nodep) override {
        beginRow("Instance");
        putArg(nameLiteral(nodep));
        endRow();
    }

    void visit(AstRtmdSignal* nodep) override {
        // A global is located via the global table, others by offset from the symbol table. A
        // signal whose value is not accessible has no location.
        const AstVar* const varp = nodep->refp() ? nodep->varp() : nullptr;
        const bool isGlobal = varp && varp->constPoolEntry();
        const std::string location = !varp      ? "VlRtmd::NOADDR"s
                                     : isGlobal ? std::to_string(varp->user2())
                                                : valueOffset(nodep);
        // No activity set without tracing, or without a value
        const uint32_t actSetIdx = nodep->actSetIdx();
        beginRow("Signal");
        putArg(nameLiteral(nodep));
        putArg(std::to_string(nodep->typeDescp()->user2()));
        putArg(actSetIdx == ~0U ? "VlRtmd::NOIDX"s : std::to_string(actSetIdx));
        putArg(location);
        putArg(isGlobal ? "true" : "false");
        endRow();
    }

    void visit(AstRtmdPartition* nodep) override {
        beginRow("Partition");
        putArg(nameLiteral(nodep));
        endRow();
    }

    // CONSTRUCTORS
    explicit EmitCRtmdHier(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdHierRow"} {
        const std::string symbol = EmitCUtil::rtmdHierTableName();

        // Open output file
        openNewOutputSourceFile(symbol, true, true, "RTMD hierarchy table");

        // Header
        puts("\n#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        puts("#include \"verilated_rtmd.h\"\n");
        puts("\n#include <cstddef>\n");
        putOffsetofPragmaPush();
        const std::string symCls = EmitCUtil::symClassName();
        puts("\n#define VL_RTMD_OFFSETOF(scopeType, scope, member) \\\n");
        puts("    (offsetof(" + symCls + ", scope) + offsetof(scopeType, member))\n");

        // Table
        AstRtmdLevel* const rootp = netlistp->topScopep()->rtmdp();
        UASSERT_OBJ(rootp->kind() == VRtmdLevelKind::ROOT, rootp, "Top scope is not the root");
        const uint32_t nRowsExpected = numberRows(rootp, 0);
        beginTable(symbol);
        iterateConst(rootp);
        endTable();
        UASSERT_OBJ(nRows() == nRowsExpected, rootp, "Hierarchy rows numbered wrong");
        V3Stats::addStat("Emit, Rtmd hierarchy table rows", nRows());

        // Footer
        puts("\n#undef VL_RTMD_OFFSETOF\n");
        putOffsetofPragmaPop();

        // Close output file
        closeOutputFile();
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdHier{netlistp}; }
};

//######################################################################
// Rtmd emit

void V3EmitC::emitcRtmd() {
    if (!v3Global.opt.rtmd()) return;

    UINFO(2, __FUNCTION__ << ":");
    // NODE STATE
    // AstNodeRtmdDataType::user2()   // uint32_t; Index of its row in the data type table
    // AstRtmdSignalType::user2()     // uint32_t; Index of its row in the signal type table
    // AstVar::user2()                // uint32_t; Index of its row in the global table, 0 if none
    // AstRtmdLevel::user2()          // uint32_t; Index of its Push row in the hierarchy table
    const VNUser2InUse user2InUse;

    // Activity sets are only meaningful with the activity flags
    if (v3Global.rootp()->activityp()) EmitCRtmdActSets::apply(v3Global.rootp());
    EmitCRtmdDataTypes::apply(v3Global.rootp());
    EmitCRtmdGlobalSyms::apply(v3Global.rootp());
    EmitCRtmdSignalTypes::apply(v3Global.rootp());
    EmitCRtmdHier::apply(v3Global.rootp());
}
