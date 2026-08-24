// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for the run time model descriptor data types
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
// Emits the data type table (VlRtmdTypeRow), one row per type descriptor. Each row points to a
// separate descriptor object with external linkage, so the descriptors can be split across
// files.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3File.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Rtmd data type table emitter

class EmitCRtmdDataTypes final : public EmitCBaseVisitorConst {
    // TYPES

    // Runtime type, VlRtmdTypeRow union member and op of a kind
    struct RowKind final {
        const char* m_cType;
        const char* m_member;
        const char* m_op;
    };

    // STATE
    V3EmitC::RtmdDataTypes m_result;  // Result
    bool m_typeDefsNeedSyms = false;  // Type definitions need the Syms header
    std::vector<const AstNodeRtmdDataType*> m_typeRows;  // Type table rows
    V3UniqueNames m_typeDefNames{""};  // Split descriptor file names
    std::unordered_map<const AstNodeRtmdDataType*, uint32_t> m_typeIdx;  // Row of each type
    std::vector<const AstRtmdDTEnum*> m_enums;  // Enum types
    std::unordered_map<const AstRtmdDTEnum*, uint32_t> m_enumIdx;  // Index of each enum
    VDouble0 m_statTypeRows;  // Statistic tracking

    // VISITORS
    // Not a visitor pass; the descriptors are walked directly
    void visit(AstNode*) override {}  // LCOV_EXCL_LINE

    // METHODS

    // Return a name as a C string literal
    static std::string nameLiteral(const std::string& name, bool protect) {
        return '"' + V3OutFormatter::quoteNameControls(VIdProtect::protectWordsIf(name, protect))
               + '"';
    }

    // Assign a type table row to each type descriptor
    void layoutTypes(AstNetlist* netlistp) {
        for (AstNodeRtmdDataType* typep = netlistp->typeTablep()->rtmdDataTypesp(); typep;
             typep = VN_AS(typep->nextp(), NodeRtmdDataType)) {
            m_typeIdx.emplace(typep, static_cast<uint32_t>(m_typeRows.size()));
            m_typeRows.push_back(typep);
        }
    }

    // Number the enums
    void layoutEnums() {
        for (const AstNodeRtmdDataType* const rowp : m_typeRows) {
            if (const AstRtmdDTEnum* const enump = VN_CAST(rowp, RtmdDTEnum)) {
                m_enumIdx.emplace(enump, static_cast<uint32_t>(m_enums.size()));
                m_enums.push_back(enump);
            }
        }
    }

    // VL_RTMD_* flags of a type
    static std::string flagsOf(const AstNodeRtmdDataType* rowp) {
        return isSignedRow(rowp) ? "VL_RTMD_SIGNED" : "0";
    }

    // Whether a packed type is signed
    static bool isSignedRow(const AstNodeRtmdDataType* rowp) {
        if (const AstRtmdDTAtom* const p = VN_CAST(rowp, RtmdDTAtom)) return p->isSigned();
        if (const AstRtmdDTEnum* const p = VN_CAST(rowp, RtmdDTEnum))
            return isSignedRow(p->rtmddtp());
        if (const AstRtmdDTPackedArray* const p = VN_CAST(rowp, RtmdDTPackedArray)) {
            return p->isSigned();
        }
        if (const AstRtmdDTPackedStruct* const p = VN_CAST(rowp, RtmdDTPackedStruct)) {
            return p->isSigned();
        }
        return VN_AS(rowp, RtmdDTPackedUnion)->isSigned();
    }

    // Members of a struct or union, or nullptr
    static AstNode* membersOf(const AstNodeRtmdDataType* rowp) {
        if (const AstRtmdDTPackedStruct* const p = VN_CAST(rowp, RtmdDTPackedStruct)) {
            return p->membersp();
        }
        if (const AstRtmdDTPackedUnion* const p = VN_CAST(rowp, RtmdDTPackedUnion)) {
            return p->membersp();
        }
        if (const AstRtmdDTUnpackedStruct* const p = VN_CAST(rowp, RtmdDTUnpackedStruct)) {
            return p->membersp();
        }
        return nullptr;
    }

    // One line summary of a row, for comments
    std::string typeComment(const AstNodeRtmdDataType* rowp) const {
        if (const AstRtmdDTAtom* const p = VN_CAST(rowp, RtmdDTAtom)) {
            return std::string{p->keyword().ascii()} + " w" + cvtToStr(p->bits());
        }
        if (const AstRtmdDTEnum* const p = VN_CAST(rowp, RtmdDTEnum)) {
            return "enum " + p->name() + " of #" + cvtToStr(m_typeIdx.at(p->rtmddtp()));
        }
        if (const AstRtmdDTPackedArray* const p = VN_CAST(rowp, RtmdDTPackedArray)) {
            return "[" + cvtToStr(p->left()) + ":" + cvtToStr(p->right()) + "] of #"
                   + cvtToStr(m_typeIdx.at(p->elemRtmddtp()));
        }
        if (const AstRtmdDTUnpackedArray* const p = VN_CAST(rowp, RtmdDTUnpackedArray)) {
            return "[" + cvtToStr(p->left()) + ":" + cvtToStr(p->right()) + "] of #"
                   + cvtToStr(m_typeIdx.at(p->elemRtmddtp()));
        }
        if (VN_IS(rowp, RtmdDTPackedStruct)) return "packed struct";
        if (VN_IS(rowp, RtmdDTPackedUnion)) return "packed union";
        return "unpacked struct";
    }

    static RowKind rowKindOf(const AstNodeRtmdDataType* rowp) {
        if (VN_IS(rowp, RtmdDTAtom)) return {"VlRtmdAtom", "m_atomp", "ATOM"};
        if (VN_IS(rowp, RtmdDTEnum)) return {"VlRtmdEnum", "m_enump", "ENUM"};
        if (VN_IS(rowp, RtmdDTPackedArray)) {
            return {"VlRtmdPackedArray", "m_packedArrayp", "PACKED_ARRAY"};
        }
        if (VN_IS(rowp, RtmdDTUnpackedArray)) {
            return {"VlRtmdUnpackedArray", "m_unpackedArrayp", "UNPACKED_ARRAY"};
        }
        if (VN_IS(rowp, RtmdDTPackedStruct)) {
            return {"VlRtmdPackedStruct", "m_packedStructp", "PACKED_STRUCT"};
        }
        if (VN_IS(rowp, RtmdDTPackedUnion)) {
            return {"VlRtmdPackedStruct", "m_packedStructp", "PACKED_UNION"};
        }
        return {"VlRtmdUnpackedStruct", "m_unpackedStructp", "UNPACKED_STRUCT"};
    }

    // Name of the descriptor of one type table row
    std::string typeDefSymbol(size_t idx) const {
        return EmitCUtil::topClassName() + "__RtmdT" + cvtToStr(idx);
    }

    // Name of the type table, unique per model
    static std::string dataTypesSymbol() { return EmitCUtil::topClassName() + "__RtmdDataTypes"; }

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

    // Open a new descriptor file if needed
    void openTypeDefFileIfNeeded() {
        if (ofp() && splitNeeded()) {
            v3Global.useParallelBuild(true);
            closeOutputFile();
        }
        if (!ofp()) {
            openNewOutputSourceFile(m_typeDefNames.get(EmitCUtil::topClassName() + "__RtmdDefs"),
                                    /* slow: */ true, /* support: */ true,
                                    "Run time model descriptor type definitions");
            // Needed for offsetof/sizeof of unpacked types only, as it is expensive
            if (m_typeDefsNeedSyms) {
                puts("\n#include \"" + EmitCUtil::symClassName() + ".h\"\n");
            }
            puts("\n#include \"verilated_rtmd.h\"\n");
        }
    }

    // Emit the descriptors the type table points to
    void emitTypeDefs() {
        for (const AstNodeRtmdDataType* const rowp : m_typeRows) {
            if (VN_IS(rowp, RtmdDTUnpackedStruct) || VN_IS(rowp, RtmdDTUnpackedArray)) {
                m_typeDefsNeedSyms = true;
            }
        }
        for (size_t idx = 0; idx < m_typeRows.size(); ++idx) {
            const AstNodeRtmdDataType* const rowp = m_typeRows[idx];
            openTypeDefFileIfNeeded();
            puts("\n// #" + cvtToStr(idx) + " " + typeComment(rowp) + "\n");
            const std::string sym = typeDefSymbol(idx);
            if (VN_IS(rowp, RtmdDTAtom)) {
                puts("VL_CONSTINIT_CXX20 extern const VlRtmdAtom " + sym + " = {VlRtmdSigType::"s
                     + VN_AS(rowp, RtmdDTAtom)->keyword().rtmdSigType() + ", " + flagsOf(rowp)
                     + ", " + cvtToStr(VN_AS(rowp, RtmdDTAtom)->bits()) + "};\n");
            } else if (const AstRtmdDTEnum* const p = VN_CAST(rowp, RtmdDTEnum)) {
                const std::string namesSym = sym + "n";
                const std::string valuesSym = sym + "v";
                uint32_t count = 0;
                std::string names;
                std::string values;
                for (AstNode* itemp = p->itemsp(); itemp; itemp = itemp->nextp()) {
                    const AstRtmdEnumItem* const ip = VN_AS(itemp, RtmdEnumItem);
                    ++count;
                    names += "\n    " + nameLiteral(ip->name(), false) + ",";
                    values += "\n    " + nameLiteral(ip->value(), false) + ",";
                }
                puts("VL_CONSTINIT_CXX20 static const char* const " + namesSym + "[] = {" + names
                     + "\n};\n");
                puts("VL_CONSTINIT_CXX20 static const char* const " + valuesSym + "[] = {" + values
                     + "\n};\n");
                puts("VL_CONSTINIT_CXX20 extern const VlRtmdEnum " + sym + " = {"
                     + cvtToStr(m_typeIdx.at(p->rtmddtp())) + ", " + nameLiteral(p->name(), false)
                     + ", " + cvtToStr(count) + ", " + namesSym + ", " + valuesSym + ", "
                     + cvtToStr(m_enumIdx.at(p) + 1) + "};\n");
            } else if (const AstRtmdDTPackedArray* const p = VN_CAST(rowp, RtmdDTPackedArray)) {
                puts("VL_CONSTINIT_CXX20 extern const VlRtmdPackedArray " + sym + " = {"
                     + flagsOf(rowp) + ", " + cvtToStr(m_typeIdx.at(p->elemRtmddtp())) + ", "
                     + cvtToStr(p->left()) + ", " + cvtToStr(p->right()) + "};\n");
            } else if (const AstRtmdDTUnpackedArray* const p
                       = VN_CAST(rowp, RtmdDTUnpackedArray)) {
                const std::string elemType
                    = VN_AS(p->dtypep(), UnpackArrayDType)->subDTypep()->cType("", false, false);
                puts("VL_CONSTINIT_CXX20 extern const VlRtmdUnpackedArray " + sym + " = {"
                     + "sizeof(" + elemType + "), " + cvtToStr(m_typeIdx.at(p->elemRtmddtp()))
                     + ", " + cvtToStr(p->left()) + ", " + cvtToStr(p->right()) + "};\n");
            } else {
                // Unpacked member offsets are offsetof the emitted struct. Packed member
                // offsets are derived at run time.
                const AstRtmdDTUnpackedStruct* const unpackedp
                    = VN_CAST(rowp, RtmdDTUnpackedStruct);
                const std::string structType
                    = unpackedp ? EmitCUtil::prefixNameProtect(unpackedp->dtypep()) : "";
                const AstMemberDType* dtMemberp
                    = unpackedp ? VN_AS(unpackedp->dtypep(), StructDType)->membersp() : nullptr;
                const std::string membersSym = sym + "m";
                uint32_t count = 0;
                if (unpackedp) putOffsetofPragmaPush();
                puts("VL_CONSTINIT_CXX20 static const VlRtmdMember " + membersSym + "[] = {\n");
                for (AstNode* itemp = membersOf(rowp); itemp; itemp = itemp->nextp()) {
                    const AstRtmdMember* const memberp = VN_AS(itemp, RtmdMember);
                    ++count;
                    // Descriptor members correspond one to one to the data type members
                    UASSERT_OBJ(!unpackedp || dtMemberp, memberp, "Member without a data type");
                    const std::string offset = dtMemberp ? "offsetof(" + structType + ", "
                                                               + dtMemberp->nameProtect() + ")"
                                                         : "0";
                    puts("    {" + nameLiteral(memberp->name(), memberp->protect()) + ", "
                         + cvtToStr(m_typeIdx.at(memberp->rtmddtp())) + ", " + offset + "},  // "
                         + memberp->name() + "\n");
                    if (dtMemberp) dtMemberp = VN_AS(dtMemberp->nextp(), MemberDType);
                }
                puts("};\n");
                if (unpackedp) putOffsetofPragmaPop();
                if (VN_IS(rowp, RtmdDTUnpackedStruct)) {
                    puts("VL_CONSTINIT_CXX20 extern const VlRtmdUnpackedStruct " + sym + " = {"
                         + cvtToStr(count) + ", " + membersSym + "};\n");
                } else {
                    puts("VL_CONSTINIT_CXX20 extern const VlRtmdPackedStruct " + sym + " = {"
                         + flagsOf(rowp) + ", " + cvtToStr(count) + ", " + membersSym + "};\n");
                }
            }
        }
        if (ofp()) closeOutputFile();
    }

    void emitTypeTable() {
        puts("\n// Row descriptors\n");
        for (size_t idx = 0; idx < m_typeRows.size(); ++idx) {
            puts("extern const "s + rowKindOf(m_typeRows[idx]).m_cType + " " + typeDefSymbol(idx)
                 + ";\n");
        }
        puts("\n// Type table\n");
        puts("VL_CONSTINIT_CXX20 extern const VlRtmdTypeRow " + dataTypesSymbol() + "[] = {\n");
        for (size_t idx = 0; idx < m_typeRows.size(); ++idx) {
            const AstNodeRtmdDataType* const rowp = m_typeRows[idx];
            const RowKind kind = rowKindOf(rowp);
            ++m_statTypeRows;
            puts("    /*" + cvtToStr(idx) + "*/ {VlRtmdTypeOp::"s + kind.m_op + ", {."
                 + kind.m_member + " = &" + typeDefSymbol(idx) + "}},  // " + typeComment(rowp)
                 + "\n");
        }
        puts("};\n");
    }

    // CONSTRUCTORS
    explicit EmitCRtmdDataTypes(AstNetlist* netlistp) {
        layoutTypes(netlistp);
        layoutEnums();
        emitTypeDefs();
        openNewOutputSourceFile(dataTypesSymbol(), /* slow: */ true, /* support: */ true,
                                "Run time model descriptor data types");
        puts("\n#include \"verilated_rtmd.h\"\n");
        emitTypeTable();
        closeOutputFile();
        m_result = {std::move(m_typeIdx), dataTypesSymbol()};
        for (AstCFile* const cfilep : getAndClearCfileps()) netlistp->addFilesp(cfilep);
    }
    ~EmitCRtmdDataTypes() override {
        V3Stats::addStatSum("Tracing, Rtmd type rows", m_statTypeRows);
    }

public:
    static V3EmitC::RtmdDataTypes apply(AstNetlist* netlistp) {
        return std::move(EmitCRtmdDataTypes{netlistp}.m_result);
    }
};

//######################################################################
// Rtmd data types emit

V3EmitC::RtmdDataTypes V3EmitC::emitcRtmdDataTypes() {
    UINFO(2, __FUNCTION__ << ":");
    return EmitCRtmdDataTypes::apply(v3Global.rootp());
}
