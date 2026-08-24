// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated run time model descriptor (RTMD) types
///
/// Types of the tables that describe a Verilated model's state as data.
/// Included by the generated descriptor tables and by verilated_trace.h.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_RTMD_H_
#define VERILATOR_VERILATED_RTMD_H_

#include "verilated.h"

#include <climits>

//=============================================================================
// Attributes

// Kind of design scope a PUSH or INSTANCE row opens
enum class VlRtmdScopeKind : uint8_t {
    // Note: Entries must match VRtmdScopeKind (by name, not necessarily by value)
    MODULE,
    INTERFACE,
    GENERATE,
    BLOCK,
    FUNCTION,
    TASK,
};

// Declared direction of a port, or NONE for anything that is not one
enum class VlRtmdDirection : uint8_t {
    NONE,
    INPUT,
    OUTPUT,
    INOUT,
};

// Kind of variable or net a signal is declared as
enum class VlRtmdVarKind : uint8_t {
    // Note: Entries must match VRtmdVarKind (by name, not necessarily by value)
    VAR,
    WIRE,
    WREAL,
    TRI,
    TRI0,
    TRI1,
    TRIAND,
    TRIOR,
    SUPPLY0,
    SUPPLY1,
    GPARAM,  // Module parameter
    LPARAM,  // localparam
    SPECPARAM,
    GENVAR,
};

// Base data type of a value
enum class VlRtmdSigType : uint8_t {
    DOUBLE,
    INTEGER,
    BIT,
    LOGIC,
    INT,
    SHORTINT,
    LONGINT,
    BYTE,
    EVENT,
    TIME,
};

//=============================================================================
// Descriptor tables
//
// Types and sub-tables are referenced by index, and values by offset from the symbol table, so
// identical modules and types produce identical rows. Names are plain string literals for now.
// TODO: Pool the names to avoid relocations.

// Kind of type a type table row describes
enum class VlRtmdTypeOp : uint8_t {
    ATOM,  // VlRtmdAtom: a builtin type
    ENUM,  // VlRtmdEnum: an enum over a base type
    PACKED_ARRAY,  // VlRtmdPackedArray: elements are bit fields of one value
    UNPACKED_ARRAY,  // VlRtmdUnpackedArray: elements are separate objects
    PACKED_STRUCT,  // VlRtmdPackedStruct: members are bit fields of one value
    PACKED_UNION,  // VlRtmdPackedStruct: members overlay each other
    UNPACKED_STRUCT  // VlRtmdUnpackedStruct: members are separate objects
};

enum class VlRtmdScopeOp : uint8_t {
    PUSH,  // Open a naming level
    POP,  // Close the level PUSH opened
    SIGNAL,  // A value, located by offset from the symbol table
    SIGNAL_CONST,  // A constant value, held in the constant pool
    INSTANCE,  // A sub-instance, described by its own table
    PARTITION  // A --lib-create library, which registers its own tables
};

// Type flags
constexpr uint16_t VL_RTMD_SIGNED = 1 << 0;

// A builtin type. Aggregates derive width and signal type from this, see vlRtmdBitsOf and
// vlRtmdSigTypeOf.
struct VlRtmdAtom final {
    VlRtmdSigType m_sigType;  // Base data type
    uint16_t m_flags;  // VL_RTMD_*
    uint32_t m_bits;  // Width
};

// How a signal is declared: kind, direction and the type of its value
struct VlRtmdSignalType final {
    uint32_t m_typeIdx;  // Type of the value, as a type table index
    VlRtmdVarKind m_varKind;
    VlRtmdDirection m_direction;  // NONE if it is not a port
};

// An enum over a base type
struct VlRtmdEnum final {
    uint32_t m_baseIdx;  // Base type, as a type table index
    const char* m_namep;  // Name of the enum
    uint32_t m_count;  // Items
    const char* const* m_namesp;  // Item names
    const char* const* m_valuesp;  // Item values, as binary strings
    int32_t m_dtypenum;  // Enum number within the model, from 1
};

// Member of a struct or union. Packed member offsets are derived from the member widths.
struct VlRtmdMember final {
    const char* m_namep;  // Name of the member
    uint32_t m_typeIdx;  // Type of the member, as a type table index
    uint32_t m_offset;  // Byte offset of an unpacked member, unused if packed
};

// Element counts derive from the declared range, see vlRtmdElementsOf
struct VlRtmdPackedArray final {
    uint16_t m_flags;  // VL_RTMD_*
    uint32_t m_elemIdx;  // Element type, as a type table index
    int32_t m_left;  // Declared range
    int32_t m_right;
};

struct VlRtmdUnpackedArray final {
    uint32_t m_elemBytes;  // Bytes per element
    uint32_t m_elemIdx;  // Element type, as a type table index
    int32_t m_left;  // Declared range
    int32_t m_right;
};

struct VlRtmdPackedStruct final {
    uint16_t m_flags;  // VL_RTMD_*
    uint32_t m_count;  // Number of members
    const VlRtmdMember* m_membersp;  // Members, most significant first
};

struct VlRtmdUnpackedStruct final {
    uint32_t m_count;  // Number of members
    const VlRtmdMember* m_membersp;  // Members
};

// Row of the type table, pointing to the descriptor of its kind
struct VlRtmdTypeRow final {
    VlRtmdTypeOp m_op;
    union {
        const VlRtmdAtom* m_atomp;
        const VlRtmdEnum* m_enump;
        const VlRtmdPackedArray* m_packedArrayp;
        const VlRtmdUnpackedArray* m_unpackedArrayp;
        const VlRtmdPackedStruct* m_packedStructp;
        const VlRtmdUnpackedStruct* m_unpackedStructp;
    };
};

struct VlRtmdScopeRow final {
    VlRtmdScopeOp m_op;
    VlRtmdScopeKind m_scopeKind;  // PUSH and INSTANCE
    const char* m_namep;  // Name of the level, signal or instance
    const char* m_libPathp;  // PARTITION: path the library registers under
    // SIGNAL/SIGNAL_CONST: signal table index. INSTANCE: scope table index.
    uint32_t m_typeIdx;
    // SIGNAL: offset from the symbol table. SIGNAL_CONST: constant pool word index.
    uint32_t m_dataOfs;
    uint32_t m_valueId;  // Signals sharing a value share a trace code; 0 if not shared
    uint32_t m_actSetId;  // Activity set table index
};

// Activity set, as a range of activity flag numbers
struct VlRtmdActSetRow final {
    const uint32_t* m_firstFlagp;  // First flag number of the set
    const uint32_t* m_lastFlagp;  // One past the last
};

// All descriptor tables of one model, handed to the runtime at registration
struct VlRtmdTables final {
    const void* m_symsp = nullptr;  // Base of SIGNAL row offsets
    const char* m_namep = "";  // Name of the model instance
    bool m_isLibInstance = false;  // A --lib-create library, walked from its PARTITION row
    const VlRtmdTypeRow* m_typesp = nullptr;  // Type table
    uint32_t m_nTypes = 0;
    const VlRtmdSignalType* m_signalsp = nullptr;  // Signal table
    uint32_t m_nSignals = 0;
    const VlRtmdScopeRow* const* m_tablesp = nullptr;  // Scope table of each instance
    const uint32_t* m_tableRowsp = nullptr;  // Rows in each scope table
    uint32_t m_nTables = 0;
    uint32_t m_rootTable = 0;  // Scope table of the model itself
    const uint32_t* m_constsp = nullptr;  // Constant pool
    // Activity. A signal need only be checked if a flag in its activity set is set. Set 0 holds
    // the flag set on every eval. An empty set means the signal never changes. All flags are
    // cleared after a dump.
    const uint8_t* m_activityFlagsp = nullptr;  // Activity flags
    uint32_t m_nActivityFlags = 0;
    const VlRtmdActSetRow* m_actSetsp = nullptr;  // Activity set table
};

// Element index meaning 'not an element of an unpacked array'
static constexpr int VL_RTMD_NO_INDEX = INT_MIN;

// How to read a value
enum class VlRtmdRead : uint8_t { BIT, CDATA, SDATA, IDATA, QDATA, WDATA, DOUBLE, EVENT };

// Return how to read a value, for both live values and constants
inline VlRtmdRead vlRtmdReadOf(VlRtmdSigType sigType, uint32_t bits) {
    if (sigType == VlRtmdSigType::EVENT) return VlRtmdRead::EVENT;
    if (sigType == VlRtmdSigType::DOUBLE) return VlRtmdRead::DOUBLE;
    if (bits == 1) return VlRtmdRead::BIT;
    if (bits <= 8) return VlRtmdRead::CDATA;
    if (bits <= 16) return VlRtmdRead::SDATA;
    if (bits <= 32) return VlRtmdRead::IDATA;
    if (bits <= 64) return VlRtmdRead::QDATA;
    return VlRtmdRead::WDATA;
}

// Number of elements in the given declared range
inline uint32_t vlRtmdElementsOf(int32_t left, int32_t right) {
    return static_cast<uint32_t>(left > right ? left - right : right - left) + 1;
}

// Width of a packed type
inline uint32_t vlRtmdBitsOf(const VlRtmdTables& tables, uint32_t typeIdx) {
    const VlRtmdTypeRow& type = tables.m_typesp[typeIdx];
    switch (type.m_op) {
    case VlRtmdTypeOp::ATOM: return type.m_atomp->m_bits;
    case VlRtmdTypeOp::ENUM: return vlRtmdBitsOf(tables, type.m_enump->m_baseIdx);
    case VlRtmdTypeOp::PACKED_ARRAY: {
        const VlRtmdPackedArray& array = *type.m_packedArrayp;
        return vlRtmdElementsOf(array.m_left, array.m_right)
               * vlRtmdBitsOf(tables, array.m_elemIdx);
    }
    case VlRtmdTypeOp::PACKED_STRUCT: {
        uint32_t bits = 0;
        const VlRtmdPackedStruct& strct = *type.m_packedStructp;
        for (uint32_t i = 0; i < strct.m_count; ++i) {
            bits += vlRtmdBitsOf(tables, strct.m_membersp[i].m_typeIdx);
        }
        return bits;
    }
    case VlRtmdTypeOp::PACKED_UNION: {
        uint32_t bits = 0;
        const VlRtmdPackedStruct& strct = *type.m_packedStructp;
        for (uint32_t i = 0; i < strct.m_count; ++i) {
            const uint32_t member = vlRtmdBitsOf(tables, strct.m_membersp[i].m_typeIdx);
            if (member > bits) bits = member;
        }
        return bits;
    }
    default: return 0;  // Unpacked
    }
}

// Base data type of a packed type. Packed structs and unions are shown as logic.
inline VlRtmdSigType vlRtmdSigTypeOf(const VlRtmdTables& tables, uint32_t typeIdx) {
    const VlRtmdTypeRow& type = tables.m_typesp[typeIdx];
    switch (type.m_op) {
    case VlRtmdTypeOp::ATOM: return type.m_atomp->m_sigType;
    case VlRtmdTypeOp::ENUM: return vlRtmdSigTypeOf(tables, type.m_enump->m_baseIdx);
    case VlRtmdTypeOp::PACKED_ARRAY:
        return vlRtmdSigTypeOf(tables, type.m_packedArrayp->m_elemIdx);
    default: return VlRtmdSigType::LOGIC;
    }
}

// Whether a type has no range, e.g. 'logic x' as opposed to 'logic [0:0] x'
inline bool vlRtmdIsScalar(const VlRtmdTables& tables, uint32_t typeIdx) {
    const VlRtmdTypeRow& type = tables.m_typesp[typeIdx];
    if (type.m_op == VlRtmdTypeOp::ENUM) {
        return vlRtmdIsScalar(tables, type.m_enump->m_baseIdx);
    }
    return type.m_op == VlRtmdTypeOp::ATOM;
}

// Bit range of a packed type. Only a packed array of single bits has a declared range,
// everything else is [width-1:0].
struct VlRtmdRange final {
    int32_t m_left;
    int32_t m_right;
};
inline VlRtmdRange vlRtmdRangeOf(const VlRtmdTables& tables, uint32_t typeIdx) {
    const VlRtmdTypeRow& type = tables.m_typesp[typeIdx];
    if (type.m_op == VlRtmdTypeOp::ENUM) { return vlRtmdRangeOf(tables, type.m_enump->m_baseIdx); }
    if (type.m_op == VlRtmdTypeOp::PACKED_ARRAY) {
        const VlRtmdPackedArray& array = *type.m_packedArrayp;
        if (vlRtmdBitsOf(tables, array.m_elemIdx) == 1) return {array.m_left, array.m_right};
    }
    return {static_cast<int32_t>(vlRtmdBitsOf(tables, typeIdx)) - 1, 0};
}

#endif  // Guard
