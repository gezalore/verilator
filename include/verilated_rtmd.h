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
// Activity set descriptors (corresponds to AstNetlist::actSets() in the compiler)

// Row of the activity set table. The first rows are the range of each set, by set index. The
// rest are the flag numbers of all sets, each set's following the previous.
class VlRtmdActSetRow final {
public:
    // TYPES

    // Range of the rows holding the flag numbers of an activity set
    struct Range final {
        uint32_t m_begin;  // First row
        uint32_t m_end;  // One past the last row
    };

    struct Flag final {
        uint32_t m_flag;  // Activity flag index
    };

private:
    // STATE
    union {
        Range m_range;  // Range of a set, in the first rows
        Flag m_flag;  // Activity flag number, in the rest
    };

public:
    // CONSTRUCTORS
    /* implicit */ constexpr VlRtmdActSetRow(const Range& range)
        : m_range(range) {}
    /* implicit */ constexpr VlRtmdActSetRow(const Flag& flag)
        : m_flag(flag) {}

    // METHOD
    // The contents of the row, which depends on the row, as above
    const Range& range() const { return m_range; }
    const Flag& flag() const { return m_flag; }
};

//=============================================================================
// Data types descriptors (corresponds to AstNodeRtmdDataType in the compiler)

// One entry in the data type descriptor table: a descriptor, tagged with its kind. The members of
// a struct or union, and the items of an enum, are the rows following it. Rows are constructed
// from the descriptor, which sets the tag, as C++14 has no designated initializers for unions.
class VlRtmdDataTypeRow final {
public:
    // TYPES

    // A builtin primitive type
    struct Atom final {
        // Base data type of a value
        enum class Kind : uint8_t {
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

        Kind m_kind;  // Base data type
        bool m_signed;  // Signed type
        uint32_t m_bits;  // Width
    };

    // An enum over a base type. Its items are the rows following it. Its row index identifies it
    // in the trace (the 'dtypenum'), which is never 0, as its base type is an earlier row.
    struct Enum final {
        const char* m_namep;  // Name of the enum
        uint32_t m_baseIdx;  // Base type, as a type table index
        uint32_t m_count;  // Number of items
    };

    // An item of an enum
    struct EnumItem final {
        const char* m_namep;  // Name of the item
        const char* m_valuep;  // Value of the item, as a binary string
    };

    // Member of a struct or union
    struct Member final {
        const char* m_namep;  // Name of the member
        uint32_t m_typeIdx;  // Type of the member, as a type table index
        uint32_t m_offset;  // Unpacked: byte offset of the member. Packed: bit offset of its LSB.
    };

    // Element counts derive from the declared range, see vlRtmdElementsOf
    struct PackedArray final {
        int32_t m_left;  // Declared range
        int32_t m_right;
        uint32_t m_elemIdx;  // Element type, as a type table index
        bool m_signed;  // Signed type
    };

    // Its members are the rows following it, most significant first
    struct PackedStruct final {
        uint32_t m_count;  // Number of members
        bool m_signed;  // Signed type
    };

    // Members overlay each other, all starting at bit 0. As wide as the widest member. Its members
    // are the rows following it.
    struct PackedUnion final {
        uint32_t m_count;  // Number of members
        bool m_signed;  // Signed type
    };

    struct UnpackedArray final {
        int32_t m_left;  // Declared range
        int32_t m_right;
        uint32_t m_elemIdx;  // Element type, as a type table index
        uint32_t m_elemBytes;  // Bytes per element
    };

    // Its members are the rows following it
    struct UnpackedStruct final {
        uint32_t m_count;  // Number of members
    };

    // The last row of the table
    struct End final {};

private:
    // STATE

    // Kind of the descriptor
    enum class Tag : uint8_t {
        // Proper type
        ATOM,
        ENUM,
        PACKED_ARRAY,
        PACKED_STRUCT,
        PACKED_UNION,
        UNPACKED_ARRAY,
        UNPACKED_STRUCT,
        // Not types, but part of preceding types
        ENUM_ITEM,  // Enum item
        MEMBER,  // Struct or union member
        // Not a type, marks the end of the table
        END
    };

    Tag m_tag;  // Kind of the descriptor
    union {
        Atom m_atom;
        Enum m_enum;
        EnumItem m_enumItem;
        Member m_member;
        PackedArray m_packedArray;
        PackedStruct m_packedStruct;
        PackedUnion m_packedUnion;
        UnpackedArray m_unpackedArray;
        UnpackedStruct m_unpackedStruct;
        End m_end;
    };

public:
    // CONSTRUCTORS
    /* implicit */ constexpr VlRtmdDataTypeRow(const Atom& d)
        : m_tag{Tag::ATOM}
        , m_atom(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const Enum& d)
        : m_tag{Tag::ENUM}
        , m_enum(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const EnumItem& d)
        : m_tag{Tag::ENUM_ITEM}
        , m_enumItem(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const Member& d)
        : m_tag{Tag::MEMBER}
        , m_member(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const PackedArray& d)
        : m_tag{Tag::PACKED_ARRAY}
        , m_packedArray(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const PackedStruct& d)
        : m_tag{Tag::PACKED_STRUCT}
        , m_packedStruct(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const PackedUnion& d)
        : m_tag{Tag::PACKED_UNION}
        , m_packedUnion(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const UnpackedArray& d)
        : m_tag{Tag::UNPACKED_ARRAY}
        , m_unpackedArray(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const UnpackedStruct& d)
        : m_tag{Tag::UNPACKED_STRUCT}
        , m_unpackedStruct(d) {}
    /* implicit */ constexpr VlRtmdDataTypeRow(const End& d)
        : m_tag{Tag::END}
        , m_end(d) {}

    // METHODS
    const Atom* atomp() const {
        if (m_tag != Tag::ATOM) return nullptr;
        return &m_atom;
    }
    const Enum* enump() const {
        if (m_tag != Tag::ENUM) return nullptr;
        return &m_enum;
    }
    const EnumItem* enumItemp() const {
        if (m_tag != Tag::ENUM_ITEM) return nullptr;
        return &m_enumItem;
    }
    const Member* memberp() const {
        if (m_tag != Tag::MEMBER) return nullptr;
        return &m_member;
    }
    const PackedArray* packedArrayp() const {
        if (m_tag != Tag::PACKED_ARRAY) return nullptr;
        return &m_packedArray;
    }
    const PackedStruct* packedStructp() const {
        if (m_tag != Tag::PACKED_STRUCT) return nullptr;
        return &m_packedStruct;
    }
    const PackedUnion* packedUnionp() const {
        if (m_tag != Tag::PACKED_UNION) return nullptr;
        return &m_packedUnion;
    }
    const UnpackedArray* unpackedArrayp() const {
        if (m_tag != Tag::UNPACKED_ARRAY) return nullptr;
        return &m_unpackedArray;
    }
    const UnpackedStruct* unpackedStructp() const {
        if (m_tag != Tag::UNPACKED_STRUCT) return nullptr;
        return &m_unpackedStruct;
    }

    bool isEnd() const { return m_tag == Tag::END; }

    // The given row following this one: a member of a struct or union, or an item of an enum
    const VlRtmdDataTypeRow& item(uint32_t i) const { return this[1 + i]; }
};

//=============================================================================
// Signal types descriptors (corresponds to AstRtmdSignalType in the compiler)

// One entry in the signal type table: a descriptor. There is only one kind, so it needs no tag.
class VlRtmdSignalTypeRow final {
public:
    // How a signal is declared: kind, direction and the type of its value
    struct Signal final {
        // Kind of variable or net a signal is declared as
        enum class Kind : uint8_t {
            // Note: Entries must match VRtmdSignalKind (by name, not necessarily by value)
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

        // Declared direction of a port, or NONE for anything that is not one
        enum class Direction : uint8_t {
            // Note: Entries must match VDirection (by name, not necessarily by value)
            NONE,
            INPUT,
            OUTPUT,
            INOUT,
            REF,
            CONSTREF,
        };

        Kind m_kind;  // Signal kind, e.g. VAR, WIRE, PARAM
        Direction m_direction;  // NONE if it is not a port
        uint32_t m_typeIdx;  // Type of the value, as a type table index
    };

private:
    union {
        Signal m_signal;
    };

public:
    /* implicit */ constexpr VlRtmdSignalTypeRow(const Signal& d)
        : m_signal(d) {}

    // The descriptor of the row
    const Signal* signalp() const { return &m_signal; }
};

//=============================================================================
// Global descriptors (corresponds to the constant pool entries described in the compiler)

// One entry in the global table: a descriptor. There is only one kind, so it needs no tag.
class VlRtmdGlobalSymRow final {
public:
    // A global constant
    struct Const final {
        const void* m_datap;  // Address of the constant
    };

private:
    union {
        Const m_const;
    };

public:
    /* implicit */ constexpr VlRtmdGlobalSymRow(const Const& d)
        : m_const(d) {}

    // The descriptor of the row
    const Const* constp() const { return &m_const; }
};

//=============================================================================
// Hierarchy descriptors (corresponds to AstNodeRtmdItem in the compiler)

// One entry in the hierarchy table: a descriptor, tagged with its kind. Rows are constructed from
// the descriptor, which sets the tag, as C++14 has no designated initializers for unions.
class VlRtmdHierRow final {
public:
    // Open a hierarchy level
    struct Push final {
        // Kind of design scope a level is
        enum class Kind : uint8_t {
            // Note: Entries must match VRtmdLevelKind (by name, not necessarily by value)
            ROOT,
            MODULE,
            INTERFACE,
            PACKAGE,
            GENERATE,
            BEGIN,
            FORK,
            FUNCTION,
            TASK,
        };

        const char* m_namep;  // Name of the level
        Kind m_kind;  // Kind of the level
    };

    // Close the level the matching Push opened
    struct Pop final {};

    // A value, located by offset from the symbol table
    struct Signal final {
        const char* m_namep;  // Name of the signal
        uint32_t m_typeIdx;  // Signal type, as a signal type table index
        uint32_t m_actSetId;  // Activity set table index
        uint32_t m_offset;  // Offset of the value from the symbol table
    };

    // A value in a global variable, located via the global table
    struct Global final {
        const char* m_namep;  // Name of the signal
        uint32_t m_typeIdx;  // Signal type, as a signal type table index
        uint32_t m_actSetId;  // Activity set table index
        uint32_t m_globalIdx;  // Index of the address of the value in the global table
    };

    // An instance: the level that follows is an instance of the given module
    struct Instance final {
        const char* m_modNamep;  // Name of the module of the level that follows
    };

    // A --lib-create library, which registers its own tables
    struct Partition final {
        const char* m_namep;  // Name of the instance
    };

    // The last row of the table
    struct End final {};

private:
    // Kind of the descriptor
    enum class Tag : uint8_t {
        PUSH,
        POP,
        SIGNAL,
        GLOBAL,
        INSTANCE,
        PARTITION,
        END,
    };

    Tag m_tag;  // Kind of the descriptor
    union {
        Push m_push;
        Pop m_pop;
        Signal m_signal;
        Global m_global;
        Instance m_instance;
        Partition m_partition;
        End m_end;
    };

public:
    /* implicit */ constexpr VlRtmdHierRow(const Push& d)
        : m_tag{Tag::PUSH}
        , m_push(d) {}
    /* implicit */ constexpr VlRtmdHierRow(const Pop& d)
        : m_tag{Tag::POP}
        , m_pop(d) {}
    /* implicit */ constexpr VlRtmdHierRow(const Signal& d)
        : m_tag{Tag::SIGNAL}
        , m_signal(d) {}
    /* implicit */ constexpr VlRtmdHierRow(const Global& d)
        : m_tag{Tag::GLOBAL}
        , m_global(d) {}
    /* implicit */ constexpr VlRtmdHierRow(const Instance& d)
        : m_tag{Tag::INSTANCE}
        , m_instance(d) {}
    /* implicit */ constexpr VlRtmdHierRow(const Partition& d)
        : m_tag{Tag::PARTITION}
        , m_partition(d) {}
    /* implicit */ constexpr VlRtmdHierRow(const End& d)
        : m_tag{Tag::END}
        , m_end(d) {}

    // The descriptor of the row, or nullptr if the row holds a different kind of descriptor
    const Push* pushp() const {
        if (m_tag != Tag::PUSH) return nullptr;
        return &m_push;
    }
    const Pop* popp() const {
        if (m_tag != Tag::POP) return nullptr;
        return &m_pop;
    }
    const Signal* signalp() const {
        if (m_tag != Tag::SIGNAL) return nullptr;
        return &m_signal;
    }
    const Global* globalp() const {
        if (m_tag != Tag::GLOBAL) return nullptr;
        return &m_global;
    }
    const Instance* instancep() const {
        if (m_tag != Tag::INSTANCE) return nullptr;
        return &m_instance;
    }
    const Partition* partitionp() const {
        if (m_tag != Tag::PARTITION) return nullptr;
        return &m_partition;
    }

    // Whether this is the last row of the table, which is not a descriptor
    bool isEnd() const { return m_tag == Tag::END; }
};

//=============================================================================
// Registration structure

// All descriptor tables of one model, handed to the runtime at registration
struct VlRtmd final {
    const void* m_symsp = nullptr;  // Base of SIGNAL row offsets
    const char* m_namep = "";  // Name of the model instance
    // Tables
    const VlRtmdActSetRow* m_actSetsTabp = nullptr;  // Activity set table
    const VlRtmdDataTypeRow* m_dataTypesTabp = nullptr;  // Data type table, ending with End
    const VlRtmdGlobalSymRow* m_globalSymsTabp = nullptr;  // Globals of GLOBAL rows
    const VlRtmdHierRow* m_hierTabp = nullptr;  // Hierarchy table, ending with End
    const VlRtmdSignalTypeRow* m_signalTypesTabp = nullptr;  // Signal type table
    // Activity. A signal need only be checked if a flag in its activity set is set. An empty set
    // means the signal never changes. All flags are cleared after a dump.
    const uint8_t* m_activityFlagsp = nullptr;  // Activity flags
    uint32_t m_nActivityFlags = 0;
};

//=============================================================================
// Helpers

// Element index meaning 'not an element of an unpacked array'
static constexpr int VL_RTMD_NO_INDEX = INT_MIN;

// How to read a value
enum class VlRtmdRead : uint8_t { BIT, CDATA, SDATA, IDATA, QDATA, WDATA, DOUBLE, EVENT };

// Return how to read a value, for both live values and constants
inline VlRtmdRead vlRtmdReadOf(VlRtmdDataTypeRow::Atom::Kind kind, uint32_t bits) {
    if (kind == VlRtmdDataTypeRow::Atom::Kind::EVENT) return VlRtmdRead::EVENT;
    if (kind == VlRtmdDataTypeRow::Atom::Kind::DOUBLE) return VlRtmdRead::DOUBLE;
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
inline uint32_t vlRtmdBitsOf(const VlRtmd& tables, uint32_t typeIdx) {
    const VlRtmdDataTypeRow& type = tables.m_dataTypesTabp[typeIdx];
    if (const VlRtmdDataTypeRow::Atom* const atomp = type.atomp()) return atomp->m_bits;
    if (const VlRtmdDataTypeRow::Enum* const enump = type.enump())
        return vlRtmdBitsOf(tables, enump->m_baseIdx);
    if (const VlRtmdDataTypeRow::PackedArray* const arrayp = type.packedArrayp()) {
        const VlRtmdDataTypeRow::PackedArray& array = *arrayp;
        return vlRtmdElementsOf(array.m_left, array.m_right)
               * vlRtmdBitsOf(tables, array.m_elemIdx);
    }
    if (const VlRtmdDataTypeRow::PackedStruct* const strctp = type.packedStructp()) {
        uint32_t bits = 0;
        const VlRtmdDataTypeRow::PackedStruct& strct = *strctp;
        for (uint32_t i = 0; i < strct.m_count; ++i) {
            bits += vlRtmdBitsOf(tables, type.item(i).memberp()->m_typeIdx);
        }
        return bits;
    }
    if (const VlRtmdDataTypeRow::PackedUnion* const unionp = type.packedUnionp()) {
        uint32_t bits = 0;
        const VlRtmdDataTypeRow::PackedUnion& unionr = *unionp;
        for (uint32_t i = 0; i < unionr.m_count; ++i) {
            const uint32_t member = vlRtmdBitsOf(tables, type.item(i).memberp()->m_typeIdx);
            if (member > bits) bits = member;
        }
        return bits;
    }
    return 0;  // Unpacked
}

// Base data type of a packed type. Packed structs and unions are shown as logic.
inline VlRtmdDataTypeRow::Atom::Kind vlRtmdAtomKindOf(const VlRtmd& tables, uint32_t typeIdx) {
    const VlRtmdDataTypeRow& type = tables.m_dataTypesTabp[typeIdx];
    if (const VlRtmdDataTypeRow::Atom* const atomp = type.atomp()) return atomp->m_kind;
    if (const VlRtmdDataTypeRow::Enum* const enump = type.enump()) {
        return vlRtmdAtomKindOf(tables, enump->m_baseIdx);
    }
    if (const VlRtmdDataTypeRow::PackedArray* const arrayp = type.packedArrayp()) {
        return vlRtmdAtomKindOf(tables, arrayp->m_elemIdx);
    }
    return VlRtmdDataTypeRow::Atom::Kind::LOGIC;
}

// Whether a type has no range, e.g. 'logic x' as opposed to 'logic [0:0] x'
inline bool vlRtmdIsScalar(const VlRtmd& tables, uint32_t typeIdx) {
    const VlRtmdDataTypeRow& type = tables.m_dataTypesTabp[typeIdx];
    if (const VlRtmdDataTypeRow::Enum* const enump = type.enump()) {
        return vlRtmdIsScalar(tables, enump->m_baseIdx);
    }
    return type.atomp();
}

// Bit range of a packed type. Only a packed array of single bits has a declared range,
// everything else is [width-1:0].
struct VlRtmdRange final {
    int32_t m_left;
    int32_t m_right;
};
inline VlRtmdRange vlRtmdRangeOf(const VlRtmd& tables, uint32_t typeIdx) {
    const VlRtmdDataTypeRow& type = tables.m_dataTypesTabp[typeIdx];
    if (const VlRtmdDataTypeRow::Enum* const enump = type.enump()) {
        return vlRtmdRangeOf(tables, enump->m_baseIdx);
    }
    if (const VlRtmdDataTypeRow::PackedArray* const arrayp = type.packedArrayp()) {
        const VlRtmdDataTypeRow::PackedArray& array = *arrayp;
        if (vlRtmdBitsOf(tables, array.m_elemIdx) == 1) return {array.m_left, array.m_right};
    }
    return {static_cast<int32_t>(vlRtmdBitsOf(tables, typeIdx)) - 1, 0};
}

#endif  // Guard
