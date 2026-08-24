// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing an RTMD type
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
// All 'AstNode' sub-types describing a type in the RTMD.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODERTMDTYPE_H_
#define VERILATOR_V3ASTNODERTMDTYPE_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// === Abstract base node types (AstNode*) =====================================

class AstNodeRtmdDataType VL_NOT_FINAL : public AstNode {
    // Describes a source level data type as represented in the RTMD
protected:
    AstNodeRtmdDataType(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeRtmdDataType;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
};

// === Concrete node types =====================================================

// === AstNode ===
class AstRtmdEnumItem final : public AstNode {
    // One item of an AstRtmdDTEnum
    const std::string m_name;  // Name of the item
    const std::string m_value;  // Value of the item FIXME: V3Number

public:
    AstRtmdEnumItem(FileLine* fl, const std::string& name, const std::string& value)
        : ASTGEN_SUPER_RtmdEnumItem(fl)
        , m_name{name}
        , m_value{value} {}
    ASTGEN_MEMBERS_AstRtmdEnumItem;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdEnumItem* const asamep = VN_DBG_AS(samep, RtmdEnumItem);
        return name() == asamep->name() && value() == asamep->value();
    }
    std::string name() const override VL_MT_STABLE { return m_name; }
    std::string value() const { return m_value; }
};
class AstRtmdMember final : public AstNode {
    // A member of an RTMD struct or union data type
    // @astgen ptr := m_rtmddtp : AstNodeRtmdDataType  // Rtmd of the member's data type
    const std::string m_name;  // Name of the member

public:
    AstRtmdMember(FileLine* fl, const std::string& name, AstNodeRtmdDataType* rtmddtp)
        : ASTGEN_SUPER_RtmdMember(fl)
        , m_name{name}
        , m_rtmddtp{rtmddtp} {}
    ASTGEN_MEMBERS_AstRtmdMember;
    const char* broken() const override {
        BROKEN_RTN(!m_rtmddtp);
        return nullptr;
    }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdMember* const asamep = VN_DBG_AS(samep, RtmdMember);
        return name() == asamep->name() && rtmddtp() == asamep->rtmddtp();
    }
    std::string name() const override VL_MT_STABLE { return m_name; }
    AstNodeRtmdDataType* rtmddtp() const { return m_rtmddtp; }
    void rtmddtp(AstNodeRtmdDataType* rtmddtp) { m_rtmddtp = rtmddtp; }
};
class AstRtmdSignalType final : public AstNode {
    // How a signal is declared: its data type, kind and direction. Not an AstNodeRtmdDataType,
    // as it does not compose.
    // @astgen ptr := m_rtmddtp : AstNodeRtmdDataType  // Type of the value
    const VRtmdVarKind m_varKind;  // Kind of variable or net
    const VDirection m_direction;  // Declared direction, or NONE if it is not a port
public:
    AstRtmdSignalType(FileLine* fl, AstNodeRtmdDataType* rtmddtp, VRtmdVarKind varKind,
                      VDirection direction)
        : ASTGEN_SUPER_RtmdSignalType(fl)
        , m_rtmddtp{rtmddtp}
        , m_varKind{varKind}
        , m_direction{direction} {}
    ASTGEN_MEMBERS_AstRtmdSignalType;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdSignalType* const asamep = VN_DBG_AS(samep, RtmdSignalType);
        return rtmddtp() == asamep->rtmddtp()  //
               && varKind() == asamep->varKind()  //
               && direction() == asamep->direction();
    }
    AstNodeRtmdDataType* rtmddtp() const { return m_rtmddtp; }
    VRtmdVarKind varKind() const { return m_varKind; }
    VDirection direction() const { return m_direction; }
};

// === AstNodeRtmdDataType ===
class AstRtmdDTAtom final : public AstNodeRtmdDataType {
    // A builtin type ('logic', 'bit', 'int', etc.)
    const VBasicDTypeKwd m_keyword;  // Which builtin
    const bool m_signed;  // Is signed/unsigned
public:
    AstRtmdDTAtom(FileLine* fl, VBasicDTypeKwd keyword, bool isSigned)
        : ASTGEN_SUPER_RtmdDTAtom(fl)
        , m_keyword{keyword}
        , m_signed{isSigned} {}
    ASTGEN_MEMBERS_AstRtmdDTAtom;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTAtom* const asamep = VN_DBG_AS(samep, RtmdDTAtom);
        return keyword() == asamep->keyword() && isSigned() == asamep->isSigned();
    }
    VBasicDTypeKwd keyword() const { return m_keyword; }
    uint32_t bits() const { return m_keyword.width(); }
    bool isSigned() const { return m_signed; }
};
class AstRtmdDTEnum final : public AstNodeRtmdDataType {
    // An enumeration type
    // @astgen op1 := itemsp : List[AstRtmdEnumItem]  // The enumerated constants
    // @astgen ptr := m_rtmddtp : AstNodeRtmdDataType  // Underlying type of the representation
    const std::string m_name;  // Name of the enum
public:
    AstRtmdDTEnum(FileLine* fl, const std::string& name, AstNodeRtmdDataType* rtmddtp)
        : ASTGEN_SUPER_RtmdDTEnum(fl)
        , m_rtmddtp{rtmddtp}
        , m_name{name} {}
    ASTGEN_MEMBERS_AstRtmdDTEnum;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTEnum* const asamep = VN_DBG_AS(samep, RtmdDTEnum);
        return name() == asamep->name() && rtmddtp() == asamep->rtmddtp();
    }
    std::string name() const override VL_MT_STABLE { return m_name; }
    AstNodeRtmdDataType* rtmddtp() const { return m_rtmddtp; }
};
class AstRtmdDTPackedArray final : public AstNodeRtmdDataType {
    // A packed array type, including ranged AstBasicDTypes
    // @astgen ptr := m_elemRtmddtp : AstNodeRtmdDataType  // Element type
    const int32_t m_left;  // Declared left index
    const int32_t m_right;  // Declared right index
    const bool m_signed;  // The value as a whole is signed
public:
    AstRtmdDTPackedArray(FileLine* fl, AstNodeRtmdDataType* elemRtmddtp, int32_t left,
                         int32_t right, bool isSigned)
        : ASTGEN_SUPER_RtmdDTPackedArray(fl)
        , m_elemRtmddtp{elemRtmddtp}
        , m_left{left}
        , m_right{right}
        , m_signed{isSigned} {}
    ASTGEN_MEMBERS_AstRtmdDTPackedArray;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTPackedArray* const asamep = VN_DBG_AS(samep, RtmdDTPackedArray);
        return elemRtmddtp() == asamep->elemRtmddtp()  //
               && left() == asamep->left()  //
               && right() == asamep->right()  //
               && isSigned() == asamep->isSigned();
    }
    AstNodeRtmdDataType* elemRtmddtp() const { return m_elemRtmddtp; }
    int32_t left() const { return m_left; }
    int32_t right() const { return m_right; }
    bool isSigned() const { return m_signed; }
};
class AstRtmdDTPackedStruct final : public AstNodeRtmdDataType {
    // A packed structure type
    // @astgen op1 := membersp : List[AstRtmdMember]  // The members
    const bool m_signed;  // The value as a whole is signed
public:
    AstRtmdDTPackedStruct(FileLine* fl, bool isSigned, AstRtmdMember* membersp)
        : ASTGEN_SUPER_RtmdDTPackedStruct(fl)
        , m_signed{isSigned} {
        this->addMembersp(membersp);
    }
    ASTGEN_MEMBERS_AstRtmdDTPackedStruct;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTPackedStruct* const asamep = VN_DBG_AS(samep, RtmdDTPackedStruct);
        return isSigned() == asamep->isSigned();
    }
    bool isSigned() const { return m_signed; }
};
class AstRtmdDTPackedUnion final : public AstNodeRtmdDataType {
    // A packed union type
    // @astgen op1 := membersp : List[AstRtmdMember]  // The members
    const bool m_signed;  // The value as a whole is signed
public:
    AstRtmdDTPackedUnion(FileLine* fl, bool isSigned, AstRtmdMember* membersp)
        : ASTGEN_SUPER_RtmdDTPackedUnion(fl)
        , m_signed{isSigned} {
        this->addMembersp(membersp);
    }
    ASTGEN_MEMBERS_AstRtmdDTPackedUnion;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTPackedUnion* const asamep = VN_DBG_AS(samep, RtmdDTPackedUnion);
        return isSigned() == asamep->isSigned();
    }
    bool isSigned() const { return m_signed; }
};
class AstRtmdDTUnpackedArray final : public AstNodeRtmdDataType {
    // An unpacked array type
    // @astgen ptr := m_elemRtmddtp : AstNodeRtmdDataType  // Element type
    const int32_t m_left;  // Declared left index
    const int32_t m_right;  // Declared right index

public:
    AstRtmdDTUnpackedArray(FileLine* fl, AstUnpackArrayDType* dtypep,
                           AstNodeRtmdDataType* elemRtmddtp, int32_t left, int32_t right)
        : ASTGEN_SUPER_RtmdDTUnpackedArray(fl)
        , m_elemRtmddtp{elemRtmddtp}
        , m_left{left}
        , m_right{right} {
        this->dtypep(dtypep);
    }
    ASTGEN_MEMBERS_AstRtmdDTUnpackedArray;
    bool hasDType() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTUnpackedArray* const asamep = VN_DBG_AS(samep, RtmdDTUnpackedArray);
        return elemRtmddtp() == asamep->elemRtmddtp()  //
               && left() == asamep->left()  //
               && right() == asamep->right();
    }
    AstNodeRtmdDataType* elemRtmddtp() const { return m_elemRtmddtp; }
    int32_t left() const { return m_left; }
    int32_t right() const { return m_right; }
};
class AstRtmdDTUnpackedStruct final : public AstNodeRtmdDataType {
    // An unpacked structure type
    // @astgen op1 := membersp : List[AstRtmdMember]  // The members
public:
    AstRtmdDTUnpackedStruct(FileLine* fl, AstStructDType* dtypep, AstRtmdMember* membersp)
        : ASTGEN_SUPER_RtmdDTUnpackedStruct(fl) {
        this->addMembersp(membersp);
        this->dtypep(dtypep);
    }
    ASTGEN_MEMBERS_AstRtmdDTUnpackedStruct;
    bool hasDType() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};

#endif  // Guard
