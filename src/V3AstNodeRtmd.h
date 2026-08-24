// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing the RTMD
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
// This file contains the 'AstNode' sub-types representing the Run Time Model Descriptors (RTMD),
// which describe the model state as data for use at run time (e.g. by tracing). Built by V3Rtmd,
// emitted by V3EmitCRtmd*.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODERTMD_H_
#define VERILATOR_V3ASTNODERTMD_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// === Abstract base node types (AstNode*) =====================================

class AstNodeRtmdItem VL_NOT_FINAL : public AstNode {
    // An entry of an AstRtmdScope
    // Parents: RTMDSCOPE
protected:
    AstNodeRtmdItem(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeRtmdItem;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
};

// === Concrete node types =====================================================

// === AstNode ===
class AstRtmdActSets final : public AstNode {
    // The activity sets of the design, built by V3Trace
    // Parents: NETLIST
    // @astgen op1 := entriesp : List[AstRtmdActSet]  // The sets
    const uint32_t m_nFlags;  // Number of activity flags
public:
    AstRtmdActSets(FileLine* fl, uint32_t nFlags)
        : ASTGEN_SUPER_RtmdActSets(fl)
        , m_nFlags{nFlags} {}
    ASTGEN_MEMBERS_AstRtmdActSets;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    uint32_t nFlags() const { return m_nFlags; }
};
class AstRtmdScope final : public AstNode {
    // Describes a design scope
    // Parents: MODULE, TOPSCOPE
    // @astgen op1 := itemsp : List[AstNodeRtmdItem]
    const VRtmdScopeKind m_kind;  // Kind of scope
    const std::string m_name;  // Name of the scope, as it appears in the trace
public:
    AstRtmdScope(FileLine* fl, VRtmdScopeKind kind, const std::string& name)
        : ASTGEN_SUPER_RtmdScope(fl)
        , m_kind{kind}
        , m_name{name} {}
    ASTGEN_MEMBERS_AstRtmdScope;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    VRtmdScopeKind kind() const { return m_kind; }
};
// === AstNodeRtmdItem ===
class AstRtmdActSet final : public AstNodeRtmdItem {
    // One activity set: the activity flags that might be set when a signal in the set changes.
    // An empty set means the signal never changes.
    // Parents: RTMDACTSETS
    const std::vector<uint32_t> m_flags;  // Flag indices, ascending
public:
    AstRtmdActSet(FileLine* fl, std::vector<uint32_t>&& flags)
        : ASTGEN_SUPER_RtmdActSet(fl)
        , m_flags{std::move(flags)} {}
    ASTGEN_MEMBERS_AstRtmdActSet;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    const std::vector<uint32_t>& flags() const { return m_flags; }
};
class AstRtmdIfaceRef final : public AstNodeRtmdItem {
    // An interface reference variable, traced as the referenced interface's scope
    // @astgen op1 := refp : Optional[AstVarRef]  // The interface reference, until linkDotScope
    // @astgen ptr := m_ifaceRtmdp : Optional[AstRtmdPush] // Inlined RTMD of the target interface
    const std::string m_name;  // Name of the reference, as it appears in the trace
public:
    AstRtmdIfaceRef(FileLine* fl, const std::string& name, AstVarRef* refp)
        : ASTGEN_SUPER_RtmdIfaceRef(fl)
        , m_name{name} {
        this->refp(refp);
    }
    ASTGEN_MEMBERS_AstRtmdIfaceRef;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    AstRtmdPush* ifaceRtmdp() const { return m_ifaceRtmdp; }
    void ifaceRtmdp(AstRtmdPush* nodep) { m_ifaceRtmdp = nodep; }
};
class AstRtmdInstance final : public AstNodeRtmdItem {
    // A sub-instance
    // @astgen ptr := m_cellp : Optional[AstCell]  // The cell, until V3Scope
    std::string m_name;  // Name of the instance, as it appears in the trace
public:
    AstRtmdInstance(FileLine* fl, const std::string& name, AstCell* cellp)
        : ASTGEN_SUPER_RtmdInstance(fl)
        , m_name{name}
        , m_cellp{cellp} {}
    ASTGEN_MEMBERS_AstRtmdInstance;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    void name(const std::string& name) override { m_name = name; }
    AstCell* cellp() const { return m_cellp; }
    void cellp(AstCell* cellp) { m_cellp = cellp; }
};
class AstRtmdPartition final : public AstNodeRtmdItem {
    // An instance of a separately verilated model (--lib-create library), with its own
    // descriptors, found by instance name at run time
    const std::string m_name;  // Name of the instance, as it appears in the trace
public:
    AstRtmdPartition(FileLine* fl, const std::string& name)
        : ASTGEN_SUPER_RtmdPartition(fl)
        , m_name{name} {}
    ASTGEN_MEMBERS_AstRtmdPartition;
    std::string name() const override VL_MT_STABLE { return m_name; }
};
class AstRtmdPop final : public AstNodeRtmdItem {
    // Ends the naming level opened by the matching AstRtmdPush
public:
    explicit AstRtmdPop(FileLine* fl)
        : ASTGEN_SUPER_RtmdPop(fl) {}
    ASTGEN_MEMBERS_AstRtmdPop;
};
class AstRtmdPush final : public AstNodeRtmdItem {
    // Opens a naming level that is not an instance (generate/begin block, function, task),
    // closed by the matching AstRtmdPop
    const VRtmdScopeKind m_kind;  // Kind of naming level
    std::string m_name;  // Name of the naming level, as it appears in the trace
public:
    AstRtmdPush(FileLine* fl, const std::string& name, VRtmdScopeKind kind)
        : ASTGEN_SUPER_RtmdPush(fl)
        , m_kind{kind}
        , m_name{name} {}
    ASTGEN_MEMBERS_AstRtmdPush;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    void name(const std::string& name) override { m_name = name; }
    VRtmdScopeKind kind() const { return m_kind; }
};
class AstRtmdSignal final : public AstNodeRtmdItem {
    // A signal
    // @astgen op1 := refp : AstVarRef  // Reference to the variable holding the value
    // @astgen ptr := m_typeDescp : AstRtmdSignalType  // Signal type
    // @astgen ptr := m_actSetp : Optional[AstRtmdActSet]  // Activity set, from V3Trace
    // Scope holding the variable, which might differ from the described scope. Set by V3Descope.
    // @astgen ptr := m_refScopep : Optional[AstScope]
    const std::string m_name;  // Name of the signal, as it appears in the trace
public:
    AstRtmdSignal(FileLine* fl, const std::string& name, AstRtmdSignalType* typeDescp,
                  AstVarRef* refp)
        : ASTGEN_SUPER_RtmdSignal(fl)
        , m_name{name}
        , m_typeDescp{typeDescp} {
        this->refp(refp);
    }
    ASTGEN_MEMBERS_AstRtmdSignal;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    AstVar* varp() const { return refp()->varp(); }
    AstVarScope* vscp() const { return refp()->varScopep(); }
    AstRtmdSignalType* typeDescp() const { return m_typeDescp; }
    void typeDescp(AstRtmdSignalType* descp) { m_typeDescp = descp; }
    AstRtmdActSet* actSetp() const { return m_actSetp; }
    void actSetp(AstRtmdActSet* entryp) { m_actSetp = entryp; }
    AstScope* refScopep() const { return m_refScopep; }
    void refScopep(AstScope* scopep) { m_refScopep = scopep; }
};

#endif  // Guard
