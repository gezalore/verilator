// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Build the run time model descriptors (RTMD)
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
// V3Rtmd's Transformations:
//
// Builds the run time model descriptors, which describe the model state as data. Runs right
// after elaboration, while the source hierarchy (begin/generate blocks, modules, function
// statics) is still intact.
//
//  Data types:
//      One AstNodeRtmdDataType per unique data type, held by the AstTypeTable. Built bottom
//      up and deduplicated structurally.
//
//  Scopes:
//      One AstRtmdScope per module, listing the signals, sub-instances and naming levels in
//      trace order. V3Scope clones them per instance, V3Inline splices them, and pruneAll
//      removes what is not traced.
//
// Only source decided filtering happens here (trace_off, --trace-underscore). Per instance
// filtering is done by pruneAll.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Rtmd.h"

#include "V3Ast.h"
#include "V3Control.h"
#include "V3DupFinder.h"
#include "V3Error.h"
#include "V3Stats.h"
#include "V3String.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Builds the data type descriptors held by the AstTypeTable

class RtmdTypeBuilder final {
    // NODE STATE
    //  AstNodeDType::user1()   -> bool. user2p is valid
    //  AstNodeDType::user2p()  -> AstNodeRtmdDataType*. RTMD data type (might be nullptr)
    // VNUser4InUse     In V3Hasher via V3DupFinder

    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

    // STATE
    // The TypeTable holding every type descriptor
    AstTypeTable* const m_typeTablep;
    // The primitive 'bit'/'logic' types
    AstBasicDType* const m_bitDtypep = VN_AS(m_typeTablep->findBitDType(), BasicDType);
    AstBasicDType* const m_logicDtypep = VN_AS(m_typeTablep->findLogicDType(), BasicDType);
    // To share structurally identical descriptor instances
    V3DupFinder m_dupFinder;

    // METHODS
    AstNodeRtmdDataType* newRtmdDataType(AstBasicDType* dtypep) {
        FileLine* const flp = dtypep->fileline();

        const VBasicDTypeKwd kwd = dtypep->keyword();

        // Ranged bit/logic types are really packed arrays
        if (dtypep->isRanged() && kwd.isBitLogic()) {
            const int l = dtypep->left();
            const int r = dtypep->right();
            AstNodeRtmdDataType* const elemp = kwd.isBit() ? dataType(m_bitDtypep)  //
                                                           : dataType(m_logicDtypep);
            return new AstRtmdDTPackedArray{flp, elemp, l, r, dtypep->isSigned()};
        }

        // Primitive types are just atoms, but only some are supported for now
        switch (kwd) {
        case VBasicDTypeKwd::BIT:
        case VBasicDTypeKwd::LOGIC:
        case VBasicDTypeKwd::BYTE:
        case VBasicDTypeKwd::SHORTINT:
        case VBasicDTypeKwd::INT:
        case VBasicDTypeKwd::LONGINT:
        case VBasicDTypeKwd::INTEGER:
        case VBasicDTypeKwd::DOUBLE:
        case VBasicDTypeKwd::TIME:
        case VBasicDTypeKwd::EVENT:
            // Supported in RTMD
            return new AstRtmdDTAtom{flp, kwd, dtypep->isSigned()};

        default:  // Unsupported in RTMD
            return nullptr;
        }
    }

    AstNodeRtmdDataType* newRtmdDataType(AstEnumDType* dtypep) {
        // Descriptor of the underlying type
        AstNodeRtmdDataType* const basep = dataType(dtypep->subDTypep());
        if (!basep) return nullptr;

        AstRtmdDTEnum* const enump
            = new AstRtmdDTEnum{dtypep->fileline(), dtypep->prettyName(), basep};
        for (AstEnumItem* itemp = dtypep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), EnumItem)) {
            const AstConst* const constp = VN_AS(itemp->valuep(), Const);
            const std::string value = constp->num().displayed(dtypep, "%0b");
            enump->addItemsp(new AstRtmdEnumItem{itemp->fileline(), itemp->prettyName(), value});
        }
        return enump;
    }

    AstNodeRtmdDataType* newRtmdDataType(AstPackArrayDType* dtypep) {
        // Descriptor of the element type
        AstNodeRtmdDataType* const elemp = dataType(dtypep->subDTypep());
        if (!elemp) return nullptr;

        FileLine* const flp = dtypep->fileline();
        const int l = dtypep->left();
        const int r = dtypep->right();
        const bool isSigned = dtypep->isSigned();
        return new AstRtmdDTPackedArray{flp, elemp, l, r, isSigned};
    }

    AstNodeRtmdDataType* newRtmdDataType(AstUnpackArrayDType* dtypep) {
        // Descriptor of the element type
        AstNodeRtmdDataType* const elemp = dataType(dtypep->subDTypep());
        if (!elemp) return nullptr;

        FileLine* const flp = dtypep->fileline();
        const int l = dtypep->left();
        const int r = dtypep->right();
        return new AstRtmdDTUnpackedArray{flp, dtypep, elemp, l, r};
    }

    AstNodeRtmdDataType* newRtmdDataType(AstStructDType* dtypep) {
        // Gather all members
        AstRtmdMember* membersp = nullptr;
        for (AstMemberDType* memberDTypep = dtypep->membersp(); memberDTypep;
             memberDTypep = VN_AS(memberDTypep->nextp(), MemberDType)) {
            AstNodeRtmdDataType* const typep = dataType(memberDTypep->subDTypep());
            // If member is not representable, the whole type is not representable
            if (!typep) {
                if (membersp) VL_DO_DANGLING(membersp->deleteTree(), membersp);
                return nullptr;
            }
            FileLine* const flp = memberDTypep->fileline();
            const std::string name = memberDTypep->prettyName();
            membersp = AstNode::addNext(membersp, new AstRtmdMember{flp, name, typep});
        }

        FileLine* const flp = dtypep->fileline();
        if (dtypep->packed()) return new AstRtmdDTPackedStruct{flp, dtypep->isSigned(), membersp};
        return new AstRtmdDTUnpackedStruct{flp, dtypep, membersp};
    }

    AstNodeRtmdDataType* newRtmdDataType(AstUnionDType* dtypep) {
        // Only packed unions are supported for now
        if (!dtypep->packed()) return nullptr;

        // Gather all members
        AstRtmdMember* membersp = nullptr;
        for (AstMemberDType* memberDTypep = dtypep->membersp(); memberDTypep;
             memberDTypep = VN_AS(memberDTypep->nextp(), MemberDType)) {
            AstNodeRtmdDataType* const typep = dataType(memberDTypep->subDTypep());
            // If member is not representable, the whole type is not representable
            if (!typep) {
                if (membersp) VL_DO_DANGLING(membersp->deleteTree(), membersp);
                return nullptr;
            }
            FileLine* const flp = memberDTypep->fileline();
            const std::string name = memberDTypep->prettyName();
            membersp = AstNode::addNext(membersp, new AstRtmdMember{flp, name, typep});
        }

        FileLine* const flp = dtypep->fileline();
        return new AstRtmdDTPackedUnion{flp, dtypep->isSigned(), membersp};
    }
    // Build the descriptor for the given data type
    AstNodeRtmdDataType* newDataType(AstNodeDType* dtypep) {
        // Dispatch to type specific fucntion above
        AstNodeRtmdDataType* const descp = [&]() -> AstNodeRtmdDataType* {
            if (AstBasicDType* const dtp = VN_CAST(dtypep, BasicDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstRefDType* const dtp = VN_CAST(dtypep, RefDType)) {
                return dataType(dtp->subDTypep());  // TODO: eventually should be emitted
            }
            if (AstEnumDType* const dtp = VN_CAST(dtypep, EnumDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstPackArrayDType* const dtp = VN_CAST(dtypep, PackArrayDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstUnpackArrayDType* const dtp = VN_CAST(dtypep, UnpackArrayDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstStructDType* const dtp = VN_CAST(dtypep, StructDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstUnionDType* const dtp = VN_CAST(dtypep, UnionDType)) {
                return newRtmdDataType(dtp);
            }
            // Straight unsopported types (for now)
            if (VN_IS(dtypep, AssocArrayDType)) return nullptr;
            if (VN_IS(dtypep, DynArrayDType)) return nullptr;
            if (VN_IS(dtypep, ClassRefDType)) return nullptr;
            if (VN_IS(dtypep, QueueDType)) return nullptr;
            // FIXME: Handle other data types as needed
            dtypep->v3fatalSrc("Unhandled data type: " + dtypep->prettyTypeName());
            return nullptr;  // LCOV_EXCL_LINE - unreachable
        }();

        // Might not be representable
        if (!descp) return nullptr;

        // Might already be the canonical node (is under the TypeTable), dupFinder won't find it
        if (descp->backp()) return descp;

        // Reuse equivalent descriptor if there is one
        const auto it = m_dupFinder.findDuplicate(descp);
        if (it != m_dupFinder.end()) {
            VL_DO_DANGLING(descp->deleteTree(), descp);
            return VN_AS(it->second, NodeRtmdDataType);
        }

        // Use the new descriptor
        m_typeTablep->addRtmdDataTypesp(descp);
        m_dupFinder.insert(descp);
        return descp;
    }

public:
    // Return the canonical data type descriptor, or nullptr if cannot be represented
    AstNodeRtmdDataType* dataType(AstNodeDType* dtypep) {
        if (!dtypep->user1SetOnce()) dtypep->user2p(newDataType(dtypep));
        return VN_AS(dtypep->user2p(), NodeRtmdDataType);
    }

    // Return the canonical signal type descriptor
    AstRtmdSignalType* signalType(AstVar* varp, AstNodeRtmdDataType* rtmdTypep) {
        const VRtmdVarKind varKind = varp->varType().rtmdVarKind();
        const VDirection direction = varp->declDirection();
        FileLine* const flp = varp->fileline();
        AstRtmdSignalType* const descp = new AstRtmdSignalType{flp, rtmdTypep, varKind, direction};

        // Reuse equivalent descriptor if there is one
        const auto it = m_dupFinder.findDuplicate(descp);
        if (it != m_dupFinder.end()) {
            VL_DO_DANGLING(descp->deleteTree(), descp);
            return VN_AS(it->second, RtmdSignalType);
        }

        // Use the new descriptor
        m_typeTablep->addRtmdSignalTypesp(descp);
        m_dupFinder.insert(descp);
        return descp;
    }

    // CONSTRUCTORS
    explicit RtmdTypeBuilder(AstNetlist* netlistp)
        : m_typeTablep{netlistp->typeTablep()} {
        UASSERT_OBJ(!m_typeTablep->rtmdDataTypesp(), netlistp, "Duplicate data type descriptors");
        UASSERT_OBJ(!m_typeTablep->rtmdSignalTypesp(), netlistp,
                    "Duplicate signal type descriptors");
    }
    ~RtmdTypeBuilder() = default;
    VL_UNCOPYABLE(RtmdTypeBuilder);
};

//######################################################################
// Builds the scope descriptor of each module

class RtmdVisitor final : public VNVisitor {
    // STATE
    RtmdTypeBuilder m_typeBuilder;  // Builds the data type and signal type descriptors
    AstRtmdScope* m_rtmdScopep = nullptr;  // Scope descriptor being built
    AstRtmdPop* m_rootioPopp = nullptr;  // Pop descriptor for the $rootio scope

    // METHODS

    static std::string rtmdName(const AstNode* nodep) {
        return AstNode::prettyName(VName::dehash(nodep->name()));
    }

    void addEntry(AstNodeRtmdItem* entryp) { m_rtmdScopep->addItemsp(entryp); }

    void visitScope(AstNode* nodep, VRtmdScopeKind kind, bool transparent) {
        UASSERT_OBJ(m_rtmdScopep, nodep, nodep->prettyTypeName() + " not under Module");

        // TODO: Unnamed scopes should not exist here, they should all be named
        if (transparent || nodep->name().empty()) {
            iterateChildren(nodep);
            return;
        }

        FileLine* const flp = nodep->fileline();
        addEntry(new AstRtmdPush{flp, rtmdName(nodep), kind});
        iterateChildren(nodep);
        addEntry(new AstRtmdPop{flp});
    }

    // VISITORS

    // NodeModule subclasses - They are scopes, hold Rtmd until flattening in V3Scope
    void visit(AstClass* nodep) override {
        // TODO: static vars under classes should be included
    }
    void visit(AstIface* nodep) override {
        UASSERT_OBJ(!m_rtmdScopep, nodep, "Should not nest");
        UASSERT_OBJ(!nodep->isTop(), nodep, "Interface should not be top");

        VL_RESTORER(m_rtmdScopep);
        VL_RESTORER(m_rootioPopp);

        FileLine* const flp = nodep->fileline();
        m_rtmdScopep = new AstRtmdScope{flp, VRtmdScopeKind::INTERFACE, nodep->origName()};
        m_rootioPopp = nullptr;
        iterateChildren(nodep);
        nodep->rtmdp(m_rtmdScopep);
    }
    void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(!m_rtmdScopep, nodep, "Should not nest");

        // No need to include partition wrappers, handled in the partitions
        if (nodep->verilatorLib()) return;

        VL_RESTORER(m_rtmdScopep);
        VL_RESTORER(m_rootioPopp);

        FileLine* const flp = nodep->fileline();
        m_rtmdScopep = new AstRtmdScope{flp, VRtmdScopeKind::MODULE, nodep->origName()};
        m_rootioPopp = nullptr;
        // The primary IOs of the top wrapper go under '$rootio'
        if (nodep->isTop()) {
            addEntry(new AstRtmdPush{flp, "$rootio", VRtmdScopeKind::ROOTIO});
            m_rootioPopp = new AstRtmdPop{flp};
            addEntry(m_rootioPopp);
        }

        // Build the descriptor for this module
        iterateChildren(nodep);
        // Attach the descriptor to the module
        nodep->rtmdp(m_rtmdScopep);
    }

    // Cells - They link hierarchies until flattening in V3Scope
    void visit(AstCell* nodep) override {
        UASSERT_OBJ(m_rtmdScopep, nodep, "Cell not under Module");
        UASSERT_OBJ(!nodep->name().empty(), nodep, "Unnamed cell");

        FileLine* const flp = nodep->fileline();
        if (nodep->modp()->verilatorLib()) {
            addEntry(new AstRtmdPartition{flp, rtmdName(nodep)});
        } else {
            addEntry(new AstRtmdInstance{flp, rtmdName(nodep), nodep});
        }
    }

    // Scopes
    void visit(AstGenBlock* nodep) override {  //
        visitScope(nodep, VRtmdScopeKind::GENERATE, nodep->implied());
    }
    void visit(AstBegin* nodep) override {  //
        visitScope(nodep, VRtmdScopeKind::BEGIN, nodep->implied());
    }
    void visit(AstFork* nodep) override {  //
        visitScope(nodep, VRtmdScopeKind::FORK, false);
    }
    void visit(AstFunc* nodep) override {  //
        if (nodep->dpiImport()) return;
        visitScope(nodep, VRtmdScopeKind::FUNCTION, false);
    }
    void visit(AstTask* nodep) override {  //
        if (nodep->dpiImport()) return;
        visitScope(nodep, VRtmdScopeKind::TASK, false);
    }

    // Signals
    void visit(AstVar* nodep) override {
        UASSERT_OBJ(m_rtmdScopep, nodep, "Var not under Module");

        // Only static variables
        if (!nodep->lifetime().isStatic()) return;
        // Skip weird stuff
        if (nodep->isSc()) return;

        FileLine* const flp = nodep->fileline();

        // Interface references need to be recorded explicitly
        if (const AstIfaceRefDType* const irdtypep
            = VN_CAST(nodep->dtypep()->skipRefp(), IfaceRefDType)) {
            // Virtual interface handles, or their targets, are excluded
            if (irdtypep->isVirtual()) return;

            // Record the interface reference
            AstVarRef* const refp = new AstVarRef{flp, nodep, VAccess::READ};
            addEntry(new AstRtmdIfaceRef{flp, rtmdName(nodep), refp});
            return;
        }

        // Build the data type descriptor
        AstNodeRtmdDataType* const rtdTypep = m_typeBuilder.dataType(nodep->dtypep());
        // Exclude if not representable
        if (!rtdTypep) return;
        // Build the signal type descriptor
        AstRtmdSignalType* const sigTypep = m_typeBuilder.signalType(nodep, rtdTypep);
        // Build the signal descriptor
        AstVarRef* const refp = new AstVarRef{flp, nodep, VAccess::READ};
        AstRtmdSignal* const rtmdSigp = new AstRtmdSignal{flp, rtmdName(nodep), sigTypep, refp};

        if (m_rootioPopp && nodep->isPrimaryIO()) {
            m_rootioPopp->addHereThisAsNext(rtmdSigp);
        } else {
            addEntry(rtmdSigp);
        }
    }

    // Skipped
    void visit(AstRandSequence*) override {}
    void visit(AstLet*) override {}
    void visit(AstProperty*) override {}
    void visit(AstSequence*) override {}

    // Base case
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTORS
    explicit RtmdVisitor(AstNetlist* nodep)
        : m_typeBuilder{nodep} {
        iterateAndNextNull(nodep->modulesp());
    }
    ~RtmdVisitor() = default;

public:
    static void apply(AstNetlist* nodep) { RtmdVisitor{nodep}; }
};

void V3Rtmd::rtmdAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    RtmdVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("rtmd", 0, dumpTreeEitherLevel() >= 3);
}

//######################################################################
// Prunes from the descriptors the signals a specific instance does not trace

class RtmdPruner final {
    // STATE
    VDouble0 m_statSignals;  // Statistic tracking

    // METHODS

    // Drop the signals turned off by '.vlt' scope rules. 'path' is the trace path of the
    // instance.
    void pruneSignals(AstRtmdScope* descp, const std::string& path) {
        std::vector<std::string> paths{path};
        for (AstNode *entryp = descp->itemsp(), *nextp; entryp; entryp = nextp) {
            nextp = entryp->nextp();
            if (const AstRtmdPush* const ep = VN_CAST(entryp, RtmdPush)) {
                // '$rootio' is not part of the path
                const bool rootio = ep->kind() == VRtmdScopeKind::ROOTIO;
                paths.push_back(rootio ? paths.back() : paths.back() + ep->name() + ".");
            } else if (VN_IS(entryp, RtmdPop)) {
                paths.pop_back();
            } else if (AstRtmdSignal* const ep = VN_CAST(entryp, RtmdSignal)) {
                UASSERT_OBJ(ep->vscp()->isTrace(), ep,
                            "Signal of a trace_off instance should be unreachable");
                if (V3Control::getScopeTraceOn(paths.back() + ep->name())) continue;
                UINFO(9, "  Pruning " << ep << " // Vlt scope trace_off");
                ++m_statSignals;
                VL_DO_DANGLING(ep->unlinkFrBack()->deleteTree(), ep);
            }
        }
        UASSERT_OBJ(paths.size() == 1, descp, "Unbalanced naming levels in descriptor");
    }

    // CONSTRUCTORS
    explicit RtmdPruner(AstNetlist* netlistp) {
        AstTopScope* const topScopep = netlistp->topScopep();
        AstRtmdScope* const rootp = topScopep->rtmdsp();
        UASSERT_OBJ(rootp, netlistp, "Top scope has no tracing descriptor");
        // prettyName drops the leading 'TOP.'
        pruneSignals(rootp, AstNode::prettyName(topScopep->scopep()->name() + "->"));
    }
    ~RtmdPruner() { V3Stats::addStat("Tracing, Rtmd pruned signals", m_statSignals); }
    VL_UNCOPYABLE(RtmdPruner);

public:
    static void apply(AstNetlist* netlistp) { RtmdPruner{netlistp}; }
};

void V3Rtmd::pruneAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    RtmdPruner::apply(nodep);
    V3Global::dumpCheckGlobalTree("rtmdprune", 0, dumpTreeEitherLevel() >= 3);
}
