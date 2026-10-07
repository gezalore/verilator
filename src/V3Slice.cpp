// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Expand unpacked array assignments and comparisons
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
// V3Slice expands operations on whole unpacked arrays element-wise:
//   - An assignment to an unpacked array becomes one assignment per element,
//     unless disabled by -fno-slice, the array has more elements than
//     -fslice-element-limit, or it is a copy of an identical array. Assignments
//     involving SystemC variables are always expanded, as these can only be
//     accessed per element.
//   - EQ, NEQ, EQCASE and NEQCASE of unpacked arrays become the LOGAND or LOGOR
//     of the element-wise comparisons.
//   - A SLICESEL used as a value (e.g. a $display argument) becomes a call to
//     VlUnpacked::slice.
// Elements are paired by position from the left (IEEE 1800-2023 7.6), so
// sides with opposite range directions are reversed. The expanded assignments
// are visited in turn, which expands further unpacked dimensions.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Slice.h"

#include "V3Stats.h"

#include <limits>

VL_DEFINE_DEBUG_FUNCTIONS;

//*************************************************************************

class SliceVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on netlist
    //  AstNodeAssign::user1()      -> bool.  Already processed
    //  AstNodeBiop::user1()        -> bool.  Already processed (Eq, Neq, EqCase, NeqCase)
    const VNUser1InUse m_inuser1;
    //  AstInitArray::user2()       -> uint64_t.  Previously accessed itemIdx
    //  AstInitItem::user2()        -> uint64_t.  Corresponding first elemIdx
    const VNUser2InUse m_inuser2;

    // STATE - across all visitors
    // Maximum number of elements to expand a slice assignment
    const int m_elementLimit = v3Global.opt.fSliceElementLimit()
                                   ? v3Global.opt.fSliceElementLimit()
                                   : std::numeric_limits<int>::max();
    VDouble0 m_statAssigns;  // Statistic tracking
    VDouble0 m_statSliceElementSkips;  // Statistic tracking

    // STATE - for current visit position (use VL_RESTORER)
    AstNode* m_assignp = nullptr;  // Assignment we are under
    bool m_assignError = false;  // True if the current assign already has an error
    bool m_okInitArray = false;  // Allow InitArray children

    // METHODS
    // Storage index of the element at position 'idxFromLeft' of 'range', counted from the left
    static int storageIndex(const VNumRange& range, uint64_t idxFromLeft) {
        const int idx = static_cast<int>(idxFromLeft);
        return range.ascending() ? idx : range.elements() - 1 - idx;
    }

    AstNodeExpr* cloneAndSel(AstNodeExpr* const nodep, uint64_t elements, uint64_t elemIdx,
                             const bool needPure) {
        // Insert an ArraySel, except for a few special cases
        const AstUnpackArrayDType* const arrayp
            = VN_CAST(nodep->dtypep()->skipRefp(), UnpackArrayDType);
        if (!arrayp) {  // V3Width should have complained, but...
            if (!m_assignError) {
                nodep->v3error(
                    nodep->prettyTypeName()
                    << " is not an unpacked array, but is in an unpacked array context");
            } else {
                V3Error::incErrors();  // Otherwise might infinite loop
            }
            m_assignError = true;
            // Likely will cause downstream errors
            return nodep->cloneTree(false, needPure);
        }
        if (static_cast<uint64_t>(arrayp->rangep()->elementsConst()) != elements) {
            if (!m_assignError) {
                nodep->v3error(
                    "Slices of arrays in assignments have different unpacked dimensions, "
                    << elements << " versus " << arrayp->rangep()->elementsConst());
            }
            m_assignError = true;
            elements = 1;
            elemIdx = 0;
        }

        if (AstInitArray* const initp = VN_CAST(nodep, InitArray)) {
            UINFO(9, "  cloneInitArray(" << elements << "," << elemIdx << ") " << nodep);

            AstNodeExpr* newp = nullptr;
            uint64_t itemIdx = 0;
            uint64_t i = 0;
            const AstInitArray::KeyItemMap& itemMap = initp->map();
            if (const uint64_t prevItemIdx = initp->user2()) {
                const auto it = itemMap.find(storageIndex(arrayp->declRange(), prevItemIdx));
                if (it != itemMap.end()) {
                    const AstInitItem* itemp = it->second;
                    if (itemp->user2() && itemp->user2() < elemIdx) {
                        // Let's resume traversal from the previous position
                        itemIdx = prevItemIdx;
                        i = itemp->user2();
                    }
                }
            }
            const AstNodeDType* const expectedItemDTypep = arrayp->subDTypep()->skipRefp();
            while (i <= elemIdx) {
                const auto itemIt = itemMap.find(storageIndex(arrayp->declRange(), itemIdx));
                AstNodeExpr* const itemp
                    = itemIt != itemMap.end() ? itemIt->second->valuep() : initp->defaultp();
                const bool directItem = itemIt != itemMap.end();
                if (!itemp && !m_assignError) {
                    nodep->v3error("Array initialization has too few elements, need element "
                                   << elemIdx);
                    m_assignError = true;
                    break;
                }
                const AstNodeDType* itemRawDTypep = itemp->dtypep()->skipRefp();
                const VCastable castable
                    = AstNode::computeCastable(expectedItemDTypep, itemRawDTypep, itemp);
                if (castable == VCastable::SAMEISH || castable == VCastable::COMPATIBLE) {
                    if (i == elemIdx) {
                        newp = itemp->cloneTree(false, !directItem && needPure);
                        break;
                    } else {  // Check the next item
                        ++i;
                        ++itemIdx;
                    }
                } else {
                    const AstUnpackArrayDType* const itemDTypep
                        = VN_CAST(itemRawDTypep, UnpackArrayDType);
                    if (!itemDTypep
                        || !expectedItemDTypep->isSame(itemDTypep->subDTypep()->skipRefp())) {
                        if (!m_assignError) {
                            itemp->v3error("Item is incompatible with the array type.");
                        }
                        m_assignError = true;
                        break;
                    }
                    if (i + itemDTypep->elementsConst()
                        > elemIdx) {  // This item contains the element
                        int offset = storageIndex(itemDTypep->declRange(), elemIdx - i);
                        if (AstSliceSel* const slicep = VN_CAST(itemp, SliceSel)) {
                            offset += slicep->declRange().lo();
                            newp = new AstArraySel{nodep->fileline(),
                                                   slicep->fromp()->cloneTreePure(false), offset};
                        } else {
                            newp = new AstArraySel{nodep->fileline(), itemp->cloneTreePure(false),
                                                   offset};
                        }

                        if (!m_assignError && elemIdx + 1 == elements
                            && i + itemDTypep->elementsConst() > elements) {
                            nodep->v3error("Array initialization has too many elements. "
                                           << elements << " elements are expected, but at least "
                                           << i + itemDTypep->elementsConst()
                                           << " elements exist.");
                            m_assignError = true;
                        }
                        break;
                    } else {  // Check the next item
                        i += itemDTypep->elementsConst();
                        ++itemIdx;
                    }
                }
            }
            if (elemIdx + 1 == elements && static_cast<size_t>(itemIdx) + 1 < initp->map().size()
                && !m_assignError) {
                nodep->v3error("Array initialization has too many elements. "
                               << elements << " elements are expected, but at least "
                               << i + initp->map().size() - itemIdx << " elements exist.");
                m_assignError = true;
            }
            if (newp) {
                const auto it = itemMap.find(storageIndex(arrayp->declRange(), itemIdx));
                if (it != itemMap.end()) {  // Remember current position for the next invocation.
                    initp->user2(itemIdx);
                    it->second->user2(i);
                }
            }
            if (!newp) newp = new AstConst{nodep->fileline(), 0};
            return newp;
        }

        if (AstCond* const snodep = VN_CAST(nodep, Cond)) {
            UINFO(9, "  cloneCond(" << elements << "," << elemIdx << ") " << nodep);
            return new AstCond{snodep->fileline(), snodep->condp()->cloneTree(false, needPure),
                               cloneAndSel(snodep->thenp(), elements, elemIdx, needPure),
                               cloneAndSel(snodep->elsep(), elements, elemIdx, needPure)};
        }

        if (const AstSliceSel* const snodep = VN_CAST(nodep, SliceSel)) {
            UINFO(9, "  cloneSliceSel(" << elements << "," << elemIdx << ") " << nodep);
            const int leOffset
                = snodep->declRange().lo() + storageIndex(snodep->declRange(), elemIdx);
            return new AstArraySel{nodep->fileline(), snodep->fromp()->cloneTree(false, needPure),
                                   leOffset};
        }

        if (const AstSampled* const snodep = VN_CAST(nodep, Sampled)) {
            UINFO(9, "  cloneSampled(" << elements << "," << elemIdx << ") " << nodep);
            AstNodeExpr* const exprp = VN_AS(snodep->exprp(), NodeExpr);
            AstNodeExpr* const selp = cloneAndSel(exprp, elements, elemIdx, needPure);
            return new AstSampled{nodep->fileline(), selp, selp->dtypep(), snodep->internal()};
        }

        if (AstExprStmt* const snodep = VN_CAST(nodep, ExprStmt)) {
            UINFO(9, "  cloneExprStmt(" << elements << "," << elemIdx << ") " << nodep);
            AstNodeExpr* const resultSelp
                = cloneAndSel(snodep->resultp(), elements, elemIdx, needPure);
            if (snodep->stmtsp()) {
                return new AstExprStmt{nodep->fileline(), snodep->stmtsp()->unlinkFrBackWithNext(),
                                       resultSelp};
            } else {
                return resultSelp;
            }
        }

        if (VN_IS(nodep, NodeVarRef) || VN_IS(nodep, NodeSel) || VN_IS(nodep, CMethodHard)
            || VN_IS(nodep, MemberSel) || VN_IS(nodep, StructSel)) {
            UINFO(9, "  cloneSel(" << elements << "," << elemIdx << ") " << nodep);
            const int leOffset = storageIndex(arrayp->declRange(), elemIdx);
            return new AstArraySel{nodep->fileline(), nodep->cloneTree(false, needPure), leOffset};
        }

        if (!m_assignError) {
            nodep->v3error(nodep->prettyTypeName()
                           << " unexpected in assignment to unpacked array");
        }
        m_assignError = true;
        // Likely will cause downstream errors
        return nodep->cloneTree(false, needPure);
    }

    // Returns true if did expand and 'nodep' was deleted
    bool expandArrayAssign(AstNodeAssign* nodep, const AstUnpackArrayDType* arrayp) {
        const bool expand = [&]() {
            // Any isSc variables must be always expanded
            const bool hasSc = nodep->exists([&](const AstVarRef* refp) -> bool {  //
                return refp->varp()->isSc();
            });
            if (hasSc) return true;

            // Don't if disabled by -fno-slice
            if (!v3Global.opt.fSlice()) return false;

            // Skip optimization if array is too large
            const int elements = arrayp->rangep()->elementsConst();
            if (elements > m_elementLimit) {
                ++m_statSliceElementSkips;
                return false;
            }

            // Skip if this is a simple a = b assignment of identical arrays
            if (AstVarRef* const lhsp = VN_CAST(nodep->lhsp(), VarRef)) {
                if (AstVarRef* const rhsp = VN_CAST(nodep->rhsp(), VarRef)) {
                    if (lhsp->dtypep()->skipRefp()->sameTree(rhsp->dtypep()->skipRefp())) {
                        return false;
                    }
                }
            }

            return true;
        }();
        if (!expand) return false;

        UINFO(4, "Slice optimizing " << nodep);
        ++m_statAssigns;

        // Element 'elemIdx' is counted from the left on both sides, as assignment pairs
        // elements left to right (IEEE 1800-2023 7.6). cloneAndSel maps it to the storage
        // index of each side, so sides with opposite range directions are reversed there.
        AstNodeAssign* newlistp = nullptr;
        const uint64_t elements = arrayp->rangep()->elementsConst();
        for (uint64_t elemIdx = 0; elemIdx < elements; ++elemIdx) {
            // Original node is replaced, so it is safe to copy it one time even if it is impure.
            AstNodeAssign* const newp
                = nodep->cloneType(cloneAndSel(nodep->lhsp(), elements, elemIdx, elemIdx != 0),
                                   cloneAndSel(nodep->rhsp(), elements, elemIdx, elemIdx != 0));
            UINFOTREE(9, newp, "", "new");
            newlistp = AstNode::addNext(newlistp, newp);
        }

        // The normal edit iterator will iterate on the replacements next
        nodep->replaceWith(newlistp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        return true;
    }

    void visit(AstNodeAssign* nodep) override {
        // The expanded assignments are visited next by the iterator
        if (nodep->user1SetOnce()) return;  // Process once
        UINFOTREE(9, nodep, "", "Deslice-In");
        VL_RESTORER(m_assignError);
        VL_RESTORER(m_assignp);
        VL_RESTORER(m_okInitArray);
        m_assignError = false;
        m_assignp = nodep;

        AstNodeDType* const dtp = nodep->lhsp()->dtypep()->skipRefp();
        if (const AstUnpackArrayDType* const uatp = VN_CAST(dtp, UnpackArrayDType)) {
            AstNode* const rhsp = nodep->rhsp();
            if (!VN_IS(rhsp, CvtPackedToArray) && !VN_IS(rhsp, CReset)) {
                if (expandArrayAssign(nodep, uatp)) return;
                m_okInitArray = true;
            }
        }

        iterateChildren(nodep);
    }

    void visit(AstConsPackUOrStruct* nodep) override {
        VL_RESTORER(m_okInitArray);
        m_okInitArray = true;
        iterateChildren(nodep);
    }
    void visit(AstConsDynArray* nodep) override {
        VL_RESTORER(m_okInitArray);
        m_okInitArray = true;
        iterateChildren(nodep);
    }
    void visit(AstConsQueue* nodep) override {
        VL_RESTORER(m_okInitArray);
        m_okInitArray = true;
        iterateChildren(nodep);
    }
    void visit(AstInitArray* nodep) override {
        UASSERT_OBJ(!m_assignp || m_okInitArray, nodep,
                    "Array initialization should have been removed earlier");
    }

    template <typename T_NodeBiop>
    void expandBiOp(T_NodeBiop* biopp) {
        AstNodeBiop* nodep = biopp;
        if (nodep->user1SetOnce()) return;  // Process once
        UINFO(9, "  Bi-Eq/Neq expansion " << nodep);

        // Only expand if lhs is an unpacked array (we assume type checks already passed)
        const AstNodeDType* const fromDtp = nodep->lhsp()->dtypep()->skipRefp();
        if (const AstUnpackArrayDType* const adtypep = VN_CAST(fromDtp, UnpackArrayDType)) {
            AstNodeBiop* logp = nullptr;

            const uint64_t elements = adtypep->rangep()->elementsConst();
            for (uint64_t elemIdx = 0; elemIdx < elements; ++elemIdx) {
                // EQ(a,b) -> LOGAND(EQ(ARRAYSEL(a,0), ARRAYSEL(b,0)), ...[1])
                // Original node is replaced, so it is safe to copy it one time even if it is
                // impure.
                T_NodeBiop* const clonep = new T_NodeBiop{
                    nodep->fileline(), cloneAndSel(nodep->lhsp(), elements, elemIdx, elemIdx != 0),
                    cloneAndSel(nodep->rhsp(), elements, elemIdx, elemIdx != 0)};
                if (!logp) {
                    logp = clonep;
                } else {
                    switch (nodep->type()) {
                    case VNType::Eq:  // FALLTHRU
                    case VNType::EqCase:
                        logp = new AstLogAnd{nodep->fileline(), logp, clonep};
                        break;
                    case VNType::Neq:  // FALLTHRU
                    case VNType::NeqCase:
                        logp = new AstLogOr{nodep->fileline(), logp, clonep};
                        break;
                    default: nodep->v3fatalSrc("Unknown node type processing array slice"); break;
                    }
                }
            }
            UASSERT_OBJ(logp, nodep, "Unpacked array with empty indices range");
            nodep->replaceWith(logp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            nodep = logp;
        }

        iterateChildren(nodep);
    }

    void visit(AstEq* nodep) override { expandBiOp(nodep); }
    void visit(AstNeq* nodep) override { expandBiOp(nodep); }
    void visit(AstEqCase* nodep) override { expandBiOp(nodep); }
    void visit(AstNeqCase* nodep) override { expandBiOp(nodep); }

    void visit(AstSliceSel* nodep) override {
        // Slice used as a bare value, e.g. a $display argument. Build it via
        // VlUnpacked::slice<N_Out>(loIdx), as DYN_SLICE already does for Queues.
        iterateChildren(nodep);
        AstNodeExpr* const fromp = nodep->fromp()->unlinkFrBack();
        AstConst* const lop = new AstConst{nodep->fileline(), AstConst::WidthedValue{}, 32,
                                           static_cast<uint32_t>(nodep->declRange().lo())};
        AstCMethodHard* const newp
            = new AstCMethodHard{nodep->fileline(), fromp, VCMethod::ARRAY_SLICE};
        newp->addPinsp(lop);
        newp->dtypeFrom(nodep);  // Reuse the already-correct sliced array dtype
        newp->didWidth(true);
        newp->protect(false);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit SliceVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~SliceVisitor() override {
        V3Stats::addStat("Optimizations, Slice, array assignments", m_statAssigns);
        V3Stats::addStat("Optimizations, Slice, array skips due to size limit",
                         m_statSliceElementSkips);
    }
};

//######################################################################
// Link class functions

void V3Slice::sliceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { SliceVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("slice", 0, dumpTreeEitherLevel() >= 3);
}
