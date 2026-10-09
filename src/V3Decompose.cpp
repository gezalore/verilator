// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Split arrays and structs into separate variables
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
// V3Decompose replaces variables of unpacked array, unpacked struct,
// multidimensional packed array, or packed struct type with one variable
// per element/member (component). This avoids UNOPTFLAT and enables further
// optimization of the individual components by downstream passes.
//
// The components of a variable are split in turn when they are aggregates, so
// the pass decides, for each original variable and each of its components at
// any depth, whether to split it. These are all called places below: a place is
// a variable followed by a path of selects, e.g. 's', 's.a', 's.a[1]'. A place
// is split if it can be, and it wants to be. It can be split if:
//   - the original variable is not of a kind that cannot be split (primary IO,
//     public, forceable, etc.), and the place is an aggregate
//   - its parent is split, if it is a component
//   - it is not blocked, by being referenced other than in these constructs:
//     - a constant select chain of ARRAYSEL, STRUCTSEL and SEL, addressing a
//       component, or a SEL within one component (e.g. 's.a', 'p[1][3:0]')
//     - the whole LHS of an assignment, where the RHS is:
//       - a select path, with constant or variable indices, and constant bit
//         selects (e.g. 'a = b[i].c', 'a = b[i][7:0]')
//       - a CRESET
//       - for packed types: any expression
//     - the whole RHS of an assignment, where the LHS is a select path
//     in both cases, if the other side does not reference the original variable
// It wants to be split if:
//   - one of its components is addressed by a select chain
//   - the original variable is marked with split_var
//   - a copy between it and another place covers only a portion of it
//
// Copies are assignments between two places. Each is recorded as a copy
// between the corresponding bits of two packed places, or between two whole
// unpacked places, and each place lists the copies covering it. When a packed
// place is split, the copies covering it are split at the boundaries of its
// components, into copies between the components and the corresponding bits of
// the other places. A copy then covering a portion of a place makes that place
// want to be split too. This propagates splitting through copies, including
// between packed types of different layouts. Unpacked places copied have the
// same shape, so their copies are split into copies between the corresponding
// components of both, and the other end wants to be split too.
//
// A splittable place that is not selected from is only ever assigned and
// read whole, by splittable assignments, so a copy is the only reason to split
// it. For example:
//
//   typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;
//   pair_t a, b;
//   assign b = {a.lo + 4'd1, in};  // 'b' is only assigned and read whole
//   assign a = b;                  // A copy between 'a' and 'b'
//   assign out = a.hi;
//
// 'a' is split, as its components are selected. This splits the copy into
// copies between 'a.hi' and 'b[7:4]', and 'a.lo' and 'b[3:0]', each covering
// only a portion of 'b', so 'b' wants to be split too. The result is, with
// each name a separate variable:
//
//   assign b.hi = a.lo + 4'd1;
//   assign b.lo = in;
//   assign a.hi = b.hi;
//   assign a.lo = b.lo;
//   assign out = a.hi;
//
// Without splitting 'b', 'b' would depend on 'a.lo', and 'a.lo' on 'b', a
// false combinational loop (UNOPTFLAT).
//
// The pass has three steps:
//   - DecomposeRecord records the facts, without changing the tree.
//   - DecomposeDecision decides which places are split, from a worklist
//     only adding splits, and creates their components. As the facts are fixed,
//     the result does not depend on the order.
//   - DecomposeRewrite replaces the select chains with references to the
//     components, then expands the recorded assignments with a split side
//     component-wise, assembling packed values of a different layout from the
//     components. Terms of a packed RHS that would be evaluated more than once,
//     or are impure, are assigned to temporaries first.
//
// The component AstVars are shared between all scopes of the original AstVar,
// each split AstVarScope gets its own component AstVarScopes. If the original
// is traced, it is kept and driven from the components, so the trace is
// unchanged. Other originals, AstVarScopes and AstVars, are left unreferenced,
// for V3Dead to remove.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Decompose.h"

#include "V3AstUserAllocator.h"
#include "V3MemberMap.h"
#include "V3SharedTmps.h"
#include "V3Stats.h"

#include <algorithm>
#include <memory>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace DecomposeNamespace {

// TYPES

// A component (element or member) of an aggregate type
struct Component final {
    std::string suffix;  // Name suffix of the AstVar for the component
    AstNodeDType* dtypep;  // Type of the component
    AstMemberDType* memberp;  // The member, if a struct
    int lsb;  // LSB in the whole value, if packed
    int msb;  // MSB in the whole value, if packed
};

struct Place;  // A variable or a component of one, see below

// A copy between bits of a packed Place and of another Place, or between two whole
// unpacked Places of the same shape, as seen from one end. Made for a splittable assignment
// between two Places, or by splitting a copy when one of its Places is split. Each end lists
// the copy, with itself as this end, until split.
struct Copy final {
    Place* otherp;  // The Place at the other end
    // Following only for packed places
    int lsb;  // The first bit covered of this end
    int otherLsb;  // The first bit covered of the other end
    int width;  // The number of bits covered at each end
};

// A component selected by a select chain: the select, and the component it addresses, or for
// bits, the component containing them, from bit 'lsb'
struct ComponentSelect final {
    AstNodeExpr* exprp;  // The select
    Place* placep;  // The component
    int lsb;  // The first bit selected from the component, for packed
};

// A place: an original variable that might be split (an eligible AstVarScope), or one of its
// components, recursively: an element or member at any depth, e.g. 's', 's.a', 's.a[1]'. A
// component becomes a variable of its own if its parent is split. They form a tree (trie)
// per original variable, created lazily as references and copies reach them, and all
// components of a Place once it is split. DecomposeRecord records the facts about each, the
// worklist decides which ones are split, then the split ones get component AstVarScopes.
struct Place final {
    Place* parentp = nullptr;  // The Place this is a component of, nullptr if original
    Place* rootp = nullptr;  // The original variable (root of the tree), root points to itself
    AstNodeDType* dtypep = nullptr;  // The data type of the variable or component
    AstVarScope* vscp = nullptr;  // The AstVarScope for this Place, null for unsplit components
    // The component Places created so far, by index, sized on the first one created
    std::vector<std::unique_ptr<Place>> childrenp;
    std::vector<Copy> copies;  // The copies covering it, until split
    bool splittable = true;  // Can be split (there is no reason not to)
    bool wantsSplit = false;  // Should be split (if possible, do split)
    bool split = false;  // Place was split
    bool queued = false;  // On the worklist
};

// An assignment to expand if a side is split
struct Assignment final {
    AstNodeAssign* assp;  // The assignment
    Place* lPlacep;  // The Place the LHS addresses exactly, if any
    Place* rPlacep;  // The Place the RHS addresses exactly, if any
};

// What DecomposeRecord records
struct DecomposeInfo final {
    std::vector<Place*> rootps;  // The original Places, in creation order
    std::vector<std::vector<ComponentSelect>> chains;  // Select chains addressing components
    std::vector<Assignment> assignments;  // Assignments to expand if a side is split
};

// FUNCTIONS

// The components of the aggregate types, see dtypeComponents. Function local, as
// the allocator checks that user4 is in use when constructed. Cleared at the end of the pass.
AstUser4Allocator<AstNodeDType, std::vector<Component>>& dtypeComponentsCache() {
    static AstUser4Allocator<AstNodeDType, std::vector<Component>> s_dtypeComponents;
    return s_dtypeComponents;
}

// The Places of the original variables, see DecomposeRecord::placeOf. Function local, as
// the allocator checks that user4 is in use when constructed. Cleared at the end of the pass.
AstUser4Allocator<AstVarScope, Place>& places() {
    static AstUser4Allocator<AstVarScope, Place> s_places;
    return s_places;
}

// Unpacked array or unpacked struct
bool isUnpacked(const AstNodeDType* dtypep) {
    dtypep = dtypep->skipRefp();
    if (VN_IS(dtypep, UnpackArrayDType)) return true;
    const AstStructDType* const structp = VN_CAST(dtypep, StructDType);
    return structp && !structp->packed();
}

// Multi-dimensional packed array or packed struct. A packed array of single bit elements
// is not split into individual bits (logic [31:0], bit_t [31:0], logic [31:0][0:0]) here.
bool isPacked(const AstNodeDType* dtypep) {
    dtypep = dtypep->skipRefp();
    if (const AstPackArrayDType* const arrayp = VN_CAST(dtypep, PackArrayDType)) {
        return arrayp->subDTypep()->width() > 1;
    }
    const AstStructDType* const structp = VN_CAST(dtypep, StructDType);
    return structp && structp->packed();
}

// Is the type an aggregate that can be split, as enabled by the options
bool isSplittableType(const AstNodeDType* dtypep) {
    if (isPacked(dtypep)) return v3Global.opt.fDecomposePacked();
    if (isUnpacked(dtypep)) return v3Global.opt.fDecomposeUnpacked();
    return false;
}

// Type of the expression. For a VarRef, this returns the type of the variable,
// which might differ from the type of the VarRef itself after earlier optimizations.
AstNodeDType* dtypeOf(const AstNodeExpr* nodep) {
    if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) return refp->varp()->dtypep();
    return nodep->dtypep();
}

// Components of an aggregate type. Indexed in storage order, that is:
// - For packed arrays, component 0 is in the LSBs
// - For packed structs, component 0 is the last declared member, in the LSBs
// - For unpacked arrays, component 0 is in storage slot 0 at runtime (element at lo() index)
// - For unpacked structs, component 0 is the last declared member, to match packed
const std::vector<Component>& dtypeComponents(AstNodeDType* dtypep) {
    dtypep = dtypep->skipRefp();
    UASSERT_OBJ(isUnpacked(dtypep) || isPacked(dtypep), dtypep,
                "dtypeComponents of non-aggregate type");

    // Cached via user4
    std::vector<Component>& compsr = dtypeComponentsCache()(dtypep);

    // Compute on first lookup
    if (compsr.empty()) {
        if (const AstNodeArrayDType* const arrayp = VN_CAST(dtypep, NodeArrayDType)) {
            const bool packed = isPacked(dtypep);
            const VNumRange range = arrayp->declRange();
            const bool rev = packed && range.ascending();  // Only for naming components
            AstNodeDType* const subp = arrayp->subDTypep();
            for (int i = 0; i < range.elements(); ++i) {
                const int lsb = packed ? i * subp->width() : 0;
                const int msb = packed ? lsb + subp->width() - 1 : 0;
                // The *declared* index of the element in slot i, only used for the name
                const std::string idx
                    = AstNode::encodeNumber(rev ? range.hi() - i : range.lo() + i);
                compsr.push_back({"__BRA__" + idx + "__KET__", subp, nullptr, lsb, msb});
            }
        } else {
            const AstStructDType* const structp = VN_AS(dtypep, StructDType);
            const bool packed = isPacked(dtypep);
            for (AstMemberDType* mp = structp->membersp(); mp;
                 mp = VN_AS(mp->nextp(), MemberDType)) {
                const int lsb = packed ? mp->lsb() : 0;
                const int msb = packed ? lsb + mp->width() - 1 : 0;
                compsr.push_back({"__DOT__" + mp->name(), mp->subDTypep(), mp, lsb, msb});
            }
            // Last member is first
            std::reverse(compsr.begin(), compsr.end());
        }
    }

    // The components of this data type
    return compsr;
}

// Index of the component of a packed type containing bit 'bit'
size_t componentIndex(AstNodeDType* dtypep, int bit) {
    UASSERT_OBJ(isPacked(dtypep), dtypep, "componentIndex of non-packed type");
    const std::vector<Component>& compsr = dtypeComponents(dtypep);
    // The first component ending above the bit. This is O(log n) binary search.
    const auto it = std::lower_bound(compsr.begin(), compsr.end(), bit,
                                     [](const Component& comp, int b) {  //
                                         return b > comp.msb;
                                     });
    return it - compsr.begin();
}

// The Place for component 'idx' of 'placep', created if needed
Place* componentOf(Place* placep, size_t idx) {
    const std::vector<Component>& comps = dtypeComponents(placep->dtypep);
    if (placep->childrenp.empty()) placep->childrenp.resize(comps.size());
    std::unique_ptr<Place>& childpr = placep->childrenp.at(idx);
    if (!childpr) {
        childpr = std::make_unique<Place>();
        childpr->parentp = placep;
        childpr->rootp = placep->rootp;
        childpr->dtypep = comps.at(idx).dtypep;
        childpr->splittable = isSplittableType(childpr->dtypep);
        childpr->wantsSplit = placep->rootp->vscp->varp()->attrSplitVar();
    }
    return childpr.get();
}

// Is 'nodep' cheap to clone
bool isCheap(const AstNodeExpr* nodep) {
    // Constants are cheap
    if (VN_IS(nodep, Const)) return true;
    // So are resets
    if (VN_IS(nodep, CReset)) return true;
    // Variable references are cheap for the most part
    if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
        // Not a forced variable, while technically splittable,
        // splitting trips several bugs in V3Force.
        if (refp->varp()->isForced()) return false;
        // Not a SystemC variable, which can only be accessed whole, not selected from.
        if (refp->varp()->isSc()) return false;
        // Otherwise the path rooted here is cheap
        return true;
    }
    // Bit selects only with a constant LSB
    if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
        return VN_IS(selp->lsbp(), Const) && isCheap(selp->fromp());
    }
    // Other selects with cheap indices are cheap
    if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
        return isCheap(selp->bitp()) && isCheap(selp->fromp());
    }
    if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {  //
        return isCheap(selp->fromp());
    }
    // Extensions of cheap expressions, e.g. of narrow indices
    if (const AstExtend* const extp = VN_CAST(nodep, Extend)) {  //
        return isCheap(extp->lhsp());
    }
    if (const AstExtendS* const extp = VN_CAST(nodep, ExtendS)) {  //
        return isCheap(extp->lhsp());
    }
    // Other expressions are not cheap
    return false;
}

}  // namespace DecomposeNamespace

using namespace DecomposeNamespace;

//######################################################################
// Record the facts about the places, without changing the tree

class DecomposeRecord final : public VNVisitorConst {
    // NODE STATE
    //  AstVar::user1()             -> int: bit 0: eligible, bit 1: evaluated, see isEligible
    //  AstStructDType::user1()     -> bool: members annotated with their indices
    //  AstMemberDType::user1()     -> uint64_t: component index of the member
    //  AstNodeExpr::user1u()       -> Place*: the one an assignment side addresses exactly
    const VNUser1InUse m_user1InUse;

    // STATE
    DecomposeInfo m_info;  // What is recorded
    VMemberMap m_memberMap;  // Struct members by name
    AstNodeAssign* m_assignp = nullptr;  // The visited assignment iff splittable

    // METHODS

    // Reason why the properties of the variable prevent splitting, nullptr if none
    static const char* cannotSplitKindReason(const AstVar* varp) {
        if (!varp->isSignal() && !varp->isTemp()) return "it is not a regular signal or temporary";
        if (varp->isConst()) return "it is a constant";
        if (varp->isPrimaryIO()) return "it is a primary input or output";
        if (varp->isFuncLocal() && varp->isIO()) return "it is a function argument";
        if (varp->isRef()) return "it is a ref port";
        if (varp->isSigPublic()) return "it is public";
        if (varp->isForced()) return "it is forceable";
        if (varp->isReadByDpi()) return "it is read via DPI";
        if (varp->isWrittenByDpi()) return "it is written via DPI";
        if (varp->delayp()) return "it has a net delay";
        return nullptr;
    }

    // Warn that splitting requested via split_var cannot be done, because of 'reasonp'
    static void warnNoSplit(AstVar* varp, const AstNode* wherep, const char* reasonp) {
        // Only warn if user requested splitting
        if (!varp->attrSplitVar()) return;
        wherep->v3warn(SPLITVAR, varp->prettyNameQ()
                                     << " marked split_var but will not be split because "
                                     << reasonp << ".\n");
        wherep->fileline()->modifyWarnOff(V3ErrorCode::SPLITVAR, true);  // Warn only once
    }

    // Is the variable eligible for splitting by its type and properties
    // Note this might be overridden by a visit to an unsupported construct,
    // so it is not completely determined until the whole netlist is visited.
    static bool isEligible(AstVar* varp) {
        // Compute and cache eligibility on first encounter
        if (!varp->user1()) {
            const bool eligible = [&]() {
                // Check data type
                if (!isSplittableType(varp->dtypep())) return false;
                // Check properties
                const char* const reasonp = cannotSplitKindReason(varp);
                // Warn that it cannot be split if user explicitly requested splitting
                if (reasonp) warnNoSplit(varp, varp, reasonp);
                // Eligible if no refusal reason returned
                return !reasonp;
            }();
            varp->user1(2 | eligible);
        }
        // Return the cached result
        return varp->user1() & 1;
    }

    // The root Place for the referenced VarScope, nullptr if not eligible
    Place* placeOf(const AstVarRef* refp) {
        AstVarScope* const vscp = refp->varScopep();
        if (!isEligible(vscp->varp())) return nullptr;
        Place& place = places()(vscp);
        if (!place.rootp) {
            place.rootp = &place;
            place.dtypep = vscp->varp()->dtypep();
            place.vscp = vscp;
            place.wantsSplit = vscp->varp()->attrSplitVar();
            m_info.rootps.push_back(&place);
        }
        return &place;
    }

    // Block the Place from splitting, due to the construct in 'wherep' which prevents splitting
    static void block(Place* placep, const AstNode* wherep) {
        placep->splittable = false;
        // Warn on the variable only, a component is split as far as possible, as requested
        if (!placep->parentp) {
            warnNoSplit(placep->vscp->varp(), wherep, "it is referenced in an unsupported way");
        }
    }

    // Resolve the select chain ending at 'exprp' to the Place it addresses exactly.
    // Returns nullptr if it does not address an eligible one exactly. A Place a component of
    // which is selected wants to be split, one used by a select that cannot be followed is
    // blocked. Iterates expressions not part of the select chain. The components selected are
    // appended to 'chain'.
    Place* resolveChain(AstNodeExpr* exprp, std::vector<ComponentSelect>& chain) {
        // Array selects correspond one to one with a component select
        if (AstArraySel* const selp = VN_CAST(exprp, ArraySel)) {
            if (Place* const fromp = resolveChain(selp->fromp(), chain)) {
                UASSERT_OBJ(isUnpacked(fromp->dtypep), selp, "ArraySel of non-unpacked Place");
                // Index must be constant and in bounds
                const AstConst* const bitp = VN_CAST(selp->bitp(), Const);
                if (bitp && bitp->toUQuad() < dtypeComponents(fromp->dtypep).size()) {
                    Place* const childp = componentOf(fromp, bitp->toUQuad());
                    fromp->wantsSplit = true;
                    chain.push_back({selp, childp, 0});
                    return childp;
                }
                // Otherwise block splitting of the Place
                block(fromp, selp->fromp());
            }
            // Must visit the non-constant index
            iterateConst(selp->bitp());
            return nullptr;
        }
        // Struct selects correspond one to one with a component select
        if (AstStructSel* const selp = VN_CAST(exprp, StructSel)) {
            if (Place* const fromp = resolveChain(selp->fromp(), chain)) {
                if (!isUnpacked(fromp->dtypep)) return nullptr;
                AstStructDType* const structp = VN_AS(fromp->dtypep->skipRefp(), StructDType);
                // Annotate member indices of the struct on first encounter
                if (!structp->user1SetOnce()) {
                    const std::vector<Component>& compsr = dtypeComponents(structp);
                    for (size_t i = 0; i < compsr.size(); ++i) compsr[i].memberp->user1(i);
                }
                const AstNode* const memberp = m_memberMap.findMember(structp, selp->name());
                UASSERT_OBJ(memberp, selp, "Struct member not found: " << selp->name());
                Place* const childp = componentOf(fromp, memberp->user1());
                fromp->wantsSplit = true;
                chain.push_back({selp, childp, 0});
                return childp;
            }
            return nullptr;
        }
        // A packed Sel corresponds to one or more component selects, depends on source dimensions
        // E.g. Sel(VarRef(a), 3) on 'logic [3:0][2:0][1:0]' a corresponds to a[0][1][1],
        // and will contribute 2 chain entries (the fastest varying dimension is not splittable)
        if (AstSel* const selp = VN_CAST(exprp, Sel)) {
            Place* placep = resolveChain(selp->fromp(), chain);
            if (!placep) {
                iterateConst(selp->lsbp());
                return nullptr;
            }
            // Not followed with a variable LSB, or if out of range, so the Place is used whole
            const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const);
            if (!lsbp || lsbp->toSInt() + selp->widthConst() > placep->dtypep->width()) {
                block(placep, selp->fromp());
                iterateConst(selp->lsbp());
                return nullptr;
            }
            // Descend into the Place containing the bits, until exact
            int lsb = lsbp->toSInt();
            int msb = lsb + selp->widthConst() - 1;
            while (lsb != 0 || msb != placep->dtypep->width() - 1) {
                // Within a component of a type not split
                if (!isPacked(placep->dtypep)) return nullptr;
                const size_t idx = componentIndex(placep->dtypep, lsb);
                // Crossing components prevents splitting
                if (idx != componentIndex(placep->dtypep, msb)) {
                    block(placep, selp->fromp());
                    return nullptr;
                }
                placep->wantsSplit = true;
                const Component& comp = dtypeComponents(placep->dtypep).at(idx);
                lsb -= comp.lsb;
                msb -= comp.lsb;
                placep = componentOf(placep, idx);
                chain.push_back({selp, placep, lsb});
            }
            return placep;
        }
        // Base case
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) return placeOf(refp);
        // Not a select chain
        iterateConst(exprp);
        return nullptr;
    }

    // 'nodep' references the Place 'placep' whole
    void referencedWhole(AstNodeExpr* nodep, Place* placep) {
        // If the reference is one of the sides of a splittable assignment, it can stay
        if (m_assignp && (nodep == m_assignp->lhsp() || nodep == m_assignp->rhsp())
            && isSplittableType(placep->dtypep)) {
            // Mark if for visitAssignment
            nodep->user1p(placep);
            return;
        }

        // Otherwise must block splitting of this Place
        block(placep, nodep);
    }

    // Visit a select expression
    void visitSelect(AstNodeExpr* nodep) {
        // Resolve the select chain to the Place it addresses exactly, and also capture the chain
        std::vector<ComponentSelect> chain;
        Place* const placep = resolveChain(nodep, chain);
        // If the select addresses a Place, it references it whole, mark it as such
        if (placep) referencedWhole(nodep, placep);
        // Record the chain for the rewriting phase
        if (!chain.empty()) m_info.chains.push_back(std::move(chain));
    }

    // Does 'nodep' reference the original variable of 'placep'
    static bool referencesVar(AstNodeExpr* nodep, const Place* placep) {
        const AstVarScope* const vscp = placep->rootp->vscp;
        return nodep->exists([&](const AstVarRef* refp) {  //
            return refp->varScopep() == vscp;
        });
    }

    // Do unpacked arrays of the types, at any depth, have ranges of opposite directions.
    // Assigning them pairs elements in reverse order (IEEE 1800-2023 7.6), not supported.
    static bool hasReversedRange(const AstNodeDType* aDTypep, const AstNodeDType* bDTypep) {
        const AstUnpackArrayDType* const aArrayp = VN_CAST(aDTypep->skipRefp(), UnpackArrayDType);
        const AstUnpackArrayDType* const bArrayp = VN_CAST(bDTypep->skipRefp(), UnpackArrayDType);
        if (!aArrayp || !bArrayp) return false;
        if (aArrayp->declRange().ascending() != bArrayp->declRange().ascending()) return true;
        return hasReversedRange(aArrayp->subDTypep(), bArrayp->subDTypep());
    }

    // Assignment visitor, shared by the assignment types that can be split
    void visitAssignment(AstNodeAssign* nodep) {
        VL_RESTORER(m_assignp);
        // Must not have timing control, but always needs to be visited
        m_assignp = nodep->timingControlp() ? nullptr : nodep;
        iterateChildrenConst(nodep);
        if (!m_assignp) return;

        AstNodeExpr* const lhsp = nodep->lhsp();
        AstNodeExpr* const rhsp = nodep->rhsp();
        Place* lPlacep = lhsp->user1u().to<Place*>();
        Place* rPlacep = rhsp->user1u().to<Place*>();
        // If one side references the other, e.g. 's = {s.b, s.a}', expanding the assignment
        // component-wise would read components already written, so block splitting.
        if (lPlacep && referencesVar(rhsp, lPlacep)) {
            block(lPlacep, lhsp);
            lPlacep = nullptr;
        }
        if (rPlacep && referencesVar(lhsp, rPlacep)) {
            block(rPlacep, rhsp);
            rPlacep = nullptr;
        }
        // Is it a splittable assignment
        const bool splittable = [&]() {
            // Not with arrays of opposite directions
            if (hasReversedRange(dtypeOf(lhsp), dtypeOf(rhsp))) return false;
            // Assignment between two Places is splittable
            if (lPlacep && rPlacep) return true;
            // If the LHS is a Place, the RHS must be a splittable expression
            if (lPlacep) {
                // Packed values are always splittable, potentially through hoisting
                if (isPacked(lPlacep->dtypep)) return true;
                // Otherwise each component is assigned a select of the RHS, so it must be cheap
                return isCheap(rhsp);
            }
            // If the RHS is a Place, the assignment must be expandable component-wise
            if (rPlacep) {
                // If packed, the LHS is assigned once, as LHS = { components of RHS }
                if (isPacked(rPlacep->dtypep)) return true;
                // Otherwise each component is assigned to a select of the LHS, so it must be cheap
                return isCheap(lhsp);
            }
            // Otherwise not splittable
            return false;
        }();
        // If not splittable, the sides use their Places whole, so they are blocked
        if (!splittable) {
            if (rPlacep) block(rPlacep, rhsp);
            if (lPlacep) block(lPlacep, lhsp);
            return;
        }

        // If both sides are places, record the whole copies for the Decision phase
        if (lPlacep && rPlacep) {
            const int width = lPlacep->dtypep->width();  // Unused when unpacked
            lPlacep->copies.push_back({rPlacep, 0, 0, width});
            rPlacep->copies.push_back({lPlacep, 0, 0, width});
        }
        // Recorrd for the rewriting phase
        m_info.assignments.push_back({nodep, lPlacep, rPlacep});
    }

    // VISITORS
    void visit(AstNodeDType*) override {}  // No references in data types
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
    // VISITORS - Selects that can cause splitting
    void visit(AstArraySel* nodep) override { visitSelect(nodep); }
    void visit(AstStructSel* nodep) override { visitSelect(nodep); }
    void visit(AstSel* nodep) override { visitSelect(nodep); }
    // VISITORS - Assignments recordeable as Copy
    void visit(AstAssign* nodep) override { visitAssignment(nodep); }
    void visit(AstAssignW* nodep) override { visitAssignment(nodep); }
    void visit(AstAssignDly* nodep) override { visitAssignment(nodep); }
    // VISITORS - References to Places
    void visit(AstVarRef* nodep) override {
        // Reference not handled explicitly in splitable constructs is to the
        // whole of the Place it references, mark as such.
        if (Place* const placep = placeOf(nodep)) referencedWhole(nodep, placep);
    }
    void visit(AstMemberSel* nodep) override {
        iterateChildrenConst(nodep);
        AstVar* const varp = nodep->varp();
        if (!isEligible(varp)) return;
        varp->user1(2);  // Mark not eligible
        warnNoSplit(varp, nodep, "it is accessed indirectly");
    }

    // CONSTRUCTORS
    explicit DecomposeRecord(AstNetlist* netlistp) {
        iterateConst(netlistp);
        // Block the original Places that became ineligible during traversal only
        for (Place* const placep : m_info.rootps) {
            if (!isEligible(placep->vscp->varp())) placep->splittable = false;
        }
    }

public:
    static DecomposeInfo apply(AstNetlist* netlistp) {
        return std::move(DecomposeRecord{netlistp}.m_info);
    }
};

//######################################################################
// Decision, which places are split, creating their components

class DecomposeDecision final {
    // NODE STATE
    //  AstVar::user1()             -> Split components, via m_splitVarps
    const VNUser1InUse m_user1InUse;

    // STATE
    std::vector<Place*> m_worklist;  // Places to consider splitting
    // The component AstVars of the AstVars, see the node state
    AstUser1Allocator<AstVar, std::vector<AstVar*>> m_splitVarps;
    VDouble0 m_statSplitUnpackedOrig;  // Original AstVars of unpacked type split
    VDouble0 m_statSplitPackedOrig;  // Original AstVars of packed type split
    VDouble0 m_statSplitUnpackedComp;  // Component AstVars of unpacked type split
    VDouble0 m_statSplitPackedComp;  // Component AstVars of packed type split

    // METHODS

    // Can the Place be split, as far as known
    static bool canSplit(const Place* placep) {
        // Not if not splittable
        if (!placep->splittable) return false;
        // Not if already split
        if (placep->split) return false;
        // Original variable or its parent was already split
        return !placep->parentp || placep->parentp->split;
    }

    // Put the Place on the worklist, if it wants to be and can be split
    void enqueue(Place* placep) {
        if (placep->queued || !placep->wantsSplit || !canSplit(placep)) return;
        placep->queued = true;
        m_worklist.push_back(placep);
    }

    // Create the component AstVarScopes of the split Place, and set them on its components.
    // The component AstVars are shared by all scopes of the AstVar, created when first split.
    void createComponents(Place* placep) {
        AstVarScope* const vscp = placep->vscp;
        AstVar* const varp = vscp->varp();
        std::vector<AstVar*>& varps = m_splitVarps(varp);
        // Create the component AstVars on first encounter
        if (varps.empty()) {
            const bool packed = isPacked(varp->dtypep());
            if (placep->parentp) {
                ++(packed ? m_statSplitPackedComp : m_statSplitUnpackedComp);
            } else {
                ++(packed ? m_statSplitPackedOrig : m_statSplitUnpackedOrig);
            }
            FileLine* const flp = varp->fileline();
            const VVarType varType = varp->varType();
            const std::string name = varp->name();
            for (const Component& comp : dtypeComponents(varp->dtypep())) {
                AstVar* const newp = new AstVar{flp, varType, name + comp.suffix, comp.dtypep};
                newp->propagateSplitAttrFrom(varp);
                varps.push_back(newp);
                varp->addHereThisAsNext(newp);
            }
        }
        // Create the component AstVarScopes
        AstScope* const scopep = vscp->scopep();
        FileLine* const flp = vscp->fileline();
        for (size_t i = 0; i < varps.size(); ++i) {
            AstVarScope* const newp = new AstVarScope{flp, scopep, varps[i]};
            componentOf(placep, i)->vscp = newp;
            vscp->addHereThisAsNext(newp);
        }
    }

    // Add the copy to the unsplit Place at its end
    void addCopy(Place* placep, const Copy& copy) {
        UASSERT(!placep->split, "Copy added to a split Place");
        // If a Place is not splittable, only the other end matters, no need to attach
        if (!placep->splittable) return;
        // Add the copy to the Place
        placep->copies.push_back(copy);
        // Covering only a portion of a packed Place makes it want to be split,
        // so the copy becomes copies within its components, aligning both ends
        if (!isPacked(placep->dtypep)) return;
        if (copy.lsb != 0 || copy.width != placep->dtypep->width()) {
            placep->wantsSplit = true;
            enqueue(placep);
        }
    }

    // A new copy between 'width' bits of Place 'ap' from 'aLsb', and of 'bp' from 'bLsb',
    // or between the whole of them if unpacked
    void newCopy(Place* ap, int aLsb, Place* bp, int bLsb, int width) {
        UASSERT(ap != bp, "Copy within a Place");
        // Split right away if one end is already split (can't add copies to a split place)
        if (ap->split) {
            splitCopy(ap, {bp, aLsb, bLsb, width});
            return;
        }
        if (bp->split) {
            splitCopy(bp, {ap, bLsb, aLsb, width});
            return;
        }
        addCopy(ap, {bp, aLsb, bLsb, width});
        addCopy(bp, {ap, bLsb, aLsb, width});
    }

    // Split the copy of split Place 'placep' into copies between its components, and for
    // packed, the corresponding bits of the other end, or for unpacked, the components of the
    // other end, which then wants to be split too
    void splitCopy(Place* placep, const Copy& copy) {
        Place* const otherp = copy.otherp;

        // If packed, split the copy based on the components of this place which is being split
        if (isPacked(placep->dtypep)) {
            const std::vector<Component>& comps = dtypeComponents(placep->dtypep);
            // For each component of this place covered by the copy, add copy with other side
            const int lsb = copy.lsb;
            const int msb = copy.lsb + copy.width - 1;
            const size_t first = componentIndex(placep->dtypep, lsb);
            for (size_t i = first; i < comps.size() && comps[i].lsb <= msb; ++i) {
                const Component& comp = comps[i];
                const int partLsb = std::max(lsb, comp.lsb);
                const int partMsb = std::min(msb, comp.msb);
                newCopy(componentOf(placep, i), partLsb - comp.lsb, otherp,
                        copy.otherLsb + partLsb - lsb, partMsb - partLsb + 1);
            }
            return;
        }

        // Unpacked copy of a split place: the other end wants to be split too
        otherp->wantsSplit = true;
        enqueue(otherp);
        // The sides are the same shape, so pairwise whole copies
        const size_t size = dtypeComponents(placep->dtypep).size();
        for (size_t i = 0; i < size; ++i) {
            Place* const ap = componentOf(placep, i);
            if (!ap->splittable) continue;
            Place* const bp = componentOf(otherp, i);
            if (!bp->splittable) continue;
            newCopy(ap, 0, bp, 0, ap->dtypep->width());
        }
    }

    // Split the Place
    void splitPlace(Place* placep) {
        UASSERT(!placep->split, "Place split twice");
        // It is now split
        placep->split = true;
        // Create its components
        createComponents(placep);
        // Enqueue the components that want to be split
        const size_t size = dtypeComponents(placep->dtypep).size();
        for (size_t i = 0; i < size; ++i) enqueue(componentOf(placep, i));
        // Split the copies covering it, unless the other end is split, which split it already
        for (const Copy& copy : placep->copies) {
            if (!copy.otherp->split) splitCopy(placep, copy);
        }
        placep->copies.clear();
    }

    // CONSTRUCTORS
    explicit DecomposeDecision(const std::vector<Place*>& rootps) {
        // Enqueue the original variables
        for (Place* const placep : rootps) enqueue(placep);
        // Split enqueued places, which might make others splittable, repeat until done
        while (!m_worklist.empty()) {
            Place* const placep = m_worklist.back();
            m_worklist.pop_back();
            placep->queued = false;
            splitPlace(placep);
        }

        V3Stats::addStat("Optimizations, Decompose, unpacked variables split",
                         m_statSplitUnpackedOrig);
        V3Stats::addStat("Optimizations, Decompose, packed variables split",
                         m_statSplitPackedOrig);
        V3Stats::addStat("Optimizations, Decompose, unpacked components split further",
                         m_statSplitUnpackedComp);
        V3Stats::addStat("Optimizations, Decompose, packed components split further",
                         m_statSplitPackedComp);
    }

public:
    static void apply(const std::vector<Place*>& rootps) { DecomposeDecision{rootps}; }
};

//######################################################################
// Rewrite, replacing the references to the split places

class DecomposeRewrite final : public VNDeleter {
    // NODE STATE
    //  AstScope::user1p()          -> AstActive*: combinational active, see comboActive
    //  AstNodeExpr::user2()        -> uint64_t: count of a term, (only in hoistTerms)
    const VNUser1InUse m_user1InUse;

    // STATE
    V3SharedTmps m_tmps{"__VdecompHoisted", VVarType::MODULETEMP};  // Temporaries of hoisted terms
    VDouble0 m_statHoisted;  // Terms assigned to temporaries
    VDouble0 m_statSliced;  // Terms sliced instead of hoisted

    // METHODS

    // Reference to the AstVarScope of the Place
    static AstVarRef* newRef(FileLine* flp, const Place* placep, VAccess access) {
        UASSERT(placep->vscp, "Place without AstVarScope");
        return new AstVarRef{flp, placep->vscp, access};
    }

    // Replace the longest prefix of the select chain addressing a
    // component of a split Place with a reference to the component
    void rewriteChain(const std::vector<ComponentSelect>& chain) {
        // The last component selected of a split Place, so all before it are too
        const ComponentSelect* compSelp = nullptr;
        for (const ComponentSelect& compSel : chain) {
            if (compSel.placep->parentp->split) compSelp = &compSel;
        }
        if (!compSelp) return;
        AstNodeExpr* const exprp = compSelp->exprp;
        // The variable reference at the root of the chain, for its access, under the first select.
        // The prefix has no other references, the indices are constant.
        const AstVarRef* refp = nullptr;
        chain.front().exprp->foreach([&](const AstVarRef* nodep) { refp = nodep; });
        FileLine* const flp = exprp->fileline();
        AstNodeExpr* newp = newRef(flp, compSelp->placep, refp->access());
        if (const AstSel* const selp = VN_CAST(exprp, Sel)) {
            const int width = selp->widthConst();
            if (width != newp->width()) newp = new AstSel{flp, newp, compSelp->lsb, width};
        }
        exprp->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(exprp), exprp);
    }

    // Select component 'idx' of 'fromp', with the components of aggregate 'dtypep'
    static AstNodeExpr* newSelect(AstNodeExpr* fromp, AstNodeDType* dtypep, size_t idx) {
        FileLine* const flp = fromp->fileline();
        const Component& comp = dtypeComponents(dtypep).at(idx);
        // If Packed, it's a Sel of the bits
        if (isPacked(dtypep)) {
            AstSel* const selp = new AstSel{flp, fromp, comp.lsb, comp.dtypep->width()};
            selp->dtypep(comp.dtypep);
            return selp;
        }
        // If unpacked array, it's an ArraySel
        if (VN_IS(dtypep->skipRefp(), UnpackArrayDType)) {
            const int i = static_cast<int>(idx);
            UASSERT_OBJ(static_cast<size_t>(i) == idx, fromp, "Index overflow");
            return new AstArraySel{flp, fromp, i};
        }
        // Otherwise must be an unpacked struct, so a StructSel
        AstStructSel* const selp = new AstStructSel{flp, fromp, comp.memberp->name()};
        selp->dtypep(comp.dtypep);
        return selp;
    }

    // Leaf terms of a Concat/Replicate tree, in LSB order, or the expression itself if neither
    static std::vector<AstNodeExpr*> concatTerms(AstNodeExpr* nodep) {
        std::vector<AstNodeExpr*> termps;
        std::vector<AstNodeExpr*> stack{nodep};
        while (!stack.empty()) {
            AstNodeExpr* const exprp = stack.back();
            stack.pop_back();
            if (AstConcat* const concatp = VN_CAST(exprp, Concat)) {
                stack.push_back(concatp->lhsp());
                stack.push_back(concatp->rhsp());
                continue;
            }
            if (AstReplicate* const repp = VN_CAST(exprp, Replicate)) {
                const AstConst* const countp = VN_AS(repp->countp(), Const);
                for (uint32_t i = 0; i < countp->toUInt(); ++i) stack.push_back(repp->srcp());
                continue;
            }
            termps.push_back(exprp);
        }
        return termps;
    }

    // Can bits of 'nodep' be selected without evaluating it more than once, see newSlice
    static bool isSliceable(const AstNodeExpr* nodep) {
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            return VN_IS(selp->lsbp(), Const) && isSliceable(selp->fromp());
        }
        if (const AstConcat* const catp = VN_CAST(nodep, Concat)) {
            return isSliceable(catp->lhsp()) && isSliceable(catp->rhsp());
        }
        if (const AstCond* const condp = VN_CAST(nodep, Cond)) {
            return isCheap(condp->condp()) && isSliceable(condp->thenp())
                   && isSliceable(condp->elsep());
        }
        if (const AstAnd* const andp = VN_CAST(nodep, And)) {
            return isSliceable(andp->lhsp()) && isSliceable(andp->rhsp());
        }
        if (const AstOr* const orp = VN_CAST(nodep, Or)) {
            return isSliceable(orp->lhsp()) && isSliceable(orp->rhsp());
        }
        if (const AstXor* const xorp = VN_CAST(nodep, Xor)) {
            return isSliceable(xorp->lhsp()) && isSliceable(xorp->rhsp());
        }
        if (const AstExtend* const extp = VN_CAST(nodep, Extend)) {
            return isSliceable(extp->lhsp());
        }
        if (const AstNot* const notp = VN_CAST(nodep, Not)) {  //
            return isSliceable(notp->lhsp());
        }
        if (const AstReplicate* const repp = VN_CAST(nodep, Replicate)) {
            return isSliceable(repp->srcp());
        }
        return isCheap(nodep);
    }

    // Select 'width' bits of 'nodep' from 'lsb', pushing the select into the operands where the
    // operation allows
    static AstNodeExpr* newSlice(AstNodeExpr* nodep, int lsb, int width) {
        FileLine* const flp = nodep->fileline();
        // A constant, as a new constant of the bits
        if (const AstConst* const constp = VN_CAST(nodep, Const)) {
            V3Number num{nodep, width};
            num.opSel(constp->num(), lsb + width - 1, lsb);
            return new AstConst{flp, num};
        }
        // A constant bit select, from the bits of what it selects from
        if (AstSel* const selp = VN_CAST(nodep, Sel)) {
            if (const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const)) {
                return newSlice(selp->fromp(), lsbp->toSInt() + lsb, width);
            }
        }
        // A concatenation, from the RHS for the low bits, and the LHS for the high bits
        if (AstConcat* const catp = VN_CAST(nodep, Concat)) {
            const int rWidth = catp->rhsp()->width();
            const int msb = lsb + width - 1;
            if (msb < rWidth) return newSlice(catp->rhsp(), lsb, width);
            if (lsb >= rWidth) return newSlice(catp->lhsp(), lsb - rWidth, width);
            return new AstConcat{flp, newSlice(catp->lhsp(), 0, msb - rWidth + 1),
                                 newSlice(catp->rhsp(), lsb, rWidth - lsb)};
        }
        if (AstCond* const condp = VN_CAST(nodep, Cond)) {
            return new AstCond{flp, condp->condp()->cloneTreePure(false),
                               newSlice(condp->thenp(), lsb, width),
                               newSlice(condp->elsep(), lsb, width)};
        }
        if (AstAnd* const andp = VN_CAST(nodep, And)) {
            return new AstAnd{flp, newSlice(andp->lhsp(), lsb, width),
                              newSlice(andp->rhsp(), lsb, width)};
        }
        if (AstOr* const orp = VN_CAST(nodep, Or)) {
            return new AstOr{flp, newSlice(orp->lhsp(), lsb, width),
                             newSlice(orp->rhsp(), lsb, width)};
        }
        if (AstXor* const xorp = VN_CAST(nodep, Xor)) {
            return new AstXor{flp, newSlice(xorp->lhsp(), lsb, width),
                              newSlice(xorp->rhsp(), lsb, width)};
        }
        // A zero extension, from the operand for its bits, and zeros above
        if (AstExtend* const extp = VN_CAST(nodep, Extend)) {
            const int srcWidth = extp->lhsp()->width();
            const int msb = lsb + width - 1;
            if (msb < srcWidth) return newSlice(extp->lhsp(), lsb, width);
            if (lsb >= srcWidth) return new AstConst{flp, AstConst::WidthedValue{}, width, 0};
            return new AstConcat{
                flp, new AstConst{flp, AstConst::WidthedValue{}, msb - srcWidth + 1, 0},
                newSlice(extp->lhsp(), lsb, srcWidth - lsb)};
        }
        if (AstNot* const notp = VN_CAST(nodep, Not)) {
            return new AstNot{flp, newSlice(notp->lhsp(), lsb, width)};
        }
        // A replication, from the portions of the copies overlapping the bits
        if (AstReplicate* const repp = VN_CAST(nodep, Replicate)) {
            AstNodeExpr* const srcp = repp->srcp();
            const int srcWidth = srcp->width();
            const int msb = lsb + width - 1;
            AstNodeExpr* resultp = nullptr;
            for (int copyLsb = lsb / srcWidth * srcWidth; copyLsb <= msb; copyLsb += srcWidth) {
                const int partLsb = std::max(lsb, copyLsb) - copyLsb;
                const int partMsb = std::min(msb, copyLsb + srcWidth - 1) - copyLsb;
                AstNodeExpr* const bitsp = newSlice(srcp, partLsb, partMsb - partLsb + 1);
                // Higher bits go to the left
                resultp = resultp ? new AstConcat{flp, bitsp, resultp} : bitsp;
            }
            return resultp;
        }
        AstNodeExpr* const clonep = nodep->cloneTreePure(false);
        if (lsb == 0 && width == nodep->width()) return clonep;
        return new AstSel{flp, clonep, lsb, width};
    }

    // Values of the components of 'nodep', with the components of 'dtypep': for a reset cloned
    // from it, for packed assembled from the portions of its terms, otherwise selected from it
    static std::vector<AstNodeExpr*> newAssignRhsps(AstNodeExpr* nodep, AstNodeDType* dtypep) {
        const std::vector<Component>& compsr = dtypeComponents(dtypep);
        std::vector<AstNodeExpr*> valueps;
        valueps.reserve(compsr.size());

        // If CReset, it is duplicated for each component
        if (AstCReset* const cresetp = VN_CAST(nodep, CReset)) {
            for (const Component& comp : compsr) {
                AstCReset* const newp = cresetp->cloneTree(false);
                newp->dtypep(comp.dtypep);
                valueps.push_back(newp);
            }
            return valueps;
        }

        // If packed, assemble each component from the portions of the terms overlapping it,
        // This avoid quadratic cloning then folding if the RHS is a concatenation.
        if (isPacked(dtypep)) {
            valueps.resize(compsr.size(), nullptr);
            int lsb = 0;  // LSB of the current term
            for (AstNodeExpr* const termp : concatTerms(nodep)) {
                const int msb = lsb + termp->width() - 1;
                const size_t first = componentIndex(dtypep, lsb);
                for (size_t i = first; i < compsr.size() && compsr[i].lsb <= msb; ++i) {
                    const Component& comp = compsr[i];
                    const int partLsb = std::max(lsb, comp.lsb);
                    const int partMsb = std::min(msb, comp.msb);
                    FileLine* const flp = termp->fileline();
                    AstNodeExpr* const sp = newSlice(termp, partLsb - lsb, partMsb - partLsb + 1);
                    valueps[i] = valueps[i] ? new AstConcat{flp, sp, valueps[i]} : sp;
                }
                lsb = msb + 1;
            }
            return valueps;
        }

        // Otherwise unpacked, so select each component
        for (size_t i = 0; i < compsr.size(); ++i) {
            valueps.push_back(newSelect(nodep->cloneTree(false), dtypep, i));
        }
        return valueps;
    }

    // Return the expression holding bits 'lsb' to 'msb' of the packed Place
    static AstNodeExpr* newBits(FileLine* flp, const Place* placep, int lsb, int msb) {
        AstNodeDType* const dtypep = placep->dtypep;
        // Note this assertion seems obtuse. 'isPacked' means a "splittable" packed
        UASSERT_OBJ(isPacked(dtypep) || !placep->split, dtypep, "Bits of non-packed Place");
        // If not split, return the bits selected out of a reference
        if (!placep->split) {
            AstVarRef* const refp = newRef(flp, placep, VAccess::READ);
            if (lsb == 0 && msb == dtypep->width() - 1) return refp;
            return new AstSel{flp, refp, lsb, msb - lsb + 1};
        }
        // Otherwise, assemble the bits from the components via concatenations
        const std::vector<Component>& comps = dtypeComponents(dtypep);
        AstNodeExpr* resultp = nullptr;
        const size_t first = componentIndex(dtypep, lsb);
        for (size_t i = first; i < comps.size() && comps[i].lsb <= msb; ++i) {
            const Component& comp = comps[i];
            const int partLsb = std::max(lsb, comp.lsb) - comp.lsb;
            const int partMsb = std::min(msb, comp.msb) - comp.lsb;
            Place* const childp = placep->childrenp.at(i).get();
            AstNodeExpr* const bitsp = newBits(flp, childp, partLsb, partMsb);
            resultp = resultp ? new AstConcat{flp, bitsp, resultp} : bitsp;
        }
        return resultp;
    }

    static void addNewAssign(AstNodeAssign* origp, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        origp->addHereThisAsNext(origp->cloneType(lhsp, rhsp));
    }

    // Expand the assignment between two split Places
    void expandSS(AstNodeAssign* origp, Place* lPlacep, Place* rPlacep) {
        FileLine* const flp = origp->fileline();
        const std::vector<Component>& compsr = dtypeComponents(lPlacep->dtypep);
        if (isPacked(rPlacep->dtypep)) {
            for (size_t i = 0; i < compsr.size(); ++i) {
                Place* const lChildp = lPlacep->childrenp.at(i).get();
                AstNodeExpr* const rp = newBits(flp, rPlacep, compsr[i].lsb, compsr[i].msb);
                expand(origp, lChildp, nullptr, nullptr, rp);
            }
        } else {
            for (size_t i = 0; i < compsr.size(); ++i) {
                Place* const lChildp = lPlacep->childrenp.at(i).get();
                expand(origp, lChildp, nullptr, rPlacep->childrenp.at(i).get(), nullptr);
            }
        }
    }

    // Expand the assignment between the split 'lPlacep' and non split 'rhsp'
    void expandSN(AstNodeAssign* origp, Place* lPlacep, AstNodeExpr* rhsp) {
        const std::vector<AstNodeExpr*> valueps = newAssignRhsps(rhsp, lPlacep->dtypep);
        for (size_t i = 0; i < valueps.size(); ++i) {
            expand(origp, lPlacep->childrenp.at(i).get(), nullptr, nullptr, valueps[i]);
        }
        VL_DO_DANGLING(pushDeletep(rhsp), rhsp);
    }

    // Expand the assignment between the non split 'lhsp' and the split 'rPlacep'
    void expandNS(AstNodeAssign* origp, AstNodeExpr* lhsp, Place* rPlacep) {
        FileLine* const flp = origp->fileline();
        // If RHS is packed, assign the whole value assembled from the components
        if (isPacked(rPlacep->dtypep)) {
            addNewAssign(origp, lhsp, newBits(flp, rPlacep, 0, rPlacep->dtypep->width() - 1));
            return;
        }
        // Unpacked of the same shape, component-wise
        AstNodeDType* const dtypep = dtypeOf(lhsp);
        const size_t size = dtypeComponents(dtypep).size();
        for (size_t i = 0; i < size; ++i) {
            AstNodeExpr* const newLhsp = newSelect(lhsp->cloneTree(false), dtypep, i);
            expand(origp, nullptr, newLhsp, rPlacep->childrenp.at(i).get(), nullptr);
        }
        VL_DO_DANGLING(pushDeletep(lhsp), lhsp);
    }

    // Expand the assignment to the LHS from the RHS, into assignments of the type of 'origp',
    // inserted before it. Each side is either a Place, a component of a split one if not
    // split itself, or an expression, the other being nullptr.
    // Takes ownership of 'lhsp' and 'rhsp'.
    void expand(AstNodeAssign* origp,  //
                Place* lPlacep, AstNodeExpr* lhsp,  //
                Place* rPlacep, AstNodeExpr* rhsp) {
        UASSERT_OBJ(!lPlacep != !lhsp, origp, "Exactly one of lPlacep or lhsp must be non-null");
        UASSERT_OBJ(!rPlacep != !rhsp, origp, "Exactly one of rPlacep or rhsp must be non-null");
        FileLine* const flp = origp->fileline();
        // A Place not split is referenced
        if (lPlacep && !lPlacep->split) {
            lhsp = newRef(flp, lPlacep, VAccess::WRITE);
            lPlacep = nullptr;
        }
        if (rPlacep && !rPlacep->split) {
            rhsp = newRef(flp, rPlacep, VAccess::READ);
            rPlacep = nullptr;
        }
        if (lPlacep && rPlacep) {
            expandSS(origp, lPlacep, rPlacep);
        } else if (lPlacep) {
            expandSN(origp, lPlacep, rhsp);
        } else if (rPlacep) {
            expandNS(origp, lhsp, rPlacep);
        } else {
            addNewAssign(origp, lhsp, rhsp);
        }
    }

    // Will bits 'lsb' to 'msb' of the Place be in different variables after splitting it?
    static bool isSplitBetween(const Place* placep, int lsb, int msb) {
        while (placep->split) {
            const size_t idx = componentIndex(placep->dtypep, lsb);
            if (idx != componentIndex(placep->dtypep, msb)) return true;
            const Component& comp = dtypeComponents(placep->dtypep).at(idx);
            lsb -= comp.lsb;
            msb -= comp.lsb;
            placep = placep->childrenp.at(idx).get();
        }
        return false;
    }

    // Assign the RHS terms of 'origp' that expanding it to the split 'lPlacep' would
    // evaluate more than once, or that are impure, to temporaries before 'origp'
    void hoistTerms(AstNodeAssign* origp, const Place* lPlacep) {
        AstNodeExpr* const rhsp = origp->rhsp();
        const std::vector<AstNodeExpr*> termps = concatTerms(rhsp);
        // A replicated term appears multiple times, so would be evaluated once for each
        const VNUser2InUse user2InUse;
        for (AstNodeExpr* const termp : termps) termp->user2Inc();
        // Hoist the terms, each once, before the assignment
        AstScope* const scopep = lPlacep->rootp->vscp->scopep();
        int lsb = 0;  // LSB of the current term
        for (AstNodeExpr* const termp : termps) {
            const int tLsb = lsb;
            const int tMsb = lsb + termp->width() - 1;
            lsb = tMsb + 1;

            // Already decided, for a replicated term
            if (!termp->user2()) continue;
            // Cheap to select from
            if (isCheap(termp)) {
                termp->user2(0);
                continue;
            }
            // No need to hoist if pure, appears once, and lands in one assignment
            if (termp->isPure() && termp->user2() == 1 && !isSplitBetween(lPlacep, tLsb, tMsb)) {
                continue;
            }
            // Bits can be selected without evaluating it more than once
            if (isSliceable(termp)) {
                termp->user2(0);
                ++m_statSliced;
                continue;
            }

            // Hoist this term to a temporary assignment before the original
            termp->user2(0);
            ++m_statHoisted;
            FileLine* const flp = termp->fileline();
            AstVarScope* const vscp = m_tmps.make(flp, scopep, termp->dtypep());
            termp->replaceWith(new AstVarRef{flp, vscp, VAccess::READ});
            AstVarRef* const tmpRefp = new AstVarRef{flp, vscp, VAccess::WRITE};
            origp->addHereThisAsNext(new AstAssign{flp, tmpRefp, termp});
        }
    }

    // Expand the assignment, if a side is split
    void rewriteAssignment(const Assignment& assignment) {
        Place* const lPlacep = assignment.lPlacep;
        Place* const rPlacep = assignment.rPlacep;
        const bool lSplit = lPlacep && lPlacep->split;
        const bool rSplit = rPlacep && rPlacep->split;
        // Nothing to do if neither side is split
        if (!lSplit && !rSplit) return;

        AstNodeAssign* const origp = assignment.assp;
        // Hoist the terms of a packed RHS that would be evaluated more than once
        if (lSplit && !rSplit && isPacked(lPlacep->dtypep)) hoistTerms(origp, lPlacep);
        AstNodeExpr* const lhsp = origp->lhsp()->unlinkFrBack();
        AstNodeExpr* const rhsp = origp->rhsp()->unlinkFrBack();
        // A side is used if not split, otherwise its components are
        expand(origp,  //
               lSplit ? lPlacep : nullptr, lSplit ? nullptr : lhsp,  //
               rSplit ? rPlacep : nullptr, rSplit ? nullptr : rhsp);
        if (lSplit) VL_DO_DANGLING(pushDeletep(lhsp), lhsp);
        if (rSplit) VL_DO_DANGLING(pushDeletep(rhsp), rhsp);
        VL_DO_DANGLING(pushDeletep(origp->unlinkFrBack()), origp);
    }

    // The combinational AstActive of the scope, cached
    static AstActive* comboActive(AstScope* scopep) {
        if (AstNode* const existingp = scopep->user1p()) return VN_AS(existingp, Active);
        // Use an existing one
        for (AstNode* nodep = scopep->blocksp(); nodep; nodep = nodep->nextp()) {
            AstActive* const activep = VN_CAST(nodep, Active);
            if (activep && activep->hasCombo()) {
                scopep->user1p(activep);
                return activep;
            }
        }
        // Otherwise create a new one
        FileLine* const flp = scopep->fileline();
        AstSenItem* const senItemp = new AstSenItem{flp, AstSenItem::Combo{}};
        AstSenTree* const senTreep = new AstSenTree{flp, senItemp};
        AstActive* const activep = new AstActive{flp, "decompose", senTreep};
        activep->senTreeStorep(activep->sentreep());
        scopep->addBlocksp(activep);
        scopep->user1p(activep);
        return activep;
    }

    // Drive the split Place 'placep' from its components, recursively,
    // so the original variable has its value available.
    static void driveFromComponents(Place* placep, AstActive* activep) {
        if (!placep->split) return;
        AstVarScope* const vscp = placep->vscp;
        FileLine* const flp = vscp->fileline();
        for (size_t i = 0; i < placep->childrenp.size(); ++i) {
            Place* const childp = placep->childrenp[i].get();
            driveFromComponents(childp, activep);
            AstNodeExpr* const rhsp = new AstVarRef{flp, childp->vscp, VAccess::READ};
            AstNodeExpr* const lhsRefp = new AstVarRef{flp, vscp, VAccess::WRITE};
            AstNodeExpr* const lhsp = newSelect(lhsRefp, placep->dtypep, i);
            activep->addStmtsp(new AstAlways{new AstAssignW{flp, lhsp, rhsp}});
        }
    }

    // CONSTRUCTORS
    DecomposeRewrite(const std::vector<Place*>& rootps,
                     const std::vector<std::vector<ComponentSelect>>& chains,
                     const std::vector<Assignment>& assignments) {
        // Rewrite the references: the select chains, then expand the assignments, so the clones
        // of their sides are rewritten already
        for (const std::vector<ComponentSelect>& chain : chains) rewriteChain(chain);
        for (const Assignment& assignment : assignments) rewriteAssignment(assignment);

        // Drive variables that must be kept from their components
        for (Place* const placep : rootps) {
            if (!placep->split) continue;
            const AstVarScope* const vscp = placep->vscp;
            // Only traced ones at this point
            if (!(vscp->varp()->isTrace() && vscp->isTrace())) continue;
            AstActive* const activep = comboActive(vscp->scopep());
            driveFromComponents(placep, activep);
        }

        V3Stats::addStat("Optimizations, Decompose, terms hoisted", m_statHoisted);
        V3Stats::addStat("Optimizations, Decompose, terms sliced", m_statSliced);
    }

public:
    static void apply(const std::vector<Place*>& rootps,
                      const std::vector<std::vector<ComponentSelect>>& chains,
                      const std::vector<Assignment>& assignments) {
        DecomposeRewrite{rootps, chains, assignments};
    }
};

//######################################################################
// V3Decompose class functions

void V3Decompose::decomposeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        // NODE STATE, shared by the steps
        //  AstNodeDType::user4()       -> Components of the type, via dtypeComponentsCache()
        //  AstVarScope::user4()        -> Place: the original variable, via places()
        const VNUser4InUse user4InUse;

        const DecomposeInfo info = DecomposeRecord::apply(nodep);
        DecomposeDecision::apply(info.rootps);
        DecomposeRewrite::apply(info.rootps, info.chains, info.assignments);
        dtypeComponentsCache().clear();
        places().clear();
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("decompose", 0, dumpTreeEitherLevel() >= 3);
}
