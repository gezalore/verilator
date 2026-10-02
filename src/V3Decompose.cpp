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
// A variable is automatically split unless it is of a kind that cannot be
// split (primary IO, public, forceable, etc.), or it is referenced other
// than in these candidate constructs:
//   - ARRAYSEL(VARREF, CONST), of an unpacked array
//   - STRUCTSEL(VARREF), of an unpacked struct
//   - SEL(VARREF, CONST), of a packed type, with the bits within one component
//   - the whole LHS of an assignment, where the RHS is:
//     - a select path, with constant or variable indices, and constant bit
//       selects (e.g. 'a = b[i].c', 'a = b[i][7:0]')
//     - a CRESET
//     - for unpacked types: a pure CONSPACKUORSTRUCT or INITARRAY independent
//       of the variable
//     - for packed types: a constant, or a CONCAT or REPLICATE independent of
//       the variable, of constants, variable references, and pure expressions
//       within one component
//   - the whole RHS of an assignment, where the LHS is:
//     - a select path like in the LHS case above
//
// A traversal records the candidates, and blocks variables referenced in any
// other way, so they are not split. A variable is split when a select candidate
// from it is split. Variables only copied whole are not split, as that would
// only expand the copies, unless marked with split_var, or copied to or from a
// variable that is split, as that copy is expanded anyway, selecting from them.
// Then the candidates are split in rounds. Selects are replaced with references
// to the components, or for packed types, a select from the component.
// Assignments are expanded component-wise, selecting the components from a side
// that is not split, or assembling them from the components of a split packed
// RHS. Replacing a select can make it, or its parent, a candidate, which is
// recorded for the next round, or reveal a use of the component that blocks it.
// All references to a component are created in the round its parent is split,
// and its candidates are only split in the next round, so a component is always
// blocked before any of its candidates are split. Assignments are only expanded
// once no select candidates remain, as expanding one would delete or move the
// selects in it. A copy where neither side is split yet waits until either side
// is split, which can happen when another copy of it is expanded. Copies still
// waiting at the end are not split.
//
// The component AstVars are shared between all scopes of the original AstVar,
// each split AstVarScope gets its own component AstVarScopes. If the original
// is traced, it is kept and driven from the components, so the trace is
// unchanged. Other original AstVarScopes are deleted, the original AstVars are
// left unreferenced, for V3Dead to remove.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Decompose.h"

#include "V3AstUserAllocator.h"
#include "V3MemberMap.h"
#include "V3Stats.h"

#include <algorithm>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class DecomposeVisitor final : public VNVisitor {
    // TYPES

    // A component (element or member) of an aggregate type
    struct Component final {
        std::string suffix;  // Name suffix of the AstVar for the component
        AstNodeDType* dtypep;  // Type of the component
        AstMemberDType* memberp;  // The member, if a struct
        int lsb;  // LSB in the whole value, if packed
        int msb;  // MSB in the whole value, if packed
    };

    // NODE STATE
    //  AstVar::user1()             -> Split elements, via m_splitVarps
    //  AstVarScope::user1()        -> Split elements, via m_splitVscps
    //  AstNodeDType::user1()       -> Components of struct or array types, via m_dtypeComponents
    //  AstMemberDType::user1()     -> uint64_t: index of the member, set by dtypeComponents()
    //  AstScope::user1p()          -> AstActive*: combinational active of the scope, if any
    //
    //  AstVar::user2()             -> int: bit 0: eligible, bit 1: evaluated (isEligible)
    //  AstVarScope::user2()        -> bool: blocked, needs the variable intact
    //  Candidate nodes::user2()    -> int: 1: recorded, 2: assignment waiting for a side to be
    //                                 split, in m_waitingAssigns
    //
    //  AstVar::user3p()            -> AstVar*, variable this was split from
    //  AstVarScope::user3p()       -> AstVarScope*, variable this was split from
    //
    //  AstVar::user4()             -> bool: warned that it will not be split
    //  AstVarScope::user4()        -> Assignments waiting for this to be split, via
    //                                 m_waitingAssigns
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;
    const VNUser4InUse m_user4InUse;
    AstUser1Allocator<AstVar, std::vector<AstVar*>> m_splitVarps;
    AstUser1Allocator<AstVarScope, std::vector<AstVarScope*>> m_splitVscps;
    AstUser1Allocator<AstNodeDType, std::vector<Component>> m_dtypeComponents;
    AstUser4Allocator<AstVarScope, std::vector<AstNodeAssign*>> m_waitingAssigns;

    // STATE
    std::vector<AstNodeExpr*> m_selectCandidates;  // Selects that can be split
    std::vector<AstNodeAssign*> m_assignCandidates;  // Assignments that can be split
    AstScope* m_scopep = nullptr;  // Current scope
    VMemberMap m_memberMap;  // Struct members by name

    VDouble0 m_statSplitUnpackedOrig;  // Original AstVars of unpacked type split
    VDouble0 m_statSplitPackedOrig;  // Original AstVars of packed type split
    VDouble0 m_statSplitUnpackedComp;  // Component AstVars of unpacked type split
    VDouble0 m_statSplitPackedComp;  // Component AstVars of packed type split

    // METHODS

    // Unpacked array or unpacked struct
    static bool isUnpacked(const AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (VN_IS(dtypep, UnpackArrayDType)) return true;
        const AstStructDType* const structp = VN_CAST(dtypep, StructDType);
        return structp && !structp->packed();
    }

    // Multi-dimensional packed array or packed struct. A packed array of single bit elements
    // is not split into individual bits (logic [31:0], bit_t [31:0], logic [31:0][0:0]) here.
    static bool isPacked(const AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (const AstPackArrayDType* const arrayp = VN_CAST(dtypep, PackArrayDType)) {
            return arrayp->subDTypep()->width() > 1;
        }
        const AstStructDType* const structp = VN_CAST(dtypep, StructDType);
        return structp && structp->packed();
    }

    // Reason why the properties of the variable prevents splitting, nullptr if splittable
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

    // Warn if splitting was requested via split_var, cannot be done for reasonp
    void warnNoSplit(AstVar* varp, const AstNode* wherep, const char* reasonp) {
        // Only warn if user requested splitting
        if (!varp->attrSplitVar()) return;
        // Not on components, the variable has been split already, maybe as requested
        if (varp->user3p()) return;
        // Only once per variable
        if (varp->user4SetOnce()) return;
        wherep->v3warn(SPLITVAR, varp->prettyNameQ()
                                     << " marked split_var but will not be split because "
                                     << reasonp << ".\n");
    }

    // Is the variable eligible for splitting by its type and properties
    // Note this might be overridden by a visit to an unsupported construct,
    // so it is not completely determined until the whole netlist is visited.
    bool isEligible(AstVar* varp) {
        // Compute and cache eligibility on first encounter
        if (!varp->user2()) {
            const bool eligible = [&]() {
                // Check data type
                const AstNodeDType* const dtypep = varp->dtypep();
                if (isPacked(dtypep)) {
                    if (!v3Global.opt.fDecomposePacked()) return false;
                } else if (isUnpacked(dtypep)) {
                    if (!v3Global.opt.fDecomposeUnpacked()) return false;
                } else {
                    return false;
                }
                // Check properties
                const char* const reasonp = cannotSplitKindReason(varp);
                // Warn that it cannot be split if user explicitly requested splitting
                if (reasonp) warnNoSplit(varp, varp, reasonp);
                // Eligible if no refusal reason returned
                return !reasonp;
            }();
            varp->user2(2 | eligible);
        }
        // Return the cached result
        return varp->user2() & 1;
    }

    // Can the variable of this reference be split: eligible, and not blocked. When called
    // during the traversal it might return true for a reference to a variable that is only
    // blocked later.
    bool canSplit(const AstVarRef* nodep) {
        if (!nodep) return false;
        const AstVarScope* const vscp = nodep->varScopep();
        return isEligible(vscp->varp()) && !vscp->user2();
    }

    // Is this reference to a variable that should be split?
    bool shouldSplit(const AstVarRef* nodep) {
        // Only if can be split
        if (!canSplit(nodep)) return false;
        // Must split the reference if already split the variable
        if (m_splitVscps.tryGet(nodep->varScopep())) return true;
        // Split if marked with split_var
        if (nodep->varp()->attrSplitVar()) return true;
        // Don't split otherwise (e.g.: aggregates used only as whole)
        return false;
    }

    // Type of the expression. For a VarRef, this returns the type of the variable,
    // which might differ from the type of the VarRef itself after earlier optimizations.
    static AstNodeDType* dtypeOf(const AstNodeExpr* nodep) {
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) return refp->varp()->dtypep();
        return nodep->dtypep();
    }

    // Record splitting candidate which is a select
    void recordSelectCandidate(AstNodeExpr* nodep) {
        if (nodep->user2()) return;  // Skip if already recorded
        nodep->user2(1);  // Mark as recorded
        m_selectCandidates.push_back(nodep);
    }

    // Record splitting candidate which is an assignment
    void recordAssignCandidate(AstNodeAssign* nodep) {
        if (nodep->user2()) return;  // Skip if already recorded
        nodep->user2(1);  // Mark as recorded
        m_assignCandidates.push_back(nodep);
    }

    // Components of an aggregate type. Indexed in storage order, that is:
    // - For packed arrays, component 0 is in the LSBs
    // - For packed structs, component 0 is the last declared member, in the LSBs
    // - For unpacked arrays, component 0 is in storage slot 0 at runtime (element at lo() index)
    // - For unpacked structs, component 0 is the last declared member, to match packed
    // This function also annotates struct MemberDTypes with their component indices
    const std::vector<Component>& dtypeComponents(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        UASSERT_OBJ(isUnpacked(dtypep) || isPacked(dtypep), dtypep,
                    "dtypeComponents of non-aggregate type");

        // Cached via user1
        std::vector<Component>& compsr = m_dtypeComponents(dtypep);

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
                // Annotate the member types with their component indices
                for (size_t i = 0; i < compsr.size(); ++i) compsr[i].memberp->user1(i);
            }
        }

        // The components of this data type
        return compsr;
    }

    // Values of the components if 'nodep' is an array or struct cons expression
    // that defines a value for every component, empty otherwise.
    std::vector<AstNodeExpr*> consComponents(AstNodeExpr* nodep) {
        std::vector<AstNodeExpr*> valueps;
        if (const AstInitArray* const initp = VN_CAST(nodep, InitArray)) {
            const size_t size = dtypeComponents(initp->dtypep()).size();
            valueps.reserve(size);
            for (size_t i = 0; i < size; ++i) {
                AstNodeExpr* const valuep = initp->getIndexDefaultedValuep(i);
                if (!valuep) return {};
                valueps.push_back(valuep);
            }
        } else if (const AstConsPackUOrStruct* const consp = VN_CAST(nodep, ConsPackUOrStruct)) {
            // Computing the components assigns the member indices
            valueps.resize(dtypeComponents(consp->dtypep()).size(), nullptr);
            size_t nValues = 0;
            for (const AstConsPackMember* mp = consp->membersp(); mp;
                 mp = VN_AS(mp->nextp(), ConsPackMember)) {
                valueps.at(static_cast<size_t>(mp->dtypep()->user1())) = mp->rhsp();
                ++nValues;
            }
            if (nValues != valueps.size()) return {};
        }
        return valueps;
    }

    // Get the split components of the given AstVar, create them if needed
    const std::vector<AstVar*>& varComponents(AstVar* varp) {
        std::vector<AstVar*>& elempsr = m_splitVarps(varp);
        if (!elempsr.empty()) return elempsr;

        // Splitting this variable, record stats
        const bool packed = isPacked(varp->dtypep());
        if (varp->user3p()) {
            ++(packed ? m_statSplitPackedComp : m_statSplitUnpackedComp);
        } else {
            ++(packed ? m_statSplitPackedOrig : m_statSplitUnpackedOrig);
        }

        // Create the split AstVars when first requested
        AstVar* newsp = nullptr;
        for (const Component& comp : dtypeComponents(varp->dtypep())) {
            const std::string name = varp->name() + comp.suffix;
            AstVar* const newp = new AstVar{varp->fileline(), varp->varType(), name, comp.dtypep};
            newp->propagateSplitAttrFrom(varp);
            newp->user3p(varp);
            elempsr.push_back(newp);
            newsp = AstNode::addNext(newsp, newp);
        }
        varp->addNextHere(newsp);

        // Return the indexable vector
        return elempsr;
    }

    // Get the split components of the given AstVarScope, create them if needed
    const std::vector<AstVarScope*>& varScopeComponents(AstVarScope* vscp) {
        std::vector<AstVarScope*>& elempsr = m_splitVscps(vscp);
        if (!elempsr.empty()) return elempsr;

        // Create the split AstVarScopes when first requested
        const std::vector<AstVar*>& varps = varComponents(vscp->varp());
        AstScope* const scopep = vscp->scopep();
        AstVarScope* newsp = nullptr;
        for (AstVar* const varp : varps) {
            AstVarScope* const newp = new AstVarScope{vscp->fileline(), scopep, varp};
            newp->user3p(vscp);
            elempsr.push_back(newp);
            newsp = AstNode::addNext(newsp, newp);
        }
        vscp->addNextHere(newsp);

        // If the original must be kept (maybe after repeated splitting),
        // drive it from the components.
        const AstVarScope* origp = vscp;
        while (origp->user3p()) origp = VN_AS(origp->user3p(), VarScope);
        const bool keep = origp->varp()->isTrace() && origp->isTrace();
        if (keep) {
            // The combinational AstActive of the scope
            AstActive* const activep = [&]() {
                if (AstNode* const existingp = scopep->user1p()) return VN_AS(existingp, Active);
                // Create new one if not yet exists
                FileLine* const flp = scopep->fileline();
                AstSenItem* const senItemp = new AstSenItem{flp, AstSenItem::Combo{}};
                AstSenTree* const senTreep = new AstSenTree{flp, senItemp};
                AstActive* const newp = new AstActive{flp, "decompose", senTreep};
                newp->senTreeStorep(newp->sentreep());
                scopep->addBlocksp(newp);
                scopep->user1p(newp);
                return newp;
            }();
            FileLine* const flp = vscp->fileline();
            AstNodeDType* const dtypep = vscp->varp()->dtypep();
            for (size_t i = 0; i < elempsr.size(); ++i) {
                AstNodeExpr* const rhsp = new AstVarRef{flp, elempsr[i], VAccess::READ};
                AstNodeExpr* const lhsRefp = new AstVarRef{flp, vscp, VAccess::WRITE};
                AstNodeExpr* const lhsp = newComponentSel(lhsRefp, dtypep, i);
                AstAlways* const alwaysp = new AstAlways{new AstAssignW{flp, lhsp, rhsp}};
                activep->addStmtsp(alwaysp);
            }
        } else {
            // Otherwise all references to the original are replaced by the end of the pass,
            // so delete it, then any reference left by mistake is caught by V3Broken. It is
            // only deleted at the end of the pass, until then, the references not yet
            // replaced can still be resolved to its components.
            VL_DO_DANGLING(pushDeletep(vscp->unlinkFrBack()), vscp);
        }

        // Return the indexable vector
        return elempsr;
    }

    // Leaf terms of a Concat/Replicate tree, in LSB order
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

    // Is 'nodep' a splittable selection path rooted at a variable reference, with only
    // constant or direct variable reference indices?
    static bool isSplittablePath(const AstNodeExpr* nodep) {
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            // Not a forced variable, while technically splittable,
            // splitting trips several bugs in V3Force.
            if (refp->varp()->isForced()) return false;
            // Not a SystemC variable, which can only be accessed whole, not selected from.
            if (refp->varp()->isSc()) return false;
            // Otherwise the path rooted here is splittable
            return true;
        }
        if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
            const AstNodeExpr* const bitp = selp->bitp();
            // Only if the index is a constant or a direct variable reference,
            // which is cheap to duplicate
            if (!VN_IS(bitp, Const) && !VN_IS(bitp, VarRef)) return false;
            // Check rest of the path
            return isSplittablePath(selp->fromp());
        }
        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            // Check rest of the path
            return isSplittablePath(selp->fromp());
        }
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            // Only if the select is a constant index, which is cheap to duplicate
            if (!VN_IS(selp->lsbp(), Const)) return false;
            // Check rest of the path
            return isSplittablePath(selp->fromp());
        }
        // Other expressions are not splittable
        return false;
    }

    // Is 'nodep' a splittable array or struct cons expression, which does not read 'vscp'?
    bool isSplittableCons(AstNodeExpr* nodep, const AstVarScope* vscp) {
        // Get the distinct values of the cons expression. Not using consComponents for arrays,
        // as the array might be large, with a default value, and never split.
        std::vector<AstNodeExpr*> valueps;
        if (const AstInitArray* const initp = VN_CAST(nodep, InitArray)) {
            const uint64_t size = static_cast<uint64_t>(
                VN_AS(initp->dtypep()->skipRefp(), UnpackArrayDType)->elementsConst());
            if (!initp->defaultp() && initp->map().size() < size) return false;
            if (initp->defaultp()) valueps.push_back(initp->defaultp());
            for (const auto& pair : initp->map()) valueps.push_back(pair.second->valuep());
        } else {
            valueps = consComponents(nodep);
        }
        // Not splittable if cannot figure out the component values
        if (valueps.empty()) return false;
        // Check each component
        for (AstNodeExpr* const valuep : valueps) {
            // Must not read 'vscp'
            const bool readsVscp = valuep->exists([&](const AstVarRef* refp) {  //
                return refp->varScopep() == vscp;
            });
            if (readsVscp) return false;
            // Must be pure
            if (!valuep->isPure()) return false;
            // An unpacked value must be splittable itself, as it is split further if the
            // component it is assigned to is split, see splitAssign. A select from another
            // unpacked expression (e.g.: a condition) is not supported downstream.
            if (isUnpacked(valuep->dtypep()) && !isSplittablePath(valuep)
                && !isSplittableCons(valuep, vscp)) {
                return false;
            }
        }
        // All good
        return true;
    }

    // Is 'nodep' a splittable concatenation with respect to 'dtypep', which does not read 'vscp'?
    bool isSplittableConcat(AstNodeExpr* nodep, AstNodeDType* dtypep, const AstVarScope* vscp) {
        if (!VN_IS(nodep, Concat) && !VN_IS(nodep, Replicate)) return false;
        int lsb = 0;  // LSB of the current term
        for (AstNodeExpr* const termp : concatTerms(nodep)) {
            const int termLsb = lsb;
            const int termMsb = lsb + termp->width() - 1;
            lsb = termMsb + 1;
            // Must not read 'vscp'
            const bool readsVscp = termp->exists([&](const AstVarRef* refp) {  //
                return refp->varScopep() == vscp;
            });
            if (readsVscp) return false;
            // Must be pure
            if (!termp->isPure()) return false;
            // Splittable path is ok, cheap to replicate
            if (isSplittablePath(termp)) continue;
            // Constant is OK
            if (VN_IS(termp, Const)) continue;
            // VarRef is ok if not forced nor SystemC (see isSplittablePath)
            if (const AstVarRef* const refp = VN_CAST(termp, VarRef)) {
                if (refp->varp()->isForced() || refp->varp()->isSc()) return false;
                continue;
            }
            // Otherwise the term must not span multiple components (would need multiple clones)
            if (componentIndex(dtypep, termLsb) != componentIndex(dtypep, termMsb)) return false;
        }
        // All good
        return true;
    }

    // Reference to component 'idx' of the split variable referenced by 'refp'
    AstVarRef* newComponentRef(FileLine* flp, const AstVarRef* refp, size_t idx) {
        AstVarScope* const vscp = varScopeComponents(refp->varScopep())[idx];
        return new AstVarRef{flp, vscp, refp->access()};
    }

    // Select component 'idx' of 'fromp', with the components of aggregate 'dtypep'
    AstNodeExpr* newComponentSel(AstNodeExpr* fromp, AstNodeDType* dtypep, size_t idx) {
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

    // CONTINUE REVIEW HERE

    // Bits 'lsb' to 'msb' of the split packed variable 'refp', from its components: the whole
    // component, a select from it, or a concatenation of the parts of those spanned, when the
    // bits come from a different packed layout. Unless the bits are exactly one whole
    // component, a component already split is read from its own components in turn, as a
    // reference to it in the result would block it, see visit(AstVarRef).
    AstNodeExpr* newComponentBits(const AstVarRef* refp, int lsb, int msb) {
        FileLine* const flp = refp->fileline();
        AstNodeDType* const dtypep = dtypeOf(refp);
        const std::vector<Component>& compsr = dtypeComponents(dtypep);
        AstNodeExpr* resultp = nullptr;
        for (size_t i = componentIndex(dtypep, lsb); i < compsr.size() && compsr[i].lsb <= msb;
             ++i) {
            const Component& comp = compsr[i];
            AstVarRef* const compRefp = newComponentRef(flp, refp, i);
            const int partLsb = std::max(lsb, comp.lsb);
            const int partMsb = std::min(msb, comp.msb);
            const bool exactlyComp = lsb == comp.lsb && msb == comp.msb;
            AstNodeExpr* bitsp = compRefp;
            if (!exactlyComp && m_splitVscps.tryGet(compRefp->varScopep())) {
                bitsp = newComponentBits(compRefp, partLsb - comp.lsb, partMsb - comp.lsb);
                VL_DO_DANGLING(compRefp->deleteTree(), compRefp);
            } else if (partLsb != comp.lsb || partMsb != comp.msb) {
                bitsp = new AstSel{flp, bitsp, partLsb - comp.lsb, partMsb - partLsb + 1};
            }
            // Higher parts go to the left
            resultp = resultp ? new AstConcat{flp, bitsp, resultp} : bitsp;
        }
        return resultp;
    }

    // Get the 'idx' component of the split expression 'nodep', with the components of 'dtypep'
    AstNodeExpr* newSplit(AstNodeExpr* nodep, AstNodeDType* dtypep, size_t idx) {
        const AstVarRef* const refp = VN_CAST(nodep, VarRef);
        if (shouldSplit(refp)) {
            // Packed, the variable may have a different layout, assemble the bits from its
            // components
            if (isPacked(dtypep)) {
                const Component& comp = dtypeComponents(dtypep).at(idx);
                return newComponentBits(refp, comp.lsb, comp.msb);
            }
            return newComponentRef(refp->fileline(), refp, idx);
        }
        // A value not being split, select the component from it
        return newComponentSel(nodep->cloneTree(false), dtypep, idx);
    }

    // Values of the components of 'nodep', with the components of 'dtypep': for a reset, a cons
    // or a concatenation cloned from it, otherwise selected from it, see newSplit.
    std::vector<AstNodeExpr*> newAssignRhsps(AstNodeExpr* nodep, AstNodeDType* dtypep) {
        // A reset of each component
        if (AstCReset* const cresetp = VN_CAST(nodep, CReset)) {
            std::vector<AstNodeExpr*> resetps;
            for (const Component& comp : dtypeComponents(dtypep)) {
                AstCReset* const newp = cresetp->cloneTree(false);
                newp->dtypep(comp.dtypep);
                resetps.push_back(newp);
            }
            return resetps;
        }
        std::vector<AstNodeExpr*> valueps = consComponents(nodep);
        for (size_t i = 0; i < valueps.size(); ++i) {
            valueps[i] = valueps[i]->cloneTreePure(false);
            // A struct cons value has the member as its type, which must not outlive the
            // struct, as V3Dead keeps a struct with referenced members, but not its package
            valueps[i]->dtypep(dtypeComponents(dtypep)[i].dtypep);
        }
        if (!valueps.empty()) return valueps;
        if (!VN_IS(nodep, Concat) && !VN_IS(nodep, Replicate)) {
            const size_t size = dtypeComponents(dtypep).size();
            valueps.reserve(size);
            for (size_t i = 0; i < size; ++i) valueps.push_back(newSplit(nodep, dtypep, i));
            return valueps;
        }
        // Assemble each component from the parts of the terms overlapping it
        const std::vector<Component>& compsr = dtypeComponents(dtypep);
        valueps.resize(compsr.size(), nullptr);
        int lsb = 0;  // LSB of the current term
        for (AstNodeExpr* const termp : concatTerms(nodep)) {
            const int msb = lsb + termp->width() - 1;
            for (size_t i = componentIndex(dtypep, lsb); i < compsr.size() && compsr[i].lsb <= msb;
                 ++i) {
                const Component& comp = compsr[i];
                const int partLsb = std::max(lsb, comp.lsb);
                const int partMsb = std::min(msb, comp.msb);
                AstNodeExpr* partp = termp->cloneTreePure(false);
                if (partLsb != lsb || partMsb != msb) {
                    partp = new AstSel{termp->fileline(), partp, partLsb - lsb,
                                       partMsb - partLsb + 1};
                }
                // Higher parts go to the left
                valueps[i]
                    = valueps[i] ? new AstConcat{termp->fileline(), partp, valueps[i]} : partp;
            }
            lsb = msb + 1;
        }
        return valueps;
    }

    // Split the candidate, if still possible: a variable might have been blocked since the
    // candidate was recorded due to other references. Returns the replacement, or nullptr.
    AstVarRef* splitSelect(AstArraySel* nodep) {
        AstVarRef* const fromp = VN_AS(nodep->fromp(), VarRef);
        // Needs the variable selected from to be splittable
        if (!canSplit(fromp)) return nullptr;
        const size_t index = VN_AS(nodep->bitp(), Const)->toUInt();
        return newComponentRef(nodep->fileline(), fromp, index);
    }
    AstVarRef* splitSelect(AstStructSel* nodep) {
        AstVarRef* const fromp = VN_AS(nodep->fromp(), VarRef);
        // Needs the variable selected from to be splittable
        if (!canSplit(fromp)) return nullptr;
        AstStructDType* const dtypep = VN_AS(dtypeOf(fromp)->skipRefp(), StructDType);
        dtypeComponents(dtypep);  // Assigns the member indices
        const AstNode* const memberp = m_memberMap.findMember(dtypep, nodep->name());
        UASSERT_OBJ(memberp, nodep, "Struct member not found: " << nodep->name());
        const size_t index = static_cast<size_t>(memberp->user1());
        return newComponentRef(nodep->fileline(), fromp, index);
    }
    AstNodeExpr* splitSelect(AstSel* nodep) {
        AstVarRef* const fromp = VN_AS(nodep->fromp(), VarRef);
        // Needs the variable selected from to be splittable
        if (!canSplit(fromp)) return nullptr;
        // Within one component, so the whole component, or a select from it
        const int lsb = VN_AS(nodep->lsbp(), Const)->toSInt();
        return newComponentBits(fromp, lsb, lsb + nodep->widthConst() - 1);
    }
    AstNodeExpr* splitSelect(AstNodeExpr* nodep) {
        if (AstArraySel* const selp = VN_CAST(nodep, ArraySel)) return splitSelect(selp);
        if (AstStructSel* const selp = VN_CAST(nodep, StructSel)) return splitSelect(selp);
        return splitSelect(VN_AS(nodep, Sel));
    }
    // Expand the assignment component-wise, or nullptr if neither side is to be split
    AstNodeAssign* splitAssign(AstNodeAssign* assp) {
        AstNodeExpr* const lhsp = assp->lhsp();
        AstNodeExpr* const rhsp = assp->rhsp();
        const AstVarRef* const lRefp = VN_CAST(lhsp, VarRef);
        const AstVarRef* const rRefp = VN_CAST(rhsp, VarRef);
        // Needs either side to be split, the components are selected from the other. If the
        // other side can be split, the selects from it in the expanded assignments are
        // candidates, so it is split too.
        const bool lShouldSplit = shouldSplit(lRefp);
        const bool rShouldSplit = shouldSplit(rRefp);
        if (!lShouldSplit && !rShouldSplit) return nullptr;
        // Only the packed RHS is split, and the LHS cannot be: assign the whole value assembled
        // from the components of the RHS, rather than each to its bits of the LHS, which would
        // be a partial write each. If the LHS can be split, it is expanded below, so the
        // selects from it make it split too.
        if (!canSplit(lRefp) && isPacked(dtypeOf(rhsp))) {
            UASSERT_OBJ(rShouldSplit, assp, "RHS should be split");
            AstNodeExpr* const newRhsp = newComponentBits(rRefp, 0, dtypeOf(rhsp)->width() - 1);
            return assp->cloneType(lhsp->cloneTree(false), newRhsp);
        }
        AstNodeDType* const dtypep = lShouldSplit ? dtypeOf(lhsp) : dtypeOf(rhsp);
        // Unpacked arrays are assigned by position from the left (IEEE 1800-2023 7.6), but
        // components are indexed by storage slot, so if the ranges have opposite directions,
        // the RHS components are in reverse order. Nested levels are handled when the expanded
        // assignments are split in turn.
        const bool reversed = [&]() {
            const AstUnpackArrayDType* const lArrayp
                = VN_CAST(dtypeOf(lhsp)->skipRefp(), UnpackArrayDType);
            if (!lArrayp) return false;
            const AstUnpackArrayDType* const rArrayp
                = VN_AS(dtypeOf(rhsp)->skipRefp(), UnpackArrayDType);
            return lArrayp->declRange().ascending() != rArrayp->declRange().ascending();
        }();
        const std::vector<AstNodeExpr*> valueps = newAssignRhsps(rhsp, dtypep);
        const size_t size = valueps.size();
        AstNodeAssign* newsp = nullptr;
        for (size_t i = 0; i < size; ++i) {
            const size_t rIdx = reversed ? size - 1 - i : i;
            AstNodeExpr* const newLhsp = newSplit(lhsp, dtypep, i);
            AstNodeExpr* const newRhsp = valueps[rIdx];
            AstNodeAssign* newp = assp->cloneType(newLhsp, newRhsp);
            // If the LHS component is already split, expand into its components right away. The
            // assignment to it might not be a candidate, and visiting it would block it.
            const AstVarRef* const compRefp = VN_CAST(newLhsp, VarRef);
            if (compRefp && m_splitVscps.tryGet(compRefp->varScopep())) {
                AstNodeAssign* const subsp = splitAssign(newp);
                UASSERT_OBJ(subsp, newp, "Assignment to split component not split");
                VL_DO_DANGLING(newp->deleteTree(), newp);
                newp = subsp;
            }
            newsp = AstNode::addNext(newsp, newp);
        }
        return newsp;
    }
    // REVIEW OK BELOW

    // Split the current select candidates. Splitting can reveal new candidates,
    // which are recorded for the next round.
    void splitSelects() {
        // Take current candidates, will add new ones as we go after splitting
        std::vector<AstNodeExpr*> candidates;
        candidates.swap(m_selectCandidates);

        // Split each candidate
        for (AstNodeExpr* const nodep : candidates) {
            // Split it, if still possible
            AstNodeExpr* const newp = splitSelect(nodep);
            if (!newp) continue;

            // The variable selected from is now split, so wake the assignments waiting for it.
            // An assignment might have been woken by its other side already, and even split
            // since, which is safe to check, as nodes are only deleted at the end of the pass.
            const AstVarScope* const vscp = [&]() {
                const AstNodeExpr* fromp;
                if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
                    fromp = selp->fromp();
                } else if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
                    fromp = selp->fromp();
                } else {
                    fromp = VN_AS(nodep, Sel)->fromp();
                }
                return VN_AS(fromp, VarRef)->varScopep();
            }();
            if (std::vector<AstNodeAssign*>* const waitingp = m_waitingAssigns.tryGet(vscp)) {
                for (AstNodeAssign* const assp : *waitingp) {
                    if (assp->user2() != 2) continue;  // Already woken
                    assp->user2(1);  // Mark as recorded
                    m_assignCandidates.push_back(assp);
                }
                waitingp->clear();
            }

            // Replace the candidate with the new split node
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);

            // Record/mark for the next round. A whole component is a single reference,
            // so visit its new parent context, if that might be a further splitting candidate.
            AstNode* const parentp = newp->firstAbovep();
            const bool possibleCandidate = VN_IS(newp, VarRef)  //
                                           && (VN_IS(parentp, ArraySel)  //
                                               || VN_IS(parentp, StructSel)  //
                                               || VN_IS(parentp, Sel)  //
                                               || VN_IS(parentp, Assign)  //
                                               || VN_IS(parentp, AssignW)  //
                                               || VN_IS(parentp, AssignDly));
            if (possibleCandidate) {
                iterateConst(parentp);
                continue;
            }

            // Otherwise visit the new node for recording/marking
            iterateConst(newp);
        }
    }

    // Split the current assignment candidates. Splitting can reveal new candidates,
    // which are recorded for the next round.
    void splitAssignments() {
        UASSERT(m_selectCandidates.empty(), "Select candidates remain");
        // Take current candidates, will add new ones as we go after splitting
        std::vector<AstNodeAssign*> candidates;
        candidates.swap(m_assignCandidates);

        // Split each candidate
        for (AstNodeAssign* const assp : candidates) {
            // If neither side is to be split yet, but a side can be split, that side might be
            // split later, when a copy of it to or from a split variable is expanded. Wait
            // for that, see splitSelects. Assignments still waiting at the end are not
            // split.
            const AstVarRef* const lRefp = VN_CAST(assp->lhsp(), VarRef);
            const AstVarRef* const rRefp = VN_CAST(assp->rhsp(), VarRef);
            const bool lCan = canSplit(lRefp);
            const bool rCan = canSplit(rRefp);
            if (!shouldSplit(lRefp) && !shouldSplit(rRefp) && (lCan || rCan)) {
                assp->user2(2);  // Mark as waiting
                if (lCan) m_waitingAssigns(lRefp->varScopep()).push_back(assp);
                if (rCan) m_waitingAssigns(rRefp->varScopep()).push_back(assp);
                continue;
            }

            // Split it, if still possible
            AstNodeAssign* const newp = splitAssign(assp);
            if (!newp) continue;

            // Replace the candidate with the new split assignments
            assp->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(assp), assp);

            // Visit the new assignments for recording/marking for the next round
            iterateAndNextConstNull(newp);
        }
    }

    // Assignment visitor, shared by the assignment types that can be split
    void visitAssignment(AstNodeAssign* nodep) {
        // Must not have timing control
        if (nodep->timingControlp()) {
            // Descend to record candidates or block variables
            iterateChildrenConst(nodep);
            return;
        }

        AstNodeExpr* const lhsp = nodep->lhsp();
        AstNodeExpr* const rhsp = nodep->rhsp();

        const bool lCan = canSplit(VN_CAST(lhsp, VarRef));
        const bool rCan = canSplit(VN_CAST(rhsp, VarRef));

        // Both sides are splittable references
        if (lCan && rCan) {
            recordAssignCandidate(nodep);
            return;
        }

        // The LHS is a splittable reference, the RHS must be a splittable expression
        if (lCan) {
            const AstVarScope* const lVscp = VN_AS(lhsp, VarRef)->varScopep();
            AstNodeDType* const lDTypep = dtypeOf(lhsp);
            const bool packed = isPacked(lDTypep);
            const bool splittable = VN_IS(rhsp, CReset)  //
                                    || isSplittablePath(rhsp)  //
                                    || (packed && VN_IS(rhsp, Const))  //
                                    || (packed && isSplittableConcat(rhsp, lDTypep, lVscp))  //
                                    || (!packed && isSplittableCons(rhsp, lVscp));
            if (splittable) {
                iterateConst(rhsp);  // Still need to gather candidates in it
                recordAssignCandidate(nodep);
                return;
            }
        }

        // The RHS is a splittable reference, the LHS must be a splittable expression
        if (rCan) {
            const bool splittable = isSplittablePath(lhsp);  // Only one form for now
            if (splittable) {
                iterateConst(lhsp);  // Still need to gather candidates in it
                recordAssignCandidate(nodep);
                return;
            }
        }

        // Otherwise descend to record candidates or block variables
        iterateChildrenConst(nodep);
    }

    // VISITORS - descent
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstActive* nodep) override {
        // Record the combinational AstActive of the scope for reuse
        if (nodep->hasCombo() && !m_scopep->user1p()) m_scopep->user1p(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeDType*) override {}  // No references in data types
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // VISITORS - potentially splittable constructs
    void visit(AstArraySel* nodep) override {
        // Record if candidate
        const AstVarRef* const fromp = VN_CAST(nodep->fromp(), VarRef);
        if (canSplit(fromp)) {
            // Constant select, in bounds. Not using dtypeComponents, as the array might be large
            // and never split.
            if (const AstConst* const bitp = VN_CAST(nodep->bitp(), Const)) {
                const AstUnpackArrayDType* const arrayp
                    = VN_AS(dtypeOf(fromp)->skipRefp(), UnpackArrayDType);
                if (bitp->toUQuad() < static_cast<uint64_t>(arrayp->elementsConst())) {
                    recordSelectCandidate(nodep);
                    return;
                }
            }
        }
        // Otherwise descend to record candidates or block variables
        iterateChildrenConst(nodep);
    }
    void visit(AstStructSel* nodep) override {
        // Record if candidate
        const AstVarRef* const fromp = VN_CAST(nodep->fromp(), VarRef);
        if (canSplit(fromp)) {
            recordSelectCandidate(nodep);
            return;
        }
        // Otherwise descend to record candidates or block variables
        iterateChildrenConst(nodep);
    }
    void visit(AstSel* nodep) override {
        // Record if candidate
        AstVarRef* const fromp = VN_CAST(nodep->fromp(), VarRef);
        if (canSplit(fromp)) {
            // Constant select, in bounds, and not crossing component boundaries
            if (const AstConst* const lsbp = VN_CAST(nodep->lsbp(), Const)) {
                const int lsb = lsbp->toSInt();
                const int msb = lsb + nodep->widthConst() - 1;
                AstNodeDType* const dtypep = dtypeOf(fromp);
                if (dtypep->width() > msb && lsb >= 0) {
                    if (componentIndex(dtypep, lsb) == componentIndex(dtypep, msb)) {
                        recordSelectCandidate(nodep);
                        return;
                    }
                }
            }
        }
        // Otherwise descend to record candidates or block variables
        iterateChildrenConst(nodep);
    }
    void visit(AstAssign* nodep) override { visitAssignment(nodep); }
    void visit(AstAssignW* nodep) override { visitAssignment(nodep); }
    void visit(AstAssignDly* nodep) override { visitAssignment(nodep); }

    // VISITORS - non splittable constructs
    void visit(AstVarRef* nodep) override {
        // A reference not explicitly found in the splittable constructs is not splittable
        AstVarScope* const vscp = nodep->varScopep();
        AstVar* const varp = vscp->varp();
        if (!isEligible(varp)) return;
        vscp->user2(true);  // Mark blocked
        warnNoSplit(varp, nodep, "it is referenced in an unsupported way");
    }
    void visit(AstMemberSel* nodep) override {
        iterateChildrenConst(nodep);
        AstVar* const varp = nodep->varp();
        if (!isEligible(varp)) return;
        varp->user2(2);  // Mark not eligible
        warnNoSplit(varp, nodep, "it is accessed indirectly");
    }

    // CONSTRUCTORS
    explicit DecomposeVisitor(AstNetlist* netlistp) {
        // Gather AstVarScopes that might be split, and their references
        iterateConst(netlistp);

        // Split them, in rounds, until no candidates remain. All selects are split before the
        // assignments, then the selects revealed by expanding the assignments, and so on.
        while (!m_selectCandidates.empty() || !m_assignCandidates.empty()) {
            while (!m_selectCandidates.empty()) splitSelects();
            splitAssignments();
        }

        V3Stats::addStat("Optimizations, Decompose, unpacked variables split",
                         m_statSplitUnpackedOrig);
        V3Stats::addStat("Optimizations, Decompose, packed variables split",
                         m_statSplitPackedOrig);
        V3Stats::addStat("Optimizations, Decompose, unpacked components split",
                         m_statSplitUnpackedComp);
        V3Stats::addStat("Optimizations, Decompose, packed components split",
                         m_statSplitPackedComp);
    }

public:
    static void apply(AstNetlist* netlistp) { DecomposeVisitor{netlistp}; }
};

//######################################################################
// V3Decompose class functions

void V3Decompose::decomposeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    DecomposeVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("decompose", 0, dumpTreeEitherLevel() >= 3);
}
