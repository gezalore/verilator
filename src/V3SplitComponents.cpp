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
// V3SplitComponents replaces variables of unpacked array, unpacked struct,
// packed array, or packed struct type with one variable per element/member
// (component). This avoids UNOPTFLAT and enables further optimization of the
// individual components.
//
// A variable is split unless it is of a kind that cannot be split (primary IO,
// public, forceable, etc.), or it is referenced other than in these candidate
// constructs:
//   - ARRAYSEL(VARREF, CONST), of an unpacked array
//   - STRUCTSEL(VARREF), of an unpacked struct
//   - SEL(VARREF, CONST), of a packed type, with the bits within one component
//   - the whole LHS of an assignment, where the RHS is:
//     - a select path, with constant or variable indices, and constant bit
//       selects (e.g. 'a = b[i].c', 'a = b[i][7:0]')
//     - a CRESET
//     - for unpacked types, a pure CONSPACKUORSTRUCT or INITARRAY independent
//       of the variable, the component values are cloned
//     - for packed types, a constant, or a CONCAT with operands aligned with the
//       components, the operands are moved
//   - the whole RHS of an assignment, where the LHS is:
//     - a select path, with constant or variable indices, and constant bit
//       selects (e.g. 'b[i].c = a', 'b[i][7:0] = a')
// Components of packed types correspond by bit position, so the value on the
// other side of an assignment can be of any packed type of the same width. If
// it is split too, each component is assembled from the bits of its components.
//
// A traversal records the candidates, and marks variables referenced in any
// other way as unsupported. It also marks variables selected from by a select
// candidate. Variables only copied whole are not split, as that would only
// expand the copies, unless marked with split_var. Then the candidates are split
// in rounds. Selects
// are replaced with references to the components, or for packed types, a
// select from the component. Assignments are expanded component-wise,
// selecting the components from a side that is not split, or assembling them
// from the components of a split packed RHS. Replacing a select
// can make it, or its parent, a candidate, which is recorded for the next
// round, or reveal an unsupported use of the component, which is marked. All
// references to a component are created in the round its parent is split, and
// its candidates are only split in the next round, so a component is always
// marked before any of its candidates are split. An assignment containing
// selects still pending is postponed until they are split, as expanding it
// would delete or move them.
//
// The component AstVars are shared between all scopes of the original AstVar,
// each split AstVarScope gets its own component AstVarScopes. If the original
// is traced, it is kept and driven from the components, so the trace is
// unchanged. Other originals are left unreferenced, for V3Dead to remove.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3SplitComponents.h"

#include "V3AstUserAllocator.h"
#include "V3MemberMap.h"
#include "V3Stats.h"

#include <algorithm>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class SplitComponentsVisitor final : public VNVisitor {
    // TYPES

    // A component (element or member) of a splittable type
    struct Component final {
        std::string suffix;  // Name suffix of the variable for the component
        AstNodeDType* dtypep;  // Type of the component
        int lsb;  // LSB in the whole value, if packed
        int msb;  // MSB in the whole value, if packed
        AstMemberDType* memberp;  // The member, if a struct
    };

    // NODE STATE
    //  AstVar::user1()             -> Split elements, via m_splitVarps
    //  AstVarScope::user1()        -> Split elements, via m_splitVscps
    //  AstNodeDType::user1()       -> Components of struct or array types, via m_componentsOf
    //  AstMemberDType::user1()     -> uint64_t: index of the member, set by componentsOf()
    //  AstScope::user1p()          -> AstActive*: combinational active of the scope, if any
    //  AstVar::user2()             -> int: bit 0: supported, bit 1: evaluated (isSupported)
    //  AstVarScope::user2()        -> bool: marked as unsupported
    //  Candidate nodes::user2()    -> int: 1: recorded, pending, 2: processed or skipped
    //  AstVarScope::user3p()       -> AstVarScope*, variable this was split from
    //  AstVar::user3p()            -> AstVar*, variable this was split from
    //  AstVar::user4()             -> bool: warned that it will not be split
    //  AstVarScope::user4()        -> bool: selected from by a candidate, not only copied whole
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;
    const VNUser4InUse m_user4InUse;
    AstUser1Allocator<AstVar, std::vector<AstVar*>> m_splitVarps;
    AstUser1Allocator<AstVarScope, std::vector<AstVarScope*>> m_splitVscps;
    AstUser1Allocator<AstNodeDType, std::vector<Component>> m_componentsOf;

    // STATE
    std::vector<AstNode*> m_candidates;  // Constructs that can be split
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

    // Packed array or packed struct
    static bool isPacked(const AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (VN_IS(dtypep, PackArrayDType)) return true;
        const AstStructDType* const structp = VN_CAST(dtypep, StructDType);
        return structp && structp->packed();
    }

    // A type this pass can split
    static bool isSplittable(const AstNodeDType* dtypep) {
        return isUnpacked(dtypep) || isPacked(dtypep);
    }

    // Type of the value of the expression. For a variable reference, the type of the variable,
    // which determines the components: the reference itself can have a different type of the
    // same width, e.g. a plain vector referencing a packed struct, after V3Const.
    static AstNodeDType* typeOf(const AstNodeExpr* nodep) {
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) return refp->varp()->dtypep();
        return nodep->dtypep();
    }

    // Reason why the kind of the variable prevents splitting, nullptr if it does not
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

    // Is the variable supported by this pass. Its eligibility is evaluated on first use, so
    // it is known even if a reference is visited before the AstVar itself.
    bool isSupported(AstVar* varp) {
        if (varp->user2()) return varp->user2() & 1;
        const bool supported = [&]() {
            // Not the job of this pass to split
            if (!isSplittable(varp->dtypep())) return false;
            // This pass should split, warn that it cannot be split
            if (const char* const reasonp = cannotSplitKindReason(varp)) {
                warnNoSplit(varp, varp, reasonp);
                return false;
            }
            return true;
        }();
        varp->user2(2 | supported);
        return supported;
    }

    // Is this reference to a supported variable. When called during the traversal it might
    // return true for a reference that is only found to be used in an unsupported way later.
    bool isSupported(const AstVarRef* nodep) {
        if (!nodep) return false;
        const AstVarScope* const vscp = nodep->varScopep();
        return isSupported(vscp->varp()) && !vscp->user2();
    }

    // Is this reference to a variable to be split: supported, and selected from by a candidate,
    // not only copied whole, or marked with split_var. Only known after the candidates of the
    // variable are recorded.
    bool shouldSplit(const AstVarRef* nodep) {
        if (!isSupported(nodep)) return false;
        return nodep->varScopep()->user4() || nodep->varp()->attrSplitVar();
    }

    // Record candidate select from 'fromp', marking the variable as selected from
    void recordSelect(AstNode* nodep, const AstVarRef* fromp) {
        fromp->varScopep()->user4(true);
        recordCandidate(nodep);
    }

    // Components of a splittable type. Indexed in storage order, that is:
    // - For packed arrays, component 0 is in the LSBs
    // - For packed structs, component 0 is the last declared member, in the LSBs
    // - For unpacked arrays, component 0 is in storage slot 0 at runtime
    // - For unpacked structs, component 0 is the last declared member, to match packed
    const std::vector<Component>& componentsOf(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        UASSERT_OBJ(isSplittable(dtypep), dtypep, "Components of non-splittable type");

        // Cached via user1
        std::vector<Component>& compsr = m_componentsOf(dtypep);

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
                    compsr.push_back({"__BRA__" + idx + "__KET__", subp, lsb, msb, nullptr});
                }
            } else {
                const AstStructDType* const structp = VN_AS(dtypep, StructDType);
                for (AstMemberDType* mp = structp->membersp(); mp;
                     mp = VN_AS(mp->nextp(), MemberDType)) {
                    const int msb = mp->lsb() + mp->width() - 1;
                    compsr.push_back(
                        {"__DOT__" + mp->name(), mp->subDTypep(), mp->lsb(), msb, mp});
                }
                std::reverse(compsr.begin(), compsr.end());
                for (size_t i = 0; i < compsr.size(); ++i) {
                    compsr[i].memberp->user1(static_cast<uint64_t>(i));
                }
            }
        }

        // Components
        return compsr;
    }

    // Index of the component of a packed type containing bit 'lsb'
    size_t componentIndex(AstNodeDType* dtypep, int lsb) {
        const std::vector<Component>& compsr = componentsOf(dtypep);
        // The first component ending above the bit - binary search
        const auto it = std::lower_bound(compsr.begin(), compsr.end(), lsb,
                                         [](const Component& comp, int bit) {  //
                                             return bit > comp.msb;
                                         });
        return static_cast<size_t>(it - compsr.begin());
    }

    // Is the bit range within one component of a packed type
    bool isWithinComponent(AstNodeDType* dtypep, int lsb, int msb) {
        if (lsb < 0 || msb >= dtypep->width()) return false;
        const Component& comp = componentsOf(dtypep).at(componentIndex(dtypep, lsb));
        return msb <= comp.msb;
    }

    // Value of element 'idx' if 'nodep' is an array or struct cons, nullptr otherwise
    AstNodeExpr* consElemp(AstNodeExpr* nodep, size_t idx) {
        if (const AstInitArray* const initp = VN_CAST(nodep, InitArray)) {
            return initp->getIndexDefaultedValuep(idx);
        }
        if (const AstConsPackUOrStruct* const consp = VN_CAST(nodep, ConsPackUOrStruct)) {
            const AstMemberDType* const memberp = componentsOf(consp->dtypep()).at(idx).memberp;
            for (AstConsPackMember* mp = consp->membersp(); mp;
                 mp = VN_AS(mp->nextp(), ConsPackMember)) {
                if (mp->dtypep() == memberp) return mp->rhsp();
            }
        }
        return nullptr;
    }

    // Operands of a concatenation tree, in LSB order
    static std::vector<AstNodeExpr*> concatOperands(AstNodeExpr* nodep) {
        std::vector<AstNodeExpr*> operandsr;
        std::vector<AstNodeExpr*> stack{nodep};
        while (!stack.empty()) {
            AstNodeExpr* const exprp = stack.back();
            stack.pop_back();
            if (AstConcat* const concatp = VN_CAST(exprp, Concat)) {
                // The RHS is the lower part, so popped first
                stack.push_back(concatp->lhsp());
                stack.push_back(concatp->rhsp());
            } else {
                operandsr.push_back(exprp);
            }
        }
        return operandsr;
    }

    // Select path rooted at a variable reference, so can be cloned and selected from. Indices
    // must be constants or variable references: these are read again by each expanded
    // assignment, but are scalars, so cannot be written by them. Bit selects must have a
    // constant LSB.
    static bool isPath(const AstNodeExpr* nodep) {
        // Not rooted at a forced variable, the expanded assignments would access it by element
        // or member, which trips several bugs in V3Force. Nor at a SystemC variable, which can
        // only be accessed whole.
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            return !refp->varp()->isForced() && !refp->varp()->isSc();
        }
        if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
            const AstNodeExpr* const bitp = selp->bitp();
            if (!VN_IS(bitp, Const) && !VN_IS(bitp, VarRef)) return false;
            return isPath(selp->fromp());
        }
        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            return isPath(selp->fromp());
        }
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            if (!VN_IS(selp->lsbp(), Const)) return false;
            return isPath(selp->fromp());
        }
        return false;
    }

    // Unpacked components correspond one to one, at all levels
    static bool isSameShape(const AstNodeDType* ap, const AstNodeDType* bp) {
        ap = ap->skipRefp();
        bp = bp->skipRefp();
        const AstUnpackArrayDType* const aArrayp = VN_CAST(ap, UnpackArrayDType);
        const AstUnpackArrayDType* const bArrayp = VN_CAST(bp, UnpackArrayDType);
        if (!aArrayp || !bArrayp) return ap == bp;
        UASSERT_OBJ(aArrayp->elementsConst() == bArrayp->elementsConst(), ap,
                    "Assignment between arrays of different size");
        if (aArrayp->declRange().ascending() != bArrayp->declRange().ascending()) return false;
        if (!isUnpacked(aArrayp->subDTypep())) return true;
        return isSameShape(aArrayp->subDTypep(), bArrayp->subDTypep());
    }

    // Array or struct cons with pure component values that do not read 'vscp'. The values are
    // cloned into the expanded assignments, which are not simultaneous, so must not read the
    // variable written by them.
    bool isIndependentCons(AstNodeExpr* nodep, const AstVarScope* vscp) {
        if (!VN_IS(nodep, InitArray) && !VN_IS(nodep, ConsPackUOrStruct)) return false;
        for (size_t i = 0; i < componentsOf(nodep->dtypep()).size(); ++i) {
            AstNodeExpr* const valuep = consElemp(nodep, i);
            if (!valuep || !valuep->isPure()) return false;
            const bool readsVar = valuep->exists([&](const AstVarRef* refp) {  //
                return refp->varScopep() == vscp;
            });
            if (readsVar) return false;
        }
        return true;
    }

    // Concatenation with an operand boundary at each component boundary of packed 'dtypep'
    bool isAlignedConcat(AstNodeDType* dtypep, AstNodeExpr* nodep) {
        if (!VN_IS(nodep, Concat)) return false;
        const std::vector<AstNodeExpr*> operands = concatOperands(nodep);
        // Both in LSB order, walk the operand boundaries up to each component boundary
        auto it = operands.begin();
        int lsb = 0;
        for (const Component& comp : componentsOf(dtypep)) {
            while (lsb < comp.lsb) lsb += (*it++)->width();
            if (lsb != comp.lsb) return false;
        }
        return true;
    }

    // Record candidate, unless already recorded
    void recordCandidate(AstNode* nodep) {
        if (nodep->user2()) return;
        nodep->user2(1);  // Pending
        m_candidates.push_back(nodep);
    }

    // Traced, so must be kept, and driven from the components
    static bool isKept(const AstVarScope* vscp) {
        if (vscp->user3p()) return isKept(VN_AS(vscp->user3p(), VarScope));
        const AstVar* const varp = vscp->varp();
        return varp->isTrace() && vscp->isTrace();
    }

    // Select component 'idx' of 'fromp', with the components of splittable 'dtypep'
    AstNodeExpr* newSel(AstNodeExpr* fromp, AstNodeDType* dtypep, size_t idx) {
        FileLine* const flp = fromp->fileline();
        const Component& comp = componentsOf(dtypep).at(idx);
        // Unpacked array, it's an ArraySel
        if (VN_IS(dtypep->skipRefp(), UnpackArrayDType)) {
            return new AstArraySel{flp, fromp, static_cast<int>(idx)};
        }
        // Packed, it's a Sel of the bits
        if (isPacked(dtypep)) {
            AstSel* const selp = new AstSel{flp, fromp, comp.lsb, comp.dtypep->width()};
            selp->dtypep(comp.dtypep);
            return selp;
        }
        // Otherwise must be an unpacked struct, so a StructSel
        AstStructSel* const selp = new AstStructSel{flp, fromp, comp.memberp->name()};
        selp->dtypep(comp.dtypep);
        return selp;
    }

    // Get the split components of the given AstVar, create them if needed
    const std::vector<AstVar*>& components(AstVar* varp) {
        std::vector<AstVar*>& elempsr = m_splitVarps(varp);
        if (!elempsr.empty()) return elempsr;

        // Splitting this variable, record stats
        if (varp->user3p()) {
            ++(isPacked(varp->dtypep()) ? m_statSplitPackedComp : m_statSplitUnpackedComp);
        } else {
            ++(isPacked(varp->dtypep()) ? m_statSplitPackedOrig : m_statSplitUnpackedOrig);
        }

        // Create the split AstVars when first requested
        AstVar* newsp = nullptr;
        for (const Component& comp : componentsOf(varp->dtypep())) {
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

    // The combinational AstActive of the scope, for the logic driving kept originals. The
    // existing one found during the traversal, or a new one if there is none.
    static AstActive* combActive(AstScope* scopep) {
        if (AstNode* const activep = scopep->user1p()) return VN_AS(activep, Active);
        FileLine* const flp = scopep->fileline();
        AstSenTree* const senTreep = new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Combo{}}};
        AstActive* const activep = new AstActive{flp, "split-components", senTreep};
        activep->senTreeStorep(activep->sentreep());
        scopep->addBlocksp(activep);
        scopep->user1p(activep);
        return activep;
    }

    // Get the split components of the given AstVarScope, create them if needed
    const std::vector<AstVarScope*>& components(AstVarScope* vscp) {
        std::vector<AstVarScope*>& elempsr = m_splitVscps(vscp);
        if (!elempsr.empty()) return elempsr;

        // Create the split AstVarScopes when first requested
        const std::vector<AstVar*>& varps = components(vscp->varp());
        AstScope* const scopep = vscp->scopep();
        AstVarScope* newsp = nullptr;
        for (AstVar* const varp : varps) {
            AstVarScope* const newp = new AstVarScope{vscp->fileline(), scopep, varp};
            newp->user3p(vscp);
            elempsr.push_back(newp);
            newsp = AstNode::addNext(newsp, newp);
        }
        vscp->addNextHere(newsp);

        // If the original is kept (maybe after repeated splitting), drive it from the components
        if (isKept(vscp)) {
            FileLine* const flp = vscp->fileline();
            AstNodeDType* const dtypep = vscp->varp()->dtypep();
            for (size_t i = 0; i < elempsr.size(); ++i) {
                AstNodeExpr* const rhsp = new AstVarRef{flp, elempsr[i], VAccess::READ};
                AstNodeExpr* const lhsp
                    = newSel(new AstVarRef{flp, vscp, VAccess::WRITE}, dtypep, i);
                AstAlways* const alwaysp = new AstAlways{new AstAssignW{flp, lhsp, rhsp}};
                combActive(scopep)->addStmtsp(alwaysp);
            }
        }

        // Return the indexable vector
        return elempsr;
    }

    // Get the 'idx' component of the split expression 'nodep', with the components of 'dtypep'
    AstNodeExpr* newSplit(AstNodeExpr* nodep, AstNodeDType* dtypep, size_t idx) {
        const AstVarRef* const refp = VN_CAST(nodep, VarRef);
        if (shouldSplit(refp)) {
            AstVarScope* const vscp = components(refp->varScopep())[idx];
            return new AstVarRef{refp->fileline(), vscp, refp->access()};
        }
        // A value not being split, select the component from it
        return newSel(nodep->cloneTree(false), dtypep, idx);
    }

    // Bits 'lsb' to 'msb' of the split packed variable 'refp', from its components: the whole
    // component, a select from it, or a concatenation of the parts of those spanned
    AstNodeExpr* newBits(const AstVarRef* refp, int lsb, int msb) {
        FileLine* const flp = refp->fileline();
        AstNodeDType* const dtypep = typeOf(refp);
        const std::vector<Component>& compsr = componentsOf(dtypep);
        const std::vector<AstVarScope*>& vscps = components(refp->varScopep());
        AstNodeExpr* resultp = nullptr;
        for (size_t i = componentIndex(dtypep, lsb); i < compsr.size() && compsr[i].lsb <= msb;
             ++i) {
            const Component& comp = compsr[i];
            AstNodeExpr* bitsp = new AstVarRef{flp, vscps[i], refp->access()};
            const int partLsb = std::max(lsb, comp.lsb);
            const int partMsb = std::min(msb, comp.msb);
            if (partLsb != comp.lsb || partMsb != comp.msb) {
                bitsp = new AstSel{flp, bitsp, partLsb - comp.lsb, partMsb - partLsb + 1};
            }
            // Higher parts go to the left
            resultp = resultp ? new AstConcat{flp, bitsp, resultp} : bitsp;
        }
        return resultp;
    }

    // Split the candidate, if still possible: a variable might have been marked as
    // unsupported since the candidate was recorded due to other references. Returns the
    // replacement, or nullptr if not split.
    AstVarRef* split(AstArraySel* nodep) {
        AstVarRef* const fromp = VN_AS(nodep->fromp(), VarRef);
        // Needs the variable selected from to be supported
        if (!isSupported(fromp)) return nullptr;
        const size_t index = VN_AS(nodep->bitp(), Const)->toUInt();
        AstVarScope* const vscp = components(fromp->varScopep())[index];
        return new AstVarRef{nodep->fileline(), vscp, fromp->access()};
    }
    AstVarRef* split(AstStructSel* nodep) {
        AstVarRef* const fromp = VN_AS(nodep->fromp(), VarRef);
        // Needs the variable selected from to be supported
        if (!isSupported(fromp)) return nullptr;
        AstStructDType* const dtypep = VN_AS(typeOf(fromp)->skipRefp(), StructDType);
        componentsOf(dtypep);  // Assigns the member indices
        const AstNode* const memberp = m_memberMap.findMember(dtypep, nodep->name());
        UASSERT_OBJ(memberp, nodep, "Struct member not found: " << nodep->name());
        const size_t index = static_cast<size_t>(memberp->user1());
        AstVarScope* const vscp = components(fromp->varScopep())[index];
        return new AstVarRef{nodep->fileline(), vscp, fromp->access()};
    }
    AstNodeExpr* split(AstSel* nodep) {
        AstVarRef* const fromp = VN_AS(nodep->fromp(), VarRef);
        // Needs the variable selected from to be supported
        if (!isSupported(fromp)) return nullptr;
        AstNodeDType* const dtypep = typeOf(fromp);
        const int lsb = VN_AS(nodep->lsbp(), Const)->toSInt();
        const int msb = lsb + nodep->widthConst() - 1;
        const size_t idx = componentIndex(dtypep, lsb);
        const Component& comp = componentsOf(dtypep).at(idx);
        AstVarScope* const vscp = components(fromp->varScopep())[idx];
        AstVarRef* const refp = new AstVarRef{nodep->fileline(), vscp, fromp->access()};
        // The whole component, or a select from it
        if (lsb == comp.lsb && msb == comp.msb) return refp;
        return new AstSel{nodep->fileline(), refp, lsb - comp.lsb, msb - lsb + 1};
    }
    AstNodeAssign* split(AstNodeAssign* assp) {
        AstNodeExpr* const lhsp = assp->lhsp();
        AstNodeExpr* const rhsp = assp->rhsp();
        // Needs either side to be split, the components are selected from the other
        const bool lSup = shouldSplit(VN_CAST(lhsp, VarRef));
        const bool rSup = shouldSplit(VN_CAST(rhsp, VarRef));
        // A supported side not to be split is only copied whole. Mark it as unsupported, so the
        // selects from it in the expanded assignments are not candidates.
        for (AstNodeExpr* const sidep : {lhsp, rhsp}) {
            const AstVarRef* const refp = VN_CAST(sidep, VarRef);
            if (isSupported(refp) && !shouldSplit(refp)) refp->varScopep()->user2(true);
        }
        if (!lSup && !rSup) return nullptr;
        AstNodeDType* const dtypep = lSup ? typeOf(lhsp) : typeOf(rhsp);
        // Concatenation operands are moved to the expanded assignments, both in LSB order
        const std::vector<AstNodeExpr*> operands
            = VN_IS(rhsp, Concat) ? concatOperands(rhsp) : std::vector<AstNodeExpr*>{};
        auto operandIt = operands.begin();
        const std::vector<Component>& compsr = componentsOf(dtypep);
        AstNodeAssign* newsp = nullptr;
        for (size_t i = 0; i < compsr.size(); ++i) {
            AstNodeExpr* const newLhsp = newSplit(lhsp, dtypep, i);
            AstNodeExpr* const newRhsp = [&]() -> AstNodeExpr* {
                if (const AstCReset* const cresetp = VN_CAST(rhsp, CReset)) {
                    // Only allowed if the LHS is being split, so the LHS is a VarRef
                    AstVar* const varp = VN_AS(newLhsp, VarRef)->varp();
                    return new AstCReset{cresetp->fileline(), varp, false};
                }
                if (AstNodeExpr* const valuep = consElemp(rhsp, i)) {
                    return valuep->cloneTreePure(false);
                }
                if (!operands.empty()) {
                    // The next operands making up this component, higher ones go to the left
                    AstNodeExpr* valuep = nullptr;
                    while (!valuep || valuep->width() < compsr[i].dtypep->width()) {
                        AstNodeExpr* const operandp = (*operandIt++)->unlinkFrBack();
                        valuep = valuep ? new AstConcat{operandp->fileline(), operandp, valuep}
                                        : operandp;
                    }
                    return valuep;
                }
                // A split packed RHS of any layout, assemble the bits from its components
                if (lSup && rSup && isPacked(dtypep)) {
                    return newBits(VN_AS(rhsp, VarRef), compsr[i].lsb, compsr[i].msb);
                }
                return newSplit(rhsp, dtypep, i);
            }();
            newsp = AstNode::addNext(newsp, assp->cloneType(newLhsp, newRhsp));
        }
        return newsp;
    }
    AstNode* split(AstNode* nodep) {
        if (AstArraySel* const selp = VN_CAST(nodep, ArraySel)) return split(selp);
        if (AstStructSel* const selp = VN_CAST(nodep, StructSel)) return split(selp);
        if (AstSel* const selp = VN_CAST(nodep, Sel)) return split(selp);
        return split(VN_AS(nodep, NodeAssign));
    }

    // Split the current candidates. Splitting can reveal new candidates, which are recorded for
    // the next round.
    void splitRound() {
        // Take current candidates, will add new ones as we go after splitting
        std::vector<AstNode*> candidates;
        candidates.swap(m_candidates);
        // Split each candidate
        for (AstNode* const nodep : candidates) {
            // Expanding an assignment deletes or moves the selects in it, so if it contains
            // selects still pending, postpone it until they are split. Only candidates have
            // user2 set, and only selects can be candidates under an assignment.
            if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
                const bool hasPending = assp->exists([](const AstNodeExpr* np) {  //
                    return np->user2() == 1;
                });
                if (hasPending) {
                    m_candidates.push_back(assp);
                    continue;
                }
            }

            // Split it, if still possible
            AstNode* const newp = split(nodep);
            if (!newp) {
                nodep->user2(2);  // Skipped
                continue;
            }

            // Replace the candidate with the new split node
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);

            // Record/mark for the next round. A whole component is a single reference, so visit
            // its new context, the parent, unless it is a leaf with nothing more to split.
            // Revisiting the parent records nothing twice. A select from a component, and
            // expanded assignments are the new contexts themselves, so are visited.
            if (AstVarRef* const refp = VN_CAST(newp, VarRef)) {
                if (isSplittable(typeOf(refp))) {
                    if (AstNode* const parentp = refp->firstAbovep()) {
                        iterateConst(parentp);
                    } else {
                        refp->varScopep()->user2(true);  // Mark as unsupported
                    }
                }
            } else if (VN_IS(newp, NodeAssign)) {
                iterateAndNextConstNull(newp);
            } else {
                iterateConst(newp);
            }
        }
    }

    // VISITORS - structure
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstActive* nodep) override {
        if (nodep->hasCombo() && !m_scopep->user1p()) m_scopep->user1p(nodep);
        iterateChildrenConst(nodep);
    }

    // VISITORS - variables
    void visit(AstVar* nodep) override {
        iterateChildrenConst(nodep);
        // Evaluate eligibility, so unreferenced variables are also warned about
        isSupported(nodep);
    }

    // VISITORS - potentially splittable constructs
    void visit(AstArraySel* nodep) override {
        // Record candidate, with constant index, from a supported variable
        const AstVarRef* const fromp = VN_CAST(nodep->fromp(), VarRef);
        if (VN_IS(nodep->bitp(), Const) && isSupported(fromp)) {
            recordSelect(nodep, fromp);
            return;
        }
        // Otherwise descend to record or mark non splittable
        iterateChildrenConst(nodep);
    }
    void visit(AstStructSel* nodep) override {
        // Record candidate, from a supported variable
        const AstVarRef* const fromp = VN_CAST(nodep->fromp(), VarRef);
        if (isSupported(fromp)) {
            recordSelect(nodep, fromp);
            return;
        }
        // Otherwise descend to record or mark non splittable
        iterateChildrenConst(nodep);
    }
    void visit(AstSel* nodep) override {
        // Record candidate, with constant range within one component of a supported variable
        AstVarRef* const refp = VN_CAST(nodep->fromp(), VarRef);
        const AstConst* const lsbp = VN_CAST(nodep->lsbp(), Const);
        if (lsbp && isSupported(refp)) {
            const int lsb = lsbp->toSInt();
            const int msb = lsb + nodep->widthConst() - 1;
            if (isWithinComponent(typeOf(refp), lsb, msb)) {
                recordSelect(nodep, refp);
                return;
            }
        }
        // Otherwise descend to record or mark non splittable
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeAssign* nodep) override {
        AstNodeExpr* const lhsp = nodep->lhsp();
        AstNodeExpr* const rhsp = nodep->rhsp();
        // A packed side can be assigned to or from any packed type, so check both
        const bool packed = isPacked(typeOf(lhsp)) || isPacked(typeOf(rhsp));

        // Check the assignment itself first
        if ((!VN_IS(nodep, Assign)  // Only Assign
             && !VN_IS(nodep, AssignW)  // or AssignW
             && !VN_IS(nodep, AssignDly)  // or AssignDly
             )
            || nodep->timingControlp()  // without timing control
            || !(isSplittable(typeOf(lhsp)) || isSplittable(typeOf(rhsp)))  // splittable
            || (!packed && !isSameShape(typeOf(lhsp), typeOf(rhsp)))  // with corresponding
                                                                      // components
        ) {
            iterateChildrenConst(nodep);
            return;
        }

        // Check the LHS and RHS
        const bool lSup = isSupported(VN_CAST(lhsp, VarRef));
        const bool rSup = isSupported(VN_CAST(rhsp, VarRef));

        // Both sides are splittable references
        if (lSup && rSup) {
            recordCandidate(nodep);
            return;
        }

        // The LHS is a splittable reference, the RHS must be a splittable expression
        else if (lSup) {
            // Reset, select path, or for unpacked a cons not reading the LHS variable, or for
            // packed a constant, or an aligned concatenation
            const bool splittable
                = VN_IS(rhsp, CReset) || isPath(rhsp)
                  || (packed ? VN_IS(rhsp, Const) || isAlignedConcat(typeOf(lhsp), rhsp)
                             : isIndependentCons(rhsp, VN_AS(lhsp, VarRef)->varScopep()));
            if (splittable) {
                iterateConst(rhsp);  // Still need to gather candidates in it
                recordCandidate(nodep);
                return;
            }
        }

        // The RHS is a splittable reference, the LHS must be a splittable expression
        else if (rSup) {
            // Select path
            if (isPath(lhsp)) {
                iterateConst(lhsp);  // Still need to gather candidates in it
                recordCandidate(nodep);
                return;
            }
        }

        // Otherwise descend to record or mark non splittable
        iterateChildrenConst(nodep);
    }

    // VISITORS - non splittable constructs
    void visit(AstVarRef* nodep) override {
        // A reference not explicitly found in the splittable constructs is not splittable
        AstVarScope* const vscp = nodep->varScopep();
        AstVar* const varp = vscp->varp();
        // Nothing to do if the variable cannot be split anyway, already warned if needed
        if (!isSupported(varp)) return;
        vscp->user2(true);
        warnNoSplit(varp, nodep, "it is referenced in an unsupported way");
    }
    void visit(AstMemberSel* nodep) override {
        iterateChildrenConst(nodep);
        AstVar* const varp = nodep->varp();
        // Nothing to do if the variable cannot be split anyway, already warned if needed
        if (!isSupported(varp)) return;
        varp->user2(2);  // Evaluated, not supported
        warnNoSplit(varp, nodep, "it is accessed indirectly");
    }

    // VISITORS - descent
    void visit(AstNodeDType*) override {}  // No references in data types
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTORS
    explicit SplitComponentsVisitor(AstNetlist* netlistp) {
        // Gather AstVarScopes that might be split, and their references
        iterateConst(netlistp);

        // Split them, in rounds, until no candidates remain
        while (!m_candidates.empty()) splitRound();

        V3Stats::addStat("Optimizations, SplitComponents, unpacked variables split",
                         m_statSplitUnpackedOrig);
        V3Stats::addStat("Optimizations, SplitComponents, packed variables split",
                         m_statSplitPackedOrig);
        V3Stats::addStat("Optimizations, SplitComponents, unpacked components split",
                         m_statSplitUnpackedComp);
        V3Stats::addStat("Optimizations, SplitComponents, packed components split",
                         m_statSplitPackedComp);
    }

public:
    static void apply(AstNetlist* netlistp) { SplitComponentsVisitor{netlistp}; }
};

//######################################################################
// V3SplitComponents class functions

void V3SplitComponents::splitComponentsAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    SplitComponentsVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("split_components", 0, dumpTreeEitherLevel() >= 3);
}
