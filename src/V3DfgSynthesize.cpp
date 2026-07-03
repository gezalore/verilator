// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgLogic into primitive operations
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
// Synthesize DfgLogic vertices in as a graph, as created by V3DfgAstToDfg
// into primitive vertices.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Ast.h"
#include "V3Cfg.h"
#include "V3Const.h"
#include "V3Dfg.h"
#include "V3DfgDataType.h"
#include "V3DfgPasses.h"
#include "V3EmitV.h"

#include <algorithm>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Create a DfgVertex out of a AstNodeExpr. For most AstNodeExpr subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename T_Vertex, typename T_Node>
T_Vertex* makeVertex(const T_Node* nodep, DfgGraph& dfg, const DfgDataType& dtype) {
    return new T_Vertex{dfg, nodep->fileline(), dtype};
}

template <>
DfgArraySel* makeVertex<DfgArraySel, AstArraySel>(const AstArraySel* nodep, DfgGraph& dfg,
                                                  const DfgDataType& dtype) {
    // Some earlier passes create malformed ArraySels, just bail on those...
    // See t_bitsel_wire_array_bad
    if (VN_IS(nodep->fromp(), Const)) return nullptr;
    if (!VN_IS(nodep->fromp()->dtypep()->skipRefp(), UnpackArrayDType)) return nullptr;
    return new DfgArraySel{dfg, nodep->fileline(), dtype};
}

}  // namespace

// Visitor that can convert Ast statements and expressions in Dfg vertices
class AstToDfgConverter final : public VNVisitor {
    // NODE STATE
    // AstNodeExpr/AstVar/AstVarScope::user2p -> DfgVertex* for this Node
    // AstVar::user3()                        -> int temporary counter for variable
    const VNUser3InUse m_user3InUse;

    // STATE
    DfgGraph& m_dfg;  // The graph being built
    V3DfgSynthesisContext& m_ctx;  // The context for stats

    // Current logic vertex we are synthesizing
    DfgLogic* m_logicp = nullptr;
    // Variable updates produced by currently converted statement. This almost
    // always have a single element, so a vector is ok
    std::vector<std::pair<AstVarScope*, DfgVertexVar*>>* m_updatesp = nullptr;

    bool m_foundUnhandled = false;  // Found node not implemented as DFG or not implemented 'visit'
    bool m_converting = false;  // We are trying to convert some logic at the moment

    size_t m_nUnpack = 0;  // Sequence numbers for temporaries

    // METHODS

    // Allocate a new non-variable vertex, add it to the currently synthesized logic
    template <typename Vertex, typename... Args>
    Vertex* make(Args&&... args) {
        static_assert(!std::is_base_of<DfgVertexVar, Vertex>::value, "Do not use for variables");
        static_assert(std::is_base_of<DfgVertex, Vertex>::value, "'Vertex' must be a 'DfgVertex'");
        Vertex* const vtxp = new Vertex{m_dfg, std::forward<Args>(args)...};
        m_logicp->synth().emplace_back(vtxp);
        return vtxp;
    }

    // Returns true if the expression cannot (or should not) be represented by DFG
    bool unhandled(AstNodeExpr* nodep) {
        // Short-circuiting if something was already unhandled
        if (m_foundUnhandled) {
            // Impure nodes cannot be represented
            if (!nodep->isPure()) {
                m_foundUnhandled = true;
                ++m_ctx.m_conv.nonRepImpure;
            }
        }
        return m_foundUnhandled;
    }

    bool isSupported(const AstVarRef* nodep) {
        // Cannot represent cross module references
        if (nodep->classOrPackagep()) return false;
        // Check target
        return V3Dfg::isSupported(nodep->varScopep());
    }

    // Given an RValue expression, return the equivalent Vertex, or nullptr if not representable.
    DfgVertex* convertRValue(AstNodeExpr* nodep) {
        UASSERT_OBJ(!m_converting, nodep, "'convertingRValue' should not be called recursively");
        VL_RESTORER(m_converting);
        VL_RESTORER(m_foundUnhandled);
        m_converting = true;
        m_foundUnhandled = false;

        // Convert the expression
        iterate(nodep);

        // If falied to convert, return nullptr
        if (m_foundUnhandled) return nullptr;

        // Traversal set user2p to the equivalent vertex
        DfgVertex* const vtxp = nodep->user2u().to<DfgVertex*>();
        UASSERT_OBJ(vtxp, nodep, "Missing Dfg vertex after conversion");
        return vtxp;
    }

    void connectLValue(DfgVertex* lVtxp, DfgVertex* rVtxp) {

        if (lVtxp->isArray()) {
            if (rVtxp->isPacked()) {
                const DfgDataType& dtype = DfgDataType::array(rVtxp->dtype(), 1);
                DfgUnitArray* const uap = make<DfgUnitArray>(rVtxp->fileline(), dtype);
                uap->srcp(rVtxp);
                rVtxp = uap;
            }
            // TODO: even out multi-dim arrays when ready
        }

        // Drive directly if it's a variable
        if (DfgVertexVar* const varp = lVtxp->cast<DfgVertexVar>()) {
            varp->srcp(rVtxp);
            return;
        }
        // Otherwise it must be a DfgInsert
        lVtxp->as<DfgInsert>()->srcp(rVtxp);
    }

    // Given an LValue expression, return the vertex that should consume the written value.
    // This is either a DfgInsert, if 'nodep' represents a partail update, or a DfgVertexVar,
    // if it's a whole update. Returns nullptr, if the given LValue expression is not supported.
    // If 'defaultpp' is not nullptr, assign it a vertex to be used as the default value
    // for a partial DfgInsert update creaed by the caller.
    DfgVertex* convertLValue(AstNodeExpr* nodep, DfgVertex** defaultpp) {
        if (const AstVarRef* const vrefp = VN_CAST(nodep, VarRef)) {
            UASSERT_OBJ(vrefp->access().isWriteOnly(), vrefp, "Non-WriteOnly reference");
            if (!isSupported(vrefp)) {
                ++m_ctx.m_conv.nonRepLValue;
                return nullptr;
            }

            // The variable being assigned
            AstVarScope* const vscp = vrefp->varScopep();

            // Find existing update, if any
            size_t idx = 0;
            while (idx < m_updatesp->size()) {
                if ((*m_updatesp)[idx].first == vscp) break;
                ++idx;
            }
            const bool firstUpdate = idx == m_updatesp->size();

            // Get current binding of this variable, must always exist
            DfgVertexVar* const oldp = idx == m_updatesp->size()
                                           ? vscp->user2u().to<DfgVertexVar*>()
                                           : (*m_updatesp)[idx].second;
            UASSERT_OBJ(oldp, vscp, "Missing Dfg vertex for written variable");

            // Create new temporary for this update
            DfgVertexVar* const newp = createTmp(*m_logicp, vscp, "SynthAssign");

            // Update mapping
            if (firstUpdate) {
                m_updatesp->emplace_back(vscp, newp);
            } else {
                (*m_updatesp)[idx].second = newp;
            }

            // Populate 'defaultpp'
            if (defaultpp) *defaultpp = oldp;

            // Return the new temporary variable that will be assigned
            return newp;
        }

        if (const AstSel* selp = VN_CAST(nodep, Sel)) {
            // Only handle constant selects
            const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const);
            if (!lsbp) {
                ++m_ctx.m_conv.nonRepLValue;
                return nullptr;
            }
            const uint32_t lsb = lsbp->toUInt();

            // Convert the 'fromp' sub-expression
            DfgVertex* defaultp = nullptr;
            DfgVertex* const snkp = convertLValue(selp->fromp(), &defaultp);
            if (!snkp) return nullptr;
            UASSERT_OBJ(defaultp, selp, "Missing default value");

            // Don't optimize if statically out of bounds. TODO: Maybe later ...
            if (lsb + static_cast<uint32_t>(selp->widthConst()) > snkp->size()) {
                ++m_ctx.m_conv.nonRepOOBSel;
                return nullptr;
            }

            // Create the DfgInsert
            DfgInsert* const insp = make<DfgInsert>(selp->fileline(), defaultp->dtype());
            // insp->srcp() connected by caller
            insp->defaultp(defaultp);
            insp->lo(lsb);
            connectLValue(snkp, insp);

            // Populate 'defaultpp'
            if (defaultpp) {
                const DfgDataType& dtype = *DfgDataType::fromAst(selp->dtypep());
                DfgSel* const dselp = make<DfgSel>(selp->fileline(), dtype);
                dselp->fromp(defaultp);
                dselp->lsb(lsb);
                *defaultpp = dselp;
            }

            // Return the new insert vertex that will be assigned
            return insp;
        }

        if (const AstArraySel* const aselp = VN_CAST(nodep, ArraySel)) {
            // Only handle constant selects
            const AstConst* const indexp = VN_CAST(aselp->bitp(), Const);
            if (!indexp) {
                ++m_ctx.m_conv.nonRepLValue;
                return nullptr;
            }
            const uint32_t index = indexp->toUInt();

            // Convert the 'fromp' sub-expression
            DfgVertex* defaultp = nullptr;
            DfgVertex* const snkp = convertLValue(aselp->fromp(), &defaultp);
            if (!snkp) return nullptr;
            UASSERT_OBJ(defaultp, aselp, "Missing default value");

            // Don't optimize if statically out of bounds. TODO: Maybe later ...
            if (index + 1U > snkp->size()) {
                ++m_ctx.m_conv.nonRepOOBSel;
                return nullptr;
            }

            // Create the DfgInsert
            DfgInsert* const insp = make<DfgInsert>(aselp->fileline(), defaultp->dtype());
            // insp->srcp() connected by caller
            insp->defaultp(defaultp);
            insp->lo(index);
            connectLValue(snkp, insp);

            // Populate 'defaultpp'
            if (defaultpp) {
                const DfgDataType& dtype = *DfgDataType::fromAst(aselp->dtypep());
                DfgArraySel* const daselp = make<DfgArraySel>(aselp->fileline(), dtype);
                daselp->fromp(defaultp);
                daselp->bitp(make<DfgConst>(aselp->fileline(), 32U, index));
                *defaultpp = daselp;
            }

            // Return the new insert vertex that will be assigned
            return insp;
        }

        ++m_ctx.m_conv.nonRepLValue;
        return nullptr;
    }

    // Given the LHS of an assignment, and the vertex representing the RHS,
    // connect up the RHS to drive the targets.
    // Returns true on success, false if the LHS is not representable.
    bool convertAssignment(FileLine* flp, AstNodeExpr* lhsp, DfgVertex* vtxp) {
        // Represents a DFG assignment contributed by the AST assignment with the above 'lhsp'.
        // There might be multiple of these if 'lhsp' is a concatenation.
        struct Assignment final {
            DfgVertex* m_lhsp;
            DfgVertex* m_rhsp;
            Assignment() = delete;
            Assignment(DfgVertex* lhsp, DfgVertex* rhsp)
                : m_lhsp{lhsp}
                , m_rhsp{rhsp} {}
        };

        // Simplify the LHS, to get rid of things like SEL(CONCAT(_, _), _)
        lhsp = VN_AS(V3Const::constifyExpensiveEdit(lhsp), NodeExpr);

        // Assigning compound expressions to a concatenated LHS requires a temporary
        // to avoid multiple use of the expression
        if (VN_IS(lhsp, Concat) && !vtxp->is<DfgVertexVar>() && !vtxp->is<DfgConst>()) {
            const size_t n = ++m_nUnpack;
            DfgVertexVar* const tmpp = createTmp(*m_logicp, flp, vtxp->dtype(), "Unpack", n);
            tmpp->srcp(vtxp);
            vtxp = tmpp;
        }

        // Convert each concatenation LHS separately, gather all assignments
        // we need to do into 'assignments', return true if all LValues
        // converted successfully.
        std::vector<Assignment> assignments;
        const std::function<bool(AstNodeExpr*, uint32_t)> convertAllLValues
            = [&](AstNodeExpr* subp, uint32_t lsb) -> bool {
            // Concatenation on the LHS, convert each part
            if (AstConcat* const concatp = VN_CAST(subp, Concat)) {
                AstNodeExpr* const cRhsp = concatp->rhsp();
                AstNodeExpr* const cLhsp = concatp->lhsp();
                // Convert Rigth of concat
                if (!convertAllLValues(cRhsp, lsb)) return false;
                // Convert Left of concat
                return convertAllLValues(cLhsp, lsb + cRhsp->width());
            }

            // Non-concatenation, convert the LValue
            DfgVertex* const lVtxp = convertLValue(subp, nullptr);
            if (!lVtxp) return false;

            // If whole lhs, just use it
            if (subp == lhsp) {
                assignments.emplace_back(lVtxp, vtxp);
                return true;
            }

            // Otherwise select the relevant bits
            const DfgDataType& dtype = *DfgDataType::fromAst(subp->dtypep());
            DfgSel* const selp = make<DfgSel>(subp->fileline(), dtype);
            selp->fromp(vtxp);
            selp->lsb(lsb);
            assignments.emplace_back(lVtxp, selp);
            return true;
        };

        // Convert the given LHS assignment, give up if any LValues failed to convert
        if (!convertAllLValues(lhsp, 0)) return false;

        // All successful, connect the drivers
        for (const Assignment& item : assignments) connectLValue(item.m_lhsp, item.m_rhsp);

        return true;
    }

    // VISITORS

    // Unhandled node
    void visit(AstNode* /*nodep*/) override {
        if (!m_foundUnhandled && m_converting) ++m_ctx.m_conv.nonRepUnknown;
        m_foundUnhandled = true;
    }

    // Expressions - mostly auto generated, but a few special ones
    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;
        // This visit method is only called on RValues, where only read refs are supported
        UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Non-ReadOnly reference");
        if (!isSupported(nodep)) {
            m_foundUnhandled = true;
            ++m_ctx.m_conv.nonRepVarRef;
            return;
        }

        // Variable should have been bound before starting conversion
        DfgVertex* const vtxp = nodep->varScopep()->user2u().template to<DfgVertexVar*>();
        UASSERT_OBJ(vtxp, nodep, "Referenced variable has no associated DfgVertexVar");
        nodep->user2p(vtxp);
    }
    void visit(AstConst* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        if (nodep->width() != nodep->num().width()) {
            // Sometimes the width of the AstConst is not the same as the
            // V3Number it holds. Truncate it here. TODO: should this be allowed?
            V3Number num{nodep, nodep->width()};
            num.opSel(nodep->num(), nodep->width() - 1, 0);
            DfgVertex* const vtxp = make<DfgConst>(nodep->fileline(), num);
            nodep->user2p(vtxp);
        } else {
            DfgVertex* const vtxp = make<DfgConst>(nodep->fileline(), nodep->num());
            nodep->user2p(vtxp);
        }
    }
    void visit(AstCReset* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        const DfgDataType* const dtypep = DfgDataType::fromAst(nodep->dtypep());
        if (!dtypep) {
            m_foundUnhandled = true;
            ++m_ctx.m_conv.nonRepDType;
            return;
        }

        UASSERT_OBJ(!nodep->constructing(), nodep,
                    "CReset should be non-constructing at this stage");

        DfgVertex* const vtxp = make<DfgCReset>(nodep->fileline(), *dtypep);
        nodep->user2p(vtxp);
    }
    void visit(AstMatchMasked* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        const DfgDataType* const dtypep = DfgDataType::fromAst(nodep->dtypep());
        if (!dtypep) {
            m_foundUnhandled = true;
            ++m_ctx.m_conv.nonRepDType;
            return;
        }

        iterate(nodep->lhsp());
        if (m_foundUnhandled) return;
        iterate(nodep->matchp());
        if (m_foundUnhandled) return;

        FileLine* const flp = nodep->fileline();
        DfgMatchMasked* const vtxp = make<DfgMatchMasked>(flp, *dtypep);
        vtxp->lhsp(nodep->lhsp()->user2u().to<DfgVertex*>());
        vtxp->matchp(nodep->matchp()->user2u().to<DfgVertex*>());
        nodep->user2p(vtxp);
    }
    void visit(AstReplicate* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        const DfgDataType* const dtypep = DfgDataType::fromAst(nodep->dtypep());
        if (!dtypep) {
            m_foundUnhandled = true;
            ++m_ctx.m_conv.nonRepDType;
            return;
        }

        iterate(nodep->srcp());
        if (m_foundUnhandled) return;

        FileLine* const flp = nodep->fileline();
        DfgRep* const vtxp = make<DfgRep>(flp, *dtypep);
        vtxp->srcp(nodep->srcp()->user2u().to<DfgVertex*>());
        nodep->user2p(vtxp);
    }
    void visit(AstSel* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        const DfgDataType* const dtypep = DfgDataType::fromAst(nodep->dtypep());
        if (!dtypep) {
            m_foundUnhandled = true;
            ++m_ctx.m_conv.nonRepDType;
            return;
        }

        iterate(nodep->fromp());
        if (m_foundUnhandled) return;

        FileLine* const flp = nodep->fileline();
        DfgVertex* vtxp = nullptr;
        if (const AstConst* const constp = VN_CAST(nodep->lsbp(), Const)) {
            const uint32_t lsb = constp->toUInt();
            const uint32_t msb = lsb + nodep->widthConst() - 1;
            DfgVertex* const fromp = nodep->fromp()->user2u().to<DfgVertex*>();
            // Unfortunately we can still have out of bounds selects due to how
            // indices are truncated for speed reasons in V3Width/V3Unknown.
            if (msb >= fromp->size()) {
                m_foundUnhandled = true;
                ++m_ctx.m_conv.nonRepOOBSel;
                return;
            }
            DfgSel* const selp = make<DfgSel>(flp, *dtypep);
            selp->fromp(fromp);
            selp->lsb(lsb);
            vtxp = selp;
        } else {
            iterate(nodep->lsbp());
            if (m_foundUnhandled) return;
            DfgMux* const muxp = make<DfgMux>(flp, *dtypep);
            muxp->fromp(nodep->fromp()->user2u().to<DfgVertex*>());
            muxp->lsbp(nodep->lsbp()->user2u().to<DfgVertex*>());
            vtxp = muxp;
        }
        nodep->user2p(vtxp);
    }

// The rest of the visit methods for expressions are generated by 'astgen'
#include "V3Dfg__gen_ast_to_dfg.h"

public:
    // PUBLIC METHODS

    // Create temporay variable capable of holding the given type
    DfgVertexVar* createTmp(DfgLogic& logic, FileLine* flp, const DfgDataType& dtype,
                            const std::string& prefix, size_t tmpCount) {
        const std::string name = m_dfg.makeUniqueName(prefix, tmpCount);
        DfgVertexVar* const vtxp = m_dfg.makeNewVar(flp, name, dtype, logic.scopep());
        logic.synth().emplace_back(vtxp);
        vtxp->vscp()->varp()->isInternal(true);
        vtxp->tmpForp(vtxp->vscp());
        return vtxp;
    }

    // Create a new temporary variable capable of holding 'varp'
    DfgVertexVar* createTmp(DfgLogic& logic, AstVarScope* vscp, const std::string& prefix) {
        AstVar* const astVarp = vscp->varp();
        FileLine* const flp = astVarp->fileline();
        const DfgDataType& dtype = *DfgDataType::fromAst(astVarp->dtypep());
        const std::string prfx = prefix + "_" + astVarp->name();
        const size_t tmpCount = astVarp->user3Inc();
        DfgVertexVar* const vtxp = createTmp(logic, flp, dtype, prfx, tmpCount);
        vtxp->tmpForp(vscp);
        return vtxp;
    }

    // Convert AstAssign to Dfg, return true if successful.
    // Fills 'updates' with bindings for assigned variables.
    bool convert(std::vector<std::pair<AstVarScope*, DfgVertexVar*>>& updates, DfgLogic& vtx,
                 AstNodeAssign* nodep) {
        UASSERT_OBJ(VN_IS(nodep, Assign) || VN_IS(nodep, AssignW), nodep, "Bad NodeAssign");
        UASSERT_OBJ(updates.empty(), nodep, "'updates' should be empty");
        VL_RESTORER(m_updatesp);
        VL_RESTORER(m_logicp);
        m_updatesp = &updates;
        m_logicp = &vtx;
        // Assignment with timing control shouldn't make it this far
        UASSERT_OBJ(!nodep->timingControlp(), nodep, "Shouldn't make it this far");
        // Convert it
        ++m_ctx.m_conv.inputAssignments;
        AstNodeExpr* const lhsp = nodep->lhsp();
        AstNodeExpr* const rhsp = nodep->rhsp();
        // Check data types are compatible.
        const DfgDataType* const lDtypep = DfgDataType::fromAst(lhsp->dtypep());
        const DfgDataType* const rDtypep = DfgDataType::fromAst(rhsp->dtypep());
        if (!lDtypep || !rDtypep) {
            ++m_ctx.m_conv.nonRepDType;
            return false;
        }
        // For now, only direct array assignment is supported (e.g. a = b, but not a = _ ? b : c)
        if (rDtypep->isArray()) {
            if (!VN_IS(rhsp, VarRef)
                || !lhsp->dtypep()->skipRefp()->sameTree(rhsp->dtypep()->skipRefp())) {
                ++m_ctx.m_conv.nonRepDType;
                return false;
            }
        }
        // Widths should match at this point
        UASSERT_OBJ(lhsp->width() == rhsp->width(), nodep, "Mismatched width reached DFG");
        // Convert the RHS expression
        DfgVertex* const rVtxp = convertRValue(rhsp);
        if (!rVtxp) return false;
        // Connect the RHS vertex to the LHS targets
        const bool success = convertAssignment(nodep->fileline(), lhsp, rVtxp);
        if (success) ++m_ctx.m_conv.representable;
        return success;
    }

    // Convert RValue expression to Dfg. Returns nullptr if failed.
    DfgVertex* convert(DfgLogic& vtx, AstNodeExpr* nodep) {
        VL_RESTORER(m_logicp);
        m_logicp = &vtx;
        // Convert it
        ++m_ctx.m_conv.inputExpressions;
        DfgVertex* const vtxp = convertRValue(nodep);
        if (vtxp) ++m_ctx.m_conv.representable;
        return vtxp;
    }

    // CONSTRUCTOR
    AstToDfgConverter(DfgGraph& dfg, V3DfgSynthesisContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {}
};

// Debug aid - outisde 'AstToDfgSynthesize' as it is a template, but want one instance
V3DebugBisect s_dfgSynthDebugBisect{"DfgSynthesize"};

class AstToDfgSynthesize final {
    // NODE STATE
    // AstNodeExpr/AstVar/AstVarScope::user2p -> DfgVertex* for this Node

    // TYPES

    // SymTab must be ordered in order to yield stable results
    struct AstVarScopeComparator final {
        bool operator()(const AstVarScope* lhs, const AstVarScope* rhs) const {
            return lhs->name() < rhs->name();
        }
    };
    using SymTab = std::map<AstVarScope*, DfgVertexVar*, AstVarScopeComparator>;

    // Represents a [potentially partial] driver of a variable
    struct Driver final {
        DfgVertex* m_vtxp = nullptr;  // Driving vertex
        uint32_t m_lo = 0;  // Low index of driven range (internal, not Verilog)
        uint32_t m_hi = 0;  // High index of driven range (internal, not Verilog)
        FileLine* m_flp = nullptr;  // Location of driver in source

        Driver() = default;
        Driver(DfgVertex* vtxp, uint32_t lo, FileLine* flp)
            : m_vtxp{vtxp}
            , m_lo{lo}
            , m_hi{lo + vtxp->size() - 1U}
            , m_flp{flp} {}
        operator bool() const { return m_vtxp != nullptr; }

        bool operator<(const Driver& other) const {
            if (m_lo != other.m_lo) return m_lo < other.m_lo;
            if (m_hi != other.m_hi) return m_hi < other.m_hi;
            return m_flp->operatorCompare(*other.m_flp) < 0;
        }

        bool operator<=(const Driver& other) const { return !(other < *this); }
    };

    // STATE - Persistent
    DfgGraph& m_dfg;  // The graph being built
    V3DfgSynthesisContext& m_ctx;  // The context for stats
    AstToDfgConverter m_converter;  // The convert instance to use for each construct
    size_t m_nBranchCond = 0;  // Sequence numbers for temporaries
    size_t m_nPathPred = 0;  // Sequence numbers for temporaries
    DfgWorklist m_toRevert{m_dfg};  // We need a worklist for reverting synthesis

    // STATE - for current DfgLogic being synthesized
    DfgLogic* m_logicp = nullptr;  // Current logic vertex we are synthesizing
    CfgBlockMap<SymTab> m_bbToISymTab;  // Map from CfgBlock -> input symbol table
    CfgBlockMap<SymTab> m_bbToOSymTab;  // Map from CfgBlock -> output symbol table
    CfgBlockMap<DfgVertexVar*> m_bbToCondp;  // Map from CfgBlock ->  terminating branch condition
    CfgEdgeMap<DfgVertexVar*> m_edgeToPredicatep;  // Map CfgGraphEdge -> path predicate to there
    CfgDominatorTree m_domTree;  // The dominator tree of the current CFG

    // STATE - Some debug aid
    // We stop after synthesizing s_dfgSynthDebugLimit vertices (if non-zero).
    // This is the problematic logic (last one we synthesize), assuming a
    // bisection search over s_dfgSynthDebugLimit.
    DfgLogic* m_debugLogicp = nullptr;
    // Source (upstream) cone of outputs of m_debugLogicp
    std::unique_ptr<std::unordered_set<const DfgVertex*>> m_debugOSrcConep{nullptr};

    // METHODS

    // Dump current graph for debugging ...
    void debugDump(const char* name) {
        // If we have the debugged logic, compute the vertices feeding its outputs
        if (VL_UNLIKELY(m_debugLogicp)) {
            std::vector<const DfgVertex*> outputs;
            m_debugLogicp->foreachSink([&outputs](const DfgVertex& v) {
                outputs.emplace_back(v.singleSink()->as<DfgVertexVar>());
                return false;
            });
            m_debugOSrcConep = m_dfg.sourceCone(outputs);
        }

        if (VL_UNLIKELY(dumpDfgLevel() >= 9 || m_debugOSrcConep)) {
            m_dfg.dumpDotFilePrefixed(name);
            if (m_debugOSrcConep) {
                // Dump only the subgraph involving the inputs and outputs of the bad vertex
                m_dfg.dumpDotFilePrefixed(name + "-min"s, [&](const DfgVertex& v) -> bool {
                    return m_debugOSrcConep->count(&v);
                });
            }
        }
    }

    // Allocate a new non-variable vertex, add it to the currently synthesized logic
    template <typename Vertex, typename... Args>
    Vertex* make(Args&&... args) {
        static_assert(!std::is_base_of<DfgVertexVar, Vertex>::value, "Do not use for variables");
        static_assert(std::is_base_of<DfgVertex, Vertex>::value, "'Vertex' must be a 'DfgVertex'");
        Vertex* const vtxp = new Vertex{m_dfg, std::forward<Args>(args)...};
        if (m_logicp) m_logicp->synth().emplace_back(vtxp);
        return vtxp;
    }

    // Initialzie input symbol table of entry CfgBlock
    void initializeEntrySymbolTable(SymTab& iSymTab) {
        // All variables read
        m_logicp->foreachSource([&](DfgVertex& src) {
            DfgVertexVar* const vvp = src.as<DfgVertexVar>();
            iSymTab[vvp->vscp()] = vvp;
            return false;
        });
        // Also all variables written, for DfgInsert defauls
        m_logicp->foreachSink([&](DfgVertex& dst) {
            DfgVertexVar* const vvp = dst.as<DfgUnresolved>()->singleSink()->as<DfgVertexVar>();
            iSymTab[vvp->vscp()] = vvp;
            return false;
        });
    }

    // Join variable drivers across a control flow confluence (insert muxes ...)
    DfgVertexVar* joinDrivers(AstVarScope* vscp, DfgVertexVar* predicatep,  //
                              DfgVertexVar* thenp, DfgVertexVar* elsep) {
        AstVarScope* const thenVscp = thenp->tmpForp() ? thenp->tmpForp() : thenp->vscp();
        AstVarScope* const elseVscp = elsep->tmpForp() ? elsep->tmpForp() : elsep->vscp();
        UASSERT_OBJ(thenVscp == elseVscp, vscp, "Attempting to join unrelated variables");

        // If both bindings are the the same (variable not updated through either path),
        // then there is nothing to do, can use the same binding
        if (thenp == elsep) return thenp;

        // Create a fresh temporary for the joined value, and join using a conditional
        FileLine* const flp = predicatep->fileline();
        DfgVertexVar* const joinp = m_converter.createTmp(*m_logicp, vscp, "SynthJoin");
        DfgCond* const condp = make<DfgCond>(flp, joinp->dtype());
        condp->condp(predicatep);
        condp->thenp(thenp);
        condp->elsep(elsep);
        joinp->srcp(condp);

        // Done
        return joinp;
    }

    // Merge 'thenSymTab' into 'elseSymTab' using the given predicate to join values
    bool joinSymbolTables(SymTab& elseSymTab, DfgVertexVar* predicatep, const SymTab& thenSymTab) {
        // Any variable that does not have a binding on both paths will be removed. These might be
        // temporaries, loop vars, etc used only in one branch. Conversion will fail if the
        // variable is actually referenced later.
        std::vector<AstVarScope*> toRemove;

        // Join each symbol
        for (std::pair<AstVarScope* const, DfgVertexVar*>& pair : elseSymTab) {
            AstVarScope* const varp = pair.first;
            // Find same variable on the else path
            const auto it = thenSymTab.find(varp);
            // Record for removal if not assigned on both paths
            if (it == thenSymTab.end()) {
                toRemove.emplace_back(varp);
                continue;
            }
            // Join paths with the predicate
            DfgVertexVar* const thenp = it->second;
            DfgVertexVar* const elsep = pair.second;
            DfgVertexVar* const newp = joinDrivers(varp, predicatep, thenp, elsep);
            if (!newp) return false;
            pair.second = newp;
        }

        // Remove variables not assigned on both paths
        for (AstVarScope* const varp : toRemove) elseSymTab.erase(varp);

        // Done
        return true;
    }

    // Given two joining control flow edges, compute how to join their symbols.
    // Returns the predicaete to join over, and the 'then' and 'else' blocks.
    std::tuple<DfgVertexVar*, const CfgBlock*, const CfgBlock*>  //
    howToJoin(const CfgEdge* const ap, const CfgEdge* const bp) {
        // Find the closest common dominator of the two paths
        const CfgBlock* const domp = m_domTree.closestCommonDominator(ap->srcp(), bp->srcp());
        // These paths join here, so 'domp' must be a branch, otherwise it's not the closest
        UASSERT_OBJ(domp->isBranch(), domp, "closestCommonDominator is not a branch");

        // The branches of the common dominator
        const CfgEdge* const takenEdgep = domp->takenEdgep();
        const CfgEdge* const untknEdgep = domp->untknEdgep();

        // We check if the taken branch dominates the path to either blocks,
        // and if the untaken branch dominates the path to the other block.
        // If so, we can use the branch condition as predicate, otherwise
        // we must use the path predicate as there are ways to get from one
        // branch of the dominator to the other. We need to be careful if
        // either branches are directly to the join block. This is fine,
        // it's as if there was an empty block on that critical edge which
        // is dominated by that path.

        if (takenEdgep == ap || m_domTree.dominates(takenEdgep->dstp(), ap->srcp())) {
            if (untknEdgep == bp || m_domTree.dominates(untknEdgep->dstp(), bp->srcp())) {
                // Taken path dominates 'ap' and untaken dominates 'bp', use the branch condition
                ++m_ctx.m_synt.joinUsingBranchCondition;
                return std::make_tuple(m_bbToCondp[domp], ap->srcp(), bp->srcp());
            }
        } else if (takenEdgep == bp || m_domTree.dominates(takenEdgep->dstp(), bp->srcp())) {
            if (untknEdgep == ap || m_domTree.dominates(untknEdgep->dstp(), ap->srcp())) {
                // Taken path dominates 'bp' and untaken dominates 'ap', use the branch condition
                ++m_ctx.m_synt.joinUsingBranchCondition;
                return std::make_tuple(m_bbToCondp[domp], bp->srcp(), ap->srcp());
            }
        }

        // The branches don't dominate the joined blocks, must use the path predicate
        ++m_ctx.m_synt.joinUsingPathPredicate;

        // TODO: We could do better here: use the path predicate of the closest
        // cominating blocks, pick the one from the lower rank, etc, but this
        // generic case is very rare, most synthesizable logic has
        // series-parallel CFGs which are covered by the earlier cases.
        return std::make_tuple(m_edgeToPredicatep[ap], ap->srcp(), bp->srcp());
    }

    // Combine the output symbol tables of the predecessors of the given
    // block to compute the input symtol table for the given block.
    bool createInputSymbolTable(const CfgBlock& bb) {
        // The input symbol table of the given block, we are computing it now
        SymTab& joined = m_bbToISymTab[bb];

        // Input symbol table of entry block is special
        if (bb.isEnter()) {
            initializeEntrySymbolTable(joined);
            return true;
        }

        // Current input symbol table should be empty, we will fill it in here
        UASSERT(joined.empty(), "Unprocessed input symbol table should be empty");

        // Fast path if there is only one predecessor - TODO: use less copying
        if (!bb.isJoin()) {
            joined = m_bbToOSymTab[bb.firstPredecessorp()];
            return true;
        }

        // We also have a simpler job if there are 2 predecessors
        if (bb.isTwoWayJoin()) {
            DfgVertexVar* predicatep = nullptr;
            const CfgBlock* thenp = nullptr;
            const CfgBlock* elsep = nullptr;
            std::tie(predicatep, thenp, elsep)
                = howToJoin(bb.firstPredecessorEdgep(), bb.lastPredecessorEdgep());
            // Copy from else
            joined = m_bbToOSymTab[elsep];
            // Join with then
            return joinSymbolTables(joined, predicatep, m_bbToOSymTab[*thenp]);
        }

        // General hard way

        // Gather predecessors
        struct Predecessor final {
            const CfgBlock* m_bbp;  // Predeccessor block
            DfgVertexVar* m_predicatep;  // Predicate predecessor reached this block with
            const SymTab* m_oSymTabp;  // Output symbol table or predecessor
            Predecessor() = delete;
            Predecessor(const CfgBlock* bbp, DfgVertexVar* predicatep, const SymTab* oSymTabp)
                : m_bbp{bbp}
                , m_predicatep{predicatep}
                , m_oSymTabp{oSymTabp} {}
        };

        const std::vector<Predecessor> predecessors = [&]() {
            std::vector<Predecessor> res;
            for (const V3GraphEdge& edge : bb.inEdges()) {
                const CfgEdge& cfgEdge = static_cast<const CfgEdge&>(edge);
                const CfgBlock* const predecessorp = cfgEdge.srcp();
                DfgVertexVar* const predicatep = m_edgeToPredicatep[cfgEdge];
                const SymTab* const oSymTabp = &m_bbToOSymTab[predecessorp];
                res.emplace_back(predecessorp, predicatep, oSymTabp);
            }
            // Sort predecessors reverse topologically. This way earlier blocks
            // will come after later blocks, and the entry block is last if present.
            std::sort(res.begin(), res.end(), [](const Predecessor& a, const Predecessor& b) {  //
                return *a.m_bbp > *b.m_bbp;
            });
            return res;
        }();

        // Start by copying the bindings from the frist predecessor
        joined = *predecessors[0].m_oSymTabp;
        // Join over all other predecessors
        for (size_t i = 1; i < predecessors.size(); ++i) {
            DfgVertexVar* const predicatep = predecessors[i].m_predicatep;
            const SymTab& oSymTab = *predecessors[i].m_oSymTabp;
            if (!joinSymbolTables(joined, predicatep, oSymTab)) return false;
        }

        return true;
    }

    // Synthesize the given statements with the given input symbol table.
    // Returns true if successfolly synthesized.
    // Populates the given output symbol table.
    // Populates the given reference with the condition of the terminator branch, if any.
    bool synthesizeBasicBlock(SymTab& oSymTab, DfgVertex*& condpr,
                              const std::vector<AstNodeStmt*>& stmtps, const SymTab& iSymTab) {
        // Use fresh set of vertices in m_converter
        const VNUser2InUse user2InUse;

        // Initialize AstVarScope -> Vertex bindings available in this block
        for (const auto& pair : iSymTab) {
            AstVarScope* const varp = pair.first;
            DfgVertexVar* const vtxp = pair.second;
            varp->user2p(vtxp);
            oSymTab[varp] = vtxp;
        }

        // Synthesize each statement one after the other
        std::vector<std::pair<AstVarScope*, DfgVertexVar*>> updates;
        for (AstNodeStmt* const stmtp : stmtps) {
            // Regular statements
            AstNodeAssign* const ap = VN_CAST(stmtp, NodeAssign);
            if (ap && (VN_IS(ap, Assign) || VN_IS(ap, AssignW))) {
                // Convert this assignment
                if (!m_converter.convert(updates, *m_logicp, ap)) {
                    ++m_ctx.m_synt.nonSynConv;
                    return false;
                }
                // Apply variable updates from this statement
                for (const auto& pair : updates) {
                    // The target variable that was assigned to
                    AstVarScope* const vscp = pair.first;
                    // The new, potentially partially assigned value
                    DfgVertexVar* const newp = pair.second;
                    // FIXME: maybe normalize?
                    // Update binding of target variable
                    vscp->user2p(newp);
                    // Update output symbol table of this block
                    oSymTab[vscp] = newp;
                }
                updates.clear();
                continue;
            }

            // Terminator branches
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                UASSERT_OBJ(ifp == stmtps.back(), ifp, "Branch should be last statement");
                // Convert condition, give up if failed
                DfgVertex* condp = m_converter.convert(*m_logicp, ifp->condp());
                if (!condp) {
                    ++m_ctx.m_synt.nonSynConv;
                    return false;
                }
                // Single bit condition can be use directly, otherwise: use 'condp != 0'
                if (condp->width() != 1) {
                    FileLine* const flp = condp->fileline();
                    DfgNeq* const neqp = make<DfgNeq>(flp, DfgDataType::packed(1));
                    neqp->lhsp(make<DfgConst>(flp, condp->width(), 0U));
                    neqp->rhsp(condp);
                    condp = neqp;
                }
                condpr = condp;
                continue;
            }

            // Unhandled
            ++m_ctx.m_synt.nonSynStmt;
            return false;
        }

        return true;
    }

    // Assign path predicates to the outgoing control flow edges of the given block
    void assignPathPredicates(const CfgBlock& bb) {
        // Nothing to do for the exit block
        if (bb.isExit()) return;

        // Get the predicate of this block
        DfgVertex* const predp = [&]() -> DfgVertex* {
            // Entry block has no predecessors, use constant true
            if (bb.isEnter()) return make<DfgConst>(m_logicp->fileline(), 1U, 1U);

            // For any other block, 'or' together all the incoming predicates
            const auto& inEdges = bb.inEdges();
            auto it = inEdges.begin();
            DfgVertex* resp = m_edgeToPredicatep[static_cast<const CfgEdge&>(*it)];
            while (++it != inEdges.end()) {
                DfgOr* const orp = make<DfgOr>(resp->fileline(), resp->dtype());
                orp->rhsp(resp);
                orp->lhsp(m_edgeToPredicatep[static_cast<const CfgEdge&>(*it)]);
                resp = orp;
            }
            return resp;
        }();

        size_t n = m_nPathPred++;  // Sequence number for temporaries
        const DfgDataType& dtype = predp->dtype();

        const auto mkTmp = [&](FileLine* flp, const char* name, DfgVertex* srcp) {
            const std::string prefix = "_BB" + std::to_string(bb.id()) + "_" + name;
            DfgVertexVar* const tmpp = m_converter.createTmp(*m_logicp, flp, dtype, prefix, n);
            tmpp->srcp(srcp);
            return tmpp;
        };

        // Assign it to a variable in case it's used multiple times
        DfgVertexVar* const pInp = mkTmp(predp->fileline(), "PathIn", predp);

        // For uncondional branches, the successor predicate edge is the same
        if (!bb.isBranch()) {
            m_edgeToPredicatep[bb.takenEdgep()] = mkTmp(pInp->fileline(), "Goto", pInp);
            return;
        }

        // For branches, we need to factor in the branch condition
        DfgVertex* const condp = m_bbToCondp[bb];
        FileLine* const flp = condp->fileline();

        // Predicate for taken branch: 'predp & condp'
        {
            DfgAnd* const takenPredp = make<DfgAnd>(flp, dtype);
            takenPredp->lhsp(pInp);
            takenPredp->rhsp(condp);
            m_edgeToPredicatep[bb.takenEdgep()] = mkTmp(flp, "Taken", takenPredp);
        }

        // Predicate for untaken branch: 'predp & ~condp'
        {
            DfgAnd* const untknPredp = make<DfgAnd>(flp, dtype);
            untknPredp->lhsp(pInp);
            DfgNot* const notp = make<DfgNot>(flp, dtype);
            notp->srcp(condp);
            untknPredp->rhsp(notp);
            m_edgeToPredicatep[bb.untknEdgep()] = mkTmp(flp, "Untkn", untknPredp);
        }
    }

    // Returns true if all external updates to volatile variables are observed correctly
    bool checkExtWrites() {
        for (const DfgVertex* const vtxp : m_logicp->synth()) {
            const DfgVertexVar* const varp = vtxp->cast<DfgVertexVar>();
            if (!varp) continue;
            // If the variable we synthesized this vertex for is volatile, and
            // the value of the synthesized temporary is observed, we might be
            // missing an external update, so we mut give up.
            if (!varp->hasSinks()) continue;
            if (!DfgVertexVar::isVolatile(varp->tmpForp())) continue;
            ++m_ctx.m_synt.nonSynExtWrite;
            return false;
        }
        return true;
    }

    // Add the synthesized values as drivers to the output variables of the current DfgLogic
    bool addSynthesizedOutput(SymTab& oSymTab) {
        // It's possible we think a variable is written by the DfgLogic when
        // it actauly isn't, e.g.: '{a[0], b[0]}[1] = ...' does not write 'b'.
        // These LHS forms can happen after some earlier tranforms. We
        // should just run V3Const on them earlier, but we will do belt and
        // braces and check here too. We can't touch any output variables if so.
        const bool missing = m_logicp->foreachSink([&](const DfgVertex& sink) {
            const DfgUnresolved* const unresolvedp = sink.as<DfgUnresolved>();
            AstVarScope* const vscp = unresolvedp->singleSink()->as<DfgVertexVar>()->vscp();
            return !oSymTab.count(vscp);
        });
        if (missing) {
            ++m_ctx.m_synt.nonSynFalseWrite;
            return false;
        }

        // Add sinks to read the computed values for the target variables
        m_logicp->foreachSink([&](DfgVertex& sink) {
            DfgUnresolved* const unresolvedp = sink.as<DfgUnresolved>();
            const DfgVertexVar* const varp = unresolvedp->singleSink()->as<DfgVertexVar>();
            DfgVertexVar* const resp = oSymTab.at(varp->vscp());
            UASSERT_OBJ(resp->srcp(), resp, "Undriven result");
            unresolvedp->addDriver(resp);
            return false;  // OK, continue
        });

        return true;
    }

    // Synthesize the given AstAssignW. Returns true on success.
    bool synthesizeAssignW(AstAssignW* nodep) {
        ++m_ctx.m_synt.inputAssign;

        // Construct an equivalent AstAssign
        AstNodeExpr* const lhsp = nodep->lhsp()->cloneTree(false);
        AstNodeExpr* const rhsp = nodep->rhsp()->cloneTree(false);
        AstAssign* const assignp = new AstAssign{nodep->fileline(), lhsp, rhsp};

        // The input and output symbol tables
        SymTab iSymTab;
        SymTab oSymTab;

        // Initialzie input symbol table
        initializeEntrySymbolTable(iSymTab);

        // Synthesize as if it was in a single CfgBlock CFG
        DfgVertex* condp = nullptr;
        const bool success = synthesizeBasicBlock(oSymTab, condp, {assignp}, iSymTab);
        UASSERT_OBJ(!condp, nodep, "Conditional AstAssignW ???");
        // Delete auxiliary AstAssign
        VL_DO_DANGLING(assignp->deleteTree(), assignp);
        if (!success) return false;

        // Check exernal writes are observed correctly
        if (!checkExtWrites()) return false;

        // Add resolved output variable drivers
        return addSynthesizedOutput(oSymTab);
    }

    // Synthesize the given AstAlways. Returns true on success.
    bool synthesizeCfg(CfgGraph& cfg) {
        ++m_ctx.m_synt.inputAlways;

        // If there is a backward edge (loop), we can't synthesize it
        if (cfg.containsLoop()) {
            ++m_ctx.m_synt.nonSynLoop;
            ++m_ctx.m_synt.cfgCyclic;
            return false;
        }

        // If it's a trivial CFG we can save on some work
        if (cfg.nBlocks() == 1) {
            ++m_ctx.m_synt.cfgTrivial;
        } else {
            // Insert two-way join blocks to aid multiplexer ordering
            if (cfg.insertTwoWayJoins()) {
                ++m_ctx.m_synt.cfgSp;
            } else {
                ++m_ctx.m_synt.cfgDag;
            }
            // Initialize maps needed for non-trivial CFGs
            m_domTree = CfgDominatorTree{cfg};
            m_edgeToPredicatep = cfg.makeEdgeMap<DfgVertexVar*>();
        }

        // Initialize CfgMaps
        m_bbToISymTab = cfg.makeBlockMap<SymTab>();
        m_bbToOSymTab = cfg.makeBlockMap<SymTab>();
        m_bbToCondp = cfg.makeBlockMap<DfgVertexVar*>();

        // Synthesize all blocks
        for (const V3GraphVertex& vtx : cfg.vertices()) {
            const CfgBlock& bb = static_cast<const CfgBlock&>(vtx);
            // Prepare the input symbol table of this block (enter, or join predecessor blocks)
            if (!createInputSymbolTable(bb)) return false;
            // Synthesize this block
            DfgVertex* condp = nullptr;
            if (!synthesizeBasicBlock(m_bbToOSymTab[bb], condp, bb.stmtps(), m_bbToISymTab[bb])) {
                return false;
            }
            // Create a temporary for the branch condition as it might be used multiple times
            if (condp) {
                FileLine* const flp = condp->fileline();
                const DfgDataType& dtype = condp->dtype();
                const std::string prefix = "_BB" + std::to_string(bb.id()) + "_Cond";
                const size_t n = m_nBranchCond++;
                DfgVertexVar* const vp = m_converter.createTmp(*m_logicp, flp, dtype, prefix, n);
                vp->srcp(condp);
                m_bbToCondp[bb] = vp;
            }
            // Set the path predicates on the successor edges
            assignPathPredicates(bb);
        }

        // Check exernal writes are observed correctly
        if (!checkExtWrites()) return false;

        // Add resolved output variable drivers
        return addSynthesizedOutput(m_bbToOSymTab[cfg.exit()]);
    }

    // Synthesize a DfgLogic into regular vertices. Returns ture on success.
    bool synthesize(DfgLogic& vtx) {
        VL_RESTORER(m_logicp);
        m_logicp = &vtx;

        if (AstAssignW* const ap = VN_CAST(vtx.nodep()->stmtsp(), AssignW)) {
            if (ap->nextp()) return false;
            if (!synthesizeAssignW(ap)) return false;
            ++m_ctx.m_synt.synthAssign;
            return true;
        }

        if (!synthesizeCfg(vtx.cfg())) return false;
        ++m_ctx.m_synt.synthAlways;
        return true;
    }

    // Revert all DfgLogic in m_toRevert, or DfgLogic driving the DfgUnresolved
    // vertices in m_toRevert, and transitively the same for any DfgUnresolved
    // driven by the reverted DfgLogic. Delete all DfgUnresolved involed.
    void revert(VDouble0& statCountr) {
        m_toRevert.foreach([&](DfgVertex& vtx) {
            // Process DfgLogic
            if (DfgLogic* const vtxp = vtx.cast<DfgLogic>()) {
                UASSERT_OBJ(vtxp->selectedForSynthesis(), vtxp, "Shouldn't reach here unselected");
                // Revert this logic
                UASSERT_OBJ(!vtxp->reverted(), vtxp, "Should be reverting now");
                ++statCountr;
                for (DfgVertex* const p : vtxp->synth()) VL_DO_DANGLING(p->unlinkDelete(m_dfg), p);
                vtxp->synth().clear();
                vtxp->setReverted();
                // Add all DfgUnresolved it drives to the work list
                vtxp->foreachSink([&](DfgVertex& snk) {
                    m_toRevert.push_front(*snk.as<DfgUnresolved>());
                    return false;
                });
                return;
            }

            // Process DfgUnresolved
            if (DfgUnresolved* const vtxp = vtx.cast<DfgUnresolved>()) {
                // The result variable will be driven from Ast code, mark as such
                vtxp->singleSink()->as<DfgVertexVar>()->setHasModWrRefs();
                // Add all driving DfgLogic to the work list
                vtxp->foreachSource([&](DfgVertex& src) {
                    DfgLogic* const lp = src.cast<DfgLogic>();
                    if (lp && !lp->reverted()) m_toRevert.push_front(*lp);
                    return false;
                });
                // Delete the DfgUnresolved driver
                VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
                return;
            }

            // There should be nothing else on the worklist
            vtx.v3fatalSrc("Unexpected vertex type");
        });
    }

    // Within the source cone of 'vtxp', rellink all references to 'varp' to refer to 'tmpp'
    void relinkSourceCone(DfgVertex* const vtxp, DfgVertexVar* const varp,
                          DfgVertexVar* const tmpp, std::unordered_set<DfgVertex*>& visited) {
        // Mark visited, stop if already visited
        if (!visited.emplace(vtxp).second) return;

        // FIXME: this should only visit within the DfgLogic worth of neighborhood, otherwise slow
        const size_t nInputs = vtxp->nInputs();
        for (size_t i = 0; i < nInputs; ++i) {
            DfgVertex* const inp = vtxp->inputp(i);
            if (!inp) continue;
            if (inp == varp) {
                vtxp->inputp(i, tmpp);
            } else {
                relinkSourceCone(inp, varp, tmpp, visited);
            }
        }
    }

    // Synthesize all of the given vertices
    void main() {
        //-------------------------------------------------------------------
        UINFO(5, "Step 0: Remove all DfgLogic not selected for synthesis");
        for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
            // Only processing DfgUnresolved
            if (!vtxp->is<DfgUnresolved>()) continue;
            bool anySelected = false;
            bool anyUnselected = false;
            vtxp->foreachSource([&](DfgVertex& src) {
                const DfgLogic& logic = *src.as<DfgLogic>();
                if (logic.selectedForSynthesis()) {
                    anySelected = true;
                } else {
                    anyUnselected = true;
                }
                return false;
            });
            // There should be a driver
            UASSERT_OBJ(anySelected || anyUnselected, vtxp, "'DfgUnresolved' with no driver");
            // All drivers should be selected or all should be unselected
            UASSERT_OBJ(!(anySelected && anyUnselected), vtxp, "Invalid 'DfgLogic' selection");
            // If all drivers are unselected, delete this DfgUnresolved here
            if (anyUnselected) {
                // The result variable will be driven from Ast code, mark as such
                vtxp->singleSink()->as<DfgVertexVar>()->setHasModWrRefs();
                VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
            }
        }
        for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
            // Only processing DfgLogic
            DfgLogic* const logicp = vtxp->cast<DfgLogic>();
            if (!logicp) continue;
            if (logicp->selectedForSynthesis()) continue;
            // There should be no sinks left for unselected DfgLogic, delete them here
            UASSERT_OBJ(!logicp->hasSinks(), vtxp, "Unselected 'DfgLogic' with sinks remaining");
            // Input variables will be read in Ast code, add Ast reference vertices
            // AstVarScope::user4p() -> corresponding DfgVertexVar* in the graph
            const VNUser4InUse m_user4InUse;
            logicp->foreachSource([](DfgVertex& src) {
                src.as<DfgVertexVar>()->vscp()->user4p(&src);
                return false;
            });
            V3DfgPasses::addAstRefs(m_dfg, logicp->nodep(), [](AstNode* varp) {  //
                return varp->user4u().to<DfgVertexVar*>();
            });
            VL_DO_DANGLING(logicp->unlinkDelete(m_dfg), logicp);
        }
        debugDump("synth-selected");

        //-------------------------------------------------------------------
        UINFO(5, "Step 1: Attempting to synthesize each of the selected DfgLogic");
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            DfgLogic* const logicp = vtx.cast<DfgLogic>();
            if (!logicp) continue;

            // We should only have DfgLogic remaining that was selected for synthesis
            UASSERT_OBJ(logicp->selectedForSynthesis(), logicp, "Unselected DfgLogic remains");

            // Debug aid
            const auto debugCallback = [&]() -> void {
                // This is the breaking logic
                m_debugLogicp = logicp;
                // Dump it
                UINFOTREE(0, logicp->nodep(), "Problematic DfgLogic: " << logicp, "  ");
                V3EmitV::debugVerilogForTree(logicp->nodep(), std::cout);
                debugDump("synth-lastok");
            };
            if (VL_UNLIKELY(s_dfgSynthDebugBisect.stop(debugCallback))) break;

            // Synthesize it, if failed, enqueue for reversion
            if (!synthesize(*logicp)) {
                logicp->setNonSynthesizable();
                m_toRevert.push_front(*logicp);
            }
        }
        debugDump("synth-converted");

        //-------------------------------------------------------------------
        UINFO(5, "Step 2: Revert drivers of variables with unsynthesizeable drivers");
        // We do this as the variables might be multi-driven, we can't know if synthesis failed
        revert(m_ctx.m_synt.revertNonSyn);
        debugDump("synth-reverted");

        //-------------------------------------------------------------------
        UINFO(5, "Step 3: Resolve synthesized drivers of original (non-temporary) variables");
        // Compute resolved drivers of all variables
        for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
            DfgUnresolved* const unresolvedp = vtxp->cast<DfgUnresolved>();
            if (!unresolvedp) continue;

            // Pick up the variable
            DfgVertexVar* const varp = unresolvedp->singleSink()->as<DfgVertexVar>();
            // Pick up synthesized drivers
            std::vector<DfgVertexVar*> driverps;
            unresolvedp->foreachSource([&](DfgVertex& src) {
                DfgVertexVar* const srcp = src.cast<DfgVertexVar>();
                if (!srcp) return false;
                driverps.emplace_back(srcp);
                return false;
            });
            // FIXME: warn on multiple drivers from different blocks

            // These writes are from different combinational blocks, ordering is undefined,
            // and also unimporant in well formed designs without multiple drivers, so we can
            // apply the updates sequentially in an arbitary stable order
            DfgVertexVar* tmpp = driverps.front();
            for (size_t i = 1; i < driverps.size(); ++i) {
                DfgVertexVar* const driverp = driverps[i];
                std::unordered_set<DfgVertex*> visited;
                relinkSourceCone(driverp, varp, tmpp, visited);
                tmpp = driverp;
            }
            // Make the final driver drive the variable
            varp->srcp(driverps.back());
            // Done with this DfgUnresolved, delete it
            VL_DO_DANGLING(unresolvedp->unlinkDelete(m_dfg), unresolvedp);
        }
        debugDump("synth-resolved");

        //-------------------------------------------------------------------
        UINFO(5, "Step 4: Remove all remaining DfgLogic and DfgUnresolved");
        for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
            // Previous step should have removed all DfgUnresolved
            UASSERT_OBJ(!vtxp->is<DfgUnresolved>(), vtxp, "DfgUnresolved remains");

            // Process only DfgLogic
            DfgLogic* const logicp = vtxp->cast<DfgLogic>();
            if (!logicp) continue;

            // Earlier pass should have removed all sinks
            UASSERT_OBJ(!logicp->hasSinks(), logicp, "DfgLogic sink remains");

            if (!logicp->synth().empty()) {
                // If synthesized, delete the corresponding AstNode. It is now in Dfg.
                logicp->nodep()->unlinkFrBack()->deleteTree();
            } else {
                // Not synthesized. Logic stays in Ast. Add Ast reference vertices.
                // Outputs already marked by revertTransivelyAndRemove.
                // AstVarScope::user4p() -> corresponding DfgVertexVar* in the graph
                const VNUser4InUse m_user4InUse;
                logicp->foreachSource([](DfgVertex& src) {
                    src.as<DfgVertexVar>()->vscp()->user4p(&src);
                    return false;
                });
                V3DfgPasses::addAstRefs(m_dfg, logicp->nodep(), [](AstNode* varp) {  //
                    return varp->user4u().to<DfgVertexVar*>();
                });
            }

            // Delete this DfgLogic
            VL_DO_DANGLING(logicp->unlinkDelete(m_dfg), logicp);
        }
        // Reset the debug pointer, we have deleted it in the loop above ...
        m_debugLogicp = nullptr;
        debugDump("synth-rmlogics");

        // FIXME: flatten out inserts
    }

    // CONSTRUCTOR
    AstToDfgSynthesize(DfgGraph& dfg, V3DfgSynthesisContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx}
        , m_converter{dfg, ctx} {
        main();
    }

public:
    static void apply(DfgGraph& dfg, V3DfgSynthesisContext& ctx) {
        AstToDfgSynthesize{dfg, ctx};

        // Final step outside, as both AstToDfgSynthesize and removeUnused used DfgUserMap
        UINFO(5, "Step 6: Remove all unused vertices");
        V3DfgPasses::removeUnused(dfg);
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed("synth-rmunused");

        // No operation vertex should have multiple sinks. Cyclic decomoposition
        // depends on this and it can easily be ensured by using temporaries.
        // Also, all sources should be connected at this point
        if (v3Global.opt.debugCheck()) {
            for (DfgVertex& vtx : dfg.opVertices()) {
                UASSERT_OBJ(!vtx.hasMultipleSinks(), &vtx, "Operation has multiple sinks");
                for (size_t i = 0; i < vtx.nInputs(); ++i) {
                    UASSERT_OBJ(vtx.inputp(i), &vtx, "Unconnected source operand");
                }
            }
            V3DfgPasses::typeCheck(dfg);
        }
    }
};

// Decide which DfgLogic to attempt to synthesize
static void dfgSelectLogicForSynthesis(DfgGraph& dfg) {
    // If we are told to synthesize everything, we will do so ...
    if (v3Global.opt.fDfgSynthesizeAll()) {
        for (DfgVertex& vtx : dfg.opVertices()) {
            if (DfgLogic* const logicp = vtx.cast<DfgLogic>()) logicp->setSelectedForSynthesis();
        }
        return;
    }

    // Otherwise figure out which vertices are likely worth synthesizing.

    // Bather circular variables
    std::vector<DfgVertexVar*> circularVarps;
    {
        DfgUserMap<uint64_t> scc = dfg.makeUserMap<uint64_t>();
        V3DfgPasses::colorStronglyConnectedComponents(dfg, scc);
        for (DfgVertexVar& var : dfg.varVertices()) {
            if (!scc.at(var)) continue;
            // This is a circular variable
            circularVarps.emplace_back(&var);
        }
    }

    // We need to expand the selection to cover all drivers, use a work list
    DfgWorklist worklist{dfg};

    // Synthesize all drivers of circular variables
    for (const DfgVertexVar* const varp : circularVarps) {
        varp->srcp()->as<DfgUnresolved>()->foreachSource([&](DfgVertex& driver) {
            worklist.push_front(*driver.as<DfgLogic>());
            return false;
        });
    }

    // Choose some simple special cases to always synthesize
    for (DfgVertex& vtx : dfg.opVertices()) {
        DfgLogic* const logicp = vtx.cast<DfgLogic>();
        if (!logicp) continue;
        // Blocks corresponding to continuous assignments
        if (logicp->nodep()->keyword() == VAlwaysKwd::CONT_ASSIGN) {
            worklist.push_front(*logicp);
            continue;
        }
        const CfgGraph& cfg = logicp->cfg();
        // Straight line code with no branches
        if (cfg.nBlocks() == 1) {
            worklist.push_front(*logicp);
            continue;
        }
        // Simple blocks driving exactly 1 variable, e.g if (rst) a = b else a = c;
        if (!logicp->hasMultipleSinks() && cfg.nBlocks() <= 4 && cfg.nEdges() <= 4) {
            worklist.push_front(*logicp);
        }
    }

    // Now expand to cover all logic driving the same set of variables and mark
    worklist.foreach([&](DfgVertex& vtx) {
        DfgLogic& logic = *vtx.as<DfgLogic>();
        UASSERT_OBJ(!logic.selectedForSynthesis(), &vtx, "Should not be visited twice");
        // Mark as selected for synthesis
        logic.setSelectedForSynthesis();
        // Enqueue all other logic driving the same variables as this one
        logic.foreachSink([&](DfgVertex& sink) {
            sink.as<DfgUnresolved>()->foreachSource([&](DfgVertex& sibling) {
                DfgLogic& siblingLogic = *sibling.as<DfgLogic>();
                if (!siblingLogic.selectedForSynthesis()) worklist.push_front(siblingLogic);
                return false;
            });
            return false;
        });
    });
}

void V3DfgPasses::synthesize(DfgGraph& dfg, V3DfgContext& ctx) {
    // Select which DfgLogic to attempt to synthesize
    dfgSelectLogicForSynthesis(dfg);
    // Synthesize them - also removes un-synthesized DfgLogic, so must run even if nothing selected
    AstToDfgSynthesize::apply(dfg, ctx.m_synthContext);
}
