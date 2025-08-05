// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert AstModule to DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Convert and AstModule to a DfgGraph. We proceed by visiting convertible logic blocks (e.g.:
// AstAssignW of appropriate type and with no delays), recursively constructing DfgVertex instances
// for the expressions that compose the subject logic block. If all expressions in the current
// logic block can be converted, then we delete the logic block (now represented in the DfgGraph),
// and connect the corresponding DfgVertex instances appropriately. If some of the expressions were
// not convertible in the current logic block, we revert (delete) the DfgVertex instances created
// for the logic block, and leave the logic block in the AstModule. Any variable reference from
// non-converted logic blocks (or other constructs under the AstModule) are marked as being
// referenced in the AstModule, which is relevant for later optimization.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Cfg.h"
#include "V3Const.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3EmitV.h"
#include "V3Os.h"

#include <algorithm>
#include <iterator>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Create a DfgVertex out of a AstNodeExpr. For most AstNodeExpr subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename T_Vertex, typename T_Node>
T_Vertex* makeVertex(const T_Node* nodep, DfgGraph& dfg) {
    return new T_Vertex{dfg, nodep->fileline(), DfgGraph::toDfgDType(nodep->dtypep())};
}

template <>
DfgArraySel* makeVertex<DfgArraySel, AstArraySel>(const AstArraySel* nodep, DfgGraph& dfg) {
    // Some earlier passes create malformed ArraySels, just bail on those...
    // See t_bitsel_wire_array_bad
    if (VN_IS(nodep->fromp(), Const)) return nullptr;
    if (!VN_IS(nodep->fromp()->dtypep()->skipRefp(), UnpackArrayDType)) return nullptr;
    return new DfgArraySel{dfg, nodep->fileline(), DfgGraph::toDfgDType(nodep->dtypep())};
}

}  // namespace

// Visitor that can convert combinational Ast logic constructs/assignments to Dfg
template <bool T_Scoped>
class AstToDfgConverter final : public VNVisitor {
    // NODE STATE
    // AstNodeExpr/AstVar/AstVarScope::user2p -> DfgVertex* for this Node
    // AstVar::user3()                        -> int temporary counter for variable
    const VNUser3InUse m_user3InUse;

    // TYPES
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;

    // STATE
    DfgGraph& m_dfg;  // The graph being built
    V3DfgSynthesisContext& m_ctx;  // The context for stats

    // Current logic vertex we are synthesizing
    DfgLogic* m_logicp = nullptr;
    // Variable updates produced by currently conveted statement
    std::unordered_map<Variable*, DfgVertexVar*>* m_updatesp;  // TODO: make updates deterministic

    bool m_foundUnhandled = false;  // Found node not implemented as DFG or not implemented 'visit'
    bool m_converting = false;  // We are trying to convert some logic at the moment

    // METHODS
    static Variable* getTarget(const AstVarRef* refp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<Variable*>(refp->varScopep());
        } else {
            return reinterpret_cast<Variable*>(refp->varp());
        }
    }

    static AstVar* getAstVar(Variable* vp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<AstVarScope*>(vp)->varp();
        } else {
            return reinterpret_cast<AstVar*>(vp);
        }
    }

    // Allocate a new non-variable vertex, add it to the currently synthesized logic
    template <typename Vertex, typename... Args>
    Vertex* make(Args&&... args) {
        static_assert(!std::is_base_of<DfgVertexVar, Vertex>::value, "Do not use for variables");
        static_assert(std::is_base_of<DfgVertex, Vertex>::value, "'Vertex' must be a 'DfgVertex'");
        Vertex* const vtxp = new Vertex{std::forward<Args>(args)...};
        m_logicp->synth().emplace_back(vtxp);
        return vtxp;
    }

    DfgVertexVar* getNet(Variable* varp) {
        UASSERT_OBJ(varp->user2p(), varp, "Missing DfgVertexVar during synthesis");
        return varp->user2u().template to<DfgVertexVar*>();
    }

    // Returns true if the expression cannot (or should not) be represented by DFG
    bool unhandled(AstNodeExpr* nodep) {
        // Short-circuiting if something was already unhandled
        if (!m_foundUnhandled) {
            // Impure nodes cannot be represented
            if (!nodep->isPure()) {
                m_foundUnhandled = true;
                ++m_ctx.m_conv.nonRepImpure;
            }
            // Check node has supported dtype
            if (!DfgGraph::isSupported(nodep->dtypep())) {
                m_foundUnhandled = true;
                ++m_ctx.m_conv.nonRepDType;
            }
        }
        return m_foundUnhandled;
    }

    bool isSupported(const AstVarRef* nodep) {
        // Cannot represent cross module references
        if (nodep->classOrPackagep()) return false;
        // Check target
        return DfgGraph::isSupported(getTarget(nodep));
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
        UASSERT_OBJ(vtxp, nodep, "Missing Dfg vertex after covnersion");
        return vtxp;
    }

    // Given an LValue expression, return the splice node that writes the
    // destination, together with the index to use for splicing in the value.
    // Returns {nullptr, 0}, if the given LValue expression is not supported.
    std::pair<DfgVertexSplice*, uint32_t> convertLValue(AstNodeExpr* nodep) {
        if (AstVarRef* const vrefp = VN_CAST(nodep, VarRef)) {
            if (!isSupported(vrefp)) {
                ++m_ctx.m_conv.nonRepLValue;
                return {nullptr, 0};
            }

            Variable* const tgtp = getTarget(vrefp);
            // Get or create a new temporary
            DfgVertexVar*& r = (*m_updatesp)[tgtp];
            if (!r) r = createTmp(m_dfg, *m_logicp, tgtp, "SynthAssign");
            DfgVertexVar* const vtxp = r;

            // Ensure the Splice driver exists for this variable
            if (!vtxp->srcp()) {
                FileLine* const flp = vtxp->fileline();
                AstNodeDType* const dtypep = vtxp->dtypep();
                if (vtxp->is<DfgVarPacked>()) {
                    DfgSplicePacked* const newp = make<DfgSplicePacked>(m_dfg, flp, dtypep);
                    vtxp->srcp(newp);
                } else if (vtxp->is<DfgVarArray>()) {
                    DfgSpliceArray* const newp = make<DfgSpliceArray>(m_dfg, flp, dtypep);
                    vtxp->srcp(newp);
                } else {
                    nodep->v3fatalSrc("Unhandled DfgVertexVar sub-type");  // LCOV_EXCL_LINE
                }
            }
            // Return the Splice driver
            return {vtxp->srcp()->as<DfgVertexSplice>(), 0};
        }

        if (AstSel* selp = VN_CAST(nodep, Sel)) {
            // Only handle constant selects
            const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const);
            if (!lsbp) {
                ++m_ctx.m_conv.nonRepLValue;
                return {nullptr, 0};
            }
            uint32_t lsb = lsbp->toUInt();

            // Convert the 'fromp' sub-expression
            const auto pair = convertLValue(selp->fromp());
            if (!pair.first) return {nullptr, 0};
            DfgSplicePacked* const splicep = pair.first->template as<DfgSplicePacked>();
            // Adjust index.
            lsb += pair.second;

            // AstSel doesn't change type kind (array vs packed), so we can use
            // the existing splice driver with adjusted lsb
            return {splicep, lsb};
        }

        if (AstArraySel* const aselp = VN_CAST(nodep, ArraySel)) {
            // Only handle constant selects
            const AstConst* const indexp = VN_CAST(aselp->bitp(), Const);
            if (!indexp) {
                ++m_ctx.m_conv.nonRepLValue;
                return {nullptr, 0};
            }
            uint32_t index = indexp->toUInt();

            // Convert the 'fromp' sub-expression
            const auto pair = convertLValue(aselp->fromp());
            if (!pair.first) return {nullptr, 0};
            DfgSpliceArray* const splicep = pair.first->template as<DfgSpliceArray>();
            // Adjust index. Note pair.second is always 0, but we might handle array slices later..
            index += pair.second;

            // Ensure the Splice driver exists for this element
            if (!splicep->driverAt(index)) {
                FileLine* const flp = nodep->fileline();
                AstNodeDType* const dtypep = DfgGraph::toDfgDType(nodep->dtypep());
                if (VN_IS(dtypep, BasicDType)) {
                    DfgSplicePacked* const newp = make<DfgSplicePacked>(m_dfg, flp, dtypep);
                    AstNodeDType* const uaDtypep = DfgGraph::dtypeArray(dtypep, 1);
                    DfgUnitArray* const uap = make<DfgUnitArray>(m_dfg, flp, uaDtypep);
                    uap->srcp(newp);
                    splicep->addDriver(flp, index, uap);
                } else if (VN_IS(dtypep, UnpackArrayDType)) {
                    DfgSpliceArray* const newp = make<DfgSpliceArray>(m_dfg, flp, dtypep);
                    splicep->addDriver(flp, index, newp);
                } else {
                    nodep->v3fatalSrc("Unhandled AstNodeDType sub-type");  // LCOV_EXCL_LINE
                }
            }

            // Return the splice driver
            DfgVertex* driverp = splicep->driverAt(index);
            if (DfgUnitArray* const uap = driverp->cast<DfgUnitArray>()) driverp = uap->srcp();
            return {driverp->as<DfgVertexSplice>(), 0};
        }

        ++m_ctx.m_conv.nonRepLValue;
        return {nullptr, 0};
    }

    // Given the LHS of an assignment, and the vertex representing the RHS,
    // connect up the RHS to drive the targets.
    // Returns true on success, false if the LHS is not representable.
    bool convertAssignment(FileLine* flp, AstNodeExpr* lhsp, DfgVertex* vtxp) {
        // Represents a DFG assignment contributed by the AST assignment with the above 'lhsp'.
        // There might be multiple of these if 'lhsp' is a concatenation.
        struct Assignment final {
            DfgVertexSplice* m_lhsp;
            uint32_t m_idx;
            DfgVertex* m_rhsp;
            Assignment() = delete;
            Assignment(DfgVertexSplice* lhsp, uint32_t idx, DfgVertex* rhsp)
                : m_lhsp{lhsp}
                , m_idx{idx}
                , m_rhsp{rhsp} {}
        };

        // Convert each concatenation LHS separately, gather all assignments
        // we need to do into 'assignments', return true if all LValues
        // converted successfully.
        std::vector<Assignment> assignments;
        const std::function<bool(AstNodeExpr*, DfgVertex*)> convertAllLValues
            = [&](AstNodeExpr* lhsp, DfgVertex* vtxp) -> bool {
            // Simplify the LHS, to get rid of things like SEL(CONCAT(_, _), _)
            lhsp = VN_AS(V3Const::constifyExpensiveEdit(lhsp), NodeExpr);

            // Concatenation on the LHS, convert each parts
            if (AstConcat* const concatp = VN_CAST(lhsp, Concat)) {
                AstNodeExpr* const cLhsp = concatp->lhsp();
                AstNodeExpr* const cRhsp = concatp->rhsp();
                // Convert Left of concat
                FileLine* const lFlp = cLhsp->fileline();
                AstNodeDType* const lDtp = DfgGraph::toDfgDType(cLhsp->dtypep());
                DfgSel* const lVtxp = make<DfgSel>(m_dfg, lFlp, lDtp);
                lVtxp->fromp(vtxp);
                lVtxp->lsb(cRhsp->width());
                if (!convertAllLValues(cLhsp, lVtxp)) return false;
                // Convert Rigth of concat
                FileLine* const rFlp = cRhsp->fileline();
                AstNodeDType* const rDtp = DfgGraph::toDfgDType(cRhsp->dtypep());
                DfgSel* const rVtxp = make<DfgSel>(m_dfg, rFlp, rDtp);
                rVtxp->fromp(vtxp);
                rVtxp->lsb(0);
                return convertAllLValues(cRhsp, rVtxp);
            }

            // Non-concatenation, convert the LValue
            const auto pair = convertLValue(lhsp);
            if (!pair.first) return false;
            assignments.emplace_back(pair.first, pair.second, vtxp);
            return true;
        };

        // Convert the given LHS assignment, give up if any LValues failed to convert
        if (!convertAllLValues(lhsp, vtxp)) return false;

        // All successful, connect the drivers
        for (const Assignment& item : assignments) {
            if (DfgSplicePacked* const spp = item.m_lhsp->template cast<DfgSplicePacked>()) {
                spp->addDriver(flp, item.m_idx, item.m_rhsp);
            } else if (DfgSpliceArray* const sap = item.m_lhsp->template cast<DfgSpliceArray>()) {
                AstUnpackArrayDType* const lDtp = VN_AS(sap->dtypep(), UnpackArrayDType);
                AstNodeDType* const lElemDtp = lDtp->subDTypep();
                AstNodeDType* const rDtp = item.m_rhsp->dtypep();
                if (lElemDtp->isSame(rDtp)) {
                    // RHS is assigning an element of this array. Need a DfgUnitArray adapter.
                    FileLine* const flp = item.m_rhsp->fileline();
                    AstNodeDType* const uaDtp = DfgGraph::dtypeArray(rDtp, 1);
                    DfgUnitArray* const uap = make<DfgUnitArray>(m_dfg, flp, uaDtp);
                    uap->srcp(item.m_rhsp);
                    sap->addDriver(flp, item.m_idx, uap);
                } else {
                    // RHS is assigning an array (or array slice). Should be the same element type.
                    AstNodeDType* const rElemDtp = VN_AS(rDtp, UnpackArrayDType)->subDTypep();
                    UASSERT_OBJ(lElemDtp->isSame(rElemDtp), item.m_rhsp, "Mismatched array types");
                    sap->addDriver(flp, item.m_idx, item.m_rhsp);
                }
            } else {
                item.m_lhsp->v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
            }
        }

        return true;
    }

    // Convert the assignment with the given LHS and RHS into DFG.
    // Returns true on success, false if not representable.
    bool convertEquation(FileLine* flp, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        // Check data types are compatible.
        if (!DfgGraph::isSupported(lhsp->dtypep()) || !DfgGraph::isSupported(rhsp->dtypep())) {
            ++m_ctx.m_conv.nonRepDType;
            return false;
        }

        // For now, only direct array assignment is supported (e.g. a = b, but not a = _ ? b : c)
        if (VN_IS(rhsp->dtypep()->skipRefp(), UnpackArrayDType) && !VN_IS(rhsp, VarRef)) {
            ++m_ctx.m_conv.nonRepDType;
            return false;
        }

        // Widths should match at this point
        UASSERT_OBJ(lhsp->width() == rhsp->width(), flp, "Mismatched width reached DFG");

        // Convert the RHS expression
        DfgVertex* const rVtxp = convertRValue(rhsp);
        if (!rVtxp) return false;

        // Connect the RHS vertex to the LHS targets
        if (!convertAssignment(flp, lhsp, rVtxp)) return false;

        // All good
        return true;
    }

    // VISITORS

    // Unhandled node
    void visit(AstNode* nodep) override {
        if (!m_foundUnhandled && m_converting) ++m_ctx.m_conv.nonRepUnknown;
        m_foundUnhandled = true;
    }

    // Expressions - mostly auto generated, but a few special ones
    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;
        // This visit method is only called on RValues, where only read refs are supported
        if (!nodep->access().isReadOnly() || !isSupported(nodep)) {
            m_foundUnhandled = true;
            ++m_ctx.m_conv.nonRepVarRef;
            return;
        }
        nodep->user2p(getNet(getTarget(nodep)));
    }
    void visit(AstConst* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;
        DfgVertex* const vtxp = make<DfgConst>(m_dfg, nodep->fileline(), nodep->num());
        nodep->user2p(vtxp);
    }
    void visit(AstSel* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        iterate(nodep->fromp());
        if (m_foundUnhandled) return;

        FileLine* const flp = nodep->fileline();
        DfgVertex* vtxp = nullptr;
        if (AstConst* const constp = VN_CAST(nodep->lsbp(), Const)) {
            DfgSel* const selp = make<DfgSel>(m_dfg, flp, DfgGraph::toDfgDType(nodep->dtypep()));
            selp->fromp(nodep->fromp()->user2u().to<DfgVertex*>());
            selp->lsb(constp->toUInt());
            vtxp = selp;
        } else {
            iterate(nodep->lsbp());
            if (m_foundUnhandled) return;
            DfgMux* const muxp = make<DfgMux>(m_dfg, flp, DfgGraph::toDfgDType(nodep->dtypep()));
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

    // Create a new temporary variable capable of holding 'varp'
    static DfgVertexVar* createTmp(DfgGraph& dfg, DfgLogic& logic, Variable* varp,
                                   const std::string& prefix) {
        AstVar* const astVarp = getAstVar(varp);
        const std::string prfx = prefix + "_" + astVarp->name();
        const std::string name = dfg.makeUniqueName(prfx, astVarp->user3Inc());
        AstNodeDType* const dtypep = DfgGraph::toDfgDType(astVarp->dtypep());
        AstScope* const scp = T_Scoped ? reinterpret_cast<AstVarScope*>(varp)->scopep() : nullptr;
        DfgVertexVar* const vtxp = dfg.makeNewVar(astVarp->fileline(), name, dtypep, scp);
        logic.synth().emplace_back(vtxp);
        vtxp->varp()->isInternal(true);
        vtxp->tmpForp(varp);
        return vtxp;
    }

    // Convert AstAssign to Dfg, return true if successful.
    // Fills 'updates' with bindings for assigned variables.
    bool convert(std::unordered_map<Variable*, DfgVertexVar*>& updates, DfgLogic& vtx,
                 AstAssign* nodep) {
        UASSERT_OBJ(updates.empty(), nodep, "'updates' should be empty");
        VL_RESTORER(m_updatesp);
        VL_RESTORER(m_logicp);
        m_updatesp = &updates;
        m_logicp = &vtx;
        // Assignment with timing control shouldn't make it this far
        UASSERT_OBJ(!nodep->timingControlp(), nodep, "Shouldn't make it this far");
        // Convert it
        ++m_ctx.m_conv.inputAssignments;
        const bool success = convertEquation(nodep->fileline(), nodep->lhsp(), nodep->rhsp());
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

// For debugging, we can stop synthesizing after a certain number of vertices.
// for this we need a global counter (inside the template makes multiple copies)
static size_t s_dfgSynthDebugCount = 0;
// The number of vertices we stop after can be passed in through the environment
// you can then use a bisection search over this value and look at the dumps
// produced with the lowest failing value
static const size_t s_dfgSynthDebugLimit
    = std::stoull(V3Os::getenvStr("VERILATOR_DFG_SYNTH_DEBUG", "0"));

template <bool T_Scoped>
class AstToDfgSynthesize final {
    // NODE STATE
    // AstNodeExpr/AstVar/AstVarScope::user2p -> DfgVertex* for this Node

    // TYPES
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;
    using SymTab = std::unordered_map<Variable*, DfgVertexVar*>;

    struct Driver final {
        FileLine* m_flp = nullptr;  // Location of driver in source
        uint32_t m_lo = 0;  // Low index of driven range
        uint32_t m_hi = 0;  // High index of driven range
        DfgVertex* m_vtxp = nullptr;  // Driving vertex

        uint32_t size() const { return m_hi - m_lo + 1; }

        Driver() = default;
        Driver(FileLine* flp, uint32_t lo, DfgVertex* vtxp)
            : m_flp{flp}
            , m_lo{lo}
            , m_hi{lo + vtxp->size() - 1}
            , m_vtxp{vtxp} {}
        Driver(FileLine* flp, uint32_t lo, uint32_t hi, DfgVertex* vtxp)
            : m_flp{flp}
            , m_lo{lo}
            , m_hi{hi}
            , m_vtxp{vtxp} {}
        operator bool() const { return m_vtxp != nullptr; }

        bool operator<(const Driver& other) const {
            if (m_lo != other.m_lo) return m_lo < other.m_lo;
            if (m_hi != other.m_hi) return m_hi < other.m_hi;
            return m_flp->operatorCompare(*other.m_flp) < 0;
        }
    };

    // STATE
    DfgGraph& m_dfg;  // The graph being built
    V3DfgSynthesisContext& m_ctx;  // The context for stats
    AstToDfgConverter<T_Scoped> m_converter;  // The convert instance to use for each construct
    // Hold on to the last true variable vertex (temporaries will be added after this)
    DfgVertexVar* const m_lastNonTmpVarp = m_dfg.varVertices().backp();
    DfgLogic* m_logicp = nullptr;  // Current logic vertex we are synthesizing

    // Some debug aid: We stop after synthesizing s_dfgSynthDebugLimit vertices (if non-zero).
    // This is the problematic logic (last one we synthesize), assuming a bisection search
    // over s_dfgSynthDebugLimit.
    DfgLogic* m_debugLogicp = nullptr;
    // Source (upstream) cone of outputs of m_debugLogicp
    std::unique_ptr<std::unordered_set<const DfgVertex*>> m_debugOSrcConep{nullptr};

    // METHODS
    void debugDump(const char* name) {
        // If we have the debugged logic, compute the vertices feeding its outputs
        if (VL_UNLIKELY(m_debugLogicp)) {
            std::vector<const DfgVertex*> outputs;
            m_debugLogicp->forEachSink([&outputs](DfgVertex& v) {  //
                outputs.emplace_back(v.singleSink()->as<DfgVertexVar>());
            });
            m_debugOSrcConep = m_dfg.sourceCone(outputs);
        }

        if (VL_UNLIKELY(dumpDfgLevel() >= 9 || m_debugOSrcConep)) {
            const auto label = m_ctx.prefix() + name;
            m_dfg.dumpDotFilePrefixed(label);
            if (m_debugOSrcConep) {
                // Dump only the subgraph involving the inputs and outputs of the bad vertex
                m_dfg.dumpDotFilePrefixed(label + "-min", [&](const DfgVertex& v) -> bool {
                    return m_debugOSrcConep->count(&v);
                });
            }
        }
    }

    static AstVar* getAstVar(Variable* vp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<AstVarScope*>(vp)->varp();
        } else {
            return reinterpret_cast<AstVar*>(vp);
        }
    }

    // Allocate a new non-variable vertex, add it to the currently synthesized logic
    template <typename Vertex, typename... Args>
    Vertex* make(Args&&... args) {
        static_assert(!std::is_base_of<DfgVertexVar, Vertex>::value, "Do not use for variables");
        static_assert(std::is_base_of<DfgVertex, Vertex>::value, "'Vertex' must be a 'DfgVertex'");
        Vertex* const vtxp = new Vertex{std::forward<Args>(args)...};
        if (m_logicp) m_logicp->synth().emplace_back(vtxp);
        return vtxp;
    }

    ////////////////////////////////
    ////////////////////////////////

    // METHODS
    static std::vector<Driver> gatherAndUnlinkResolvedDrivers(DfgVertexSplice* splicep) {
        std::vector<Driver> drivers;
        drivers.reserve(splicep->arity());
        std::vector<DfgLogic*> udriverps;
        udriverps.reserve(splicep->arity());

        const std::function<void(FileLine*, uint32_t, DfgVertex*)> gather
            = [&](FileLine* flp, uint32_t lo, DfgVertex* vtxp) -> void {
            if (splicep->is<DfgSplicePacked>()) {
                if (DfgConcat* const concatp = vtxp->cast<DfgConcat>()) {
                    DfgVertex* const rhsp = concatp->rhsp();
                    gather(rhsp->fileline(), lo, rhsp);
                    DfgVertex* const lhsp = concatp->lhsp();
                    gather(lhsp->fileline(), lo + rhsp->width(), lhsp);
                    return;
                }
                drivers.emplace_back(flp, lo, vtxp);
            } else if (splicep->is<DfgSpliceArray>()) {
                drivers.emplace_back(flp, lo, vtxp);
            } else {
                splicep->v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
            }
        };

        // Gather and unlink all non-default drivers
        splicep->forEachSourceEdge([&](DfgEdge& edgeA, size_t iA) {
            DfgVertex* const driverAp = edgeA.sourcep();
            UASSERT_OBJ(driverAp, splicep, "Should not have created undriven sources");

            // Leave the default driver alone
            if (driverAp == splicep->defaultp()) return;

            // Gather
            if (!splicep->driverIsUnresolved(iA)) {
                // Previously resolved driver
                gather(splicep->driverFileLine(iA), splicep->driverLo(iA), driverAp);
            } else if (DfgLogic* const logicp = driverAp->cast<DfgLogic>()) {
                // Still unresolved
                udriverps.emplace_back(logicp);
            } else if (!driverAp->is<DfgVertexSplice>()) {
                // Previously unresolved, but now resolved after synthesis into
                // a complete assignment, integrate it.
                UASSERT_OBJ(driverAp->dtypep()->sameTree(splicep->dtypep()), splicep,
                            "Should be driver for whole variable");
                gather(splicep->driverFileLine(iA), 0, driverAp);
            } else {
                // Previously unresolved, but now resolved after synthesis into
                // a partial assignment, integrate each part.
                DfgVertexSplice* const spliceBp = driverAp->as<DfgVertexSplice>();
                spliceBp->forEachSourceEdge([&](DfgEdge& edgeB, size_t iB) {
                    DfgVertex* const driverBp = edgeB.sourcep();
                    UASSERT_OBJ(driverBp, spliceBp, "Should not have created undriven sources");

                    // Leave the default driver alone
                    if (driverBp == spliceBp->defaultp()) return;

                    UASSERT_OBJ(!spliceBp->driverIsUnresolved(iB), spliceBp,
                                "Synthesized driver should not be unresolved");

                    // Resolved driver
                    gather(spliceBp->driverFileLine(iB), spliceBp->driverLo(iB), driverBp);
                });
            }

            // Unlink
            edgeA.unlinkSource();
        });
        splicep->resetSources();

        // Re-inset unresolved drivers
        for (DfgLogic* const vtxp : udriverps) splicep->addUnresolvedDriver(vtxp);

        // Sort the drivers
        std::stable_sort(drivers.begin(), drivers.end());

        return drivers;
    }

    void warnMultidriver(DfgVertexVar& var, const std::string& what, const std::string& sub,
                         FileLine* ap, FileLine* bp) {
        Variable* const varp
            = reinterpret_cast<Variable*>(var.tmpForp() ? var.tmpForp() : var.nodep());

        // Loop index often abused, so suppress
        if (getAstVar(varp)->isUsedLoopIdx()) return;

        varp->v3warn(  //
            MULTIDRIVEN,  //
            what << " of signal '" << varp->prettyName() << sub << "'"
                 << " have multiple combinational drivers."
                 << " This can cause performance degradation.\n"
                 << ap->warnOther() << "... Location of offending driver\n"
                 << ap->warnContextPrimary() << '\n'
                 << bp->warnOther() << "... Location of offending driver\n"
                 << bp->warnContextSecondary());
    }

    // Normalize packed driver - returns true iff no multi-driven bits are present
    bool normalizePacked(DfgVertexVar& var, const std::string& sub,
                         DfgSplicePacked* const splicep) {
        UASSERT_OBJ(splicep->arity() >= 1, splicep, "Undriven DfgSplicePacked");
        // The resolved drivers of 'splicep'
        std::vector<Driver> drivers = gatherAndUnlinkResolvedDrivers(splicep);
        // In case nothing is resolved
        if (drivers.empty()) return true;

        // Check for multiply driven ranges
        bool multiDriven = false;

        // Iterate through the sorted drivers pair-wise
        for (size_t i = 0, j = 1; j < drivers.size();) {
            UASSERT_OBJ(i < j, splicep, "Invalid iteration");
            Driver& iD = drivers[i];
            Driver& jD = drivers[j];
            UASSERT_OBJ(iD.m_lo <= jD.m_lo, splicep, "Should always be sorted");

            // If no overlap, consider next pair
            if (iD.m_hi < jD.m_lo) {
                ++i;
                if (i == j) ++j;
                continue;
            }

            // Found overlap that cannot be resolved
            multiDriven = true;

            // Warn the user
            const std::string lo = std::to_string(jD.m_lo);
            const std::string hi = std::to_string(std::min(iD.m_hi, jD.m_hi));
            const std::string what
                = hi == lo ? ("Bit [" + lo + "]") : ("Bits [" + hi + ":" + lo + "]");
            warnMultidriver(var, what, sub, iD.m_flp, jD.m_flp);

            // Compare next driver
            ++j;
        }

        // Coalesce adjacent ranges
        coalesce(drivers);

        // Reinsert drivers in order
        for (const Driver& d : drivers) splicep->addDriver(d.m_flp, d.m_lo, d.m_vtxp);

        // Done
        return !multiDriven;
    }

    // Normalize array driver - returns true iff no multi-driven bits are present
    bool normalizeArray(DfgVertexVar& var, const std::string& sub, DfgSpliceArray* const splicep) {
        UASSERT_OBJ(splicep->arity() >= 1, splicep, "Undriven DfgSpliceArray");
        // The resolved drivers of 'splicep'
        std::vector<Driver> drivers = gatherAndUnlinkResolvedDrivers(splicep);
        // In case nothing is resolved
        if (drivers.empty()) return true;

        // Combine and check for multiply driven ranges
        bool multiDriven = false;

        // Iterate through the sorted drivers pair-wise
        for (size_t i = 0, j = 1; j < drivers.size();) {
            UASSERT_OBJ(i < j, splicep, "Invalid iteration");
            Driver& iD = drivers[i];
            Driver& jD = drivers[j];

            // If 'j' was moved, step forward
            if (!jD) {
                ++j;
                continue;
            }
            // If 'i' was moved, move 'j' in it's place
            if (!iD) {
                iD = jD;
                jD = Driver{};
                ++j;
                continue;
            }
            // We have 2 valid drivers now
            UASSERT_OBJ(iD.m_lo <= jD.m_lo, splicep, "Should always be sorted");

            // If no overlap, consider next pair
            if (iD.m_hi < jD.m_lo) {
                ++i;
                if (i == j) ++j;
                continue;
            }

            // If writing the same element, attempt to resolve it
            bool resolved = false;
            bool warned = false;
            std::tie(resolved, warned) = [&]() -> std::pair<bool, bool> {
                if (iD.m_lo != jD.m_lo) return {false, false};
                DfgUnitArray* const iUap = iD.m_vtxp->template cast<DfgUnitArray>();
                if (!iUap) return {false, false};
                DfgUnitArray* const jUap = jD.m_vtxp->template cast<DfgUnitArray>();
                if (!jUap) return {false, false};
                DfgVertexSplice* const iSp = iUap->srcp()->template cast<DfgVertexSplice>();
                if (!iSp) return {false, false};
                DfgVertexSplice* const jSp = jUap->srcp()->template cast<DfgVertexSplice>();
                if (!jSp) return {false, false};
                UASSERT_OBJ(iSp->type() == jSp->type(), splicep, "Types should match");
                UASSERT_OBJ(iSp->dtypep()->isSame(jSp->dtypep()), splicep, "DTypes should match");

                // Attempt to combine them. To do this, we create a new splice
                FileLine* const flp = splicep->fileline();
                AstNodeDType* const dtypep = iSp->dtypep();
                DfgVertexSplice* const nSp = iSp->is<DfgSplicePacked>()
                                                 ? static_cast<DfgVertexSplice*>(
                                                     make<DfgSplicePacked>(m_dfg, flp, dtypep))
                                                 : static_cast<DfgVertexSplice*>(
                                                     make<DfgSpliceArray>(m_dfg, flp, dtypep));

                nSp->addUnresolvedDriver(iSp);
                nSp->addUnresolvedDriver(jSp);
                if (!normalizeSplice(var, sub + "[" + std::to_string(iD.m_lo) + "]", nSp)) {
                    VL_DO_DANGLING(nSp->unlinkDelete(m_dfg), nSp);
                    return {false, true};
                }
                // Successfully resolved, Keep using the combined splice, but needs a unit
                DfgUnitArray* const nUap = make<DfgUnitArray>(m_dfg, flp, jUap->dtypep());
                nUap->srcp(nSp);
                iD.m_vtxp = nUap;
                return {true, false};
            }();

            // If sucessfully resolved
            if (resolved) {
                // 'jD' is no longer needed, but the vertices might be used, so don't delete them
                jD = Driver{};
                ++j;
                continue;
            }

            // Found overlap that cannot be resolved
            multiDriven = true;

            // If we didn't warn during the checking of the element, warn now
            if (!warned) {
                const std::string lo = std::to_string(jD.m_lo);
                const std::string hi = std::to_string(std::min(iD.m_hi, jD.m_hi));
                const std::string what
                    = hi == lo ? ("Element [" + lo + "]") : ("Elements [" + hi + ":" + lo + "]");
                warnMultidriver(var, what, sub, iD.m_flp, jD.m_flp);
            }

            // Compare next driver
            ++j;
        }

        // Reinsert drivers in order
        for (const Driver& d : drivers) {
            if (!d) break;
            splicep->addDriver(d.m_flp, d.m_lo, d.m_vtxp);
        }

        // Done
        return !multiDriven;
    }

    bool normalizeSplice(DfgVertexVar& var, const std::string& sub, DfgVertexSplice* splicep) {
        // If the driver is a splice, normalize it
        if (DfgSpliceArray* const sap = splicep->cast<DfgSpliceArray>()) {
            return normalizeArray(var, sub, sap);
        } else if (DfgSplicePacked* const spp = splicep->cast<DfgSplicePacked>()) {
            return normalizePacked(var, sub, spp);
        } else {
            var.v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
        }
    }

    bool normalizeDrivers(DfgVertexVar& var) {
        return normalizeSplice(var, "", var.srcp()->as<DfgVertexSplice>());
    }

    void coalesce(std::vector<Driver>& drivers) {
        UASSERT(!drivers.empty(), "Can't coalesce 0 drivers");
        size_t i = 0;
        for (size_t j = 1; j < drivers.size();) {
            UASSERT(i < j, "Invalid iteration");
            Driver& iD = drivers[i];
            Driver& jD = drivers[j];

            // If 'j' was moved, step forward
            if (!jD) {
                ++j;
                continue;
            }
            // If 'i' was moved, move 'j' in it's place
            if (!iD) {
                iD = jD;
                jD = Driver{};
                ++j;
                continue;
            }
            // We have 2 valid drivers now
            UASSERT(iD.m_lo <= jD.m_lo, "Should always be sorted");

            // If not adjacent, move on
            if (iD.m_hi + 1 != jD.m_lo) {
                ++i;
                if (i == j) ++j;
                continue;
            }

            // Coalesce Adjacent ranges,
            const auto dtypep = DfgGraph::dtypePacked(iD.size() + jD.size());
            DfgConcat* const concatp = make<DfgConcat>(m_dfg, iD.m_flp, dtypep);
            concatp->rhsp(iD.m_vtxp);
            concatp->lhsp(jD.m_vtxp);
            iD.m_vtxp = concatp;
            iD.m_hi = jD.m_hi;
            jD = Driver{};

            // Consider next driver
            ++j;
        }
        // Rightsize vector
        drivers.resize(i + 1);
    }

    ////////////////////////////////
    ////////////////////////////////
    ////////////////////////////////

    // If any written variables are forced or otherwise udpated from outside,
    // we generally cannot synthesie the construct, as we will likely need to
    // introduce intermediate values that would not be updated.
    static bool hasExternallyWrittenVariable(DfgLogic& vtx) {
        return vtx.findSink<DfgVertex>([](const DfgVertex& sink) -> bool {
            // 'sink' is a splice (for which 'vtxp' is an unresolved driver),
            // which drives the target variable.
            DfgVertexVar* varp = sink.singleSink()->as<DfgVertexVar>();
            if (varp->hasXRefs()) return true;  // Target of a hierarchical reference
            AstVar* const astVarp = varp->varp();
            if (astVarp->isForced()) return true;  // Forced
            if (astVarp->isSigPublic()) return true;  // Public
            return false;
        });
    }

    void initializeEntrySymbolTable(SymTab& iSymTab) {
        // Initialzie input symbol table of entry block
        m_logicp->forEachSource([&](DfgVertex& src) {
            DfgVertexVar* const vvp = src.as<DfgVertexVar>();
            Variable* const varp = reinterpret_cast<Variable*>(vvp->nodep());
            iSymTab[varp] = vvp;
        });
    }

    static std::pair<std::vector<Driver>, DfgVertex*> gatherDrivers(Variable* varp,
                                                                    DfgVertexVar* vtxp) {
        std::vector<Driver> drivers;
        DfgVertex* defaultp = nullptr;

        UASSERT_OBJ(vtxp->nodep() != varp, varp, "Can't handle input variable");
        UASSERT_OBJ(vtxp->srcp(), vtxp, "Should have a driver");

        if (DfgSplicePacked* const spp = vtxp->srcp()->cast<DfgSplicePacked>()) {
            defaultp = spp->defaultp();
            spp->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
                DfgVertex* const driverp = edge.sourcep();
                UASSERT_OBJ(driverp, vtxp, "Should not have created undriven sources");
                // Ignore default driver
                if (driverp == defaultp) return;
                // Should not have an unresolved driver
                UASSERT_OBJ(!spp->driverIsUnresolved(i), vtxp, "Should not be unresolved");
                // Resolved driver
                const uint32_t lo = spp->driverLo(i);
                UASSERT_OBJ(drivers.empty() || lo > drivers.back().m_hi, spp, "Unordered drivers");
                drivers.emplace_back(spp->driverFileLine(i), lo, driverp);
            });
        } else if (vtxp->is<DfgVertexSplice>()) {
            vtxp->v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
        } else {
            // Variable driven whole, just add the single driver
            drivers.emplace_back(vtxp->fileline(), 0, vtxp);
        }

        return {std::move(drivers), defaultp};
    }

    DfgVertexVar* joinDrivers(Variable* varp, DfgVertex* predicatep,  //
                              DfgVertexVar* thenp, DfgVertexVar* elsep) {
        UASSERT_OBJ(!predicatep->is<DfgConst>(), predicatep, "joinDrivers with cons predicate");

        AstNode* const thenVarp = thenp->tmpForp() ? thenp->tmpForp() : thenp->nodep();
        AstNode* const elseVarp = elsep->tmpForp() ? elsep->tmpForp() : elsep->nodep();
        UASSERT_OBJ(thenVarp == elseVarp, varp, "Attempting to join unrelated variables");

        // If both bindings are the the same (variable not updated through either path),
        // then there is nothing to do, canuse the same binding
        if (thenp == elsep) return thenp;

        // We can't join the input variable just yet, so bail
        if (thenp->nodep() == varp) {
            ++m_ctx.m_synt.nonSynJoinInput;
            return nullptr;
        }
        if (elsep->nodep() == varp) {
            ++m_ctx.m_synt.nonSynJoinInput;
            return nullptr;
        }

        // Can't do arrays yet
        if (VN_IS(thenp->dtypep(), UnpackArrayDType)) {
            ++m_ctx.m_synt.nonSynArray;
            return nullptr;
        }

        // Gather drivers of 'thenp' - only if 'thenp' is not an input to the synthesized block
        std::vector<Driver> tDrivers;
        DfgVertex* tDefaultp = nullptr;
        std::tie(tDrivers, tDefaultp) = gatherDrivers(varp, thenp);

        // Gather drivers of 'elsep' - only if 'thenp' is not an input to the synthesized block
        std::vector<Driver> eDrivers;
        DfgVertex* eDefaultp = nullptr;
        std::tie(eDrivers, eDefaultp) = gatherDrivers(varp, elsep);

        // Default drivers should be the same or not present on either
        UASSERT_OBJ(tDefaultp == eDefaultp, varp, "Different default drivers");

        // Location to use for the join vertices
        FileLine* const flp = predicatep->fileline();

        // Create a fresh temporary for the joined value
        DfgVertexVar* const joinp = m_converter.createTmp(m_dfg, *m_logicp, varp, "SynthJoin");
        AstNodeDType* const dtypep = joinp->dtypep();
        DfgVertexSplice* const joinSplicep = make<DfgSplicePacked>(m_dfg, flp, dtypep);
        joinp->srcp(joinSplicep);

        // If both paths are fully driven, just create a simple conditional
        if (tDrivers.size() == 1  //
            && tDrivers[0].m_lo == 0  //
            && tDrivers[0].m_hi == thenp->width() - 1  //
            && eDrivers.size() == 1  //
            && eDrivers[0].m_lo == 0  //
            && eDrivers[0].m_hi == elsep->width() - 1) {
            UASSERT_OBJ(!tDefaultp, varp, "Fully driven variable have default driver");

            AstNodeDType* const dtypep = DfgGraph::toDfgDType(getAstVar(varp)->dtypep());
            DfgCond* const condp = make<DfgCond>(m_dfg, flp, dtypep);
            condp->condp(predicatep);
            condp->thenp(thenp);
            condp->elsep(elsep);
            joinSplicep->addDriver(tDrivers[0].m_flp, 0, condp);

            // Done
            return joinp;
        }

        // Otherwise we need to merge them part by part

        // If different bits are driven, then some might not have been assigned.. Latch?
        if (tDrivers.size() != eDrivers.size()) {
            ++m_ctx.m_synt.nonSynLatch;
            return nullptr;
        }

        for (size_t i = 0; i < tDrivers.size(); ++i) {
            const Driver& tDriver = tDrivers[i];
            const Driver& eDriver = eDrivers[i];
            // If different bits are driven, then some might not have been assigned.. Latch?
            if (tDriver.m_lo != eDriver.m_lo || tDriver.m_hi != eDriver.m_hi) {
                ++m_ctx.m_synt.nonSynLatch;
                return nullptr;
            }

            AstNodeDType* const dtypep = DfgGraph::dtypePacked(tDriver.m_hi - tDriver.m_lo + 1);
            DfgCond* const condp = make<DfgCond>(m_dfg, flp, dtypep);
            condp->condp(predicatep);

            // We actally need to select the bits from the joined variables, not use the drivers
            DfgSel* const thenSelp = make<DfgSel>(m_dfg, flp, tDriver.m_vtxp->dtypep());
            thenSelp->lsb(tDriver.m_lo);
            thenSelp->fromp(thenp);
            condp->thenp(thenSelp);

            // Same for the 'else' part
            DfgSel* const elseSelp = make<DfgSel>(m_dfg, flp, eDriver.m_vtxp->dtypep());
            elseSelp->lsb(eDriver.m_lo);
            elseSelp->fromp(elsep);
            condp->elsep(elseSelp);

            // Add it as a driver to the join
            joinSplicep->addDriver(tDriver.m_flp, tDriver.m_lo, condp);
        }

        // If there was a default driver, add it to te join
        if (tDefaultp) joinSplicep->defaultp(tDefaultp);

        // Done
        return joinp;
    }

    bool createInputSymbolTable(SymTab& joined, const BasicBlock& bb,
                                const BasicBlockMap<SymTab>& bbToOSymTab,
                                const ControlFlowEdgeMap<DfgVertex*>& edgeToPredicatep) {
        // Input symbol table of entry block was previously initialzied
        if (bb.inEmpty()) return true;

        // We will fill it in here
        UASSERT(joined.empty(), "Unresolved input symbol table should be empty");

        // Fast path if there is only one predecessor
        if (bb.inSize1()) {
            joined = bbToOSymTab[*(bb.inEdges().frontp()->fromp()->as<BasicBlock>())];
            return true;
        }

        // Gather predecessors and the path predicates
        struct Predecessor final {
            const BasicBlock* m_bbp;
            DfgVertex* m_predicatep;
            Predecessor() = delete;
            Predecessor(const BasicBlock* bbp, DfgVertex* predicatep)
                : m_bbp{bbp}
                , m_predicatep{predicatep} {}
        };

        const std::vector<Predecessor> predecessors = [&]() {
            std::vector<Predecessor> res;
            for (const V3GraphEdge& edge : bb.inEdges()) {
                const ControlFlowEdge& cfgEdge = static_cast<const ControlFlowEdge&>(edge);
                res.emplace_back(&cfgEdge.src(), edgeToPredicatep[cfgEdge]);
            }
            // Sort predecessors topologically. This way later blocks will come
            // after earlier blocks, and the entry block will be first if present.
            std::sort(res.begin(), res.end(), [](const Predecessor& a, const Predecessor& b) {  //
                return a.m_bbp->id() < b.m_bbp->id();
            });
            return res;
        }();

        // Start by copying the bindings from the oldest predecessor
        joined = bbToOSymTab[*predecessors[0].m_bbp];
        // Join over all other predecessors
        for (size_t i = 1; i < predecessors.size(); ++i) {
            DfgVertex* const predicatep = predecessors[i].m_predicatep;
            const SymTab& oSymTab = bbToOSymTab[*predecessors[i].m_bbp];
            // Give up if something is not assigned on all paths ... Latch?
            if (joined.size() != oSymTab.size()) {
                ++m_ctx.m_synt.nonSynLatch;
                return false;
            }
            // Join each symbol
            for (auto& pair : joined) {
                Variable* const varp = pair.first;
                // Find same variable on other path
                auto it = oSymTab.find(varp);
                // Give up if something is not assigned on all paths ... Latch?
                if (it == oSymTab.end()) {
                    ++m_ctx.m_synt.nonSynLatch;
                    return false;
                }
                // Join paths with the block predicate
                DfgVertexVar* const thenp = it->second;
                DfgVertexVar* const elsep = pair.second;
                DfgVertexVar* const newp = joinDrivers(varp, predicatep, thenp, elsep);
                if (!newp) return false;
                pair.second = newp;
            }
        }

        return true;
    }

    bool incorporatePreviousValue(Variable* varp, DfgVertexVar* newp, DfgVertexVar* oldp) {
        UASSERT_OBJ(newp->srcp(), varp, "Assigned variable has no driver");

        // Easy if there is no old value...
        if (!oldp) return true;

        // New driver was not yet coalesced, so should always be a splice
        DfgVertexSplice* const nSplicep = newp->srcp()->as<DfgVertexSplice>();

        // If the old value is the real variable we just computed the new value for,
        // then it is the circular feedback into the synthesized block, add it as default driver.
        if (oldp->nodep() == varp) {
            if (!nSplicep->wholep()) nSplicep->defaultp(oldp);
            return true;
        }

        UASSERT_OBJ(oldp->srcp(), varp, "Previously assigned variable has no driver");

        // Can't do arrays yet
        if (VN_IS(newp->dtypep(), UnpackArrayDType)) {
            ++m_ctx.m_synt.nonSynArray;
            return false;
        }

        // Gather drivers of 'newp' - they are in incresing range order with no overlaps
        std::vector<Driver> nDrivers;
        DfgVertex* nDefaultp;
        std::tie(nDrivers, nDefaultp) = gatherDrivers(varp, newp);
        UASSERT_OBJ(!nDrivers.empty(), varp, "Should have a proper driver");
        UASSERT_OBJ(!nDefaultp, varp, "Should not have a default after conversion");

        // Gather drivers of 'oldp' - they are in incresing range order with no overlaps
        std::vector<Driver> oDrivers;
        DfgVertex* oDefaultp;
        std::tie(oDrivers, oDefaultp) = gatherDrivers(varp, oldp);
        UASSERT_OBJ(!oDrivers.empty(), varp, "Should have a proper driver");

        // Additional drivers of 'newp' propagated from 'oldp'
        std::vector<Driver> pDrivers;

        // Add bits between 'msb' and 'lsb' from 'oldp' to 'pDrivers'
        const auto addToPDriver = [&](FileLine* const flp, uint32_t msb, uint32_t lsb) {
            UASSERT_OBJ(pDrivers.empty() || lsb > pDrivers.back().m_hi, flp, "Non ascending");
            DfgSel* const selp = make<DfgSel>(m_dfg, flp, DfgGraph::dtypePacked(msb - lsb + 1));
            selp->lsb(lsb);
            selp->fromp(oldp);
            pDrivers.emplace_back(flp, lsb, selp);
        };

        // Incorporate old drivers
        for (const Driver& oDriver : oDrivers) {
            FileLine* const flp = oDriver.m_flp;
            // Range to consider inserting, we will adjust oldLo as we process drivers
            uint32_t oldLo = oDriver.m_lo;
            const uint32_t oldHi = oDriver.m_hi;

            // Loop for now, can move to bisection search if this is a problem, shouldn't be ...
            for (const Driver& nDriver : nDrivers) {
                UASSERT_OBJ(oldHi >= oldLo, flp, "Should have stopped iteration");
                // If new driver is entirely below old driver, move on to
                if (nDriver.m_hi < oldLo) continue;
                // If new driver is entirely above old driver, we can stop
                if (oldHi < nDriver.m_lo) break;

                // There is an overlap between 'oDriver' and 'nDriver'.
                // Insert the low bits and adjust the insertion range.
                // The rest will take care of itself on subsequent iterations.
                if (oldLo < nDriver.m_lo) addToPDriver(flp, nDriver.m_lo - 1, oldLo);
                oldLo = nDriver.m_hi + 1;

                // Stop if no more bits remaining in the old driver
                if (oldLo > oldHi) break;
            }

            // Insert remaining bits if any
            if (oldHi >= oldLo) addToPDriver(flp, oldHi, oldLo);
        }

        if (!pDrivers.empty()) {
            // Need to merge propatated sources, so unlink and reset the splice
            nSplicep->forEachSourceEdge([](DfgEdge& edge, size_t) { edge.unlinkSource(); });
            nSplicep->resetSources();
            // Merge drivers - they are both sorted and non-overlapping
            std::vector<Driver> drivers;
            drivers.reserve(nDrivers.size() + pDrivers.size());
            std::merge(nDrivers.begin(), nDrivers.end(), pDrivers.begin(), pDrivers.end(),
                       std::back_inserter(drivers));
            // Coalesce adjacent ranges
            coalesce(drivers);
            // Reinsert drivers in order
            for (const Driver& d : drivers) nSplicep->addDriver(d.m_flp, d.m_lo, d.m_vtxp);
        }

        // If the old had a default, add to the new one too, unless redundant
        if (oDefaultp && !nSplicep->wholep()) nSplicep->defaultp(oDefaultp);

        // Done
        return true;
    }

    // Synthesize the given statements with the given input symbol table.
    // Returnt true if successfolly synthesized.
    // Populates the given output symbol table.
    // Populates the given reference with the condition of the terminator branch, if any.
    bool synthesizeBasicBlock(SymTab& oSymTab, DfgVertex*& condpr,
                              const std::vector<AstNodeStmt*>& stmtps, const SymTab& iSymTab) {
        // Use fresh set of vertices in m_converter
        const VNUser2InUse user2InUse;

        // Initialize Variable -> Vertex bindings available in this block
        for (const auto& pair : iSymTab) {
            Variable* const varp = pair.first;
            DfgVertexVar* const vtxp = pair.second;
            varp->user2p(vtxp);
            oSymTab[varp] = vtxp;
        }

        // Synthesize each statement one after the other
        std::unordered_map<Variable*, DfgVertexVar*> updates;
        for (AstNodeStmt* const stmtp : stmtps) {
            // Regular statements
            if (AstAssign* const ap = VN_CAST(stmtp, Assign)) {
                // Convet this assignment
                if (!m_converter.convert(updates, *m_logicp, ap)) {
                    ++m_ctx.m_synt.nonSynConv;
                    return false;
                }
                // Apply variable updates from this statement
                for (const auto& pair : updates) {
                    // The target variable that was assigned to
                    Variable* const varp = pair.first;
                    // The new, potentially partially assigned value
                    DfgVertexVar* const newp = pair.second;
                    // Normalize drivers within this statement, bail if multidriven
                    if (!normalizeDrivers(*newp)) {
                        getAstVar(varp)->setDfgMultidriven();
                        ++m_ctx.m_synt.nonSynMultidrive;
                        return false;
                    }
                    // The old value, if any
                    DfgVertexVar* const oldp = varp->user2u().template to<DfgVertexVar*>();
                    // Inncorporate old value into the new value
                    if (!incorporatePreviousValue(varp, newp, oldp)) return false;
                    // Update binding of target variable
                    varp->user2p(newp);
                    // Update output symbol table of this block
                    oSymTab[varp] = newp;
                }
                updates.clear();
                continue;
            }

            // Terminator branches
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                UASSERT_OBJ(ifp == stmtps.back(), ifp, "Branch should be last statement");
                // Convet condition, give up if failed
                DfgVertex* const condp = m_converter.convert(*m_logicp, ifp->condp());
                if (!condp) {
                    ++m_ctx.m_synt.nonSynConv;
                    return false;
                }
                //
                if (condp->width() == 1) {
                    // Single bit condition can be use directly
                    condpr = condp;
                } else {
                    // Multi bit condition: use 'condp != 0'
                    FileLine* const flp = condp->fileline();
                    DfgNeq* const neqp = make<DfgNeq>(m_dfg, flp, DfgGraph::dtypePacked(1));
                    neqp->lhsp(make<DfgConst>(m_dfg, flp, condp->width(), 0U));
                    neqp->rhsp(condp);
                    condpr = neqp;
                }
                continue;
            }

            // Unhandled
            ++m_ctx.m_synt.nonSynStmt;
            return false;
        }

        return true;
    }

    // Given a basic block, and the condition of the terminating branch (if any),
    // assign perdicates to the block's outgoing control flow edges.
    void assignSuccessorPredicates(ControlFlowEdgeMap<DfgVertex*>& edgeToPredicatep,
                                   const BasicBlock& bb, DfgVertex* condp) {
        // Nothing to do for the exit block
        if (bb.outEmpty()) return;

        // Get the predicate of this block
        DfgVertex* const predp = [&]() -> DfgVertex* {
            // Entry block has no predecessors, use constant true
            if (bb.inEmpty()) return make<DfgConst>(m_dfg, m_logicp->fileline(), 1U, 1U);

            // For any other block, 'or' together all the incoming predicates
            const auto& inEdges = bb.inEdges();
            auto it = inEdges.begin();
            DfgVertex* resp = edgeToPredicatep[static_cast<const ControlFlowEdge&>(*it)];
            while (++it != inEdges.end()) {
                DfgOr* const orp = make<DfgOr>(m_dfg, resp->fileline(), resp->dtypep());
                orp->rhsp(resp);
                orp->lhsp(edgeToPredicatep[static_cast<const ControlFlowEdge&>(*it)]);
                resp = orp;
            }
            return resp;
        }();

        if (!condp) {
            // There should be 1 successors for a block with an unconditional terminator
            UASSERT_OBJ(!bb.untknEdgep(), predp, "Expecting 1 successor for BasicBlock");
            // Successor predicate edge is the same
            edgeToPredicatep[*bb.takenEdgep()] = predp;
        } else {
            // There should be 2 successors for a block with an conditional terminator
            UASSERT_OBJ(bb.untknEdgep(), predp, "Expecting 2 successors for BasicBlock");
            FileLine* const flp = condp->fileline();
            AstNodeDType* const dtypep = condp->dtypep();  // Single bit

            // Predicate for taken branch: 'predp & condp'
            DfgAnd* const takenPredp = make<DfgAnd>(m_dfg, flp, dtypep);
            takenPredp->lhsp(predp);
            takenPredp->rhsp(condp);
            edgeToPredicatep[*bb.takenEdgep()] = takenPredp;

            // Predicate for untaken branch: 'predp & ~condp'
            DfgAnd* const untknPredp = make<DfgAnd>(m_dfg, flp, dtypep);
            untknPredp->lhsp(predp);
            DfgNot* const notp = make<DfgNot>(m_dfg, flp, dtypep);
            notp->srcp(condp);
            untknPredp->rhsp(notp);
            edgeToPredicatep[*bb.untknEdgep()] = untknPredp;
        }
    }

    bool relinkOutputs(SymTab& oSymTab) {
        // It's possible we think a variable is written by the DfgLogic when
        // it actauly isn't, e.g.: '{a[0], b[0]}[1] = ...' does not write 'b'.
        // These LHS forms can happen after some earlier tranforms. We
        // should just run V3Const on them earleir, but we will do belt and
        // braces and check here too. We can't touch any output variabels if so.
        const bool missing = m_logicp->findSink<DfgVertex>([&](const DfgVertex& sink) -> bool {
            const DfgVertexSplice* const splicep = sink.as<DfgVertexSplice>();
            AstNode* const tgtp = splicep->singleSink()->as<DfgVertexVar>()->nodep();
            Variable* const varp = reinterpret_cast<Variable*>(tgtp);
            return !oSymTab.count(varp);
        });
        if (missing) {
            ++m_ctx.m_synt.nonSynFalseWrite;
            return false;
        }

        // Add sinks to read the computed values for the target variables
        m_logicp->forEachSink([&](DfgVertex& sink) {
            DfgVertexSplice* const splicep = sink.as<DfgVertexSplice>();
            AstNode* const tgtp = splicep->singleSink()->as<DfgVertexVar>()->nodep();
            Variable* const varp = reinterpret_cast<Variable*>(tgtp);
            DfgVertexVar* const resp = oSymTab.at(varp);
            UASSERT_OBJ(resp->srcp(), resp, "Undriven result");
            splicep->addUnresolvedDriver(resp->srcp());
        });
        return true;
    }

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

        // Synthesize as if it was in a single BasicBlock CFG
        DfgVertex* condp = nullptr;
        const bool success = synthesizeBasicBlock(oSymTab, condp, {assignp}, iSymTab);
        UASSERT_OBJ(!condp, nodep, "Conditional AstAssignW ???");
        // Delete auxiliary AstAssign
        VL_DO_DANGLING(assignp->deleteTree(), assignp);
        if (!success) return false;

        // Add resovled output variable drivers
        return relinkOutputs(oSymTab);
    }

    bool synthesizeCfg(const ControlFlowGraph& cfg) {
        ++m_ctx.m_synt.inputAlways;

        if (hasExternallyWrittenVariable(*m_logicp)) {
            ++m_ctx.m_synt.nonSynExtWrite;
            return false;
        }

        // If there is a backward edge (loop), we can't synthesize it
        if (cfg.containsLoop()) {
            ++m_ctx.m_synt.nonSynLoop;
            return false;
        }

        // Maps from BasicBlock to its input and output symbol tables
        BasicBlockMap<SymTab> bbToISymTab = cfg.makeBasicBlockMap<SymTab>();
        BasicBlockMap<SymTab> bbToOSymTab = cfg.makeBasicBlockMap<SymTab>();

        // Map from ControlFlowGraphEdge to its predicate
        ControlFlowEdgeMap<DfgVertex*> edgeToPredicatep = cfg.makeEdgeMap<DfgVertex*>();

        // Initialzie input symbol table of entry block
        initializeEntrySymbolTable(bbToISymTab[cfg.enter()]);

        // Synthesize all blocks
        for (const V3GraphVertex& cfgVtx : cfg.vertices()) {
            const BasicBlock& bb = *cfgVtx.as<BasicBlock>();
            // Symbol tables of the block
            SymTab& iSymTab = bbToISymTab[bb];
            SymTab& oSymTab = bbToOSymTab[bb];
            // Join symbol tables from predecessor blocks
            if (!createInputSymbolTable(iSymTab, bb, bbToOSymTab, edgeToPredicatep)) return false;
            // Condition of the terminating branch, if any
            DfgVertex* condp = nullptr;
            // Synthesize the block
            if (!synthesizeBasicBlock(oSymTab, condp, bb.stmtps(), iSymTab)) return false;
            // Set the predicates on the successor edges
            assignSuccessorPredicates(edgeToPredicatep, bb, condp);
        }

        // Add resovled output variable drivers
        return relinkOutputs(bbToOSymTab[cfg.exit()]);
    }

    // Synthesize a DfgLogic into regular vertices. Return ture on success.
    bool synthesize(DfgLogic& vtx) {
        VL_RESTORER(m_logicp);
        m_logicp = &vtx;

        if (AstAssignW* const nodep = VN_CAST(vtx.nodep(), AssignW)) {
            if (!synthesizeAssignW(nodep)) return false;
            ++m_ctx.m_synt.synthAssign;
            return true;
        }

        if (!synthesizeCfg(vtx.cfg())) return false;
        ++m_ctx.m_synt.synthAlways;
        return true;
    }

    // Revert synthesis of a DfgLogic
    void revert(DfgLogic& vtx) {
        for (DfgVertex* const p : vtx.synth()) VL_DO_DANGLING(p->unlinkDelete(m_dfg), p);
        vtx.synth().clear();
    }

    // Revert all logic driving the given splice, delete the splice,
    // and transitively the same for splices driven by the reverted logic.
    void revertTransivelyAndRemove(DfgVertexSplice* splicep, VDouble0& statCountr) {
        // The result variable will be driven from Ast code, mark as such
        splicep->singleSink()->as<DfgVertexVar>()->setHasModWrRefs();

        // Gather all logic driving this splice
        std::vector<DfgLogic*> logicps;
        logicps.reserve(splicep->arity());
        splicep->forEachSource([&](DfgVertex& src) {
            if (DfgLogic* const p = src.cast<DfgLogic>()) logicps.emplace_back(p);
        });

        // Delete the splice
        VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);

        // Transitively for the rest
        for (DfgLogic* const logicp : logicps) {
            if (!logicp->synth().empty()) {
                ++statCountr;
                revert(*logicp);
            }
            while (DfgVertex* const sinkp = logicp->firtsSinkp()) {
                revertTransivelyAndRemove(sinkp->as<DfgVertexSplice>(), statCountr);
            }
        }
    }

    // Synthesize all of the given vertices
    void main(const std::vector<DfgLogic*>& logicps) {
        // Attempt to synthesize each of the given DfgLogic
        {
            for (DfgLogic* const logicp : logicps) {
                // Debug aid
                if (VL_UNLIKELY(s_dfgSynthDebugLimit)) {
                    if (s_dfgSynthDebugCount == s_dfgSynthDebugLimit) break;
                    ++s_dfgSynthDebugCount;
                    if (s_dfgSynthDebugCount == s_dfgSynthDebugLimit) {
                        // This is the breaking logic
                        m_debugLogicp = logicp;
                        // Dump it
                        UINFOTREE(0, logicp->nodep(), "Problematic DfgLogic: " << logicp, "  ");
                        V3EmitV::debugVerilogForTree(logicp->nodep(), std::cout);
                        debugDump("synth-lastok");
                    }
                }

                // Synthesize it, if failed revert partial construction if failed
                if (!synthesize(*logicp)) revert(*logicp);
            }
            debugDump("synth-conv");
        }

        // Any variable that is driven from a non synthesized block might be multi-driven, remove
        {
            for (DfgVertexVar& var : m_dfg.varVertices()) {
                if (var.srcp()) {
                    DfgVertexSplice* const sp = var.srcp()->as<DfgVertexSplice>();
                    const bool revert = sp->findSourceEdge([&](const DfgEdge& e, size_t) -> bool {
                        DfgLogic* const driverp = e.sourcep()->cast<DfgLogic>();
                        // Driver was not synthesized
                        return driverp && driverp->synth().empty();
                    });
                    if (revert) revertTransivelyAndRemove(sp, m_ctx.m_synt.revertNonSyn);
                }
                // No need to do the temporaries again
                if (&var == m_lastNonTmpVarp) break;
            }
            debugDump("synth-rvrt");
        }

        // Normalize drivers of the original variables
        {
            std::vector<DfgVertexVar*> multidrivenps;
            for (DfgVertexVar& var : m_dfg.varVertices()) {
                if (var.srcp() && !normalizeDrivers(var)) multidrivenps.emplace_back(&var);
                // No need to do the temporaries again
                if (&var == m_lastNonTmpVarp) break;
            }
            // Revert and remove drivers of multi-driven variables, flag them for future invocation
            for (DfgVertexVar* const vtxp : multidrivenps) {
                // Might not have a driver if revertTransivelyAndRemove removed
                // it on an earleir iteration
                if (vtxp->srcp()) {
                    DfgVertexSplice* const splicep = vtxp->srcp()->as<DfgVertexSplice>();
                    revertTransivelyAndRemove(splicep, m_ctx.m_synt.revertMultidrive);
                }
                vtxp->varp()->setDfgMultidriven();
            }
            debugDump("synth-norm");
        }

        // Now that we synthesized everyting possible, remove every DfgLogic
        {
            for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
                DfgLogic* const logicp = vtxp->cast<DfgLogic>();
                if (!logicp) continue;

                if (!logicp->synth().empty()) {
                    // If synthesized, delete the corresponding AstNode. It is now in Dfg.
                    logicp->nodep()->unlinkFrBack()->deleteTree();
                } else {
                    // Not synthesized. Logic stays in Ast.
                    // Mark source variabels as read in module
                    logicp->forEachSource([](DfgVertex& source) {  //
                        source.as<DfgVertexVar>()->setHasModRdRefs();
                    });
                    // Mark sink variables as written in module, gather splice vertices
                    logicp->forEachSink([&](DfgVertex& sink) {  //
                        sink.singleSink()->as<DfgVertexVar>()->setHasModWrRefs();
                    });
                }

                // Delete this DfgLogic
                VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
            }
            // We have deleted it ..
            m_debugLogicp = nullptr;
            // Re-pack splices and remove unnecessary ones
            for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
                DfgVertexSplice* const splicep = vtxp->cast<DfgVertexSplice>();
                if (!splicep) continue;
                // Remove sources deleted when removing DfgLogic above
                splicep->removeUndrivenSources();
                // If does nothing, remove it
                if (!splicep->arity()) {
                    VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
                    continue;
                }
                // If redundant, remove it
                if (DfgVertex* const wholep = splicep->wholep()) {
                    if (DfgVertexVar* const varp = splicep->singleSink()->cast<DfgVertexVar>()) {
                        varp->driverFileLine(splicep->driverFileLine(0));
                    }
                    splicep->replaceWith(wholep);
                    VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
                }
            }
            // Remove all unused vertices
            V3DfgPasses::removeUnused(m_dfg);
            debugDump("synth-prun");
        }
    }

    // CONSTRUCTOR
    AstToDfgSynthesize(DfgGraph& dfg, const std::vector<DfgLogic*>& logicps,
                       V3DfgSynthesisContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx}
        , m_converter{dfg, ctx} {}

public:
    static void apply(DfgGraph& dfg, const std::vector<DfgLogic*>& logicps,
                      V3DfgSynthesisContext& ctx) {
        AstToDfgSynthesize{dfg, logicps, ctx}.main(logicps);
    }
};

void V3DfgPasses::synthesize(DfgGraph& dfg, V3DfgContext& ctx) {
    // The vertices to synthesize
    std::vector<DfgLogic*> logicps;

    if (v3Global.opt.fDfgSynthesizeAll()) {
        // If we are told to synthesize everything, we will do so ...
        for (DfgVertex& vtx : dfg.opVertices()) {
            if (DfgLogic* const logicp = vtx.cast<DfgLogic>()) logicps.emplace_back(logicp);
        }
    } else {
        // Otherwise figure out which vertices are worth synthesizing.

        // Find cycles
        const auto userDataInUse = dfg.userDataInUse();
        V3DfgPasses::colorStronglyConnectedComponents(dfg);

        // First, gather variables, we will then attempt to synthesize all their drivers
        std::vector<DfgVertexVar*> varps;
        for (DfgVertexVar& var : dfg.varVertices()) {
            // Can ignore variables with no drivers
            if (!var.srcp()) continue;

            // Circular variable - synthesize
            if (var.getUser<uint64_t>()) {
                varps.emplace_back(&var);
                continue;
            }

            // Must be driven from a splice at this point, pick it up
            DfgVertexSplice* const splicep = var.srcp()->as<DfgVertexSplice>();

            // Inspect drivers to figure out if we should synthesize them
            const bool doIt = splicep->findSourceEdge([](const DfgEdge& edge, size_t) -> bool {
                DfgLogic* const logicp = edge.sourcep()->as<DfgLogic>();
                // Synthesize continuous assignments (this is the earlier behaviour)
                if (VN_IS(logicp->nodep(), AssignW)) return true;
                // Synthesize always blocks with no more than 4 basic blocks and 4 edges
                // These are usually simple branches (if (rst) ... else ...), or close to it
                return logicp->cfg().nBasicBlocks() <= 4 && logicp->cfg().nEdges() <= 4;
            });
            if (doIt) varps.emplace_back(&var);
        }

        // Gather all drivers of the selected variabels
        const VNUser2InUse user2InUse;  // AstNode (logic) -> bool: already collected
        for (const DfgVertexVar* const varp : varps) {
            varp->srcp()->as<DfgVertexSplice>()->forEachSource([&](DfgVertex& source) {
                DfgLogic* const logicp = source.as<DfgLogic>();
                if (!logicp->nodep()->user2Inc()) logicps.emplace_back(logicp);
            });
        }
    }

    // Synthesize them - also removes un-synthesized DfgLogic, so must run even if logicps.empty()
    if (dfg.modulep()) {
        AstToDfgSynthesize</* T_Scoped: */ false>::apply(dfg, logicps, ctx.m_synthContext);
    } else {
        AstToDfgSynthesize</* T_Scoped: */ true>::apply(dfg, logicps, ctx.m_synthContext);
    }
}
