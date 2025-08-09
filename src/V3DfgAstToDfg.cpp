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

#include <iterator>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Create a DfgVertex out of a AstNodeExpr. For most AstNodeExpr subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename T_Vertex, typename T_Node>
T_Vertex* makeVertex(const T_Node* nodep, DfgGraph& dfg) {
    return new T_Vertex{dfg, nodep->fileline(), DfgVertex::dtypeFor(nodep)};
}

template <>
DfgArraySel* makeVertex<DfgArraySel, AstArraySel>(const AstArraySel* nodep, DfgGraph& dfg) {
    // Some earlier passes create malformed ArraySels, just bail on those...
    // See t_bitsel_wire_array_bad
    if (VN_IS(nodep->fromp(), Const)) return nullptr;
    AstUnpackArrayDType* const fromDtypep
        = VN_CAST(nodep->fromp()->dtypep()->skipRefp(), UnpackArrayDType);
    if (!fromDtypep) return nullptr;
    return new DfgArraySel{dfg, nodep->fileline(), DfgVertex::dtypeFor(nodep)};
}

//======================================================================
// Currently unhandled nodes
// LCOV_EXCL_START
// AstCCast changes width, but should not exists where DFG optimization is currently invoked
template <>
DfgCCast* makeVertex<DfgCCast, AstCCast>(const AstCCast*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on strings which we don't optimize anyway
template <>
DfgAtoN* makeVertex<DfgAtoN, AstAtoN>(const AstAtoN*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on strings which we don't optimize anyway
template <>
DfgCompareNN* makeVertex<DfgCompareNN, AstCompareNN>(const AstCompareNN*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on unpacked arrays which we don't optimize anyway
template <>
DfgSliceSel* makeVertex<DfgSliceSel, AstSliceSel>(const AstSliceSel*, DfgGraph&) {
    return nullptr;
}
// LCOV_EXCL_STOP

}  // namespace

static DfgVertexVar* createTmpImpl(DfgGraph& dfg, AstVar* varp, const char* prefixp, size_t n,
                                   AstScope* scopep) {
    std::string prefix{prefixp};
    prefix += "_";
    prefix += varp->name();
    const std::string name = dfg.makeUniqueName(prefix, n);
    AstNodeDType* const dtypep = DfgVertex::dtypeFor(varp);
    DfgVertexVar* const vtxp = dfg.makeNewVar(varp->fileline(), name, dtypep, scopep);
    vtxp->varp()->isInternal(true);
    return vtxp;
}

// Create a new temporary variable capable of holding 'varp'
static DfgVertexVar* createTmp(DfgGraph& dfg, AstVar* varp, const char* prefixp, size_t n) {
    DfgVertexVar* const vtxp = createTmpImpl(dfg, varp, prefixp, n, nullptr);
    vtxp->tmpForp(varp);
    return vtxp;
}

// Create a new temporary variable capable of holding 'vscp'
static DfgVertexVar* createTmp(DfgGraph& dfg, AstVarScope* vscp, const char* prefixp, size_t n) {
    DfgVertexVar* const vtxp = createTmpImpl(dfg, vscp->varp(), prefixp, n, vscp->scopep());
    vtxp->tmpForp(vscp);
    return vtxp;
}

// Visitor that can convert combinational Ast logic constructs/assignments to Dfg
template <bool T_Scoped, bool T_Synthesis>
class AstToDfgConverter final : public VNVisitor {
    // NODE STATE
    // AstNodeExpr/AstVar/AstVarScope::user2p -> DfgVertex* for this Node

    // TYPES
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;

    // STATE
    DfgGraph& m_dfg;  // The graph being built
    V3DfgAstToDfgContext& m_ctx;  // The context for stats
    bool m_foundUnhandled = false;  // Found node not implemented as DFG or not implemented 'visit'
    bool m_converting = false;  // We are trying to convert some logic at the moment
    std::vector<DfgVertexSplice*> m_uncommittedSpliceps;  // New splices made during convertLValue

    // STATE - only used when T_Synthesis
    // Variable updates produced by currently conveted statement
    std::unordered_map<Variable*, DfgVertexVar*>* m_updatesp;
    size_t* const m_tmpCntp;  // Temporary counter

    // METHODS
    static Variable* getTarget(const AstVarRef* refp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<Variable*>(refp->varScopep());
        } else {
            return reinterpret_cast<Variable*>(refp->varp());
        }
    }

    DfgVertexVar* getNet(Variable* varp) {
        if VL_CONSTEXPR_CXX17 (T_Synthesis) {
            UASSERT_OBJ(varp->user2p(), varp, "Missing DfgVertexVar during synthesis");
        } else {
            if (!varp->user2p()) {
                AstNodeDType* const dtypep = varp->dtypep()->skipRefp();
                DfgVertexVar* const vtxp
                    = VN_IS(dtypep, UnpackArrayDType)
                          ? static_cast<DfgVertexVar*>(new DfgVarArray{m_dfg, varp})
                          : static_cast<DfgVertexVar*>(new DfgVarPacked{m_dfg, varp});
                varp->user2p(vtxp);
            }
        }
        return varp->user2u().template to<DfgVertexVar*>();
    }

    // Returns true if the expression cannot (or should not) be represented by DFG
    bool unhandled(AstNodeExpr* nodep) {
        // Short-circuiting if something was already unhandled
        if (!m_foundUnhandled) {
            // Impure nodes cannot be represented
            if (!nodep->isPure()) {
                m_foundUnhandled = true;
                ++m_ctx.m_nonRepImpure;
            }
            // Check node has supported dtype
            if (!DfgVertex::isSupportedDType(nodep->dtypep())) {
                m_foundUnhandled = true;
                ++m_ctx.m_nonRepDType;
            }
        }
        return m_foundUnhandled;
    }

    bool isSupported(const AstVar* varp) {
        if (varp->isIfaceRef()) return false;  // Cannot handle interface references
        if (varp->delayp()) return false;  // Cannot handle delayed variables
        if (varp->isSc()) return false;  // SystemC variables are special and rare, we can ignore
        return DfgVertex::isSupportedDType(varp->dtypep());
    }

    bool isSupported(const AstVarScope* vscp) {
        // Check the Var fist
        if (!isSupported(vscp->varp())) return false;
        // If the variable is not in a regular module, then do not convert it.
        // This is especially needed for variabels in interfaces which might be
        // referenced via virtual intefaces, which cannot be resovled statically.
        if (!VN_IS(vscp->scopep()->modp(), Module)) return false;
        // Otherwise OK
        return true;
    }

    bool isSupported(const AstVarRef* nodep) {
        // Cannot represent cross module references
        if (nodep->classOrPackagep()) return false;
        // Check target
        return isSupported(getTarget(nodep));
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
                ++m_ctx.m_nonRepLhs;
                return {nullptr, 0};
            }
            Variable* const tgtp = getTarget(vrefp);
            DfgVertexVar* vtxp = nullptr;
            if VL_CONSTEXPR_CXX17 (!T_Synthesis) {
                // Get the variable vertex
                vtxp = getNet(tgtp);
            } else {
                // Get or create a new temporary
                DfgVertexVar*& r = (*m_updatesp)[tgtp];
                if (!r) r = createTmp(m_dfg, tgtp, "SynthAssign", (*m_tmpCntp)++);
                vtxp = r;
            }

            // Ensure the Splice driver exists for this variable
            if (!vtxp->srcp()) {
                FileLine* const flp = vtxp->fileline();
                AstNodeDType* const dtypep = vtxp->dtypep();
                if (vtxp->is<DfgVarPacked>()) {
                    DfgSplicePacked* const newp = new DfgSplicePacked{m_dfg, flp, dtypep};
                    m_uncommittedSpliceps.emplace_back(newp);
                    vtxp->srcp(newp);
                } else if (vtxp->is<DfgVarArray>()) {
                    DfgSpliceArray* const newp = new DfgSpliceArray{m_dfg, flp, dtypep};
                    m_uncommittedSpliceps.emplace_back(newp);
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
                ++m_ctx.m_nonRepLhs;
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
                ++m_ctx.m_nonRepLhs;
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
                AstNodeDType* const dtypep = DfgVertex::dtypeFor(nodep);
                if (VN_IS(dtypep, BasicDType)) {
                    DfgSplicePacked* const newp = new DfgSplicePacked{m_dfg, flp, dtypep};
                    m_uncommittedSpliceps.emplace_back(newp);
                    splicep->addDriver(flp, index, newp);
                } else if (VN_IS(dtypep, UnpackArrayDType)) {
                    DfgSpliceArray* const newp = new DfgSpliceArray{m_dfg, flp, dtypep};
                    m_uncommittedSpliceps.emplace_back(newp);
                    splicep->addDriver(flp, index, newp);
                } else {
                    nodep->v3fatalSrc("Unhandled AstNodeDType sub-type");  // LCOV_EXCL_LINE
                }
            }

            // Return the splice driver
            return {splicep->driverAt(index)->as<DfgVertexSplice>(), 0};
        }

        ++m_ctx.m_nonRepLhs;
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
                DfgSel* const lVtxp = new DfgSel{m_dfg, lFlp, DfgVertex::dtypeFor(cLhsp)};
                lVtxp->fromp(vtxp);
                lVtxp->lsb(cRhsp->width());
                if (!convertAllLValues(cLhsp, lVtxp)) return false;
                // Convert Rigth of concat
                FileLine* const rFlp = cRhsp->fileline();
                DfgSel* const rVtxp = new DfgSel{m_dfg, rFlp, DfgVertex::dtypeFor(cRhsp)};
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
        if (!convertAllLValues(lhsp, vtxp)) {
            for (DfgVertexSplice* const splicep : m_uncommittedSpliceps) {
                VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
            }
            m_uncommittedSpliceps.clear();
            return false;
        }
        m_uncommittedSpliceps.clear();

        // All successful, connect the drivers
        for (const Assignment& a : assignments) {
            if (DfgSplicePacked* const spp = a.m_lhsp->template cast<DfgSplicePacked>()) {
                spp->addDriver(flp, a.m_idx, a.m_rhsp);
            } else if (DfgSpliceArray* const sap = a.m_lhsp->template cast<DfgSpliceArray>()) {
                sap->addDriver(flp, a.m_idx, a.m_rhsp);
            } else {
                a.m_lhsp->v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
            }
        }
        return true;
    }

    // Convert the assignment with the given LHS and RHS into DFG.
    // Returns true on success, false if not representable.
    bool convertEquation(FileLine* flp, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        // Check data types are compatible.
        if (!DfgVertex::isSupportedDType(lhsp->dtypep())
            || !DfgVertex::isSupportedDType(rhsp->dtypep())) {
            ++m_ctx.m_nonRepDType;
            return false;
        }

        // For now, only direct array assignment is supported (e.g. a = b, but not a = _ ? b : c)
        if (VN_IS(rhsp->dtypep()->skipRefp(), UnpackArrayDType) && !VN_IS(rhsp, VarRef)) {
            ++m_ctx.m_nonRepDType;
            return false;
        }

        // Cannot handle mismatched widths. Mismatched assignments should have been fixed up in
        // earlier passes anyway, so this should never be hit, but being paranoid just in case.
        if (lhsp->width() != rhsp->width()) {  // LCOV_EXCL_START
            ++m_ctx.m_nonRepWidth;
            return false;
        }  // LCOV_EXCL_STOP

        // Convert the RHS expression
        DfgVertex* const rVtxp = convertRValue(rhsp);
        if (!rVtxp) return false;

        // Connect the RHS vertex to the LHS targets
        if (!convertAssignment(flp, lhsp, rVtxp)) return false;

        // All good
        ++m_ctx.m_representable;
        return true;
    }

    // Convert an AstNodeAssign (AstAssign or AstAssignW)
    bool convertNodeAssign(AstNodeAssign* nodep) {
        UASSERT_OBJ(VN_IS(nodep, AssignW) || VN_IS(nodep, Assign), nodep, "Invalid subtype");
        ++m_ctx.m_inputEquations;

        // Cannot handle assignment with timing control yet
        if (nodep->timingControlp()) {
            ++m_ctx.m_nonRepTiming;
            return false;
        }

        return convertEquation(nodep->fileline(), nodep->lhsp(), nodep->rhsp());
    }

    // Convert special simple form Always block into DFG.
    // Returns true on success, false if not representable/not simple.
    bool convertSimpleAlways(AstAlways* nodep) {
        // Only consider single statement block
        if (!nodep->isJustOneBodyStmt()) return false;

        AstNode* const stmtp = nodep->stmtsp();

        if (AstAssign* const assignp = VN_CAST(stmtp, Assign)) {
            return convertNodeAssign(assignp);
        }

        if (AstIf* const ifp = VN_CAST(stmtp, If)) {
            // Will only handle single assignments to the same LHS in both branches
            AstAssign* const thenp = VN_CAST(ifp->thensp(), Assign);
            AstAssign* const elsep = VN_CAST(ifp->elsesp(), Assign);
            if (!thenp || !elsep || thenp->nextp() || elsep->nextp()
                || !thenp->lhsp()->sameTree(elsep->lhsp())) {
                return false;
            }

            ++m_ctx.m_inputEquations;
            if (thenp->timingControlp() || elsep->timingControlp()) {
                ++m_ctx.m_nonRepTiming;
                return false;
            }

            // Create a conditional for the rhs by borrowing the components from the AstIf
            AstCond* const rhsp = new AstCond{ifp->fileline(),  //
                                              ifp->condp()->unlinkFrBack(),  //
                                              thenp->rhsp()->unlinkFrBack(),  //
                                              elsep->rhsp()->unlinkFrBack()};
            const bool success = convertEquation(ifp->fileline(), thenp->lhsp(), rhsp);
            // Put the AstIf back together
            ifp->condp(rhsp->condp()->unlinkFrBack());
            thenp->rhsp(rhsp->thenp()->unlinkFrBack());
            elsep->rhsp(rhsp->elsep()->unlinkFrBack());
            // Delete the auxiliary conditional
            VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
            return success;
        }

        return false;
    }

    bool convertComplexAlways(AstAlways* nodep) {
        // Attempt to build CFG of block, give up if failed
        std::unique_ptr<const ControlFlowGraph> cfgp = V3Cfg::build(nodep);
        if (!cfgp) return false;

        // Gather written variables, give up if any are not supported.
        std::unordered_set<DfgVertexVar*> outputs;
        {
            bool abort = false;
            // We can ignore AstVarXRef here. The only thing we can do with DfgAlways is
            // synthesize it into regular vertices, which will fail on a VarXRef at that point.
            nodep->foreach([&](AstVarRef* vrefp) {
                if (!isSupported(vrefp)) {
                    abort = true;
                    return;
                }
                if (vrefp->access().isReadOnly()) return;
                outputs.emplace(getNet(getTarget(vrefp)));
            });
            if (abort) return false;
        }

        // Gather read variables, give up if any are not supported
        std::vector<DfgVertexVar*> inputs;
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            std::unique_ptr<std::vector<AstVarScope*>> readVscps = V3Cfg::liveVarScopes(*cfgp);
            if (!readVscps) return false;
            for (AstVarScope* const varp : *readVscps) {
                if (!DfgVertex::isSupportedDType(varp->varp()->dtypep())) return false;
                inputs.emplace_back(getNet(reinterpret_cast<Variable*>(varp)));
            }
        } else {
            std::unique_ptr<std::vector<AstVar*>> readVarps = V3Cfg::liveVars(*cfgp);
            if (!readVarps) return false;
            for (AstVar* const varp : *readVarps) {
                if (!DfgVertex::isSupportedDType(varp->dtypep())) return false;
                inputs.emplace_back(getNet(reinterpret_cast<Variable*>(varp)));
            }
        }

        // OK, we can convert the AstAlways into a DfgAlways

        // Create the DfgAlways
        DfgAlways* const alwaysp = new DfgAlways{m_dfg, nodep, std::move(cfgp)};
        // Connect inputs
        for (DfgVertexVar* const vtxp : inputs) alwaysp->addInput(vtxp);
        // Connect outputs
        for (DfgVertexVar* const vtxp : outputs) {
            FileLine* const flp = vtxp->fileline();
            AstNodeDType* const dtypep = vtxp->dtypep();
            if (vtxp->is<DfgVarPacked>()) {
                if (!vtxp->srcp()) vtxp->srcp(new DfgSplicePacked{m_dfg, flp, dtypep});
                DfgSplicePacked* const splicep = vtxp->srcp()->as<DfgSplicePacked>();
                splicep->addUnresolvedDriver(alwaysp);
            } else {
                nodep->v3fatalSrc("Unhandled DfgVertexVar sub-type");  // LCOV_EXCL_LINE
            }
        }

        // Done
        return true;
    }

    // VISITORS

    // Unhandled node
    void visit(AstNode* nodep) override {
        if (!m_foundUnhandled && m_converting) ++m_ctx.m_nonRepUnknown;
        m_foundUnhandled = true;
    }

    // Expressions - mostly auto generated, but a few special ones
    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;
        // This visit method is only called on RValues, where only read refs are supportes
        if (!nodep->access().isReadOnly() || !isSupported(nodep)) {
            m_foundUnhandled = true;
            ++m_ctx.m_nonRepVarRef;
            return;
        }
        nodep->user2p(getNet(getTarget(nodep)));
    }
    void visit(AstConst* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;
        DfgVertex* const vtxp = new DfgConst{m_dfg, nodep->fileline(), nodep->num()};
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
            DfgSel* const selp = new DfgSel{m_dfg, flp, DfgVertex::dtypeFor(nodep)};
            selp->fromp(nodep->fromp()->user2u().to<DfgVertex*>());
            selp->lsb(constp->toUInt());
            vtxp = selp;
        } else {
            iterate(nodep->lsbp());
            if (m_foundUnhandled) return;
            DfgMux* const muxp = new DfgMux{m_dfg, flp, DfgVertex::dtypeFor(nodep)};
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

    // Convert AstAssignW to Dfg, return true if successful.
    template <bool Enabled = !T_Synthesis, std::enable_if_t<Enabled, bool> = true>
    bool convert(AstAssignW* nodep) {
        if (convertNodeAssign(nodep)) {
            // Remove node from Ast. Now represented by the Dfg.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return true;
        }

        return false;
    }

    // Convert AstAlways to Dfg, return true if successful.
    template <bool Enabled = !T_Synthesis, std::enable_if_t<Enabled, bool> = true>
    bool convert(AstAlways* nodep) {
        // Ignore sequential logic
        const VAlwaysKwd kwd = nodep->keyword();
        if (nodep->sensesp() || (kwd != VAlwaysKwd::ALWAYS && kwd != VAlwaysKwd::ALWAYS_COMB)) {
            return false;
        }

        // Attemp to convert special forms
        if (convertSimpleAlways(nodep)) {
            // Remove node from Ast. Now represented by the Dfg.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return true;
        }

        // Attempt to convert whole process
        if (convertComplexAlways(nodep)) {
            // Keep original node, referenced by the resulting DfgAlways
            return true;
        }

        return false;
    }

    // Convert AstAssign to Dfg return true if successful. Fills 'updates'
    // with bindings for assigned variables
    template <bool Enabled = T_Synthesis, std::enable_if_t<Enabled, bool> = true>
    bool convert(AstAssign* nodep, std::unordered_map<Variable*, DfgVertexVar*>& updates) {
        UASSERT_OBJ(updates.empty(), nodep, "'updates' should be empty");
        VL_RESTORER(m_updatesp);
        m_updatesp = &updates;
        return convertNodeAssign(nodep);
    }

    // Convert RValue expression to Dfg. Returns nullptr if failed.
    template <bool Enabled = T_Synthesis, std::enable_if_t<Enabled, bool> = true>
    DfgVertex* convert(AstNodeExpr* nodep) {
        ++m_ctx.m_inputExpressions;
        DfgVertex* const vtxp = convertRValue(nodep);
        if (vtxp) ++m_ctx.m_representable;
        return vtxp;
    }

    // CONSTRUCTORS

    // When T_Syntheis == false
    template <bool Enabled = !T_Synthesis, std::enable_if_t<Enabled, bool> = true>
    AstToDfgConverter(DfgGraph& dfg, V3DfgAstToDfgContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx}
        , m_tmpCntp{nullptr} {}

    // When T_Syntheis == true
    template <bool Enabled = T_Synthesis, std::enable_if_t<Enabled, bool> = true>
    AstToDfgConverter(DfgGraph& dfg, V3DfgAstToDfgContext& ctx, size_t& tmpCntr)
        : m_dfg{dfg}
        , m_ctx{ctx}
        , m_tmpCntp{&tmpCntr} {}
};

// Resolves multiple drivers (keep only the first one),
// and ensures drivers are stored in ascending index order
class AstToDfgNormalizeDrivers final {
    // TYPES
    struct Driver final {
        FileLine* m_flp;  // Location of driver in source
        uint32_t m_low;  // Low index of driven range
        DfgVertex* m_vtxp;  // Driving vertex
        Driver() = delete;
        Driver(FileLine* flp, uint32_t low, DfgVertex* vtxp)
            : m_flp{flp}
            , m_low{low}
            , m_vtxp{vtxp} {}
    };

    // STATE
    DfgGraph& m_dfg;  // The graph being processed
    DfgVertexVar& m_var;  // The variable being normalzied

    // METHODS

    // Normalize packed driver
    void normalizePacked(const std::string& sub, DfgSplicePacked* const splicep) {
        UASSERT_OBJ(splicep->arity() >= 1, splicep, "Undriven DfgSplicePacked");

        // The drivers of 'splicep'
        std::vector<Driver> drivers;
        drivers.reserve(splicep->arity());
        // The unresolved drivers of 'splicep'
        std::vector<DfgVertex*> udriverps;
        udriverps.reserve(splicep->arity());

        // Sometime assignment ranges are coalesced by V3Const,
        // so we unpack concatenations for better error reporting.
        const std::function<void(FileLine*, uint32_t, DfgVertex*)> gather
            = [&](FileLine* flp, uint32_t lsb, DfgVertex* vtxp) -> void {
            if (DfgConcat* const concatp = vtxp->cast<DfgConcat>()) {
                DfgVertex* const rhsp = concatp->rhsp();
                auto const rhs_width = rhsp->width();
                gather(rhsp->fileline(), lsb, rhsp);
                DfgVertex* const lhsp = concatp->lhsp();
                gather(lhsp->fileline(), lsb + rhs_width, lhsp);
            } else {
                drivers.emplace_back(flp, lsb, vtxp);
            }
        };

        // Gather and unlink all drivers
        splicep->forEachSourceEdge([&](DfgEdge& edgeA, size_t iA) {
            DfgVertex* const driverAp = edgeA.sourcep();
            UASSERT_OBJ(driverAp, splicep, "Should not have created undriven sources");
            UASSERT_OBJ(!splicep->driverIsDefault(iA), splicep, "Should not be default");

            // Gather
            if (!splicep->driverIsUnresolved(iA)) {
                // Resolved driver
                UASSERT_OBJ(!driverAp->is<DfgVertexSplice>(), splicep,
                            "Should not be DfgVertexSplice");
                gather(splicep->driverFileLine(iA), splicep->driverLsb(iA), driverAp);
            } else if (DfgAlways* const alwaysp = driverAp->cast<DfgAlways>()) {
                // Still unresolved (Other DfgAlways driving same variable)
                udriverps.emplace_back(alwaysp);
            } else if (!driverAp->is<DfgSplicePacked>()) {
                // Previously unresolved, but now resolved after synthesis into
                // a complete assignment, integrate it.
                UASSERT_OBJ(driverAp->width() == splicep->width(), splicep,
                            "Should be driver for whole variable");
                gather(splicep->driverFileLine(iA), 0, driverAp);
            } else {
                // Previously unresolved, but now resolved after synthesis into
                // a partial assignment, integrate each part.
                DfgSplicePacked* const spliceBp = driverAp->as<DfgSplicePacked>();
                spliceBp->forEachSourceEdge([&](DfgEdge& edgeB, size_t iB) {
                    DfgVertex* const driverBp = edgeB.sourcep();
                    UASSERT_OBJ(driverBp, spliceBp, "Should not have created undriven sources");
                    UASSERT_OBJ(!spliceBp->driverIsUnresolved(iB), spliceBp,
                                "Should not be unresolved");

                    // Default driver of circular variable, we can ignore
                    if (spliceBp->driverIsDefault(iB)) return;

                    // Resolved driver
                    UASSERT_OBJ(!driverBp->is<DfgVertexSplice>(), spliceBp,
                                "Should not be DfgVertexSplice");
                    gather(spliceBp->driverFileLine(iB), spliceBp->driverLsb(iB), driverBp);
                });
            }

            // Unlink
            edgeA.unlinkSource();
        });
        splicep->resetSources();

        const auto cmp = [](const Driver& a, const Driver& b) {
            if (a.m_low != b.m_low) return a.m_low < b.m_low;
            return a.m_flp->operatorCompare(*b.m_flp) < 0;
        };

        // Sort drivers by LSB
        std::stable_sort(drivers.begin(), drivers.end(), cmp);

        // Fix multiply driven ranges
        for (auto it = drivers.begin(); it != drivers.end();) {
            Driver& a = *it++;
            const uint32_t aWidth = a.m_vtxp->width();
            const uint32_t aEnd = a.m_low + aWidth;
            while (it != drivers.end()) {
                Driver& b = *it;
                // If no overlap, then nothing to do
                if (b.m_low >= aEnd) break;

                const uint32_t bWidth = b.m_vtxp->width();
                const uint32_t bEnd = b.m_low + bWidth;
                const uint32_t overlapEnd = std::min(aEnd, bEnd) - 1;

                // The AstVar/AstVarScope to report errors against
                AstNode* const nodep = m_var.tmpForp() ? m_var.tmpForp() : m_var.nodep();
                AstVar* const varp
                    = VN_IS(nodep, Var) ? VN_AS(nodep, Var) : VN_AS(nodep, VarScope)->varp();
                // Loop index often abused, so suppress
                if (!varp->isUsedLoopIdx()) {
                    nodep->v3warn(  //
                        MULTIDRIVEN,
                        "Bits ["  //
                            << overlapEnd << ":" << b.m_low << "] of signal '"
                            << nodep->prettyName() << sub
                            << "' have multiple combinational drivers\n"
                            << a.m_flp->warnOther() << "... Location of first driver\n"
                            << a.m_flp->warnContextPrimary() << '\n'
                            << b.m_flp->warnOther() << "... Location of other driver\n"
                            << b.m_flp->warnContextSecondary() << nodep->warnOther()
                            << "... Only the first driver will be respected");
                }

                // If the first driver completely covers the range of the second driver,
                // we can just delete the second driver completely, otherwise adjust the
                // second driver to apply from the end of the range of the first driver.
                if (aEnd >= bEnd) {
                    it = drivers.erase(it);
                } else {
                    const auto dtypep = DfgVertex::dtypeForWidth(bEnd - aEnd);
                    DfgSel* const selp = new DfgSel{m_dfg, b.m_vtxp->fileline(), dtypep};
                    selp->fromp(b.m_vtxp);
                    selp->lsb(aEnd - b.m_low);
                    b.m_low = aEnd;
                    b.m_vtxp = selp;
                    std::stable_sort(it, drivers.end(), cmp);
                }
            }
        }

        // Reinsert drivers in order
        for (const Driver& d : drivers) splicep->addDriver(d.m_flp, d.m_low, d.m_vtxp);
        for (DfgVertex* const vtxp : udriverps) splicep->addUnresolvedDriver(vtxp);
    }

    // Normalize array driver
    void normalizeArray(const std::string& sub, DfgSpliceArray* const splicep) {
        UASSERT_OBJ(splicep->arity() >= 1, splicep, "Undriven DfgSpliceArray");

        // The drivers of 'splicep'
        std::vector<Driver> drivers;
        drivers.reserve(splicep->arity());

        // Normalize, gather, and unlink all drivers
        splicep->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
            DfgVertex* const driverp = edge.sourcep();
            UASSERT(driverp, "Should not have created undriven sources");
            const uint32_t idx = splicep->driverIndex(i);
            // Normalize
            if (DfgSplicePacked* const splicePackedp = driverp->cast<DfgSplicePacked>()) {
                normalizePacked(sub + "[" + std::to_string(idx) + "]", splicePackedp);
            } else if (DfgSpliceArray* const spliceArrayp = driverp->cast<DfgSpliceArray>()) {
                normalizeArray(sub + "[" + std::to_string(idx) + "]", spliceArrayp);
            } else if (driverp->is<DfgVertexSplice>()) {
                driverp->v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
            }
            // Gather
            drivers.emplace_back(splicep->driverFileLine(i), idx, driverp);
            // Unlink
            edge.unlinkSource();
        });
        splicep->resetSources();

        const auto cmp = [](const Driver& a, const Driver& b) {
            if (a.m_low != b.m_low) return a.m_low < b.m_low;
            return a.m_flp->operatorCompare(*b.m_flp) < 0;
        };

        // Sort drivers by index
        std::stable_sort(drivers.begin(), drivers.end(), cmp);

        // Fix multiply driven ranges
        for (auto it = drivers.begin(); it != drivers.end();) {
            Driver& a = *it++;
            AstUnpackArrayDType* aArrayDTypep = VN_CAST(a.m_vtxp->dtypep(), UnpackArrayDType);
            const uint32_t aElements = aArrayDTypep ? aArrayDTypep->elementsConst() : 1;
            const uint32_t aEnd = a.m_low + aElements;
            while (it != drivers.end()) {
                Driver& b = *it;
                // If no overlap, then nothing to do
                if (b.m_low >= aEnd) break;

                AstUnpackArrayDType* bArrayDTypep = VN_CAST(b.m_vtxp->dtypep(), UnpackArrayDType);
                const uint32_t bElements = bArrayDTypep ? bArrayDTypep->elementsConst() : 1;
                const uint32_t bEnd = b.m_low + bElements;
                const uint32_t overlapEnd = std::min(aEnd, bEnd) - 1;

                // The AstVar/AstVarScope to report errors against
                AstNode* const nodep = m_var.tmpForp() ? m_var.tmpForp() : m_var.nodep();
                nodep->v3warn(  //
                    MULTIDRIVEN,
                    "Elements ["  //
                        << overlapEnd << ":" << b.m_low << "] of signal '" << nodep->prettyName()
                        << sub << "' have multiple combinational drivers\n"
                        << a.m_flp->warnOther() << "... Location of first driver\n"
                        << a.m_flp->warnContextPrimary() << '\n'
                        << b.m_flp->warnOther() << "... Location of other driver\n"
                        << b.m_flp->warnContextSecondary() << nodep->warnOther()
                        << "... Only the first driver will be respected");

                // If the first driver completely covers the range of the second driver,
                // we can just delete the second driver completely, otherwise adjust the
                // second driver to apply from the end of the range of the first driver.
                if (aEnd >= bEnd) {
                    it = drivers.erase(it);
                } else {
                    const auto distance = std::distance(drivers.begin(), it);
                    DfgVertex* const bVtxp = b.m_vtxp;
                    FileLine* const flp = b.m_vtxp->fileline();
                    AstNodeDType* const elemDtypep = DfgVertex::dtypeFor(
                        VN_AS(splicep->dtypep(), UnpackArrayDType)->subDTypep());
                    // Remove this driver
                    it = drivers.erase(it);
                    // Add missing items element-wise
                    for (uint32_t i = aEnd; i < bEnd; ++i) {
                        DfgArraySel* const aselp = new DfgArraySel{m_dfg, flp, elemDtypep};
                        aselp->fromp(bVtxp);
                        aselp->bitp(new DfgConst{m_dfg, flp, 32, i});
                        drivers.emplace_back(flp, i, aselp);
                    }
                    it = drivers.begin();
                    std::advance(it, distance);
                    std::stable_sort(it, drivers.end(), cmp);
                }
            }
        }

        // Reinsert drivers in order
        for (const Driver& d : drivers) splicep->addDriver(d.m_flp, d.m_low, d.m_vtxp);
    }

    // CONSTRUCTOR
    AstToDfgNormalizeDrivers(DfgGraph& dfg, DfgVertexVar& var)
        : m_dfg{dfg}
        , m_var{var} {
        // Nothing to do for un-driven (input) variables
        if (!var.srcp()) return;

        // The driver of a variable must always be a splice vertex, normalize it
        if (DfgSpliceArray* const sArrayp = var.srcp()->cast<DfgSpliceArray>()) {
            normalizeArray("", sArrayp);
        } else if (DfgSplicePacked* const sPackedp = var.srcp()->cast<DfgSplicePacked>()) {
            normalizePacked("", sPackedp);
        } else {
            var.v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
        }
    }

public:
    // Normalize drivers of given variable
    static void apply(DfgGraph& dfg, DfgVertexVar& var) { AstToDfgNormalizeDrivers{dfg, var}; }
};

// Coalesce contiguous driver ranges,
// and remove redundant splice vertices (when the variable is driven whole)
class AstToDfgCoalesceDrivers final {
    // TYPES
    struct Driver final {
        FileLine* m_flp;  // Location of driver in source
        uint32_t m_low;  // Low index of driven range
        DfgVertex* m_vtxp;  // Driving vertex
        Driver() = delete;
        Driver(FileLine* flp, uint32_t low, DfgVertex* vtxp)
            : m_flp{flp}
            , m_low{low}
            , m_vtxp{vtxp} {}
    };

    // STATE
    DfgGraph& m_dfg;  // The graph being processed
    V3DfgAstToDfgContext& m_ctx;  // The context for stats

    // METHODS

    // Coalesce packed driver - return the coalesced vertex and location for 'splicep'
    std::pair<DfgVertex*, FileLine*> coalescePacked(DfgSplicePacked* const splicep) {
        UASSERT_OBJ(splicep->arity() >= 1, splicep, "Undriven DfgSplicePacked");

        // The drivers of 'splicep'
        std::vector<Driver> drivers;
        drivers.reserve(splicep->arity());
        // The unresolved drivers of 'splicep'
        std::vector<DfgVertex*> udriverps;
        udriverps.reserve(splicep->arity());
        // The default driver of 'splicep'
        Driver ddriver{nullptr, 0, nullptr};

        // Gather and unlink all drivers
        int64_t prevHigh = -1;  // High index of previous driven range
        splicep->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
            DfgVertex* const driverp = edge.sourcep();
            UASSERT_OBJ(driverp, splicep, "Should not have created undriven sources");

            // Gather
            if (splicep->driverIsDefault(i)) {
                // Default driver
                UASSERT_OBJ(!ddriver.m_vtxp, driverp, "Multiple default drivers");
                ddriver.m_vtxp = driverp;
                ddriver.m_flp = splicep->driverFileLine(i);
            } else if (splicep->driverIsUnresolved(i)) {
                // Unresolved driver
                UASSERT_OBJ(driverp->is<DfgAlways>(), splicep, "Should be DfgAlways");
                udriverps.emplace_back(driverp);
            } else {
                // Resolved driver
                UASSERT_OBJ(!driverp->is<DfgVertexSplice>(), splicep,
                            "Should not be DfgVertexSplice");
                const uint32_t low = splicep->driverLsb(i);
                UASSERT_OBJ(static_cast<int64_t>(low) > prevHigh, splicep,
                            "Drivers should have been normalized");
                prevHigh = low + driverp->width() - 1;
                drivers.emplace_back(splicep->driverFileLine(i), low, driverp);
            }

            // Unlink
            edge.unlinkSource();
        });
        splicep->resetSources();

        // Coalesce adjacent ranges
        if (drivers.size() > 1) {
            size_t mergeInto = 0;
            size_t mergeFrom = 1;
            do {
                Driver& into = drivers[mergeInto];
                Driver& from = drivers[mergeFrom];
                const uint32_t intoWidth = into.m_vtxp->width();
                const uint32_t fromWidth = from.m_vtxp->width();

                if (into.m_low + intoWidth == from.m_low) {
                    // Adjacent ranges, coalesce
                    const auto dtypep = DfgVertex::dtypeForWidth(intoWidth + fromWidth);
                    DfgConcat* const concatp = new DfgConcat{m_dfg, into.m_flp, dtypep};
                    concatp->rhsp(into.m_vtxp);
                    concatp->lhsp(from.m_vtxp);
                    into.m_vtxp = concatp;
                    from.m_vtxp = nullptr;  // Mark as moved
                    ++m_ctx.m_coalescedAssignments;
                } else {
                    // There is a gap - future merges go into the next position
                    ++mergeInto;
                    // Move 'from' into the next position, unless it's already there
                    if (mergeFrom != mergeInto) {
                        Driver& next = drivers[mergeInto];
                        UASSERT_OBJ(!next.m_vtxp, next.m_flp, "Should have been marked moved");
                        next = from;
                        from.m_vtxp = nullptr;  // Mark as moved
                    }
                }

                // Consider next driver
                ++mergeFrom;
            } while (mergeFrom < drivers.size());
            // Rightsize vector
            drivers.erase(drivers.begin() + (mergeInto + 1), drivers.end());
        }

        // If the variable is driven whole, we can just use that driver
        if (udriverps.empty()  //
            && drivers.size() == 1  //
            && drivers[0].m_low == 0  //
            && drivers[0].m_vtxp->width() == splicep->width()) {
            VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
            // Use the driver directly
            return {drivers[0].m_vtxp, drivers[0].m_flp};
        }

        // Reinsert drivers in order
        for (const Driver& d : drivers) splicep->addDriver(d.m_flp, d.m_low, d.m_vtxp);
        for (DfgVertex* const vtxp : udriverps) splicep->addUnresolvedDriver(vtxp);
        if (ddriver.m_vtxp) splicep->addDefaultDriver(ddriver.m_flp, ddriver.m_vtxp);
        // Use the original splice
        return {splicep, splicep->fileline()};
    }

    // Coalesce array driver - return the coalesced vertex and location for 'splicep'
    std::pair<DfgVertex*, FileLine*> coalesceArray(DfgSpliceArray* const splicep) {
        UASSERT_OBJ(splicep->arity() >= 1, splicep, "Undriven DfgSpliceArray");

        // The drivers of 'splicep'
        std::vector<Driver> drivers;
        drivers.reserve(splicep->arity());

        // Coalesce, gather and unlink all drivers
        int64_t prevHigh = -1;  // High index of previous driven range
        splicep->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
            DfgVertex* driverp = edge.sourcep();
            UASSERT_OBJ(driverp, splicep, "Should not have created undriven sources");
            const uint32_t low = splicep->driverIndex(i);
            UASSERT_OBJ(static_cast<int64_t>(low) > prevHigh, splicep,
                        "Drivers should have been normalized");
            prevHigh = low;
            FileLine* flp = splicep->driverFileLine(i);
            // Coalesce
            if (DfgSplicePacked* const spp = driverp->cast<DfgSplicePacked>()) {
                std::tie(driverp, flp) = coalescePacked(spp);
            } else if (DfgSpliceArray* const sap = driverp->cast<DfgSpliceArray>()) {
                std::tie(driverp, flp) = coalesceArray(sap);
            } else if (driverp->is<DfgVertexSplice>()) {
                driverp->v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
            }
            // Gather
            drivers.emplace_back(flp, low, driverp);
            // Unlink
            edge.unlinkSource();
        });
        splicep->resetSources();

        // If the variable is driven whole, we can just use that driver
        if (drivers.size() == 1  //
            && drivers[0].m_low == 0  //
            && drivers[0].m_vtxp->dtypep()->isSame(splicep->dtypep())) {
            VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
            // Use the driver directly
            return {drivers[0].m_vtxp, drivers[0].m_flp};
        }

        // Reinsert drivers in order
        for (const Driver& d : drivers) splicep->addDriver(d.m_flp, d.m_low, d.m_vtxp);
        // Use the original splice
        return {splicep, splicep->fileline()};
    }

    // CONSTRUCTOR
    AstToDfgCoalesceDrivers(DfgGraph& dfg, DfgVertexVar& var, V3DfgAstToDfgContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {
        // Nothing to do for un-driven (input) variables
        if (!var.srcp()) return;

        // If the driver of the variable is not a splice, it was already coalesced
        DfgVertexSplice* const srcp = var.srcp()->cast<DfgVertexSplice>();
        UASSERT(srcp, "EEEE?");
        if (!srcp) return;

        // Coalesce
        std::pair<DfgVertex*, FileLine*> normalizedDriver;
        if (DfgSpliceArray* const sArrayp = srcp->cast<DfgSpliceArray>()) {
            normalizedDriver = coalesceArray(sArrayp);
        } else if (DfgSplicePacked* const sPackedp = srcp->cast<DfgSplicePacked>()) {
            normalizedDriver = coalescePacked(sPackedp);
        } else {
            var.v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
        }
        var.srcp(normalizedDriver.first);
        var.driverFileLine(normalizedDriver.second);
    }

public:
    // Coalesce drivers of given variable
    static void apply(DfgGraph& dfg, DfgVertexVar& var, V3DfgAstToDfgContext& ctx) {
        AstToDfgCoalesceDrivers{dfg, var, ctx};
    }
};

// Visitor that converts a whole module (when T_Scoped is false),
// or the whole netlist (when T_Scoped is true).
template <bool T_Scoped>
class AstToDfgVisitor final : public VNVisitor {
    // NODE STATE
    const VNUser2InUse m_user2InUse;  // Used by AstToDfgConverter

    // TYPES
    using RootType = std::conditional_t<T_Scoped, AstNetlist, AstModule>;
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;

    // STATE
    // The convert instance to use for each construct
    AstToDfgConverter<T_Scoped, /* T_Synthesis: */ false> m_converter;

    // METHODS
    static Variable* getTarget(const AstVarRef* refp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<Variable*>(refp->varScopep());
        } else {
            return reinterpret_cast<Variable*>(refp->varp());
        }
    }

    // Mark variables referenced under node
    static void markReferenced(AstNode* nodep) {
        nodep->foreach([](const AstVarRef* refp) {
            Variable* const tgtp = getTarget(refp);
            // Mark as read from non-DFG logic
            if (refp->access().isReadOrRW()) DfgVertexVar::setHasModRdRefs(tgtp);
            // Mark as written from non-DFG logic
            if (refp->access().isWriteOrRW()) DfgVertexVar::setHasModWrRefs(tgtp);
        });
    }

    // VISITORS
    // Unhandled node
    void visit(AstNode* nodep) override { markReferenced(nodep); }

    // Containers to descend through to find logic constructs
    void visit(AstNetlist* nodep) override { iterateAndNextNull(nodep->modulesp()); }
    void visit(AstModule* nodep) override { iterateAndNextNull(nodep->stmtsp()); }
    void visit(AstTopScope* nodep) override { iterate(nodep->scopep()); }
    void visit(AstScope* nodep) override { iterateChildren(nodep); }
    void visit(AstActive* nodep) override {
        if (nodep->hasCombo()) {
            iterateChildren(nodep);
        } else {
            markReferenced(nodep);
        }
    }

    // Non-representable constructs
    void visit(AstCell* nodep) override { markReferenced(nodep); }
    void visit(AstNodeProcedure* nodep) override { markReferenced(nodep); }

    // Potentially representable constructs
    void visit(AstAssignW* nodep) override {
        if (!m_converter.convert(nodep)) markReferenced(nodep);
    }
    void visit(AstAlways* nodep) override {
        if (!m_converter.convert(nodep)) markReferenced(nodep);
    }

    // CONSTRUCTOR
    AstToDfgVisitor(DfgGraph& dfg, RootType& root, V3DfgAstToDfgContext& ctx)
        : m_converter{dfg, ctx} {
        iterate(&root);
    }

public:
    static void apply(DfgGraph& dfg, RootType& root, V3DfgAstToDfgContext& ctx) {
        // Convert all logic under 'root'
        AstToDfgVisitor{dfg, root, ctx};
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-conv");
        // Normalize and coalesce all variable drivers
        for (DfgVertexVar& var : dfg.varVertices()) {
            AstToDfgNormalizeDrivers::apply(dfg, var);
            AstToDfgCoalesceDrivers::apply(dfg, var, ctx);
        }
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-norm");
        // Remove all unused vertices
        V3DfgPasses::removeUnused(dfg);
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-prun");
    }
};

std::unique_ptr<DfgGraph> V3DfgPasses::astToDfg(AstModule& module, V3DfgContext& ctx) {
    DfgGraph* const dfgp = new DfgGraph{&module, module.name()};
    AstToDfgVisitor</* T_Scoped: */ false>::apply(*dfgp, module, ctx.m_ast2DfgContext);
    return std::unique_ptr<DfgGraph>{dfgp};
}

std::unique_ptr<DfgGraph> V3DfgPasses::astToDfg(AstNetlist& netlist, V3DfgContext& ctx) {
    DfgGraph* const dfgp = new DfgGraph{nullptr, "netlist"};
    AstToDfgVisitor</* T_Scoped: */ true>::apply(*dfgp, netlist, ctx.m_ast2DfgContext);
    return std::unique_ptr<DfgGraph>{dfgp};
}

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
        Driver() = default;
        Driver(FileLine* flp, uint32_t lo, DfgVertex* vtxp)
            : m_flp{flp}
            , m_lo{lo}
            , m_hi{lo + vtxp->width() - 1}
            , m_vtxp{vtxp} {}
    };

    // STATE
    DfgGraph& m_dfg;  // The graph being built
    V3DfgSynthesisContext& m_ctx;  // The context for stats
    size_t m_tmpCnt = 0;  // Temporary variable counter
    // The convert instance to use for each construct
    AstToDfgConverter<T_Scoped, /* T_Synthesis: */ true> m_converter;

    // METHODS
    static AstVar* getAstVar(Variable* vp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<AstVarScope*>(vp)->varp();
        } else {
            return reinterpret_cast<AstVar*>(vp);
        }
    }

    std::pair<std::vector<Driver>, Driver> gatherDrivers(Variable* varp, DfgVertexVar* vtxp) {
        std::vector<Driver> drivers;
        Driver defaultDriver;

        UASSERT_OBJ(vtxp->nodep() != varp, varp, "Can't handle input variable");
        UASSERT_OBJ(vtxp->srcp(), vtxp, "Should have a driver");

        if (DfgSplicePacked* const spp = vtxp->srcp()->cast<DfgSplicePacked>()) {
            spp->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
                DfgVertex* const driverp = edge.sourcep();
                UASSERT_OBJ(driverp, vtxp, "Should not have created undriven sources");
                FileLine* const flp = spp->driverFileLine(i);

                // Should not have an unresovled driver
                UASSERT_OBJ(!spp->driverIsUnresolved(i), vtxp, "Should not be unresolved");

                // Default driver
                if (spp->driverIsDefault(i)) {
                    UASSERT_OBJ(!defaultDriver.m_vtxp, vtxp, "Multiple default drivers");
                    defaultDriver.m_vtxp = driverp;
                    defaultDriver.m_flp = flp;
                    return;
                }

                // Resolved driver
                const uint32_t lo = spp->driverLsb(i);
                UASSERT_OBJ(drivers.empty() || lo > drivers.back().m_hi, spp, "Unordered drivers");
                drivers.emplace_back(flp, lo, driverp);
            });
        } else if (vtxp->is<DfgVertexSplice>()) {
            vtxp->v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
        } else {
            // Variable driven whole, just add the single driver
            drivers.emplace_back(vtxp->fileline(), 0, vtxp);
        }

        return {std::move(drivers), defaultDriver};
    }

    void incorporatePreviousDriver(Variable* varp, DfgVertexVar* newp, DfgVertexVar* oldp) {
        UASSERT_OBJ(newp->srcp(), varp, "Assigned variable has no driver");

        // New driver was not yet coalesced, so should always be a splice
        DfgSplicePacked* const nSplicep = newp->srcp()->as<DfgSplicePacked>();

        // If the old value is the real variable we just computed the new value for,
        // then it is the circular feedback into the synthesized block, add it as default driver.
        if (oldp->nodep() == varp) {
            nSplicep->addDefaultDriver(oldp->fileline(), oldp);
            return;
        }

        UASSERT_OBJ(oldp->srcp(), varp, "Previously assigned variable has no driver");

        // Gather drivers of 'newp' - they are in incresing range order with no overlaps
        std::vector<Driver> nDrivers;
        Driver nDefault;
        std::tie(nDrivers, nDefault) = gatherDrivers(varp, newp);
        UASSERT_OBJ(!nDrivers.empty(), varp, "Should have a proper driver");
        UASSERT_OBJ(!nDefault.m_vtxp, varp, "Should not have a default after conversion");

        // Gather drivers of 'oldp' - they are in incresing range order with no overlaps
        std::vector<Driver> oDrivers;
        Driver oDefault;
        std::tie(oDrivers, oDefault) = gatherDrivers(varp, oldp);
        UASSERT_OBJ(!oDrivers.empty(), varp, "Should have a proper driver");

        // Additional drivers of 'newp' propagated from 'oldp'
        std::vector<Driver> pDrivers;

        // Add bits between 'msb' and 'lsb' from 'oldp' to 'pDrivers'
        const auto addToPDriver = [&](FileLine* const flp, uint32_t msb, uint32_t lsb) {
            UASSERT_OBJ(pDrivers.empty() || lsb > pDrivers.back().m_hi, flp, "Non ascending");
            DfgSel* const selp = new DfgSel{m_dfg, flp, DfgVertex::dtypeForWidth(msb - lsb + 1)};
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
            // Need to merge propatated sources
            nSplicep->forEachSourceEdge([](DfgEdge& edge, size_t) { edge.unlinkSource(); });
            nSplicep->resetSources();

            // Both 'nDrivers' and 'pDrivers' are in ascending order, add them merged
            auto nIt = nDrivers.begin();
            auto pIt = pDrivers.begin();
            while (nIt != nDrivers.end() && pIt != pDrivers.end()) {
                const Driver& nD = *nIt;
                const Driver& pD = *pIt;
                if (nD.m_lo < pD.m_lo) {
                    nSplicep->addDriver(nD.m_flp, nD.m_lo, nD.m_vtxp);
                    ++nIt;
                } else {
                    nSplicep->addDriver(pD.m_flp, pD.m_lo, pD.m_vtxp);
                    ++pIt;
                }
            }
            // Append rest of longer lit
            while (nIt != nDrivers.end()) {
                const Driver& d = *nIt++;
                nSplicep->addDriver(d.m_flp, d.m_lo, d.m_vtxp);
            }
            while (pIt != pDrivers.end()) {
                const Driver& d = *pIt++;
                nSplicep->addDriver(d.m_flp, d.m_lo, d.m_vtxp);
            }
        }

        // If the old had a default, add to the new one too
        if (oDefault.m_vtxp) nSplicep->addDefaultDriver(oDefault.m_flp, oDefault.m_vtxp);
    }

    bool synthesizeBasicBlock(const SymTab& iSymTab, SymTab& oSymTab, const BasicBlock& bb) {
        // Initialize Variable -> Vertex bindings available in this block
        for (const auto& pair : iSymTab) {
            Variable* const varp = pair.first;
            DfgVertexVar* const vtxp = pair.second;
            varp->user2p(vtxp);
            oSymTab[varp] = vtxp;
        }

        // Synthesize each statement individually
        std::unordered_map<Variable*, DfgVertexVar*> updates;
        for (AstNode* stmtp : bb.stmtps()) {
            // Regular statements
            if (AstAssign* const ap = VN_CAST(stmtp, Assign)) {
                // Convet this assignment
                if (!m_converter.convert(ap, updates)) return false;
                // Apply variable updates from this statement
                for (const auto& pair : updates) {
                    // The target variable that was assigned to
                    Variable* const varp = pair.first;
                    // The new, potentially partially assigned value
                    DfgVertexVar* const newp = pair.second;
                    // Resolve multi-drivers of this variable withih this statement
                    AstToDfgNormalizeDrivers::apply(m_dfg, *newp);
                    // If exists, inncorporate old value into the new value
                    if (DfgVertexVar* const oldp = varp->user2u().template to<DfgVertexVar*>()) {
                        incorporatePreviousDriver(varp, newp, oldp);
                    }
                    // Coalesce drivers
                    AstToDfgCoalesceDrivers::apply(m_dfg, *newp, m_ctx.m_ast2DfgContext);
                    // Update binding of target variable
                    varp->user2p(newp);
                    // Update output symbol table of this block
                    oSymTab[varp] = newp;
                }
                updates.clear();
                continue;
            }
            // Terminators
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                UASSERT_OBJ(ifp == bb.stmtps().back(), ifp, "Branch should be last statement");
                continue;
            }
            // Unhandled
            return false;
        }
        return true;
    }

    // Construct predicate of basic block
    DfgVertex* getBasicBlockPredicate(FileLine* const flp, const BasicBlock& bb) {
        // Entry block has no predecessors, use constant true;
        if (bb.inEmpty()) return new DfgConst{m_dfg, flp, 1, 1};

        // Or together all the incoming predicates
        const auto& inEdges = bb.inEdges();
        auto it = inEdges.begin();
        DfgVertex* resp = reinterpret_cast<DfgVertex*>((*it).userp());
        while (++it != inEdges.end()) {
            DfgOr* const orp = new DfgOr{m_dfg, flp, resp->dtypep()};
            orp->rhsp(resp);
            orp->lhsp(reinterpret_cast<DfgVertex*>((*it).userp()));
            resp = orp;
        }
        return resp;
    }

    // Given a basic block, and it's predicate, assign perdicates to its outgoing edges
    bool assignSuccessorPredicates(const BasicBlock& bb, DfgVertex* predp) {
        // The predicate of the block should be set
        UASSERT_OBJ(predp, predp, "Missing BasicBlock predicate");
        // There should be at most 2 successors
        UASSERT_OBJ(bb.outEdges().size() <= 2, predp, "More than 2 successor for BasicBlock");
        // Get the predictes based on the condition in the the terminator statement
        DfgVertex* takenPredp = nullptr;  // Predicate for taken branch
        DfgVertex* untknPredp = nullptr;  // Predicate for untaken branch - or nullptr if goto
        std::tie(takenPredp, untknPredp) = [&]() -> std::pair<DfgVertex*, DfgVertex*> {
            // Empty block -> implicit goto
            if (bb.stmtps().empty()) return {predp, nullptr};
            // Last statement in block
            AstNode* const stmtp = bb.stmtps().back();
            // Regular statements -> implicit goto
            if (!stmtp) return {predp, nullptr};
            if (VN_IS(stmtp, Assign)) return {predp, nullptr};
            // Branches
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                // Convet condition, give up if failed
                DfgVertex* const condp = m_converter.convert(ifp->condp());
                if (!condp) return {nullptr, nullptr};
                FileLine* const flp = condp->fileline();
                AstNodeDType* const bitDTypep = DfgVertex::dtypeForWidth(1);
                DfgVertex* const truthyp = [&]() -> DfgVertex* {
                    // Single bit condition can be use directly
                    if (condp->width() == 1) return condp;
                    // Multi bit condition: use 'condp != 0'
                    DfgNeq* const neqp = new DfgNeq{m_dfg, flp, bitDTypep};
                    neqp->lhsp(new DfgConst{m_dfg, flp, condp->width(), 0});
                    neqp->rhsp(condp);
                    return neqp;
                }();
                // New predicats are 'predp & truthyp' and 'predp & ~truthyp'
                DfgAnd* const takenp = new DfgAnd{m_dfg, flp, bitDTypep};
                takenp->lhsp(predp);
                takenp->rhsp(truthyp);
                DfgNot* const falsyp = new DfgNot{m_dfg, flp, bitDTypep};
                falsyp->srcp(truthyp);
                DfgAnd* const untknp = new DfgAnd{m_dfg, flp, bitDTypep};
                untknp->lhsp(predp);
                untknp->rhsp(falsyp);
                return {takenp, untknp};
            }
            // Unhandled
            return {nullptr, nullptr};
        }();
        if (!takenPredp) return false;
        // Assign predicates to successor edges
        for (const V3GraphEdge& edge : bb.outEdges()) {
            const ControlFlowGraphEdge& cfgEdge = *edge.as<ControlFlowGraphEdge>();
            DfgVertex* const edgePredp
                = cfgEdge.kind() == ControlFlowGraphEdge::Kind::ConditionFalse ? untknPredp
                                                                               : takenPredp;
            UASSERT_OBJ(edgePredp, takenPredp, "Missing untaken pedicate");
            // Set user pointer of edge
            const_cast<ControlFlowGraphEdge&>(cfgEdge).userp(edgePredp);
        }
        // Done
        return true;
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
        if (thenp->nodep() == varp) return nullptr;
        if (elsep->nodep() == varp) return nullptr;

        // Gather drivers of 'thenp' - only if 'thenp' is not an input to the synthesized block
        std::vector<Driver> tDrivers;
        Driver tDefault;
        std::tie(tDrivers, tDefault) = gatherDrivers(varp, thenp);

        // Gather drivers of 'elsep' - only if 'thenp' is not an input to the synthesized block
        std::vector<Driver> eDrivers;
        Driver eDefault;
        std::tie(eDrivers, eDefault) = gatherDrivers(varp, elsep);

        // Default drivers should be the same or not present on either
        UASSERT_OBJ(tDefault.m_vtxp == eDefault.m_vtxp, varp, "Different default drivers");

        // Location to use for the join vertices
        FileLine* const flp = predicatep->fileline();

        // Create a fresh temporary for the joined value
        DfgVertexVar* const joinp = createTmp(m_dfg, varp, "SynthJoin", m_tmpCnt++);

        // If both paths are fully driven, just create a simple conditional
        if (tDrivers.size() == 1  //
            && tDrivers[0].m_lo == 0  //
            && tDrivers[0].m_hi == thenp->width() - 1  //
            && eDrivers.size() == 1  //
            && eDrivers[0].m_lo == 0  //
            && eDrivers[0].m_hi == elsep->width() - 1) {
            UASSERT_OBJ(!tDefault.m_vtxp, varp, "Fully driven variable have default driver");

            AstNodeDType* const dtypep = DfgVertex::dtypeFor(getAstVar(varp));
            DfgCond* const condp = new DfgCond{m_dfg, flp, dtypep};
            condp->condp(predicatep);
            condp->thenp(thenp);
            condp->elsep(elsep);
            joinp->srcp(condp);

            // Done
            return joinp;
        }

        // Otherwise we need to merge them part by part

        // If different bits are driven, then some might not have been assigned.. Latch?
        if (tDrivers.size() != eDrivers.size()) return nullptr;

        DfgSplicePacked* const joinSplicep
            = new DfgSplicePacked{m_dfg, flp, DfgVertex::dtypeFor(getAstVar(varp))};
        joinp->srcp(joinSplicep);

        for (size_t i = 0; i < tDrivers.size(); ++i) {
            const Driver& tDriver = tDrivers[i];
            const Driver& eDriver = eDrivers[i];
            // If different bits are driven, then some might not have been assigned.. Latch?
            if (tDriver.m_lo != eDriver.m_lo || tDriver.m_hi != eDriver.m_hi) return nullptr;

            AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(tDriver.m_hi - tDriver.m_lo + 1);
            DfgCond* const condp = new DfgCond{m_dfg, flp, dtypep};
            condp->condp(predicatep);

            // We actally need to select the bits from the joined variables, not use the drivers
            DfgSel* const thenSelp = new DfgSel{m_dfg, flp, tDriver.m_vtxp->dtypep()};
            thenSelp->lsb(tDriver.m_lo);
            thenSelp->fromp(thenp);
            condp->thenp(thenSelp);

            // Same for the 'else' part
            DfgSel* const elseSelp = new DfgSel{m_dfg, flp, eDriver.m_vtxp->dtypep()};
            elseSelp->lsb(eDriver.m_lo);
            elseSelp->fromp(elsep);
            condp->elsep(elseSelp);

            // Add it as a driver to the join
            joinSplicep->addDriver(tDriver.m_flp, tDriver.m_lo, condp);
        }

        // If there was a default driver, add it to te join
        if (tDefault.m_vtxp) joinSplicep->addDefaultDriver(tDefault.m_flp, tDefault.m_vtxp);

        // Done
        return joinp;
    }

    bool createInputSymbolTable(SymTab& joined, const BasicBlock& bb,
                                const BasicBlockMap<SymTab>& bb2OSymTab) {
        // Input symbol table of entry block was previously initialzied
        if (bb.inEmpty()) return true;
        UASSERT(joined.empty(), "Unresolved input symbol table should be empty");

        // Fast path if there is only one predecessor
        if (bb.inSize1()) {
            joined = bb2OSymTab[*(bb.inEdges().frontp()->fromp()->as<BasicBlock>())];
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
                DfgVertex* const predicatep = reinterpret_cast<DfgVertex*>(edge.userp());
                const BasicBlock* const predecessorp = edge.fromp()->as<BasicBlock>();
                res.emplace_back(predecessorp, predicatep);
            }
            // Sort predecessors topologically. This way later blocks will come
            // after earlier blocks, and the entry block will be first if present.
            std::sort(res.begin(), res.end(), [](const Predecessor& a, const Predecessor& b) {  //
                return a.m_bbp->id() < b.m_bbp->id();
            });
            return res;
        }();

        // Start by copying the bindings from the oldest predecessor
        joined = bb2OSymTab[*predecessors[0].m_bbp];
        // Join over all other predecessors
        for (size_t i = 1; i < predecessors.size(); ++i) {
            DfgVertex* const predicatep = predecessors[i].m_predicatep;
            const SymTab& oSymTab = bb2OSymTab[*predecessors[i].m_bbp];
            // Give up if something is not assigned on all paths ... Latch?
            if (joined.size() != oSymTab.size()) return false;
            // Join each symbol
            for (auto& pair : joined) {
                Variable* const varp = pair.first;
                // Find same variable on other path
                auto it = oSymTab.find(varp);
                // Give up if something is not assigned on all paths ... Latch?
                if (it == oSymTab.end()) return false;
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

    // Synthesize a DfgAlways into regular vertices. Return ture on success.
    bool synthesizeAlways(DfgAlways& vtx) {
        // If any written variables are forced or otherwise udpated from
        // outside, we can't do it, as we will likely need to introduce
        // intermediate values that would not be updated.
        const bool hasExternalWriter = vtx.findSink<DfgVertex>([](const DfgVertex& sink) -> bool {
            // 'sink' is a splice (for which 'vtxp' is an unresolved driver),
            // which drives the target variable.
            DfgVertexVar* varp = sink.singleSink()->as<DfgVertexVar>();
            if (varp->hasXRefs()) return true;  // Target of a hierarchical reference
            AstVar* const astVarp = varp->varp();
            if (astVarp->isForced()) return true;  // Forced
            if (astVarp->isSigPublic()) return true;  // Public
            return false;
        });
        if (hasExternalWriter) return false;

        // Fetch the CFG of the always
        const ControlFlowGraph& cfg = vtx.cfg();

        // If there is a backward edge (loop), we can't synthesize it
        for (const V3GraphVertex& vtx : cfg.vertices()) {
            const BasicBlock& curr = *vtx.as<BasicBlock>();
            bool hasLoop = false;
            curr.forEachSuccessor([&](const BasicBlock& succ) {
                // IDs are the reverse post-order numbering, so easy to check for a back-edge
                if (succ.id() < curr.id()) hasLoop = true;
            });
            if (hasLoop) return false;
        }

        // Maps from BasicBlock to its input and output symbol tables
        BasicBlockMap<SymTab> bb2ISymTab{cfg};
        BasicBlockMap<SymTab> bb2OSymTab{cfg};

        // Initialzie input symbol table of entry block
        vtx.forEachSource([&](DfgVertex& src) {
            DfgVertexVar* const vvp = src.as<DfgVertexVar>();
            Variable* const varp = reinterpret_cast<Variable*>(vvp->nodep());
            bb2ISymTab[cfg.enter()][varp] = vvp;
        });

        // Synthesize all blocks
        for (const V3GraphVertex& cfgVtx : cfg.vertices()) {
            const BasicBlock& bb = *cfgVtx.as<BasicBlock>();
            // Join symbol tables from predecessor blocks
            if (!createInputSymbolTable(bb2ISymTab[bb], bb, bb2OSymTab)) return false;
            // Get the predicate of this block
            DfgVertex* const predp = getBasicBlockPredicate(vtx.fileline(), bb);
            {
                // Use fresh set of vertices in m_converter
                const VNUser2InUse user2InUse;
                // Synthesize the block
                if (!synthesizeBasicBlock(bb2ISymTab[bb], bb2OSymTab[bb], bb)) return false;
                // Set the predicates on the successor edges
                if (!assignSuccessorPredicates(bb, predp)) return false;
            }
        }

        // Relink sinks to read the computed values for the target variables
        vtx.forEachSinkEdge([&](DfgEdge& edge) {
            AstNode* const tgtp = edge.sinkp()->singleSink()->as<DfgVertexVar>()->nodep();
            Variable* const varp = reinterpret_cast<Variable*>(tgtp);
            DfgVertexVar* const resp = bb2OSymTab[cfg.exit()].at(varp);
            edge.relinkSource(resp->srcp());
        });

        return true;
    }

    // Synthesize DfgAlways
    AstToDfgSynthesize(DfgGraph& dfg, V3DfgSynthesisContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx}
        , m_converter{dfg, ctx.m_ast2DfgContext, m_tmpCnt} {}

    static std::unordered_set<const DfgVertex*> gatherSubGraph(  //
        const std::unordered_set<const DfgVertex*>& inputs,  //
        const std::unordered_set<const DfgVertex*>& outputs,  //
        const std::unordered_set<std::pair<const DfgVertex*, const DfgVertex*>>& ignored  //
    ) {
        // Work queue for depth first traversal starting from this vertex
        std::vector<const DfgVertex*> queue;

        // Start from all input vertices
        for (const DfgVertex* const vtxp : inputs) queue.emplace_back(vtxp);

        // Set of already visited vertices
        std::unordered_set<const DfgVertex*> visited;

        // Depth first traversal
        while (!queue.empty()) {
            // Pop next work item
            const DfgVertex* const vtxp = queue.back();
            queue.pop_back();

            // Mark vertex as visited, move on if already visited
            if (!visited.insert(vtxp).second) continue;

            // If we reached an outoput, move on
            if (outputs.count(vtxp)) continue;

            // Enqueue all sinks of this vertex, except those reached via ignored edges
            vtxp->forEachSink([&](const DfgVertex& sink) {
                if (ignored.count({vtxp, &sink})) return;
                queue.push_back(&sink);
            });
        }

        return visited;
    }

public:
    static void synthesize(DfgGraph& dfg, const std::vector<DfgAlways*>& vtxps,
                           V3DfgSynthesisContext& ctx) {
        // Gather the output variables of the always blocks - so we can normalzie them at the end
        std::vector<DfgVertexVar*> oVarps;
        std::unordered_set<const DfgVertex*> oUnique;

        AstToDfgSynthesize instance{dfg, ctx};

        std::unordered_set<const DfgVertex*> outputs;
        std::unordered_set<const DfgVertex*> inputs;
        std::unordered_set<std::pair<const DfgVertex*, const DfgVertex*>> ignored;

        // Attempt to synthesize each always block
        for (DfgAlways* const vtxp : vtxps) {
            // OK
            // static int n = 2;
            // static int n = 3;
            // static int n = 5;
            // static int n = 6;

            // This One
            static int n = 7;

            // BAD
            // static int n = 7;

            if (!n) continue;

            outputs.clear();
            inputs.clear();
            ignored.clear();

            vtxp->forEachSink([&](DfgVertex& sink) {
                UASSERT_OBJ(sink.is<DfgVertexSplice>(), vtxp,
                            "Output of DfgAlways should be a splice");
                // Sink of the splice should be the variable.
                DfgVertexVar* const varp = sink.singleSink()->as<DfgVertexVar>();
                outputs.emplace(varp);
                if (!oUnique.emplace(varp).second) return;
                oVarps.emplace_back(varp);
            });

            vtxp->forEachSource([&](const DfgVertex& source) {  //
                inputs.emplace(&source);
                source.forEachSink([&](const DfgVertex& sink) {
                    if (&sink == vtxp) return;
                    ignored.emplace(&source, &sink);
                });
            });

            const bool dumpThisOne = dumpDfgLevel() >= 9 || n == 1;

            if (dumpThisOne) {
                const auto vtxps = gatherSubGraph(inputs, outputs, ignored);
                dfg.dumpDotFilePrefixed(vtxps, "synthesized-in");
                vtxp->cfg().dumpDotFilePrefixed("synthesized-cfg");
            }

            const bool success = instance.synthesizeAlways(*vtxp);
            if (success) {
                // Delete the always block and vertex, now represented in regular DFG
                vtxp->nodep()->unlinkFrBack()->deleteTree();
                VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
                --n;
                ++ctx.m_nAlwaysSynthesized;
            } else {
                ++ctx.m_nAlwaysSynthFailed;
            }

            if (dumpThisOne) {
                const auto vtxps = gatherSubGraph(inputs, outputs, ignored);
                dfg.dumpDotFilePrefixed(vtxps, success ? "synthesized-ok" : "synthesized-no");
            }
        }
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-synth-conv");

        dfg.dumpDotFilePrefixed(gatherSubGraph(inputs, outputs, ignored), "synthesized-bug-1");

        // Normalize and coalesce all output variable drivers
        for (DfgVertexVar* const varp : oVarps) {
            AstToDfgNormalizeDrivers::apply(dfg, *varp);
            AstToDfgCoalesceDrivers::apply(dfg, *varp, ctx.m_ast2DfgContext);
        }
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-synth-norm");

        dfg.dumpDotFilePrefixed(gatherSubGraph(inputs, outputs, ignored), "synthesized-bug-2");

        // Remove all unused vertices
        // V3DfgPasses::removeUnused(dfg);
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-synth-prun");

        dfg.dumpDotFilePrefixed(gatherSubGraph(inputs, outputs, ignored), "synthesized-bug-3");
    }
};

static void synthesizeDfgAlways(DfgGraph& dfg, const std::vector<DfgAlways*>& vtxps,
                                V3DfgSynthesisContext& ctx) {
    if (vtxps.empty()) return;
    if (dfg.modulep()) {
        AstToDfgSynthesize</* T_Scoped: */ false>::synthesize(dfg, vtxps, ctx);
    } else {
        AstToDfgSynthesize</* T_Scoped: */ true>::synthesize(dfg, vtxps, ctx);
    }
}

void V3DfgPasses::synthesizeAlwaysAll(DfgGraph& dfg, V3DfgContext& ctx) {
    // Gather all vertices
    std::vector<DfgAlways*> alwaysps;
    for (DfgVertex& vtx : dfg.opVertices()) {
        DfgAlways* const alwaysp = vtx.cast<DfgAlways>();
        if (!alwaysp) continue;
        alwaysps.emplace_back(alwaysp);
    }

    // Synthesize them
    synthesizeDfgAlways(dfg, alwaysps, ctx.m_synthesisContext);
}

void V3DfgPasses::synthesizeAlwaysAuto(DfgGraph& dfg, V3DfgContext& ctx) {
    // Gather all DfgAlways that are part of a cycle
    std::vector<DfgAlways*> alwaysps;
    {
        // Find cycles
        const auto userDataInUse = dfg.userDataInUse();
        const uint32_t numNonTrivialSCCs = V3DfgPasses::colorStronglyConnectedComponents(dfg);
        // Nothing to do if no cycles
        if (!numNonTrivialSCCs) return;
        // Collect vertices
        for (DfgVertex& vtx : dfg.opVertices()) {
            // Ignore if not part of cycle
            if (!vtx.getUser<uint32_t>()) continue;
            // Ignore if not an always
            DfgAlways* const alwaysp = vtx.cast<DfgAlways>();
            if (!alwaysp) continue;
            alwaysps.emplace_back(alwaysp);
        }
    }

    // Synthesize them
    synthesizeDfgAlways(dfg, alwaysps, ctx.m_synthesisContext);
}
