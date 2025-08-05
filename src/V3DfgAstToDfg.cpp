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
                    vtxp->srcp(new DfgSplicePacked{m_dfg, flp, dtypep});
                } else if (vtxp->is<DfgVarArray>()) {
                    vtxp->srcp(new DfgSpliceArray{m_dfg, flp, dtypep});
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
                    splicep->addDriver(flp, index, new DfgSplicePacked{m_dfg, flp, dtypep});
                } else if (VN_IS(dtypep, UnpackArrayDType)) {
                    splicep->addDriver(flp, index, new DfgSpliceArray{m_dfg, flp, dtypep});
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
        if (!convertAllLValues(lhsp, vtxp)) return false;

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
        return convertRValue(nodep);
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

// Driver normalization removes unnecessary splice vertices,
// and resolves multiple drivers (keep only one).
class AstToDfgNormalizeDrivers final {
    // STATE
    DfgGraph& m_dfg;  // The graph being processed
    DfgVertexVar& m_var;  // The variable being normalzied
    V3DfgAstToDfgContext& m_ctx;  // The context for stats

    // METHODS

    // Normalize packed driver - return the normalized vertex and location for 'splicep'
    std::pair<DfgVertex*, FileLine*>  //
    normalizePacked(const std::string& sub, DfgSplicePacked* const splicep) {
        // Represents a driver of 'splicep'
        struct Driver final {
            FileLine* m_fileline;
            DfgVertex* m_vtxp;
            uint32_t m_lsb;
            Driver() = delete;
            Driver(FileLine* flp, uint32_t lsb, DfgVertex* vtxp)
                : m_fileline{flp}
                , m_vtxp{vtxp}
                , m_lsb{lsb} {}
        };

        // The drivers of 'splicep'
        std::vector<Driver> drivers;
        drivers.reserve(splicep->arity());
        std::vector<DfgAlways*> alwaysDriverps;
        alwaysDriverps.reserve(splicep->arity());

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
                concatp->unlinkDelete(m_dfg);
            } else {
                drivers.emplace_back(flp, lsb, vtxp);
            }
        };

        // Gather and unlink drivers
        splicep->forEachSourceEdge([&](DfgEdge& edgeA, size_t iA) {
            DfgVertex* const driverAp = edgeA.sourcep();
            UASSERT_OBJ(driverAp, splicep, "Should not have created undriven sources");
            UASSERT_OBJ(!splicep->driverIsDefault(iA), splicep, "Should not be default");

            if (!splicep->driverIsUnresolved(iA)) {
                // Resolved driver
                UASSERT_OBJ(!driverAp->is<DfgSplicePacked>(), splicep,
                            "Should not be SplicePacked");
                gather(splicep->driverFileLine(iA), splicep->driverLsb(iA), driverAp);
            } else if (DfgAlways* const alwaysp = driverAp->cast<DfgAlways>()) {
                // Still unresolved (Other DfgAlways driving same variable)
                alwaysDriverps.emplace_back(alwaysp);
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
                    UASSERT_OBJ(!driverBp->is<DfgSplicePacked>(), spliceBp,
                                "Should not be SplicePacked");
                    gather(spliceBp->driverFileLine(iB), spliceBp->driverLsb(iB), driverBp);
                });
            }

            // Unlink
            edgeA.unlinkSource();
        });

        const auto cmp = [](const Driver& a, const Driver& b) {
            if (a.m_lsb != b.m_lsb) return a.m_lsb < b.m_lsb;
            return a.m_fileline->operatorCompare(*b.m_fileline) < 0;
        };

        // Sort drivers by LSB
        std::stable_sort(drivers.begin(), drivers.end(), cmp);

        // Fix multiply driven ranges
        for (auto it = drivers.begin(); it != drivers.end();) {
            Driver& a = *it++;
            const uint32_t aWidth = a.m_vtxp->width();
            const uint32_t aEnd = a.m_lsb + aWidth;
            while (it != drivers.end()) {
                Driver& b = *it;
                // If no overlap, then nothing to do
                if (b.m_lsb >= aEnd) break;

                const uint32_t bWidth = b.m_vtxp->width();
                const uint32_t bEnd = b.m_lsb + bWidth;
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
                            << overlapEnd << ":" << b.m_lsb << "] of signal '"
                            << nodep->prettyName() << sub
                            << "' have multiple combinational drivers\n"
                            << a.m_fileline->warnOther() << "... Location of first driver\n"
                            << a.m_fileline->warnContextPrimary() << '\n'
                            << b.m_fileline->warnOther() << "... Location of other driver\n"
                            << b.m_fileline->warnContextSecondary() << nodep->warnOther()
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
                    selp->lsb(aEnd - b.m_lsb);
                    b.m_lsb = aEnd;
                    b.m_vtxp = selp;
                    std::stable_sort(it, drivers.end(), cmp);
                }
            }
        }

        // Coalesce adjacent ranges
        for (size_t i = 0, j = 1; j < drivers.size(); ++j) {
            Driver& a = drivers[i];
            Driver& b = drivers[j];

            // Coalesce adjacent range
            const uint32_t aWidth = a.m_vtxp->width();
            const uint32_t bWidth = b.m_vtxp->width();
            if (a.m_lsb + aWidth == b.m_lsb) {
                const auto dtypep = DfgVertex::dtypeForWidth(aWidth + bWidth);
                DfgConcat* const concatp = new DfgConcat{m_dfg, a.m_fileline, dtypep};
                concatp->rhsp(a.m_vtxp);
                concatp->lhsp(b.m_vtxp);
                a.m_vtxp = concatp;
                b.m_vtxp = nullptr;  // Mark as moved
                ++m_ctx.m_coalescedAssignments;
                continue;
            }

            ++i;

            // Compact non-adjacent ranges within the vector
            if (j != i) {
                Driver& c = drivers[i];
                UASSERT_OBJ(!c.m_vtxp, c.m_fileline, "Should have been marked moved");
                c = b;
                b.m_vtxp = nullptr;  // Mark as moved
            }
        }

        // Reinsert drivers in order
        splicep->resetSources();
        for (const Driver& driver : drivers) {
            if (!driver.m_vtxp) break;  // Stop at end of compacted list
            splicep->addDriver(driver.m_fileline, driver.m_lsb, driver.m_vtxp);
        }
        for (DfgAlways* const alwaysp : alwaysDriverps) splicep->addUnresolvedDriver(alwaysp);

        // If the whole variable is driven whole, we can just use that driver
        if (splicep->drivesWholeResult()) {
            const auto result = std::make_pair(splicep->source(0), splicep->driverFileLine(0));
            VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
            return result;
        }
        return {splicep, splicep->fileline()};
    }

    // Normalize array driver - return the normalized vertex and location for 'splicep'
    std::pair<DfgVertex*, FileLine*>  //
    normalizeArray(const std::string& sub, DfgSpliceArray* const splicep) {
        // Represents a driver of 'splicep'
        struct Driver final {
            FileLine* m_fileline;
            DfgVertex* m_vtxp;
            uint32_t m_idx;
            Driver() = delete;
            Driver(FileLine* flp, uint32_t idx, DfgVertex* vtxp)
                : m_fileline{flp}
                , m_vtxp{vtxp}
                , m_idx{idx} {}
        };

        // The drivers of 'splicep'
        std::vector<Driver> drivers;
        drivers.reserve(splicep->arity());

        // Normalize, gather, and unlink all drivers
        splicep->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
            DfgVertex* const driverp = edge.sourcep();
            UASSERT(driverp, "Should not have created undriven sources");
            const uint32_t idx = splicep->driverIndex(i);
            if (DfgSplicePacked* const spp = driverp->cast<DfgSplicePacked>()) {
                const auto pair = normalizePacked(sub + "[" + std::to_string(idx) + "]", spp);
                drivers.emplace_back(pair.second, idx, pair.first);
            } else if (DfgSpliceArray* const sap = driverp->cast<DfgSpliceArray>()) {
                const auto pair = normalizeArray(sub + "[" + std::to_string(idx) + "]", sap);
                drivers.emplace_back(pair.second, idx, pair.first);
            } else if (driverp->is<DfgVertexSplice>()) {
                driverp->v3fatalSrc("Unhandled DfgVertexSplice sub-type");
            } else {
                drivers.emplace_back(splicep->driverFileLine(i), idx, driverp);
            }
            edge.unlinkSource();
        });

        const auto cmp = [](const Driver& a, const Driver& b) {
            if (a.m_idx != b.m_idx) return a.m_idx < b.m_idx;
            return a.m_fileline->operatorCompare(*b.m_fileline) < 0;
        };

        // Sort drivers by index
        std::stable_sort(drivers.begin(), drivers.end(), cmp);

        // Fix multiply driven ranges
        for (auto it = drivers.begin(); it != drivers.end();) {
            Driver& a = *it++;
            AstUnpackArrayDType* aArrayDTypep = VN_CAST(a.m_vtxp->dtypep(), UnpackArrayDType);
            const uint32_t aElements = aArrayDTypep ? aArrayDTypep->elementsConst() : 1;
            const uint32_t aEnd = a.m_idx + aElements;
            while (it != drivers.end()) {
                Driver& b = *it;
                // If no overlap, then nothing to do
                if (b.m_idx >= aEnd) break;

                AstUnpackArrayDType* bArrayDTypep = VN_CAST(b.m_vtxp->dtypep(), UnpackArrayDType);
                const uint32_t bElements = bArrayDTypep ? bArrayDTypep->elementsConst() : 1;
                const uint32_t bEnd = b.m_idx + bElements;
                const uint32_t overlapEnd = std::min(aEnd, bEnd) - 1;

                // The AstVar/AstVarScope to report errors against
                AstNode* const nodep = m_var.tmpForp() ? m_var.tmpForp() : m_var.nodep();
                nodep->v3warn(  //
                    MULTIDRIVEN,
                    "Elements ["  //
                        << overlapEnd << ":" << b.m_idx << "] of signal '" << nodep->prettyName()
                        << sub << "' have multiple combinational drivers\n"
                        << a.m_fileline->warnOther() << "... Location of first driver\n"
                        << a.m_fileline->warnContextPrimary() << '\n'
                        << b.m_fileline->warnOther() << "... Location of other driver\n"
                        << b.m_fileline->warnContextSecondary() << nodep->warnOther()
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
        splicep->resetSources();
        for (const Driver& driver : drivers) {
            if (!driver.m_vtxp) break;  // Stop at end of compacted list
            splicep->addDriver(driver.m_fileline, driver.m_idx, driver.m_vtxp);
        }

        // If the whole variable is driven whole, we can just use that driver
        if (splicep->arity() == 1  //
            && splicep->driverIndex(0) == 0  //
            && splicep->source(0)->dtypep()->isSame(splicep->dtypep())) {
            const auto result = std::make_pair(splicep->source(0), splicep->driverFileLine(0));
            VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
            return result;
        }
        return {splicep, splicep->fileline()};
    }

    // CONSTRUCTOR
    AstToDfgNormalizeDrivers(DfgGraph& dfg, DfgVertexVar& var, V3DfgAstToDfgContext& ctx)
        : m_dfg{dfg}
        , m_var{var}
        , m_ctx{ctx} {
        // Nothing to do for un-driven (input) variables
        if (!var.srcp()) return;

        // If the driver of the variable is not a splice, it is already normalized
        DfgVertexSplice* const srcp = var.srcp()->cast<DfgVertexSplice>();
        if (!srcp) return;

        std::pair<DfgVertex*, FileLine*> normalizedDriver;
        if (DfgSpliceArray* const sArrayp = srcp->cast<DfgSpliceArray>()) {
            normalizedDriver = normalizeArray("", sArrayp);
        } else if (DfgSplicePacked* const sPackedp = srcp->cast<DfgSplicePacked>()) {
            normalizedDriver = normalizePacked("", sPackedp);
        } else {
            var.v3fatalSrc("Unhandled DfgVertexSplice sub-type");  // LCOV_EXCL_LINE
        }
        var.srcp(normalizedDriver.first);
        var.driverFileLine(normalizedDriver.second);
    }

public:
    static void apply(DfgGraph& dfg, DfgVertexVar& var, V3DfgAstToDfgContext& ctx) {
        AstToDfgNormalizeDrivers{dfg, var, ctx};
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
        // Normalize all variable drivers
        for (DfgVertexVar& var : dfg.varVertices()) AstToDfgNormalizeDrivers::apply(dfg, var, ctx);
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
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;
    using SymTab = std::unordered_map<Variable*, DfgVertexVar*>;

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

    void incorporatePreviousDriver(DfgVertexVar* newp, DfgVertexVar* oldp, Variable* varp) {
        DfgSplicePacked* const newSplicep = newp->srcp()->cast<DfgSplicePacked>();
        // If the new driver is not a splice, the variable is fully driven, nothing to do
        if (!newSplicep) return;

        // If the old value is the real variable we just computed the new value for,
        // then it is the circular feedback into the synthesized block, add it as default driver.
        if (oldp->nodep() == varp) {
            // If the new value is fully defined, we should have noticed during live variabel
            // analysis and not include 'oldp' as input to the synthesized block.
            UASSERT_OBJ(!newSplicep->drivesWholeResult(), newp, "Live variable analysis failed");
            newSplicep->addDefaultDriver(oldp->fileline(), oldp);
            return;
        }

        // TODO: Coalesce drivers ...

        // Represents a range driven in the new value
        struct Range final {
            uint32_t m_msb;
            uint32_t m_lsb;
            Range() = delete;
            Range(uint32_t msb, uint32_t lsb)
                : m_msb{msb}
                , m_lsb{lsb} {}
        };

        // Gather all driven ranges - note we have run AstToDfgNormalizeDrivers
        // on 'newp' before, so there are no overlapping (multi-driven) ranges
        std::vector<Range> driven;
        newSplicep->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
            DfgVertex* const driverp = edge.sourcep();
            UASSERT_OBJ(driverp, newSplicep, "Should not have created undriven sources");
            UASSERT_OBJ(!newSplicep->driverIsUnresolved(i), newSplicep,
                        "Should not be unresolved");
            UASSERT_OBJ(!newSplicep->driverIsDefault(i), newSplicep, "Should not be default");
            const uint32_t lsb = newSplicep->driverLsb(i);
            const uint32_t msb = lsb + driverp->width() - 1;
            driven.emplace_back(msb, lsb);
        });
        UASSERT_OBJ(!driven.empty(), newp, "Should have at least one driver");

        // Sort the driven ranges
        std::stable_sort(driven.begin(), driven.end(), [](const Range& a, const Range& b) {
            if (a.m_lsb != b.m_lsb) return a.m_lsb < b.m_lsb;
            return a.m_msb < b.m_msb;
        });

        // Add bits between 'msb' and 'lsb' from 'oldp' as a driver of 'newp'
        const auto addOldDriver = [&](FileLine* const flp, uint32_t msb, uint32_t lsb) {
            DfgSel* const selp = new DfgSel{m_dfg, flp, DfgVertex::dtypeForWidth(msb - lsb + 1)};
            selp->lsb(lsb);
            selp->fromp(oldp);
            newSplicep->addDriver(flp, lsb, selp);
        };

        // Insert bits betwen 'msb' and 'lsb' from 'oldp' that do not overlap a
        // new driver of 'newp' as additional drivers into 'newp'
        const auto mergeOldDriver = [&](FileLine* flp, uint32_t msb, uint32_t lsb) -> void {
            auto it = driven.begin();
            // drivenRanges most often only have one element, so loop is fine
            while (msb >= lsb) {
                // Insert remaining bits if no more new drivers or they are above old range
                if (it == driven.end() || it->m_lsb > msb) {
                    addOldDriver(flp, msb, lsb);
                    break;
                }
                const Range& range = *it;
                // If the old driver is below the new one, move on to the next new driver
                if (lsb > range.m_msb) {
                    ++it;
                    continue;
                }
                // Old driver overlaps with new driver. Insert only the bits not written by new.
                if (range.m_lsb > lsb) addOldDriver(flp, std::min(msb, range.m_lsb - 1), lsb);
                // Need to insert remaining bits starting above new driver
                lsb = range.m_msb + 1;
                // Old range is now below new one, so move on to the next new driver
                ++it;
            }
        };

        if (DfgSplicePacked* const oldSplicep = oldp->srcp()->cast<DfgSplicePacked>()) {
            // Old value is partial via a splice, insert each driven range
            // separately. Also propagate the default if present.
            DfgVertex* defaultp = nullptr;
            oldSplicep->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
                DfgVertex* const driverp = edge.sourcep();
                UASSERT_OBJ(driverp, oldSplicep, "Should not have created undriven sources");
                UASSERT_OBJ(!oldSplicep->driverIsUnresolved(i), oldSplicep,
                            "Should not be unresolved");
                if (oldSplicep->driverIsDefault(i)) {
                    UASSERT_OBJ(!defaultp, driverp, "Multiple default drivers");
                    defaultp = driverp;
                    return;
                }

                FileLine* const flp = oldSplicep->driverFileLine(i);
                const uint32_t lsb = oldSplicep->driverLsb(i);
                const uint32_t msb = lsb + driverp->width() - 1;
                mergeOldDriver(flp, msb, lsb);
            });
            if (defaultp) newSplicep->addDefaultDriver(defaultp->fileline(), defaultp);
        } else {
            // Old value is wholly defined, so process it as a whole
            mergeOldDriver(oldp->driverFileLine(), oldp->width() - 1, 0);
        }
    }

    bool synthesizeBasicBlock(const SymTab& iSymTab, SymTab& oSymTab, const BasicBlock& bb) {
        // Initialize Variable -> Vertex bindings available in this block
        // UINFO(0, "synthesizeBasicBlock " << bb.id());
        for (const auto& pair : iSymTab) {
            Variable* const varp = pair.first;
            DfgVertexVar* const vtxp = pair.second;
            // UINFO(0, varp->name() << " -> " << vtxp);
            varp->user2p(vtxp);
            oSymTab[varp] = vtxp;
        }

        // Synthesize each statement individually
        std::unordered_map<Variable*, DfgVertexVar*> updates;
        for (AstNode* stmtp : bb.stmtps()) {
            // Regular statements
            if (AstAssign* const ap = VN_CAST(stmtp, Assign)) {
                if (!m_converter.convert(ap, updates)) return false;
                // m_dfg.dumpDotFilePrefixed("xxx");
                // Apply variable updates from this statement
                for (const auto& pair : updates) {
                    // The target variable that was assigned to
                    Variable* const varp = pair.first;
                    // The new, potentially partially assigned value
                    DfgVertexVar* const newVtxp = pair.second;
                    // Resolve multi-drivers of this variable withih this 'ap' assignment
                    AstToDfgNormalizeDrivers::apply(m_dfg, *newVtxp, m_ctx.m_ast2DfgContext);
                    // The previous value of the same variable
                    DfgVertexVar* const oldVtxp = varp->user2u().template to<DfgVertexVar*>();
                    // Incorporate old value into the new value
                    if (oldVtxp) incorporatePreviousDriver(newVtxp, oldVtxp, varp);
                    // Update binding of target variable
                    varp->user2p(newVtxp);
                    // Update output symbol table of this block
                    oSymTab[varp] = newVtxp;
                }
                // m_dfg.dumpDotFilePrefixed("zzz");
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
        DfgVertex* const resp = reinterpret_cast<DfgVertex*>((*it).userp());
        while (++it != inEdges.end()) {
            DfgOr* const orp = new DfgOr{m_dfg, flp, resp->dtypep()};
            orp->rhsp(resp);
            orp->lhsp(reinterpret_cast<DfgVertex*>((*it).userp()));
        }
        return resp;
    }

    // Given a basic block, and it's predicate, assign perdicates to its outgoing edges
    bool assignSuccessorPredicates(const BasicBlock& bb, DfgVertex* predp) {
        // The predicate of the block should be set
        UASSERT_OBJ(predp, predp, "Missing BasicBlock predicate");
        // There should be at most 2 successors
        UASSERT_OBJ(bb.outEdges().size() <= 2, predp, "More than 2 successor for BasicBlock");
        // Get the predicate if the terminator statement is a "taken branch" (or implicit "goto")
        DfgVertex* const takenPredp = [&]() -> DfgVertex* {
            // Empty block -> implicit goto
            if (bb.stmtps().empty()) return predp;
            // Last statement in block
            AstNode* const stmtp = bb.stmtps().back();
            // Regular statements -> implicit goto
            if (!stmtp) return predp;
            if (VN_IS(stmtp, Assign)) return predp;
            // Branches
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                // Convet condition
                DfgVertex* const condp = m_converter.convert(ifp->condp());
                if (!condp) return nullptr;
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
                // New predicate is 'predp & truthyp'
                DfgAnd* const andp = new DfgAnd{m_dfg, flp, bitDTypep};
                andp->lhsp(predp);
                andp->rhsp(truthyp);
                return andp;
            }
            // Unhandled
            return nullptr;
        }();
        if (!takenPredp) return false;
        // Assign predicates to successor edges
        for (const V3GraphEdge& edge : bb.outEdges()) {
            const ControlFlowGraphEdge& cfgEdge = *edge.as<ControlFlowGraphEdge>();
            DfgVertex* edgePredp = takenPredp;
            // If it's a not taken edge, invert the predicate
            if (cfgEdge.kind() == ControlFlowGraphEdge::Kind::ConditionFalse) {
                DfgNot* const notp = new DfgNot{m_dfg, edgePredp->fileline(), edgePredp->dtypep()};
                notp->srcp(edgePredp);
                edgePredp = notp;
            }
            // Set user pointer of edge
            const_cast<ControlFlowGraphEdge&>(cfgEdge).userp(edgePredp);
        }
        // Done
        return true;
    }

    DfgVertexVar* joinDrivers(Variable* varp, DfgVertex* predicatep, DfgVertexVar* thenp,
                              DfgVertexVar* elsep) {
        UASSERT_OBJ(!predicatep->is<DfgConst>(), predicatep, "joinDrivers with cons predicate");

        // UINFO(0, "joinDrivers " << varp->name() << " " << predicatep << " ? " << thenp << " : "
        // << elsep);

        // If both bindings are the the same, then no need to resolve them
        if (thenp == elsep) return thenp;

        DfgSplicePacked* const thenSplicep = thenp->srcp()->as<DfgSplicePacked>();
        DfgSplicePacked* const elseSplicep = elsep->srcp()->as<DfgSplicePacked>();

        // If both paths are fully driven, just create a conditionsl
        if (thenSplicep->drivesWholeResult() && elseSplicep->drivesWholeResult()) {
            AstNodeDType* const dtypep = DfgVertex::dtypeFor(getAstVar(varp));
            FileLine* const flp = predicatep->fileline();

            DfgCond* const condp = new DfgCond{m_dfg, flp, dtypep};
            condp->condp(predicatep);
            condp->thenp(thenp);
            condp->elsep(elsep);

            DfgSplicePacked* const splicep = new DfgSplicePacked{m_dfg, flp, dtypep};
            splicep->addDriver(thenp->fileline(), 0, condp);

            DfgVertexVar* const tmpp = createTmp(m_dfg, varp, "SynthJoin", m_tmpCnt++);
            tmpp->srcp(splicep);
            return tmpp;
        }

        return nullptr;
        // struct Range final {
        //     uint32_t m_msb;
        //     uint32_t m_lsb;
        //     Range() = delete;
        //     Range(uint32_t msb, uint32_t lsb)
        //         : m_msb{msb}
        //         , m_lsb{lsb} {}
        // };

        // // TODO: resolve multi-driven ranges
        // std::vector<Range> driven;
        // newSplicep->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
        //     DfgVertex* const driverp = edge.sourcep();
        //     UASSERT_OBJ(driverp, newSplicep, "Should not have created undriven sources");
        //     UASSERT_OBJ(!newSplicep->driverIsUnresolved(i), newSplicep,
        //                 "Should not be unresolved");
        //     UASSERT_OBJ(!newSplicep->driverIsDefault(i), newSplicep, "Should not be default");
        //     const uint32_t lsb = newSplicep->driverLsb(i);
        //     const uint32_t msb = lsb + driverp->width() - 1;
        //     driven.emplace_back(msb, lsb);
        // });
    }

    bool createInputSymbolTable(SymTab& joined, const BasicBlock& bb,
                                const BasicBlockMap<SymTab>& bb2OSymTab) {
        // Input symbol table of entry block was previously initialzied
        if (bb.inEmpty()) return true;
        UASSERT(joined.empty(), "Unresolved input symbol table should be empty");

        // If there is only one predecessor, just copy
        if (bb.inSize1()) {
            joined = bb2OSymTab[*(bb.inEdges().frontp()->fromp()->as<BasicBlock>())];
            return true;
        }

        // Gather predecessors and the path predicates
        using Predessor = std::pair<const BasicBlock*, DfgVertex*>;
        std::vector<Predessor> predecessors;
        for (const V3GraphEdge& edge : bb.inEdges()) {
            DfgVertex* const predicatep = reinterpret_cast<DfgVertex*>(edge.userp());
            const BasicBlock* const predecessorp = edge.fromp()->as<BasicBlock>();
            predecessors.emplace_back(predecessorp, predicatep);
        }
        // Sort predecessors topologically. This way more specifics will
        // come after less specifics, and the entry block will be first if present.
        std::sort(
            predecessors.begin(), predecessors.end(),
            [](const Predessor& a, const Predessor& b) { return a.first->id() < b.first->id(); });

        joined = bb2OSymTab[*predecessors[0].first];
        for (size_t i = 1; i < predecessors.size(); ++i) {
            DfgVertex* const predicatep = predecessors[i].second;
            const SymTab& oSymTab = bb2OSymTab[*predecessors[i].first];
            // Give up if something is not assigned on all paths ... Latch?
            if (joined.size() != oSymTab.size()) return false;
            // Join each symbol
            for (auto& pair : joined) {
                Variable* const varp = pair.first;
                // Find same variable on other path
                auto it = oSymTab.find(varp);
                // Give up if something is not assigned on all paths ... Latch?
                if (it == oSymTab.end()) return false;
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
            if (varp->nodep()->user2()) return true;  // Target of a hierarchical reference
            AstVar* const astVarp = varp->varp();
            if (astVarp->isForced()) return true;  // Forced
            if (astVarp->isSigPublic()) return true;  // Forced
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

        // Maps from basic block to its input and symbol tables
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

        // m_dfg.dumpDotFilePrefixed("eee");

        // Relink sinks to read the computed values for the target variable
        vtx.forEachSinkEdge([&](DfgEdge& edge) {
            AstNode* const tgtp = edge.sinkp()->singleSink()->as<DfgVertexVar>()->nodep();
            Variable* const varp = reinterpret_cast<Variable*>(tgtp);
            DfgVertexVar* const resp = bb2OSymTab[cfg.exit()].at(varp);
            edge.relinkSource(resp->srcp());
            if (resp->hasSinks()) {
                resp->replaceWith(edge.sinkp()->singleSink()->as<DfgVertexVar>());
            }
        });

        // m_dfg.dumpDotFilePrefixed("fff");

        // Remove unused temporaries
        for (const auto& pair : bb2OSymTab[cfg.exit()]) {
            DfgVertexVar* tmpp = pair.second;
            if (tmpp->hasSinks()) continue;
            VL_DO_DANGLING(tmpp->unlinkDelete(m_dfg), tmpp);
        }

        return true;
    }

    // Synthesize DfgAlways
    AstToDfgSynthesize(DfgGraph& dfg, V3DfgSynthesisContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx}
        , m_converter{dfg, ctx.m_ast2DfgContext, m_tmpCnt} {}

public:
    static void synthesize(DfgGraph& dfg, const std::vector<DfgAlways*>& vtxps,
                           V3DfgSynthesisContext& ctx) {
        // Gather the output variables of the always blocks - so we can normalzie them at the end
        std::vector<DfgVertexVar*> varps;
        for (DfgAlways* const vtxp : vtxps) {
            vtxp->forEachSink([&](DfgVertex& sink) {
                UASSERT_OBJ(sink.is<DfgVertexSplice>(), vtxp,
                            "Output of DfgAlways should be a splice");
                // Sink of the splice should be the variable.
                varps.emplace_back(sink.singleSink()->as<DfgVertexVar>());
            });
        }

        // Attempt to synthesize each always block
        AstToDfgSynthesize instance{dfg, ctx};
        for (DfgAlways* const vtxp : vtxps) {
            if (instance.synthesizeAlways(*vtxp)) {
                // Delete the always block and vertex, now represented in regular DFG
                vtxp->nodep()->unlinkFrBack()->deleteTree();
                VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
                ++ctx.m_nAlwaysSynthesized;
                continue;
            }
            ++ctx.m_nAlwaysSynthFailed;
        }
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-synth-conv");

        // Normalize all output variable drivers
        for (DfgVertexVar* const varp : varps) {
            AstToDfgNormalizeDrivers::apply(dfg, *varp, ctx.m_ast2DfgContext);
        }
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-synth-norm");

        // Remove all unused vertices
        V3DfgPasses::removeUnused(dfg);
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "ast2dfg-synth-prun");
    }
};

void V3DfgPasses::synthesize(DfgGraph& dfg, const std::vector<DfgAlways*>& vtxps,
                             V3DfgSynthesisContext& ctx) {
    if (vtxps.empty()) return;
    if (dfg.modulep()) {
        AstToDfgSynthesize</* T_Scoped: */ false>::synthesize(dfg, vtxps, ctx);
    } else {
        AstToDfgSynthesize</* T_Scoped: */ true>::synthesize(dfg, vtxps, ctx);
    }
}

void V3DfgPasses::synthesizeAllAlways(DfgGraph& dfg, V3DfgContext& ctx) {
    // Gather all vertices
    std::vector<DfgAlways*> alwaysps;
    for (DfgVertex& vtx : dfg.opVertices()) {
        DfgAlways* const alwaysp = vtx.cast<DfgAlways>();
        if (!alwaysp) continue;
        alwaysps.emplace_back(alwaysp);
    }

    // Synthesize them
    V3DfgPasses::synthesize(dfg, alwaysps, ctx.m_synthesisContext);
}

void V3DfgPasses::synthesizeCyclicAlways(DfgGraph& dfg, V3DfgContext& ctx) {
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
    V3DfgPasses::synthesize(dfg, alwaysps, ctx.m_synthesisContext);
}
