// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow based optimization of combinational logic
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Dataflow's Transformations:
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Dataflow.h"
#include "V3Error.h"
#include "V3Global.h"
#include "V3Graph.h"

#include "V3Dfg.h"
#include "V3DfgPasses.h"

#include <vector>

// Visitor to apply prior to DFG optimizer. This does a couple of different things
// - Mark variables referenced via AstVarXRef a such
// - Mark modules not to be optimized as such
// - Extract more combinational logic equations from procedures for better optimization
//   opportunities
class DataflowPrepVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user4    -> Flag indicating driven by AssignW
    const VNUser4InUse m_user4InUse;

    // STATE
    AstNodeModule* const m_modp;  // The module being visited
    bool m_impure = false;  // True if the visited tree has a side effect
    // List of AstVar nodes read by the visited tree. 'vector' rather than 'set' as duplicates are
    // somewhat unlikely and we can handle them later.
    std::vector<const AstVar*> m_readVars;

    // Nodes considered for extraction as separate assignment to gain more opportunities for
    // optimization, together with the set of variable they read. All the candidates are pure
    // expressions.
    std::vector<std::pair<AstNodeMath*, std::vector<const AstVar*>>> m_extractionCandidates;

    // METHODS

    // Node considered for extraction as a combinational equation. Trace variable usage/purity.
    void iterateExtractionCandidate(AstNode* nodep) {
        // Simple VarRefs should not be extracted, as they only yield trivial assignments.
        // We still need to visit them though, to mark hierarchical references.
        if (VN_IS(nodep, NodeVarRef)) {
            iterate(nodep);
            return;
        }

        // Don't extract plain constants
        if (VN_IS(nodep, Const)) return;

        m_impure = false;
        m_readVars.clear();

        // Trace variable usage
        iterateChildrenConst(nodep);

        // We are only interested in pure expressions
        if (m_impure) return;

        // Don't extract constant expressions
        if (m_readVars.empty()) return;

        // Add to candidate list
        m_extractionCandidates.emplace_back(VN_AS(nodep, NodeMath), std::move(m_readVars));
    }

    // VISIT methods

    void visit(AstNodeModule* modp) override {
        // Analyse whole module
        iterateChildrenConst(modp);
        // Replace expressions only reading combinationally driven signals with variables
        size_t ord = 0;
        for (const auto& pair : m_extractionCandidates) {
            AstNodeMath* const nodep = pair.first;
            bool allReadVarsCombinationallyDriven = true;
            for (const AstVar* const readVarp : pair.second) {
                if (!readVarp->user4()) {
                    allReadVarsCombinationallyDriven = false;
                    break;
                }
            }
            if (!allReadVarsCombinationallyDriven) continue;

            // Create temporary variable
            string name{"_VdfgExtractedTmp__"};
            name += cvtToStr(++ord);
            AstVar* const varp
                = new AstVar{nodep->fileline(), VVarType::MODULETEMP, name, nodep->dtypep()};
            m_modp->addStmtp(varp);

            // Replace expression with temporary variable
            nodep->replaceWith(new AstVarRef{nodep->fileline(), varp, VAccess::READ});

            // Create assignment driving temporary variable
            AstAssignW* const assignp = new AstAssignW{
                nodep->fileline(), new AstVarRef{nodep->fileline(), varp, VAccess::WRITE}, nodep};
            m_modp->addStmtp(assignp);
        }
    }

    void visit(AstAssignW* nodep) override {
        // Mark LHS variable as combinationally driven
        if (AstVarRef* const vrefp = VN_CAST(nodep->lhsp(), VarRef)) { vrefp->varp()->user4(1); }
        //
        iterateChildrenConst(nodep);
    }

    void visit(AstAssign* nodep) override {
        iterateChildrenConst(nodep->lhsp());
        iterateExtractionCandidate(nodep->rhsp());
    }
    
    void visit(AstAssignDly* nodep) override {
        iterateChildrenConst(nodep->lhsp());
        iterateExtractionCandidate(nodep->rhsp());
    }

    void visit(AstIf* nodep) override {
        iterateExtractionCandidate(nodep->condp());
        iterateAndNextConstNull(nodep->ifsp());
        iterateAndNextConstNull(nodep->elsesp());
    }

    void visit(AstNode* nodep) override {
        // Conservatively assume unhandled nodes are impure. This covers all AstNodeFTaskRef
        // as AstNodeFTaskRef are sadly not AstNodeMath.
        m_impure = true;
        //
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeMath* nodep) override { iterateChildrenConst(nodep); }

    void visit(AstNodeVarRef* nodep) override {
        // Mark variable reverenced via hierarchical reference as such
        if (VN_IS(nodep, VarXRef)) { nodep->varp()->user2(1); }

        if (nodep->access().isWriteOrRW()) {
            // If it writes a variable, mark as impure
            m_impure = true;
        } else {
            // Otherwise, add read reference
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "What else could it be?");
            m_readVars.push_back(nodep->varp());
        }
    }

    void visit(AstPragma* nodep) override {
        // Disable DFG optimizer for module
        if (nodep->pragType() == VPragmaType::NO_DFG) m_modp->user2(1);
    }

    // CONSTRUCTOR
    explicit DataflowPrepVisitor(AstNodeModule* modp)
        : m_modp{modp} {
        iterate(modp);
    }

public:
    static void apply(AstNodeModule* modp) { DataflowPrepVisitor{modp}; }
};

void V3Dataflow::all(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    // NODE STATE
    // AstVar::user1        -> Used by V3DfgPasses::astToDfg
    // AstVar::user2        -> Flag indicating referenced by AstVarXRef
    // AstNodeModule::user2 -> Flag indicating DFG optimizer disabled for this module
    const VNUser2InUse m_user2InUse;

    // Run the prep phase
    for (AstNodeModule* nodep = netlistp->modulesp(); nodep;
         nodep = VN_AS(nodep->nextp(), NodeModule)) {
        DataflowPrepVisitor::apply(nodep);
    }

    V3Global::dumpCheckGlobalTree("dataflow-pre", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);

    V3DfgOptimizationContext ctx;

    // Run the optimization phase
    for (AstNode* nodep = netlistp->modulesp(); nodep; nodep = nodep->nextp()) {
        // TODO: all but astToDfg can be run in parallel, but need atomic stats
        //      (astToDfg uses AstNode::user* which are not thread safe)
        AstModule* const modp = VN_CAST(nodep, Module);
        if (!modp) continue;

        // Skip modules specified by the user
        if (modp->user2()) {
            UINFO(3, "Skipping DFG optimization of module '"
                         << modp->name() << "' due to \"no_dfg\" directive" << endl);
            continue;
        }

        UINFO(3, "Applying DFG optimization to module'" << modp->name() << "'" << endl);

        // Build the DFG of this module
        const std::unique_ptr<DfgGraph> dfg{V3DfgPasses::astToDfg(*modp)};
        if (v3Global.opt.dumpDfg() >= 6) { dfg->dumpDotFilePrefixed(dfg->name()); }

        // Split the DFG into independent components
        const std::vector<std::unique_ptr<DfgGraph>>& components = dfg->splitIntoComponents();

        UINFO(3, "Number of DFG components in '" << modp->name() << "':"  //
                                                 << components.size() << endl);

        // For each component
        for (auto& component : components) {
            if (v3Global.opt.dumpDfg() >= 1) { component->dumpDotFilePrefixed(component->name()); }

            // If a DFG only contains DfgVar and DfgConst nodes, then there is not much we can
            // do about it (could still eliminate redundant nets, but we will do that in V3Gate
            // anyway, so we won't bother here). // TODO: actually do it here to save memory
            const bool isTrivial = !component->findVertex<DfgVertex>(
                [](const DfgVertex& vtx) { return !vtx.is<DfgVar>() && !vtx.is<DfgConst>(); });

            // Optimize non-trivial graphs
            if (!isTrivial) {
                V3DfgPasses::optimize(*component, ctx);

                if (v3Global.opt.dumpDfg() >= 1) {
                    component->dumpDotFilePrefixed(component->name() + "-optimized");
                }

                if (v3Global.opt.dumpDfg() >= 3) {
                    component->dumpDotAllVarConesPrefixed(component->name() + "-optimized");
                }
            }

            // Convert back to Ast
            AstModule* const resultModp = V3DfgPasses::dfgToAst(*component);
            UASSERT_OBJ(resultModp == modp, modp, "Should be the same module");
        }
    }
    V3Global::dumpCheckGlobalTree("dataflow", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
