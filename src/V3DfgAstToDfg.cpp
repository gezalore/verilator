// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert AstModule to DfgGraph
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
#include "V3Error.h"
#include "V3Global.h"

#include "V3Dfg.h"
#include "V3DfgPasses.h"

namespace {

// Create a DfgVertex out of a AstNodeMath. For most AstNodeMath subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename Vertex, typename Node>  //
Vertex* makeVertex(const Node* nodep, DfgGraph& dfg) {
    static_assert(std::is_base_of<DfgVertex, Vertex>::value,
                  "'Vertex' must be subclass of 'DfgVertex'");
    static_assert(std::is_base_of<AstNodeMath, Node>::value,
                  "'Node' must be subclass of 'AstNodeMath'");
    return new Vertex{dfg, nodep->fileline(), static_cast<uint32_t>(nodep->width())};
}

// Currently unhandled nodes
template <>  //
DfgAtoN* makeVertex<DfgAtoN, AstAtoN>(const AstAtoN*, DfgGraph&) {
    return nullptr;
}

template <>  //
DfgCCast* makeVertex<DfgCCast, AstCCast>(const AstCCast*, DfgGraph&) {
    return nullptr;
}

template <>  //
DfgCompareNN* makeVertex<DfgCompareNN, AstCompareNN>(const AstCompareNN*, DfgGraph&) {
    return nullptr;
}

template <>  //
DfgSliceSel* makeVertex<DfgSliceSel, AstSliceSel>(const AstSliceSel*, DfgGraph&) {
    return nullptr;
}

template <>  // TODO: CONSIDER REMOVING
DfgArraySel* makeVertex<DfgArraySel, AstArraySel>(const AstArraySel*, DfgGraph&) {
    return nullptr;
}

}  // namespace

class AstToDfgVisitor final : public VNVisitor {
    // NODE STATE

    // AstNode::user1p   // DfgVertex for this AstNode
    const VNUser1InUse m_user1InUse;

    // STATE

    DfgGraph* const m_dfgp;  // The dataflow graph being built
    bool m_foundUnhandled = false;  // Found node not implemented as DFG or not implemented 'visit'
    std::vector<DfgVertex*> m_uncommittedVertices;  // Vertices that we might decide to revert

    // Utility visitor
    class MarkExtRefs final : private VNVisitor {
        AstToDfgVisitor& m_outer;
        void visit(AstNode* nodep) { iterateChildrenConst(nodep); }
        void visit(AstVarRef* nodep) { m_outer.getNet(nodep->varp())->setHasExtRefs(); }

    public:
        explicit MarkExtRefs(AstToDfgVisitor& outer)
            : m_outer{outer} {}
        void operator()(AstNode* nodep) { iterate(nodep); }
    } m_markExtRefs{*this};

    // METHODS

    VL_DEBUG_FUNC;

    void commitVertices() { m_uncommittedVertices.clear(); }

    void revertUncommittedVertices() {
        for (DfgVertex* const vtxp : m_uncommittedVertices) vtxp->unlinkDelete(*m_dfgp);
        m_uncommittedVertices.clear();
    }

    DfgVar* getNet(AstVar* varp) {
        DfgVar* resultp = varp->user1u().to<DfgVar*>();
        if (!resultp) {
            resultp = new DfgVar{*m_dfgp, varp};
            // Note DfgVar vertices are not added to m_uncommittedVertices, because we want to
            // hold onto them via the AstVar, which might be referenced via multiple AstVar
            // instances, so we will never revert a DfgVar once created.
            varp->user1p(resultp);
        }
        return resultp;
    }

    DfgVertex* getVertex(AstNode* nodep) {
        DfgVertex* vtxp = nodep->user1u().to<DfgVertex*>();
        UASSERT_OBJ(vtxp, nodep, "Missing Dfg vertex");
        return vtxp;
    }

    // VISITORS
    void visit(AstNode* nodep) {
        m_markExtRefs(nodep);
        m_foundUnhandled = true;
    }
    void visit(AstModule* nodep) { iterateChildren(nodep); }
    void visit(AstCell* nodep) { m_markExtRefs(nodep); }
    void visit(AstVar* nodep) {
        // Mark ports having external references
        if (nodep->isIO()) getNet(nodep)->setHasExtRefs();
        // Mark variables that are the target of a hierarchical reference
        if (nodep->user2()) getNet(nodep)->setHasExtRefs();
    }
    void visit(AstNodeProcedure* nodep) { m_markExtRefs(nodep); }

    void visit(AstAssignW* nodep) {
        // Cannot handle assignments between different types at the moment
        if (!nodep->lhsp()->dtypep()->similarDType(nodep->rhsp()->dtypep())) {
            m_markExtRefs(nodep);
            return;
        }

        // Cannot handle mismatched widths at the moment
        if (nodep->lhsp()->width() != nodep->rhsp()->width()) {
            m_markExtRefs(nodep);
            return;
        }

        // Simple assignment with whole variable on left-hand side
        if (AstVarRef* const vrefp = VN_CAST(nodep->lhsp(), VarRef)) {
            UASSERT_OBJ(m_uncommittedVertices.empty(), nodep, "Should not nest");

            // Build DFG vertices representing the two sides
            {
                m_foundUnhandled = false;
                iterate(vrefp);
                iterate(nodep->rhsp());
                // If this assignment contains an AstNode not representable by a DfgVertex,
                // then revert the graph.
                if (m_foundUnhandled) {
                    m_foundUnhandled = false;
                    revertUncommittedVertices();
                    m_markExtRefs(nodep);
                    return;
                }
            }

            // Connect the vertices representing the 2 sides
            DfgVar* const lVtxp = getNet(vrefp->varp());
            DfgVertex* const rVtxp = getVertex(nodep->rhsp());
            lVtxp->relinkSource<0>(rVtxp);
            commitVertices();

            // Remove assignment from Ast. Now represented by the Dfg.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);

            //
            return;
        }

        // TODO: handle complex left-hand sides
        m_markExtRefs(nodep);
    }

    void visit(AstVarRef* nodep) {
        UASSERT_OBJ(!nodep->user1p(), nodep, "Already has Dfg vertex");
        if (nodep->classOrPackagep()) {
            // Cannot handle cross module references yet
            m_markExtRefs(nodep);
            m_foundUnhandled = true;
            return;
        }
        nodep->user1p(getNet(nodep->varp()));
    }

    void visit(AstConst* nodep) {
        UASSERT_OBJ(!nodep->user1p(), nodep, "Already has Dfg vertex");
        DfgVertex* const vtxp = new DfgConst{*m_dfgp, nodep->cloneTree(false)};
        m_uncommittedVertices.push_back(vtxp);
        nodep->user1p(vtxp);
    }

#include "V3Dfg__gen_ast_to_dfg.h"

    // CONSTRUCTOR
    explicit AstToDfgVisitor(AstModule& module)
        : m_dfgp{new DfgGraph{module, module.name()}} {
        // Build the DFG
        iterate(&module);
        UASSERT_OBJ(m_uncommittedVertices.empty(), &module, "Uncommitted vertices remain");
    }

public:
    static DfgGraph* apply(AstModule& module) { return AstToDfgVisitor{module}.m_dfgp; }
};

DfgGraph* V3DfgPasses::astToDfg(AstModule& module) { return AstToDfgVisitor::apply(module); }
