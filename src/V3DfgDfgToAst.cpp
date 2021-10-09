// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Data flow graph data structures
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3File.h"

#include <cctype>
#include <unordered_map>

namespace {

// Create an AstNodeMath out of a DfgVertex. For most AstNodeMath subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename Node, typename Vertex, typename... Ops>  //
Node* makeNode(const Vertex* vtxp, Ops... ops) {
    static_assert(std::is_base_of<AstNodeMath, Node>::value,
                  "'Node' must be subclass of 'AstNodeMath'");
    static_assert(std::is_base_of<DfgVertex, Vertex>::value,
                  "'Vertex' must be subclass of 'DfgVertex'");
    Node* const nodep = new Node{vtxp->fileline(), ops...};
    UASSERT_OBJ(nodep->width() == vtxp->width(), vtxp,
                "Incorrect width in AstNode created from DfgVertex "
                    << vtxp->typeName() << ": " << nodep->width() << " vs " << vtxp->width());
    return nodep;
}

template <>
AstExtend* makeNode<AstExtend, DfgExtend, AstNodeMath*>(  //
    const DfgExtend* vtxp, AstNodeMath* op1) {
    return new AstExtend{vtxp->fileline(), op1, static_cast<int>(vtxp->width())};
}

template <>
AstExtendS* makeNode<AstExtendS, DfgExtendS, AstNodeMath*>(  //
    const DfgExtendS* vtxp, AstNodeMath* op1) {
    return new AstExtendS{vtxp->fileline(), op1, static_cast<int>(vtxp->width())};
}

template <>
AstShiftL* makeNode<AstShiftL, DfgShiftL, AstNodeMath*, AstNodeMath*>(  //
    const DfgShiftL* vtxp, AstNodeMath* op1, AstNodeMath* op2) {
    return new AstShiftL{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

template <>
AstShiftR* makeNode<AstShiftR, DfgShiftR, AstNodeMath*, AstNodeMath*>(  //
    const DfgShiftR* vtxp, AstNodeMath* op1, AstNodeMath* op2) {
    return new AstShiftR{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

template <>
AstShiftRS* makeNode<AstShiftRS, DfgShiftRS, AstNodeMath*, AstNodeMath*>(  //
    const DfgShiftRS* vtxp, AstNodeMath* op1, AstNodeMath* op2) {
    return new AstShiftRS{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

// LCOV_EXCL_START
template <>  //
AstAtoN* makeNode<AstAtoN, DfgAtoN, AstNodeMath*>(  //
    const DfgAtoN* vtxp, AstNodeMath*) {
    vtxp->v3fatal("not implemented");
}

template <>  //
AstCCast* makeNode<AstCCast, DfgCCast, AstNodeMath*>(  //
    const DfgCCast* vtxp, AstNodeMath*) {
    vtxp->v3fatal("not implemented");
}

template <>  //
AstCompareNN* makeNode<AstCompareNN, DfgCompareNN, AstNodeMath*, AstNodeMath*>(  //
    const DfgCompareNN* vtxp, AstNodeMath*, AstNodeMath*) {
    vtxp->v3fatal("not implemented");
}

template <>  //
AstSliceSel* makeNode<AstSliceSel, DfgSliceSel, AstNodeMath*, AstNodeMath*, AstNodeMath*>(
    const DfgSliceSel* vtxp, AstNodeMath*, AstNodeMath*, AstNodeMath*) {
    vtxp->v3fatal("not implemented");
}
// LCOV_EXCL_STOP

}  // namespace

class DfgToAstVisitor final : DfgVVisitor {
    // STATE

    AstModule* const m_modp;  // The parent/result module

    AstNodeMath* m_resultp = nullptr;  // The result node of the current traversal

    std::unordered_map<const DfgVertex*, AstVar*> resultVars;

    // Given a DfgVertex, return an AstVar that will hold the value of the given DfgVertex once we
    // are done with converting this Dfg into Ast form.
    AstVar* getResultVar(const DfgVertex* vtxp) {
        // Check if we already have a variable for this vertex
        const auto it = resultVars.find(vtxp);
        if (it != resultVars.end()) return it->second;
        // We do not have a variable for this vertex yet.
        AstVar* varp = nullptr;
        // If this vertex is a DfgVar, then we know the variable. If this node is not a DfgVar,
        // then first we try to find a DfgVar driven by this node, and use that, otherwise we
        // create a temporary
        if (const DfgVar* const thisDfgVarp = vtxp->cast<DfgVar>()) {
            // This is a DfgVar
            varp = thisDfgVarp->varp();
        } else if (const DfgVar* const sinkDfgVarp = vtxp->findSink<DfgVar>()) {
            // We found a DfgVar driven by this node
            varp = sinkDfgVarp->varp();
        } else {
            // No DfgVar driven by this node. Create a temporary.
            string name{"_VdfgTmp__"};
            static size_t ord = 0;
            name += cvtToStr(++ord);
            // TODO: signed!!!
            AstNodeDType* const dtypep
                = v3Global.rootp()->findBitDType(vtxp->width(), vtxp->width(), VSigning::UNSIGNED);
            varp = new AstVar{vtxp->fileline(), VVarType::MODULETEMP, name, dtypep};
            // Add temporary AstVar to containing module
            m_modp->addStmtp(varp);
        }
        // Add to map
        resultVars[vtxp] = varp;
        //
        return varp;
    };

    // METHODS
    AstNodeMath* convertDfgVertexToAstNodeMath(DfgVertex* vtxp) {
        UASSERT_OBJ(!m_resultp, vtxp, "Result already computed");
        iterate(vtxp);
        AstNodeMath* const resultp = m_resultp;
        UASSERT_OBJ(resultp, vtxp, "Missing result");
        m_resultp = nullptr;
        return resultp;
    }

    AstNodeMath* convertSource(DfgVertex* vtxp) {
        if (vtxp->hasMultipleSinks()) {
            // Vertices with multiple sinks need a temporary variable, just return a reference
            return new AstVarRef{vtxp->fileline(), getResultVar(vtxp), VAccess::READ};
        } else {
            // Vertex with single sink is simply recursively converted
            UASSERT_OBJ(vtxp->hasSinks(), vtxp, "Must have one sink: " << vtxp->typeName());
            return convertDfgVertexToAstNodeMath(vtxp);
        }
    }

    // VISITORS
    void visit(DfgVertex* vtxp) override {  // LCOV_EXCL_START
        vtxp->v3fatal("Unhandled DfgVertex: " << vtxp->typeName());
    }  // LCOV_EXCL_STOP

    void visit(DfgVar* vtxp) override {
        m_resultp = new AstVarRef{vtxp->fileline(), vtxp->varp(), VAccess::READ};
    }

    void visit(DfgConst* vtxp) override {  //
        m_resultp = vtxp->constp()->cloneTree(false);
    }

#include "V3Dfg__gen_dfg_to_ast.h"

    // Constructor
    explicit DfgToAstVisitor(DfgGraph& dfg)
        : m_modp{dfg.modulep()} {
        dfg.forEachVertex([this](DfgVertex& vtx) {
            // Compute the AstNodeMath expression representing this DfgVertex
            AstNodeMath* rhsp = nullptr;
            if (const DfgVar* const dfgVarp = vtx.cast<DfgVar>()) {
                // DfgVar instances (these might be driving the given AstVar variable)
                // If there is no driver (i.e.: this DfgVar is an input to the Dfg), then nothing
                // to do
                if (!dfgVarp->driverp()) return;
                // The driver of this DfgVar might drive multiple variables. Only emit one
                // assignment from the driver to an arbitrarily chosen canonical variable, and
                // assign the other variables from that canonical variable
                AstVar* const canonVarp = getResultVar(dfgVarp->driverp());
                if (canonVarp == dfgVarp->varp()) {
                    // This is the canonical variable, so render the driver
                    rhsp = convertDfgVertexToAstNodeMath(dfgVarp->driverp());
                } else {
                    // Not the canonical variable, just assign from the canonical variable
                    rhsp = new AstVarRef{canonVarp->fileline(), canonVarp, VAccess::READ};
                }
            } else if (vtx.hasMultipleSinks() && !vtx.findSink<DfgVar>()) {
                // DfgVertex that has multiple sinks, but does not drive a DfgVar (needs temporary)
                // Render vertex
                rhsp = convertDfgVertexToAstNodeMath(&vtx);
            } else {
                // Every other DfgVertex will be inlined by 'dfg2Ast' as an AstNodeMath at use,
                // and hence need not be converted
                return;
            }
            // Reference to the variable holding the result of this DfgVertex
            AstVarRef* const lhsp
                = new AstVarRef{vtx.fileline(), getResultVar(&vtx), VAccess::WRITE};
            // Assign the result of the Vertex to the variable.
            // TODO: preserve locations better
            AstNode* const logicp = new AstAssignW{vtx.fileline(), lhsp, rhsp};
            // Add logic to containing module
            m_modp->addStmtp(logicp);
        });
    }

public:
    static AstModule* apply(DfgGraph& dfg) { return DfgToAstVisitor{dfg}.m_modp; }
};

AstModule* V3DfgPasses::dfgToAst(DfgGraph& dfg) { return DfgToAstVisitor::apply(dfg); }
