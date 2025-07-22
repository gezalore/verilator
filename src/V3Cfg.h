// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Control flow graph (CFG) builder
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
//*************************************************************************

#ifndef VERILATOR_V3CFG_H_
#define VERILATOR_V3CFG_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3EmitV.h"
#include "V3Graph.h"

#include <functional>
#include <memory>
#include <unordered_map>
#include <vector>

class CfgVertex;

class CfgGraph final : public V3Graph {
    CfgVertex* const m_entryp = addVertex();  // The singular entry vertex
    CfgVertex* const m_exitp = addVertex();  // The singular exit vertex

public:
    CfgGraph() = default;
    ~CfgGraph() override = default;

    inline CfgVertex* addVertex();
    inline void addEdge(CfgVertex* srcp, CfgVertex* dstp);

    CfgVertex* entryp() const { return m_entryp; }
    CfgVertex* exitp() const { return m_exitp; }
};

// Verticies of the control flow graph (a basic block)
class CfgVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(CfgVertex, V3GraphVertex)
    friend class CfgGraph;

    std::vector<AstNode*> m_stmtps;

    CfgVertex(CfgGraph* graphp)
        : V3GraphVertex{graphp} {}
    ~CfgVertex() override = default;

public:
    void forEachSuccessor(std::function<void(CfgVertex*)> f) {
        for (V3GraphEdge& edge : outEdges()) f(edge.top()->as<CfgVertex>());
    }

    void forEachPredecessor(std::function<void(CfgVertex*)> f) {
        for (V3GraphEdge& edge : inEdges()) f(edge.fromp()->as<CfgVertex>());
    }

    std::vector<AstNode*>& stmtps() { return m_stmtps; }
    const std::vector<AstNode*>& stmtps() const { return m_stmtps; }

    std::string dotShape() const override { return "rect"; }
    std::string name() const override {
        std::stringstream ss;
        for (AstNode* nodep : m_stmtps) {
            if (AstIf* const ifp = VN_CAST(nodep, If)) {
                ss << "if (";
                V3EmitV::verilogForTree(ifp->condp(), ss, /* suppressUnknown: */ true);
                ss << ") ...";
            } else if (AstWhile* const whilep = VN_CAST(nodep, While)) {
                ss << "while (";
                V3EmitV::verilogForTree(whilep->condp(), ss, /* suppressUnknown: */ true);
                ss << ") ...";
            } else {
                V3EmitV::verilogForTree(nodep, ss, /* suppressUnknown: */ true);
            }
        }
        return ss.str();
    }
};

class CfgEdge final : public V3GraphEdge {
    friend class CfgGraph;

    CfgEdge(CfgGraph* graphp, CfgVertex* srcp, CfgVertex* dstp)
        : V3GraphEdge{graphp, srcp, dstp, /* weight: */ 1, /* cuttable: */ false} {}
    ~CfgEdge() override = default;
};

//////////////////////////////////////////////////////////////////////////////
// Inline method definitions
//////////////////////////////////////////////////////////////////////////////

CfgVertex* CfgGraph::addVertex() { return new CfgVertex{this}; }

void CfgGraph::addEdge(CfgVertex* srcp, CfgVertex* dstp) {
    for (V3GraphEdge& edge : srcp->outEdges()) {
        UASSERT(edge.top() != dstp, "Attempting to create duplicate edge");
    }
    new CfgEdge{this, srcp, dstp};
}

//////////////////////////////////////////////////////////////////////////////
// CfgBuilder
//////////////////////////////////////////////////////////////////////////////

class CfgBuilder final : VNVisitorConst {
    VL_DEFINE_DEBUG_FUNCTIONS;

    // STATE
    // The graph being built, or nullptr if failed to build one
    std::unique_ptr<CfgGraph> m_cfgp{new CfgGraph};
    CfgVertex* m_currp = m_cfgp->entryp();  // Current basic block to add statements to
    // Continuation block for given JumpBlock
    std::unordered_map<AstJumpBlock*, CfgVertex*> m_jumpBlockContp;

    // METHODS
    void nonRepresentable() {
        if (!m_cfgp) return;
        m_cfgp.reset();
    }

    void simpleStatement(AstNode* nodep, bool representable = true) {
        if (!m_cfgp) return;
        // If non-representable, reset graph
        if (!representable) {
            m_cfgp.reset();
            return;
        }
        // Just add to current block
        m_currp->stmtps().emplace_back(nodep);
    }

    // VISITORS

    // Base case, conservatively assume non-representable
    void visit(AstNode* nodep) override {
        if (!m_cfgp) return;
        UINFO(9, "Unhandled AstNode type " << nodep->typeName());
        m_cfgp.reset();
        UASSERT(false, "E " << nodep->typeName());
    }

    // Representable control flow statements
    void visit(AstIf* nodep) override {
        if (!m_cfgp) return;

        // Add terminator statement to current block
        m_currp->stmtps().emplace_back(nodep);

        // Create then/else/continuation blocks
        CfgVertex* const thenp = m_cfgp->addVertex();
        CfgVertex* const elsep = m_cfgp->addVertex();
        CfgVertex* const contp = m_cfgp->addVertex();
        m_cfgp->addEdge(m_currp, thenp);
        m_cfgp->addEdge(m_currp, elsep);

        // Build then branch
        m_currp = thenp;
        iterateAndNextConstNull(nodep->thensp());
        if (!m_cfgp) return;
        if (m_currp) m_cfgp->addEdge(m_currp, contp);

        // Build else branch
        m_currp = elsep;
        iterateAndNextConstNull(nodep->elsesp());
        if (!m_cfgp) return;
        if (m_currp) m_cfgp->addEdge(m_currp, contp);

        // Set continuation
        m_currp = contp;
    }
    void visit(AstWhile* nodep) override {
        if (!m_cfgp) return;

        // Create header/body/continuation blocks
        CfgVertex* const headp = m_cfgp->addVertex();
        CfgVertex* const bodyp = m_cfgp->addVertex();
        CfgVertex* const contp = m_cfgp->addVertex();
        m_cfgp->addEdge(m_currp, headp);
        m_cfgp->addEdge(headp, contp);
        m_cfgp->addEdge(headp, bodyp);

        // The While goes in the header block - the condition check only ...
        headp->stmtps().emplace_back(nodep);

        // Build the body
        m_currp = bodyp;
        iterateAndNextConstNull(nodep->stmtsp());
        iterateAndNextConstNull(nodep->incsp());
        if (!m_cfgp) return;
        if (m_currp) m_cfgp->addEdge(m_currp, headp);

        // Set continuation
        m_currp = contp;
    }
    void visit(AstJumpBlock* nodep) override {
        if (!m_cfgp) return;

        // Don't acutally need to add this 'nodep' to any block - but we could later if needed

        // Create continuation block
        CfgVertex* const contp = m_cfgp->addVertex();
        const bool newEntry = m_jumpBlockContp.emplace(nodep, contp).second;
        UASSERT_OBJ(newEntry, nodep, "AstJumpBlock visited twice");

        // Build the body
        iterateAndNextConstNull(nodep->stmtsp());
        if (!m_cfgp) return;
        if (m_currp) m_cfgp->addEdge(m_currp, contp);

        // Set continuation
        m_currp = contp;
    }
    void visit(AstJumpGo* nodep) override {
        if (!m_cfgp) return;

        // Non-representable if not last in statement list (V3Const will fix this later)
        if (nodep->nextp()) {
            m_cfgp.reset();
            return;
        }

        // Don't acutally need to add this 'nodep' to any block - but we could later if needed

        // Make current block go to the continuation of the JumpBlock
        m_cfgp->addEdge(m_currp, m_jumpBlockContp.at(nodep->blockp()));

        // There should be no statements after a JumpGo!
        m_currp = nullptr;
    }

    // Representable non control-flow statements
    void visit(AstAssign* nodep) override { simpleStatement(nodep, !nodep->timingControlp()); }
    void visit(AstComment*) override { /* ignore entirely */
    }
    void visit(AstDisplay* nodep) override { simpleStatement(nodep); }
    void visit(AstFinish* nodep) override { simpleStatement(nodep); }
    void visit(AstStmtExpr* nodep) override { simpleStatement(nodep); }
    void visit(AstStop* nodep) override { simpleStatement(nodep); }

    // Non-representable nodes
    void visit(AstAssignDly* nodep) override { nonRepresentable(); }
    void visit(AstCase* nodep) override { nonRepresentable(); }  // V3Case will eliminate
    void visit(AstCReset* nodep) override { nonRepresentable(); }
    void visit(AstDelay* nodep) override { nonRepresentable(); }

    // CONSTRUCTOR
    CfgBuilder(AstNodeProcedure* procp) {
        // procp->dumpTree("Proc: ");
        // Visit each statement to build the control flow graph
        iterateAndNextConstNull(procp->stmtsp());
        // Make final block go to the exit block
        if (m_cfgp) m_cfgp->addEdge(m_currp, m_cfgp->exitp());
    }

public:
    static std::unique_ptr<CfgGraph> apply(AstNodeProcedure* procp) {
        return std::move(CfgBuilder{procp}.m_cfgp);
    }
};

#endif  // VERILATOR_V3CFG_H_
