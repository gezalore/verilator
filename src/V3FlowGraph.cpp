// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Control Flow Graph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3FlowGraph.h"

#include "V3PartitionGraph.h"
#include "V3Error.h"

#include VL_INCLUDE_UNORDERED_MAP

// The only reason EntryVertex and ExitVertex exist is to override DOT
// formatting so we can produce nice dumps. All actual processing is via
// V3FlowVertex.
class EntryVertex : public V3FlowVertex {
public:
    explicit EntryVertex(V3FlowGraph* graphp)
        : V3FlowVertex(graphp, NULL) {}
    string name() const VL_OVERRIDE { return "ENTRY"; }
};
class ExitVertex : public V3FlowVertex {
public:
    explicit ExitVertex(V3FlowGraph* graphp)
        : V3FlowVertex(graphp, NULL) {}
    string name() const VL_OVERRIDE { return "EXIT"; }
};

V3FlowGraph::V3FlowGraph()
    : V3Graph()
    , m_entryp(new EntryVertex(this))
    , m_exitp(new ExitVertex(this)) {}

V3FlowGraph::~V3FlowGraph() {
    m_entryp->unlinkDelete(this);
    m_exitp->unlinkDelete(this);
}

class BuildGraphForNode;

class V3FlowGraphBuilder {
    friend class BuildGraphForNode;

    V3FlowGraph& m_graph;  // The graph being built

    // Note: we use a map instead of using the node UserN pointers as the cache
    // needs to be invalidated at different points for different subsets of nodes.
    typedef vl_unordered_map<AstNode*, V3FlowVertex*> VertexCache;  // The cache map type
    VertexCache m_vertexCache;  // The cache map

    // Get the flow vertex holding the given node.
    V3FlowVertex* vertexFor(AstNode* nodep) {
        UASSERT(nodep, "vertexFor called with NULL");
        // Get vertex from cache, create it if it does not yet exist
        VertexCache::iterator it = m_vertexCache.find(nodep);
        if (it == m_vertexCache.end()) {
            it = m_vertexCache.insert(make_pair(nodep, new V3FlowVertex(&m_graph, nodep))).first;
        }
        return it->second;
    }

    // Create a new empty vertex that can be used as a placeholder during
    // the flow graph construction process.
    V3FlowVertex* emptyVertex() { return new V3FlowVertex(&m_graph, NULL); }

    // Build a sub flow graph for a single node (ignoring nextp), and link the
    // exits of the sub grap to the given successor node. Returns the header
    // (entry point) of the resulting sub graph.
    V3FlowVertex* buildNode(AstNode* nodep, V3FlowVertex* succ);

    // Build a sub flow graph for the given list of nodes, and link the exits
    // of the last node to the given successor. Return the header (entry point)
    // of the resulting sub graph. If the given list is NULL, returns the given
    // successor.
    V3FlowVertex* buildList(AstNode* nodep, V3FlowVertex* succp) {
        UASSERT(succp, "buildList called with NULL successor");
        if (!nodep) {
            // Easy
            return succp;
        } else {
            // Note: This could be written simply as
            //   return buildNode(nodep, buildList(nodep->nextp(), succp));
            // but that recursion risks a stack overflow, so we process the
            // reversed list without recursion instead.
            const AstNode* const headp = nodep;
            // Fast forward (can't we just use AstNode::m_headtailp?)
            while (nodep->nextp()) nodep = nodep->nextp();
            // Walk backwards
            for (; nodep != headp; nodep = nodep->backp()) succp = buildNode(nodep, succp);
            // Finish up with the head
            return buildNode(nodep, succp);
        }
    }

    // Add edge 'fromp' -> 'top'
    void link(V3FlowVertex* fromp, V3FlowVertex* top) { new V3GraphEdge(&m_graph, fromp, top, 1); }

    explicit V3FlowGraphBuilder(V3FlowGraph& graph)
        : m_graph(graph) {}

public:
    // Build the flow graph for a CFunc
    static V3FlowGraph* build(AstCFunc* nodep) {
        // Create graph
        V3FlowGraph* graphp = new V3FlowGraph();
        // Create builder
        V3FlowGraphBuilder builder(*graphp);
        // Build the node, linking it between the graph entry and exit vertices
        builder.link(graphp->m_entryp, builder.buildNode(nodep, graphp->m_exitp));

        // if (debug() >= 6)
        graphp->dumpDotFilePrefixed("flow-graph-raw");

        // Simplify the graph a bit by removing nodes that carry no information
        // but were necessary for construction.
        for (V3GraphVertex *nextp, *itp = graphp->verticesBeginp(); itp; itp = nextp) {
            nextp = itp->verticesNextp();
            V3FlowVertex* const vertexp = reinterpret_cast<V3FlowVertex*>(itp);
            if (!vertexp->m_nodep) continue;
            UASSERT(!VN_IS(vertexp->m_nodep, CFunc), "Should not have added CFunc");
            UASSERT(!VN_IS(vertexp->m_nodep, JumpBlock), "Should not have added JumpBlock");
            UASSERT(!VN_IS(vertexp->m_nodep, JumpGo), "Should not have added JumpGo");
            UASSERT(!VN_IS(vertexp->m_nodep, MTaskBody), "Should not have added MTaskBody");
            if (VN_IS(vertexp->m_nodep, JumpLabel) || VN_IS(vertexp->m_nodep, Comment)
                || VN_IS(vertexp->m_nodep, ExecGraph)) {
                vertexp->rerouteEdges(graphp);
                vertexp->unlinkDelete(graphp);
            }
        }

        // if (debug() >= 6)
        graphp->dumpDotFilePrefixed("flow-graph-simplfied");
        return graphp;
    }
};

// This visitor implements V3FlowGraphBuilder::buildNode, building the flow
// graph for a single node. The only reason this is a visitor is to utilize
// dynamic dispatch over the node type. There is no actual visitation involved
// (though there is recursive invocation of V3FlowGraphBuilder::*). The
// alternative would be a function with a big chain of dynamic casts. Note: We
// cannot use a visitor to directly build the flow graph as it is built right
// to left in lists of nodes, while the visitor walks left to right.
class BuildGraphForNode : AstNVisitor {
    friend class V3FlowGraphBuilder;
    V3FlowVertex* const m_succp;  // The successor node for the sub-graph being built
    V3FlowGraphBuilder& m_builder;  // The builder invoking this visitor instance
    V3FlowVertex* m_headerp;  // The result header vertex

    BuildGraphForNode(AstNode* nodep, V3FlowVertex* succp, V3FlowGraphBuilder& builder)
        : m_succp(succp)
        , m_builder(builder)
        , m_headerp(NULL) {
        iterate(nodep);  // Build the sub-graph
    }

    // Build single node sub-graph (common case)
    void single(AstNode* nodep) {
        // Create the vertex and link it before the successor
        m_headerp = m_builder.vertexFor(nodep);
        m_builder.link(m_headerp, m_succp);
    }

    // VISITORS
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        // Ignore the CFunc node itself, build graph just for the contents.
        V3FlowVertex* const fHeaderP = m_builder.buildList(nodep->finalsp(), m_succp);
        V3FlowVertex* const sHeaderP = m_builder.buildList(nodep->stmtsp(), fHeaderP);
        V3FlowVertex* const iHeaderP = m_builder.buildList(nodep->initsp(), sHeaderP);
        // The header is the header of the body
        m_headerp = iHeaderP;
    }

    virtual void visit(AstIf* nodep) VL_OVERRIDE {
        // Create the test vertex
        V3FlowVertex* const selfp = m_builder.vertexFor(nodep);
        // Build branches, link them after the test. Note: It's OK for now if
        // both ifsp and elsesp are empty, we get the same result in analysis
        m_builder.link(selfp, m_builder.buildList(nodep->ifsp(), m_succp));
        m_builder.link(selfp, m_builder.buildList(nodep->elsesp(), m_succp));
        // The header is the test vertex
        m_headerp = selfp;
    }

    virtual void visit(AstWhile* nodep) VL_OVERRIDE {
        // Create the test node
        V3FlowVertex* const selfp = m_builder.vertexFor(nodep);
        // Build the loop
        V3FlowVertex* const pHeaderP = m_builder.buildList(nodep->precondsp(), selfp);
        V3FlowVertex* const iHeaderP = m_builder.buildList(nodep->incsp(), pHeaderP);
        V3FlowVertex* const bHeaderP = m_builder.buildList(nodep->bodysp(), iHeaderP);
        m_builder.link(selfp, bHeaderP);
        // Add the loop exit branch
        m_builder.link(selfp, m_succp);
        // The header is the header of the precondition sequence
        m_headerp = pHeaderP;
    }

    virtual void visit(AstJumpBlock* nodep) VL_OVERRIDE {
        // Ignore the JumpBlock node itself, build graph just for the contents.
        V3FlowVertex* const eHeaderP = m_builder.buildList(nodep->endStmtsp(), m_succp);
        V3FlowVertex* const sHeaderP = m_builder.buildList(nodep->stmtsp(), eHeaderP);
        // The header is the header of the body
        m_headerp = sHeaderP;
    }

    virtual void visit(AstJumpLabel* nodep) VL_OVERRIDE {
        // Note: need to add a Vertex for the label, so we can go to it.
        // The label vertex is otherwise a no-op so can be ignored/removed.
        single(nodep);
    }

    virtual void visit(AstJumpGo* nodep) VL_OVERRIDE {
        // Ignore the JumpGo node itself, go straight to the label.
        m_headerp = m_builder.vertexFor(nodep->labelp());
    }

    virtual void visit(AstExecGraph* nodep) VL_OVERRIDE {
        // Build a sub-graph for each MTask, and link them in dependency order.
        // Link MTasks with no upstream dependencies to this node, and MTasks
        // with no downstream dependents to the successor node. To be able
        // to build nodes with multiple successors, we allocate an empty
        // successor node for each MTask that has downstream dependents and
        // resolve to that. We will later remove these empty vertices.
        const V3Graph* const dgp = nodep->depGraphp();
        // Create the ExecGraph entry point
        V3FlowVertex* const selfp = m_builder.vertexFor(nodep);
        // Build the successor vertices up front
        vl_unordered_map<const AstMTaskBody*, V3FlowVertex*> successor;
        for (V3GraphVertex* dvp = dgp->verticesBeginp(); dvp; dvp = dvp->verticesNextp()) {
            AstMTaskBody* const mtp = dynamic_cast<ExecMTask*>(dvp)->bodyp();
            successor[mtp] = dvp->outEmpty() ? m_succp : m_builder.emptyVertex();
        }
        // Build the sub-graphs, and link the vertices
        for (V3GraphVertex* dvp = dgp->verticesBeginp(); dvp; dvp = dvp->verticesNextp()) {
            AstMTaskBody* const mtp = dynamic_cast<ExecMTask*>(dvp)->bodyp();
            V3FlowVertex* const succp = successor[mtp];
            // Build the flow graph for the MTask
            V3FlowVertex* const vertexp = m_builder.buildNode(mtp, succp);
            // Link upstream dependencies. Observe that downstream linking is
            // done by buildNode itself via the successor map, or when linking
            // the upstream dependencies of the dependents right here.
            if (dvp->inEmpty()) {
                // MTask with no upstream dependencies
                m_builder.link(selfp, vertexp);
            } else {
                // MTask with upstream dependencies
                for (V3GraphEdge* ep = dvp->inBeginp(); ep; ep = ep->inNextp()) {
                    AstMTaskBody* const fromp = dynamic_cast<ExecMTask*>(ep->fromp())->bodyp();
                    m_builder.link(successor[fromp], vertexp);
                }
            }
        }
        // The header is the exec graph node
        m_headerp = selfp;
    }

    virtual void visit(AstMTaskBody* nodep) VL_OVERRIDE {
        // Ignore the MTaskBody node itself, build graph just for the contents.
        m_headerp = m_builder.buildList(nodep->stmtsp(), m_succp);
    }

    virtual void visit(AstCCall* nodep) VL_OVERRIDE {
        // Build a sub graph for the body using a fresh builder. This ensures
        // that if multiple calls are made to the same procedure, each call
        // site will have a unique copy of the control flow graph inlined.
        // This enables context sensitive data flow analysis.
        m_headerp = m_builder.vertexFor(nodep);
        V3FlowGraphBuilder builder(m_builder.m_graph);
        m_builder.link(m_headerp, builder.buildNode(nodep->funcp(), m_succp));
    }

    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE { single(nodep); }

    virtual void visit(AstCoverInc* nodep) VL_OVERRIDE { single(nodep); }

    virtual void visit(AstDisplay* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstDumpCtl* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstStop* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstFinish* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstFOpen* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstFOpenMcd* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstFClose* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstFFlush* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstTimeFormat* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstSFormat* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstPrintTimeScale* nodep) VL_OVERRIDE { single(nodep); }

    virtual void visit(AstComment* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstCStmt* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstUCStmt* nodep) VL_OVERRIDE { single(nodep); }
    virtual void visit(AstCMethodHard* nodep) VL_OVERRIDE {
        UASSERT_OBJ(nodep->isStatement(), nodep, "CMethodHard not a statement in flow graph");
        single(nodep);
    }
    virtual void visit(AstAlwaysPublic* nodep) VL_OVERRIDE {
        single(nodep); // TODO: Not sure what this is
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        single(nodep);// TODO: Not sure what this is
    }


    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        v3fatal(string("Don't know how to build control flow graph for ") + nodep->typeName());
    }
};

V3FlowVertex* V3FlowGraphBuilder::buildNode(AstNode* nodep, V3FlowVertex* succp) {
    UASSERT(nodep, "buildNode called with NULL node");
    UASSERT(succp, "buildNode called with NULL successor");
    // Dispatch to the implementation
    BuildGraphForNode instance(nodep, succp, *this);
    UASSERT(instance.m_headerp, "Missing result in BuildGraphForNode");
    return instance.m_headerp;
}

void V3FlowGraph::build(AstCFunc* nodep) {
    V3FlowGraph* graphp = V3FlowGraphBuilder::build(nodep);

    delete graphp;
}
