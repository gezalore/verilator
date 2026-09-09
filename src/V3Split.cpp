// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into separate statements to reduce temps
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
// V3Split transformation:
//
//  splitAll() splits large always blocks into smaller always blocks when possible,
//  without changing the order of statements relative to one another. Splitting is not
//  limited to top-level statements, we can split within if-else blocks, so that:
//
//    always @ (...) begin
//      if (reset) begin
//        a <= 0;
//        b <= 0;
//         // ... ten thousand more
//      end
//      else begin
//        a <= a_in;
//        b <= b_in;
//         // ... ten thousand more
//      end
//    end
//
// ...becomes a separate block for each of a, b, and so on.  Even though this
// requires duplicating the conditional many times, it's usually
// better. Later modules (V3Gate, V3Order) run faster if they aren't
// handling enormous blocks with long lists of inputs and outputs.
//
// To find what must stay together, a graph is built per always block, holding a vertex
// per statement, each 'if' included, and up to two vertices per variable. Statements in
// the same connected component must stay in one block, and each component then becomes
// a block of its own. The edges are:
//
//   - Blocking write: variable -> statement. Such a write is observable within the
//     block, so the readers of the variable stay with the writer.
//   - Non-blocking write: a separate 'post' vertex of the variable -> statement. All
//     writers of a variable stay together, but the readers, which see the value from
//     before the block, are not held together with them.
//   - Read: statement -> variable. For an 'if', only the reads in its own condition
//     count, not those in its branches.
//   - Impure statement: statement -> a vertex shared by all of them, so that $display
//     and such stay in one block, in order.
//
// A variable with no blocking write is an input to the block, so its vertex is removed,
// and with it the dependencies on it, as two statements both reading an input need not
// stay together. An 'if' left with no dependencies of its own is removed likewise, so
// that the statements under it can separate, each taking a copy of the condition.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Split.h"

#include "V3Graph.h"
#include "V3Stats.h"

#include <string>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

//######################################################################
// Support classes

class SplitNodeVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(SplitNodeVertex, V3GraphVertex)
    AstNode* const m_nodep;

protected:
    SplitNodeVertex(V3Graph* graphp, AstNode* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    // ACCESSORS
    std::string name() const override {
        return cvtToHex(m_nodep) + ' ' + m_nodep->prettyTypeName();
    }

public:
    AstNode* nodep() const { return m_nodep; }
};

class SplitImpureVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitImpureVertex, SplitNodeVertex)

    std::string name() const override VL_MT_STABLE { return "*IMPURE*"; }
    std::string dotColor() const override { return "green"; }

public:
    explicit SplitImpureVertex(V3Graph* graphp, AstNode* nodep)
        : SplitNodeVertex{graphp, nodep} {}
};

class SplitStmtVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitStmtVertex, SplitNodeVertex)

    std::string dotColor() const override { return "yellow"; }

public:
    SplitStmtVertex(V3Graph* graphp, AstNode* nodep)
        : SplitNodeVertex{graphp, nodep} {}
};

class SplitVarStdVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitVarStdVertex, SplitNodeVertex)

    std::string dotColor() const override { return "skyblue"; }

public:
    SplitVarStdVertex(V3Graph* graphp, AstVarScope* vscp)
        : SplitNodeVertex{graphp, vscp} {}
};

class SplitVarPostVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitVarPostVertex, SplitNodeVertex)

    std::string name() const override { return "POST "s + SplitNodeVertex::name(); }
    std::string dotColor() const override { return "CadetBlue"; }

public:
    SplitVarPostVertex(V3Graph* graphp, AstVarScope* vscp)
        : SplitNodeVertex{graphp, vscp} {}
};

// Take the statements of the given list, and return them distributed into one list per color,
// indexed by color, which V3Graph::weaklyConnected assigns densely. Statements are moved, so
// the given list is left holding only what we do not split out. An 'if' is rebuilt around its
// branches once those are known, so is created only for the colors that have something under
// it, and no empty 'if' is ever constructed.
std::vector<AstNode*> splitStatements(AstNode* stmtsp, uint32_t numColors) {
    std::vector<AstNode*> result{numColors, nullptr};
    AstNode* nextp = nullptr;
    for (AstNode* stmtp = stmtsp; stmtp; stmtp = nextp) {
        nextp = stmtp->nextp();  // 'stmtp' is unlinked below
        // Comments are dropped, see 'SplitVisitor::scanBlock'
        if (VN_IS(stmtp, Comment)) continue;
        // The vertex holding the color assigned by 'SplitVisitor::colorAlwaysGraph'. Null for
        // an 'if' that was removed there as having no dependencies at all.
        const SplitStmtVertex* const vtxp = stmtp->user3u().to<SplitStmtVertex*>();
        if (AstIf* const ifp = VN_CAST(stmtp, If)) {
            const auto thens = splitStatements(ifp->thensp(), numColors);
            const auto elses = splitStatements(ifp->elsesp(), numColors);
            // Rebuild the 'if' in each color present in either branch
            bool anyColor = false;
            for (uint32_t color = 0; color < numColors; ++color) {
                if (!thens[color] && !elses[color]) continue;
                anyColor = true;
                // The condition is checked for isPure earlier, but may still be a non-pure
                // expression we are separating from other pure statements.
                AstIf* const clonep = new AstIf{ifp->fileline(), ifp->condp()->cloneTree(true),
                                                thens[color], elses[color]};
                // Preserve pragmas from unique if's so assertions work properly
                clonep->uniquePragma(ifp->uniquePragma());
                clonep->unique0Pragma(ifp->unique0Pragma());
                clonep->priorityPragma(ifp->priorityPragma());
                result[color] = AstNode::addNext(result[color], clonep);
            }
            // Nothing under the 'if' to guard. If its vertex was removed as having no
            // dependencies at all, then its condition reads only block inputs and is pure, so
            // the whole 'if' can go. Otherwise the condition might have a side effect, so keep
            // just the condition, evaluated as a statement, under the color of the 'if' itself.
            // There is only this one 'if' to emit, so the condition can be taken, not cloned.
            if (!anyColor && vtxp) {
                const uint32_t color = vtxp->color();
                AstNodeExpr* const condp = ifp->condp();
                condp->unlinkFrBack();
                result[color]
                    = AstNode::addNext(result[color], new AstStmtExpr{ifp->fileline(), condp});
            }
        } else {
            // Move the leaf into its color's list
            const uint32_t color = vtxp->color();
            result[color] = AstNode::addNext(result[color], stmtp->unlinkFrBack());
        }
    }
    return result;
}

class SplitVisitor final : public VNVisitor {
    // NODE STATE
    // AstAlways::user4     -> bool.  Block created by splitting, needs no further splitting
    const VNUser4InUse m_inuser4;
    // NODE STATE - Only under AstAlways
    // AstVarScope::user1p  -> SplitVarStdVertex*.  Usage var, 0=not set yet
    // AstVarScope::user2p  -> SplitVarPostVertex*.  Delayed assignment var, 0=not set yet
    // Ast*::user3p         -> SplitStmtVertex*.  Statement (temporary only)

    // STATE
    // Scoreboard of var usages/dependencies. Only set while under an AstAlways, so also
    // serves as the flag for whether the scoreboard and user attributes are available.
    V3Graph* m_graphp = nullptr;
    std::vector<SplitStmtVertex*> m_stmtStackps;  // Current statements being tracked
    SplitImpureVertex* m_impureVtxp = nullptr;  // Element specifying impure statement order
    const char* m_noSplitWhy = nullptr;  // Reason we can't split
    bool m_inDly = false;  // Inside ASSIGNDLY
    const AstIf* m_curIfConditional = nullptr;  // The 'if' whose condition we're visiting
    VDouble0 m_statSplits;  // Statistic tracking

    // METHODS
    // All edges are equivalent to the coloring, and the weight is irrelevant, it only has to
    // be non zero for the edge to show up in the .dot dumps
    void addEdge(V3GraphVertex* fromp, V3GraphVertex* top) {
        new V3GraphEdge{m_graphp, fromp, top, 1};
    }

    void scanBlock(AstNode* nodep) {
        if (m_noSplitWhy) return;
        // Iterate across current block, making the scoreboard
        for (AstNode* stmtp = nodep; stmtp; stmtp = stmtp->nextp()) {
            // Skip comments. They have no dependencies at all, so would always form a
            // component, and hence a split block, of their own. 'splitStatements' drops them.
            if (VN_IS(stmtp, Comment)) continue;
            UASSERT_OBJ(!stmtp->user3p(), stmtp, "user3p should not be set");
            SplitStmtVertex* const vtxp = new SplitStmtVertex{m_graphp, stmtp};
            stmtp->user3p(vtxp);
            m_stmtStackps.push_back(vtxp);
            iterate(stmtp);
            m_stmtStackps.pop_back();
        }
    }

    uint32_t colorAlwaysGraph() {
        // Color the graph to indicate subsets, each of which
        // we can split into its own always block.
        m_graphp->removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);

        for (V3GraphVertex* const vtxp : m_graphp->vertices().unlinkable()) {
            SplitVarStdVertex* const vstdp = vtxp->cast<SplitVarStdVertex>();
            if (!vstdp) continue;
            // A var vertex has an out edge only for a blocking write, which is the only kind
            // of write observable within the block, as an NBA takes effect only after it. So
            // with no out edge the variable is an input to the block, whoever writes it.
            // Remove it, together with the dependencies on it. Reasoning: if two statements
            // both depend on input A, it's ok to split these statements. Whereas if they both
            // depend on locally-generated variable B, they must be kept together.
            if (!vstdp->outEmpty()) continue;
            UINFOTREE(9, vstdp->nodep(), "", "Will remove deps on var:");
            vstdp->nodep()->user1p(nullptr);  // Don't leave a dangling pointer behind
            vstdp->unlinkDelete(m_graphp);
        }

        // For any 'if' node with no remaining out edges (meaning, its conditional expression
        // only looks at block inputs) remove all edges that depend on the 'if'.
        for (V3GraphVertex* const vtxp : m_graphp->vertices().unlinkable()) {
            SplitStmtVertex* const stmtVtxp = vtxp->cast<SplitStmtVertex>();
            if (!stmtVtxp) continue;
            if (!VN_IS(stmtVtxp->nodep(), If)) continue;

            // An out edge remains only for a dependency we could not remove - a variable
            // generated in the current block, or an impure statement under the 'if'
            if (!stmtVtxp->outEmpty()) {
                const V3GraphEdge* const edgep = stmtVtxp->outEdges().frontp();
                UINFOTREE(9, edgep->top()->as<SplitNodeVertex>()->nodep(),
                          "Cannot remove if-node due to edge " << edgep, "Edge points to node:");
                continue;
            }

            // This 'if' can be split, so remove it, and with it the dependencies on it.
            // Clearing user3p also stops it forming a color, and hence an empty split
            // always block, of its own.
            stmtVtxp->nodep()->user3p(nullptr);
            stmtVtxp->unlinkDelete(m_graphp);
        }

        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_nodup", false);

        // Weak coloring to determine what must remain grouped in a single always block
        const uint32_t numColors = m_graphp->weaklyConnected(&V3GraphEdge::followAlwaysTrue);
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_colored", false);
        return numColors;
    }

    // VISITORS
    void visit(AstAlways* nodep) override {
        // A block created by splitting an earlier block is already minimal
        if (nodep->user4()) return;

        UASSERT_OBJ(!m_graphp, nodep, "AstAlways should not nest");
        VL_RESTORER(m_graphp);
        VL_RESTORER(m_impureVtxp);
        VL_RESTORER(m_noSplitWhy);
        VL_RESTORER(m_inDly);
        V3Graph graph;
        m_graphp = &graph;
        m_impureVtxp = nullptr;
        m_noSplitWhy = nullptr;
        m_inDly = false;
        UASSERT_OBJ(m_stmtStackps.empty(), nodep, "Statement stack not empty");

        // Build the scoreboard
        const VNUser1InUse user1InUse;
        const VNUser2InUse user2InUse;
        const VNUser3InUse user3InUse;
        scanBlock(nodep->stmtsp());

        // We might have to give up
        if (m_noSplitWhy) {
            UINFO(9, "  NoSplitBlock because " << m_noSplitWhy);
            return;
        }

        // Color the graph to identify separable statements
        const uint32_t numColors = colorAlwaysGraph();
        if (numColors <= 1) return;  // The whole block is one component, nothing to split

        // Counting original always blocks rather than newly-split always blocks makes it a
        // little easier to use this stat to check the result of the t_alw_split test:
        m_statSplits += numColors - 1;  // -1 for the original always

        // Take the statements out of the original block, into one list per color
        UINFO(6, "  splitting always " << nodep);
        const auto lists = splitStatements(nodep->stmtsp(), numColors);

        // Whatever 'splitStatements' did not take, the comments and the hollowed out 'if's,
        // is not needed any more
        if (AstNode* const restp = nodep->stmtsp()) {
            restp->unlinkFrBackWithNext();
            VL_DO_DANGLING(restp->deleteTree(), restp);
        }

        // Every color has a statement in it, see 'colorAlwaysGraph'. Reuse the original
        // block for the first color, and add a new block after it for each of the rest.
        // Iteration continues with those, so mark them to not split again.
        UASSERT_OBJ(lists.front(), nodep, "Color with no statements");
        nodep->addStmtsp(lists.front());
        AstNode* lastp = nodep;
        for (auto it = lists.begin() + 1; it != lists.end(); ++it) {
            UASSERT_OBJ(*it, nodep, "Color with no statements");
            // We don't need to clone nodep->sensesp() here, V3Activate already moved it to
            // a parent node.
            AstAlways* const newp
                = new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS, nullptr, *it};
            newp->user4(1);  // Do not split again
            lastp->addNextHere(newp);
            lastp = newp;
        }
    }

    void visit(AstIf* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        UINFO(4, "     IF " << nodep);
        if (!nodep->condp()->isPure()) {
            m_noSplitWhy = "Impure IF condition";
            return;
        }
        {
            VL_RESTORER(m_curIfConditional);
            m_curIfConditional = nodep;
            iterateAndNextNull(nodep->condp());
        }
        scanBlock(nodep->thensp());
        scanBlock(nodep->elsesp());
    }

    // We don't do AstLoop, due to the standard question of what is before vs. after

    void visit(AstExprStmt* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        VL_RESTORER(m_inDly);
        m_inDly = false;
        iterateChildren(nodep);
    }

    void visit(AstAssignDly* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        UINFO(4, "    ASSIGNDLY " << nodep);
        iterate(nodep->rhsp());
        VL_RESTORER(m_inDly);
        m_inDly = true;
        iterate(nodep->lhsp());
    }

    void visit(AstJumpGo*) override {
        if (!m_graphp || m_noSplitWhy) return;
        m_noSplitWhy = "JumpGo";
    }

    void visit(AstVarRef* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        UASSERT_OBJ(!m_stmtStackps.empty(), nodep, "Not under a statement");

        // Constant lookups can be ignored
        if (nodep->varp()->isConst()) return;

        AstVarScope* const vscp = nodep->varScopep();

        // SPEEDUP: We add duplicate edges, that should be fixed
        if (m_inDly && nodep->access().isWriteOrRW()) {
            UINFO(4, "     VARREFDLY: " << nodep);
            // Delayed variable is different from non-delayed variable
            if (!vscp->user2p()) vscp->user2p(new SplitVarPostVertex{m_graphp, vscp});
            SplitVarPostVertex* const vpostp = vscp->user2u().to<SplitVarPostVertex*>();
            for (SplitStmtVertex* const vtxp : m_stmtStackps) addEdge(vpostp, vtxp);
        } else if (nodep->access().isWriteOrRW()) {
            // Non-delay; need to maintain dataflow
            UINFO(4, "     VARREFLV: " << nodep);
            if (!vscp->user1p()) vscp->user1p(new SplitVarStdVertex{m_graphp, vscp});
            SplitVarStdVertex* const vstdp = vscp->user1u().to<SplitVarStdVertex*>();
            for (SplitStmtVertex* const vtxp : m_stmtStackps) addEdge(vstdp, vtxp);
        } else {
            UINFO(4, "     VARREF:   " << nodep);
            if (!vscp->user1p()) vscp->user1p(new SplitVarStdVertex{m_graphp, vscp});
            SplitVarStdVertex* const vstdp = vscp->user1u().to<SplitVarStdVertex*>();
            for (SplitStmtVertex* const vtxp : m_stmtStackps) {
                // Each 'if' depends on refs in its own condition ONLY, not refs in the branches
                const AstIf* const ifNodep = VN_CAST(vtxp->nodep(), If);
                if (ifNodep && (m_curIfConditional != ifNodep)) continue;
                addEdge(vtxp, vstdp);
            }
        }
    }

    void visit(AstNode* nodep) override {
        // Outside AstAlways, just descend
        if (!m_graphp) {
            iterateChildren(nodep);
            return;
        }
        // Early exit if decided not to split
        if (m_noSplitWhy) return;

        UASSERT_OBJ(!m_stmtStackps.empty(), nodep, "Not under a statement");

        // Timing control prevents splitting
        if (nodep->isTimingControl()) {
            m_noSplitWhy = "TimingControl";
            return;
        }

        // All impure statements must be grouped together.
        if (!nodep->isPure()) {
            if (!m_impureVtxp) m_impureVtxp = new SplitImpureVertex{m_graphp, nodep};
            // One edge is enough to find the weakly connected components, but it must point at
            // the impure vertex, so it is an out edge of any enclosing 'if' to prevent pruning.
            for (SplitStmtVertex* const vtxp : m_stmtStackps) addEdge(vtxp, m_impureVtxp);
        }

        iterateChildren(nodep);
    }

    // CONSTRUCTORS
    explicit SplitVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~SplitVisitor() override { V3Stats::addStat("Optimizations, Split always", m_statSplits); }
    VL_UNCOPYABLE(SplitVisitor);

public:
    static void apply(AstNetlist* nodep) { SplitVisitor{nodep}; }
};

}  //namespace

//######################################################################
// Split class functions

void V3Split::splitAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    SplitVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("split", 0, dumpTreeEitherLevel() >= 3);
}
