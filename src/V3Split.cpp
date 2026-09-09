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
//  splitAll() splits large always blocks into smaller always blocks
//  when possible (but does not change the order of statements relative
//  to one another.)
//
// The scoreboard tracks data deps as follows:
//
//      ALWAYS
//              ASSIGN ({var} <= {cons})
//              Record as generating var_DLY (independent of use of var), consumers
//              ASSIGN ({var} = {cons}
//              Record generator and consumer
//      Any var that is only consumed can be ignored.
//      Then we split into separate ALWAYS blocks.
//
// The scoreboard includes innards of if/else nodes also.  Splitting is no
// longer limited to top-level statements, we can split within if-else
// blocks. We want to be able to split this:
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
// ...into a separate block for each of a, b, and so on.  Even though this
// requires duplicating the conditional many times, it's usually
// better. Later modules (V3Gate, V3Order) run faster if they aren't
// handling enormous blocks with long lists of inputs and outputs.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Split.h"

#include "V3Graph.h"
#include "V3Stats.h"

#include <string>
#include <unordered_map>
#include <unordered_set>
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

class SplitLogicVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitLogicVertex, SplitNodeVertex)

    std::string dotColor() const override { return "yellow"; }

public:
    SplitLogicVertex(V3Graph* graphp, AstNode* nodep)
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

//######################################################################
// Edge types

class SplitEdge VL_NOT_FINAL : public V3GraphEdge {
    VL_RTTI_IMPL(SplitEdge, V3GraphEdge)
protected:
    SplitEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : V3GraphEdge{graphp, fromp, top, 1, CUTABLE} {}

    virtual bool followScoreboard() const = 0;

public:
    // Iterator for graph functions
    static bool followScoreboard(const V3GraphEdge* edgep) {
        return edgep->as<SplitEdge>()->followScoreboard();
    }
};

class SplitPostEdge final : public SplitEdge {
    VL_RTTI_IMPL(SplitPostEdge, SplitEdge)

    bool followScoreboard() const override { return false; }
    std::string dotColor() const override { return "khaki"; }

public:
    SplitPostEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge{graphp, fromp, top} {}
};

class SplitLVEdge final : public SplitEdge {
    VL_RTTI_IMPL(SplitLVEdge, SplitEdge)

    bool followScoreboard() const override { return true; }
    std::string dotColor() const override { return "yellowGreen"; }

public:
    SplitLVEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge{graphp, fromp, top} {}
};

class SplitRVEdge final : public SplitEdge {
    VL_RTTI_IMPL(SplitRVEdge, SplitEdge)

    bool followScoreboard() const override { return true; }
    std::string dotColor() const override { return "green"; }

public:
    SplitRVEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge{graphp, fromp, top} {}
};

class SplitScorebdEdge final : public SplitEdge {
    VL_RTTI_IMPL(SplitScorebdEdge, SplitEdge)

    bool followScoreboard() const override { return true; }
    std::string dotColor() const override { return "blue"; }

public:
    SplitScorebdEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge{graphp, fromp, top} {}
};

using ColorSet = std::unordered_set<uint32_t>;

// For each color, the statement list to put into that color's split always block
using ColorLists = std::unordered_map<uint32_t, AstNode*>;

// The color of a statement, as assigned by 'SplitVisitor::colorAlwaysGraph'
uint32_t colorOf(const AstNode* nodep) { return nodep->user3u().to<SplitLogicVertex*>()->color(); }

// Clone 'ifp', with the given branches, which the caller has already built
AstIf* cloneIf(const AstIf* ifp, AstNode* thensp, AstNode* elsesp) {
    // The condition is checked for isPure earlier, but may still be a non-pure expression we
    // are separating from other pure statements.
    AstIf* const clonep
        = new AstIf{ifp->fileline(), ifp->condp()->cloneTree(true), thensp, elsesp};
    // Preserve pragmas from unique if's so assertions work properly
    clonep->uniquePragma(ifp->uniquePragma());
    clonep->unique0Pragma(ifp->unique0Pragma());
    clonep->priorityPragma(ifp->priorityPragma());
    return clonep;
}

// Take the statements of the given list, and return them distributed into one list per color.
// Statements are moved, so the given list is left holding only what we do not split out. An
// 'if' is rebuilt around its branches once those are known, so is created only for the colors
// that have something under it, and no empty 'if' is ever constructed.
ColorLists splitStatements(AstNode* stmtsp) {
    ColorLists result;
    for (AstNode* stmtp = stmtsp; stmtp;) {
        AstNode* const nextp = stmtp->nextp();  // 'stmtp' is unlinked below
        if (AstIf* const ifp = VN_CAST(stmtp, If)) {
            ColorLists thens = splitStatements(ifp->thensp());
            ColorLists elses = splitStatements(ifp->elsesp());
            if (thens.empty() && elses.empty()) {
                // Nothing under the 'if'. If its vertex was removed as having no dependencies
                // at all, then its condition reads only block inputs and is pure, so the whole
                // 'if' can go. Otherwise keep it, under its own color, as the condition might
                // have a side effect.
                if (ifp->user3p()) {
                    const uint32_t color = colorOf(ifp);
                    result[color]
                        = AstNode::addNext(result[color], cloneIf(ifp, nullptr, nullptr));
                }
            } else {
                // Rebuild the 'if' in each color present in either branch
                for (const auto& pair : thens) {
                    const uint32_t color = pair.first;
                    AstNode* elsesp = nullptr;
                    const auto it = elses.find(color);
                    if (it != elses.end()) {
                        elsesp = it->second;
                        elses.erase(it);
                    }
                    result[color]
                        = AstNode::addNext(result[color], cloneIf(ifp, pair.second, elsesp));
                }
                for (const auto& pair : elses) {  // Colors under the else branch only
                    result[pair.first]
                        = AstNode::addNext(result[pair.first], cloneIf(ifp, nullptr, pair.second));
                }
            }
        } else if (!VN_IS(stmtp, Comment)) {
            // Move the leaf into its color's list. Comments are dropped, see
            // 'SplitVisitor::scanBlock'.
            const uint32_t color = colorOf(stmtp);
            result[color] = AstNode::addNext(result[color], stmtp->unlinkFrBack());
        }
        stmtp = nextp;
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
    // Ast*::user3p         -> SplitLogicVertex*.  Statement (temporary only)

    // STATE
    // Scoreboard of var usages/dependencies. Only set while under an AstAlways, so also
    // serves as the flag for whether the scoreboard and user attributes are available.
    V3Graph* m_graphp = nullptr;
    std::vector<SplitLogicVertex*> m_stmtStackps;  // Current statements being tracked
    SplitImpureVertex* m_impureVtxp = nullptr;  // Element specifying impure statement order
    const char* m_noSplitWhy = nullptr;  // Reason we can't split
    bool m_inDly = false;  // Inside ASSIGNDLY
    const AstIf* m_curIfConditional = nullptr;  // The 'if' whose condition we're visiting
    VDouble0 m_statSplits;  // Statistic tracking

    // METHODS
    void scanBlock(AstNode* nodep) {
        if (m_noSplitWhy) return;
        // Iterate across current block, making the scoreboard
        for (AstNode* stmtp = nodep; stmtp; stmtp = stmtp->nextp()) {
            // Skip comments. They have no dependencies at all, so would always form a
            // component, and hence a split block, of their own. 'splitStatements' drops them.
            if (VN_IS(stmtp, Comment)) continue;
            UASSERT_OBJ(!stmtp->user3p(), stmtp, "user3p should not be set");
            SplitLogicVertex* const vtxp = new SplitLogicVertex{m_graphp, stmtp};
            stmtp->user3p(vtxp);
            m_stmtStackps.push_back(vtxp);
            iterate(stmtp);
            m_stmtStackps.pop_back();
        }
    }

    void makeRvalueEdges(SplitVarStdVertex* vstdp) {
        // Each 'if' depends on rvalues in its own conditional ONLY,
        // not rvalues in the if/else bodies.
        for (SplitLogicVertex* const vtxp : m_stmtStackps) {
            const AstIf* const ifNodep = VN_CAST(vtxp->nodep(), If);
            if (ifNodep && (m_curIfConditional != ifNodep)) continue;
            new SplitRVEdge{m_graphp, vtxp, vstdp};
        }
    }

    void removeInputVars() {
        // A var vertex with no out edges is never written in this block, so is an input to it.
        // Remove those vertices, and with them the dependencies on them.
        for (V3GraphVertex* const vtxp : m_graphp->vertices().unlinkable()) {
            if (!vtxp->outEmpty()) continue;
            SplitVarStdVertex* const vstdp = vtxp->cast<SplitVarStdVertex>();
            if (!vstdp) continue;
            UINFOTREE(9, vstdp->nodep(), "", "Will remove deps on var:");
            vstdp->nodep()->user1p(nullptr);  // Don't leave a dangling pointer behind
            vstdp->unlinkDelete(m_graphp);
        }
    }

    void colorAlwaysGraph() {
        // Color the graph to indicate subsets, each of which
        // we can split into its own always block.
        m_graphp->removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);

        // Some vars are inputs to the always block; remove them. Reasoning: if two
        // statements both depend on input A, it's ok to split these statements. Whereas
        // if they both depend on locally-generated variable B, the statements must be
        // kept together.
        removeInputVars();

        // For any 'if' node with no remaining out edges (meaning, its conditional expression
        // only looks at block inputs) remove all edges that depend on the 'if'.
        for (V3GraphVertex* const vtxp : m_graphp->vertices().unlinkable()) {
            SplitLogicVertex* const logicp = vtxp->cast<SplitLogicVertex>();
            if (!logicp) continue;
            if (!VN_IS(logicp->nodep(), If)) continue;

            // An out edge remains only for a dependency we could not remove - a variable
            // generated in the current block, or an impure statement under the 'if'
            if (!logicp->outEmpty()) {
                const V3GraphEdge* const edgep = logicp->outEdges().frontp();
                UINFOTREE(9, edgep->top()->as<SplitNodeVertex>()->nodep(),
                          "Cannot remove if-node due to edge " << edgep, "Edge points to node:");
                continue;
            }

            // This 'if' can be split, so remove it, and with it the dependencies on it.
            // Clearing user3p also stops it forming a color, and hence an empty split
            // always block, of its own.
            logicp->nodep()->user3p(nullptr);
            logicp->unlinkDelete(m_graphp);
        }

        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_nodup", false);

        // Weak coloring to determine what needs to remain grouped
        // in a single always. This follows all edges excluding:
        //  - PostEdges, which are done later
        m_graphp->weaklyConnected(&SplitEdge::followScoreboard);
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_colored", false);
    }

    // VISITORS
    void visit(AstAlways* nodep) override {
        // A block created by splitting an earlier block is already minimal
        if (nodep->user4()) return;

        UASSERT_OBJ(!m_graphp, nodep, "AstAlways should not nest");
        // The scoreboard, and hence the user attributes, are per always block
        const VNUser1InUse user1InUse;
        const VNUser2InUse user2InUse;
        const VNUser3InUse user3InUse;
        VL_RESTORER(m_graphp);
        VL_RESTORER(m_impureVtxp);
        VL_RESTORER(m_noSplitWhy);
        VL_RESTORER(m_inDly);

        V3Graph graph;
        m_graphp = &graph;
        m_impureVtxp = nullptr;
        m_noSplitWhy = nullptr;
        m_inDly = false;
        m_stmtStackps.clear();

        // Build the scoreboard
        scanBlock(nodep->stmtsp());

        if (m_noSplitWhy) {
            // We saw a jump or something else rare that we don't handle.
            UINFO(9, "  NoSplitBlock because " << m_noSplitWhy);
            return;
        }

        // Look across the entire tree of if/else blocks in the always,
        // and color regions that must be kept together.
        UINFO(5, "SplitVisitor @ " << nodep);
        colorAlwaysGraph();

        // The set of colors, one split always block per color. The statement vertices are
        // exactly the statements to emit, so their colors are the whole set.
        ColorSet colors;
        for (V3GraphVertex& vertex : m_graphp->vertices()) {
            if (const SplitLogicVertex* const logicp = vertex.cast<SplitLogicVertex>()) {
                colors.insert(logicp->color());
            }
        }
        if (colors.size() <= 1) return;  // Nothing to split

        // Counting original always blocks rather than newly-split always blocks makes it a
        // little easier to use this stat to check the result of the t_alw_split test:
        m_statSplits += colors.size() - 1;  // -1 for the original always

        // Take the statements out of the original block, into one list per color
        UINFO(6, "  splitting always " << nodep);
        const ColorLists lists = splitStatements(nodep->stmtsp());

        // Splice a new block per color in after the original, which must stay linked until
        // they are all in, as it is the iteration point until unlinked below.
        for (const auto& pair : lists) {
            // We don't need to clone nodep->sensesp() here, V3Activate already moved it to
            // a parent node.
            AstAlways* const newp
                = new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS, nullptr, pair.second};
            newp->user4(1);  // Do not split again
            nodep->addNextHere(newp);
        }

        // Unlinking moves the iteration point on to the new blocks, which are skipped
        // above, so the now empty original can go.
        nodep->unlinkFrBack();  // Without next
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
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

    void visit(AstJumpGo* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        m_noSplitWhy = "JumpGo";
    }

    void visit(AstVarRef* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        if (m_stmtStackps.empty()) return;

        AstVarScope* const vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Not linked");

        // Constant lookups can be ignored
        if (nodep->varp()->isConst()) return;

        // Note it is safe to split an always block containing a public variable, as splitting
        // does not perturb PLI's view of the variable.

        // Create vertexes for variable
        if (!vscp->user1p()) vscp->user1p(new SplitVarStdVertex{m_graphp, vscp});
        SplitVarStdVertex* const vstdp = vscp->user1u().to<SplitVarStdVertex*>();

        // SPEEDUP: We add duplicate edges, that should be fixed
        if (m_inDly && nodep->access().isWriteOrRW()) {
            UINFO(4, "     VARREFDLY: " << nodep);
            // Delayed variable is different from non-delayed variable
            if (!vscp->user2p()) {
                SplitVarPostVertex* const vpostp = new SplitVarPostVertex{m_graphp, vscp};
                vscp->user2p(vpostp);
                new SplitPostEdge{m_graphp, vstdp, vpostp};
            }
            SplitVarPostVertex* const vpostp = vscp->user2u().to<SplitVarPostVertex*>();
            for (SplitLogicVertex* const vtxp : m_stmtStackps) {
                new SplitLVEdge{m_graphp, vpostp, vtxp};
            }
        } else if (nodep->access().isWriteOrRW()) {
            // Non-delay; need to maintain existing ordering with all consumers of the signal
            UINFO(4, "     VARREFLV: " << nodep);
            for (SplitLogicVertex* const vtxp : m_stmtStackps) {
                new SplitLVEdge{m_graphp, vstdp, vtxp};
            }
        } else {
            UINFO(4, "     VARREF:   " << nodep);
            makeRvalueEdges(vstdp);
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

        // Timing control prevents splitting
        if (nodep->isTimingControl()) {
            m_noSplitWhy = "TimingControl";
            return;
        }

        // All impure statements must be grouped together.
        if (!m_stmtStackps.empty() && !nodep->isPure()) {
            if (!m_impureVtxp) m_impureVtxp = new SplitImpureVertex{m_graphp, nodep};
            // One edge is enough to find the weakly connected components, but it must point at
            // the impure vertex, so it is an out edge of any enclosing 'if' to prevent pruning.
            for (SplitLogicVertex* const vtxp : m_stmtStackps) {
                new SplitScorebdEdge{m_graphp, vtxp, m_impureVtxp};
            }
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
