// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Clocking POS/NEGEDGE insertion
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
// V3Clock's Transformations:
//
// Top Scope:
//   Check created ACTIVEs
//      Compress adjacent ACTIVEs with same sensitivity list
//      Form master _eval function
//              Add around the SENTREE a (IF POSEDGE(..))
//                      Add a __Vlast_{clock} for the comparison
//                      Set the __Vlast_{clock} at the end of the block
//              Replace UNTILSTABLEs with loops until specified signals become const.
//   Create global calling function for any per-scope functions.  (For FINALs).
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Clock.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Hashed.h"

#include <algorithm>
#include <list>

//######################################################################
// Clock state, as a visitor of each AstNode

class ClockVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared each Module:
    //  AstVarScope::user1p()   -> AstVarScope*.  Temporary signal that was created.
    AstUser1InUse m_inuser1;

    // STATE
    AstNodeModule* m_modp;  // Current module
    AstTopScope* m_topScopep;  // Current top scope
    AstScope* m_scopeTopp;  // The Scope unedr TopScope
    AstCFunc* m_evalFuncp;  // Top eval function we are creating
    AstCFunc* m_initFuncp;  // Top initial function we are creating
    AstCFunc* m_finalFuncp;  // Top final function we are creating
    AstCFunc* m_settleFuncp;  // Top settlement function we are creating

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstVarScope* getCreateLastClk(AstVarScope* vscp) {
        if (vscp->user1p()) return static_cast<AstVarScope*>(vscp->user1p());
        AstVar* varp = vscp->varp();
        if (!varp->width1()) {
            varp->v3warn(E_UNSUPPORTED, "Unsupported: Clock edge on non-single bit signal: "
                                            << varp->prettyNameQ());
        }
        string newvarname
            = (string("__Vclklast__") + vscp->scopep()->nameDotless() + "__" + varp->name());
        AstVar* newvarp = new AstVar(vscp->fileline(), AstVarType::MODULETEMP, newvarname,
                                     VFlagLogicPacked(), 1);
        newvarp->noReset(true);  // Reset by below assign
        m_modp->addStmtp(newvarp);
        AstVarScope* newvscp = new AstVarScope(vscp->fileline(), m_scopeTopp, newvarp);
        vscp->user1p(newvscp);
        m_scopeTopp->addVarp(newvscp);
        // Add init
        AstNode* fromp = new AstVarRef(newvarp->fileline(), vscp, false);
        if (v3Global.opt.xInitialEdge()) fromp = new AstNot(fromp->fileline(), fromp);
        AstNode* newinitp = new AstAssign(
            vscp->fileline(), new AstVarRef(newvarp->fileline(), newvscp, true), fromp);
        m_initFuncp->addStmtsp(newinitp);
        // At bottom, assign them
        AstAssign* finalp
            = new AstAssign(vscp->fileline(), new AstVarRef(vscp->fileline(), newvscp, true),
                            new AstVarRef(vscp->fileline(), vscp, false));
        m_evalFuncp->addFinalsp(finalp);
        //
        UINFO(4, "New Last: " << newvscp << endl);
        return newvscp;
    }
    AstNode* createSenItemEquation(const AstSenItem* nodep) {
        // We know the var is clean, and one bit, so we use binary ops
        // for speed instead of logical ops.
        // POSEDGE:  var & ~var_last
        // NEGEDGE:  ~var & var_last
        // BOTHEDGE:  var ^ var_last
        // HIGHEDGE:  var
        // LOWEDGE:  ~var
        AstNode* newp = NULL;
        if (nodep->edgeType() == VEdgeType::ET_ILLEGAL) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Complicated event expression in sensitive activity list");
            return NULL;
        }
        AstVarScope* clkvscp = nodep->varrefp()->varScopep();
        if (nodep->edgeType() == VEdgeType::ET_POSEDGE) {
            AstVarScope* lastVscp = getCreateLastClk(clkvscp);
            newp = new AstAnd(
                nodep->fileline(),
                new AstVarRef(nodep->fileline(), nodep->varrefp()->varScopep(), false),
                new AstNot(nodep->fileline(), new AstVarRef(nodep->fileline(), lastVscp, false)));
        } else if (nodep->edgeType() == VEdgeType::ET_NEGEDGE) {
            AstVarScope* lastVscp = getCreateLastClk(clkvscp);
            newp = new AstAnd(
                nodep->fileline(),
                new AstNot(nodep->fileline(),
                           new AstVarRef(nodep->fileline(), nodep->varrefp()->varScopep(), false)),
                new AstVarRef(nodep->fileline(), lastVscp, false));
        } else if (nodep->edgeType() == VEdgeType::ET_BOTHEDGE) {
            AstVarScope* lastVscp = getCreateLastClk(clkvscp);
            newp = new AstXor(
                nodep->fileline(),
                new AstVarRef(nodep->fileline(), nodep->varrefp()->varScopep(), false),
                new AstVarRef(nodep->fileline(), lastVscp, false));
        } else if (nodep->edgeType() == VEdgeType::ET_HIGHEDGE) {
            newp = new AstVarRef(nodep->fileline(), clkvscp, false);
        } else if (nodep->edgeType() == VEdgeType::ET_LOWEDGE) {
            newp = new AstNot(nodep->fileline(), new AstVarRef(nodep->fileline(), clkvscp, false));
        } else {
            nodep->v3fatalSrc("Bad edge type");
        }
        return newp;
    }
    AstNode* createSenseEquation(const AstSenItem* nodesp) {
        // Nodep may be a list of elements; we need to walk it
        AstNode* senEqnp = NULL;
        for (const AstSenItem* senp = nodesp; senp; senp = VN_CAST_CONST(senp->nextp(), SenItem)) {
            AstNode* const senOnep = createSenItemEquation(senp);
            if (senEqnp) {
                // Add new OR to the sensitivity list equation
                senEqnp = new AstOr(senp->fileline(), senEqnp, senOnep);
            } else {
                senEqnp = senOnep;
            }
        }
        return senEqnp;
    }

    AstIf* makeActiveIf(const AstSenItem* sensesp) {
        AstNode* senEqnp = createSenseEquation(sensesp);
        UASSERT_OBJ(senEqnp, sensesp, "No sense equation, shouldn't be in sequent activation.");
        return new AstIf(sensesp->fileline(), senEqnp, NULL, NULL);
    }

    typedef std::list<AstActive*> ActList;
    typedef std::list<AstSenItem*> SenList;

    // Given a list of Activate nodes that need to be converted for this
    // function, return a list of SenItem nodes which should be specialized.
    SenList getSenItemsToSpecialize(const ActList& actList) {
        // Count how many Active blocks depend on each unique SenItem
        struct Hash {
            size_t operator()(const AstSenItem* kp) const {
                return V3Hashed::uncachedHash(kp).fullValue();
            }
        };
        struct Equals {
            bool operator()(const AstSenItem* ap, const AstSenItem* bp) const {
                return ap->sameTree(bp);
            }
        };
        typedef vl_unordered_map<AstSenItem*, int, Hash, Equals> SenItemCount;
        SenItemCount senItemCount;

        for (ActList::const_iterator it = actList.begin(); it != actList.end(); ++it) {
            const AstActive* const active = *it;
            if (!active->hasClocked()) continue;  // Only care about clocked nodes
            const AstSenTree* treep = active->sensesp();
            for (AstSenItem* itemp = treep->sensesp(); itemp;
                 itemp = VN_CAST(itemp->nextp(), SenItem)) {
                // Increment mapped value (with default to 0)
                senItemCount.insert(make_pair(itemp, 0)).first->second++;
            }
        }

        // Sort the SenItems by frequency
        typedef std::multimap<int, AstSenItem*> SortedMap;
        SortedMap sortedMap;
        for (SenItemCount::iterator it = senItemCount.begin(); it != senItemCount.end(); ++it) {
            sortedMap.insert(make_pair(it->second, it->first));
        }

        // Pick the first 2 // TODO: better heuristic
        SenList result;
        SortedMap ::reverse_iterator it = sortedMap.rbegin();
        for (int n = 0; n < 2; ++n, ++it) {
            if (it == sortedMap.rend()) break;
            result.push_back(it->second);
        }
        return result;
    }

    AstSenItem* complementEdge(AstSenItem* nodep) {
        if (nodep->edgeType() == VEdgeType::ET_POSEDGE) {
            AstSenItem* const clonep = nodep->cloneTree(false);
            pushDeletep(clonep);
            clonep->edgeType(VEdgeType::ET_NEGEDGE);
            return clonep;
        } else if (nodep->edgeType() == VEdgeType::ET_NEGEDGE) {
            AstSenItem* const clonep = nodep->cloneTree(false);
            pushDeletep(clonep);
            clonep->edgeType(VEdgeType::ET_POSEDGE);
            return clonep;
        }
        return NULL;
    }

    void addActiveToList(AstActive* activep, ActList& actList) {
        if (!actList.empty() && actList.back()->sensesp()->sameTree(activep->sensesp())) {
            // Same sensitivity. Merge into previous Active node, delete Active.
            actList.back()->addStmtsp(activep->stmtsp()->unlinkFrBackWithNext());
            activep->deleteTree();
        } else {
            // Different sensitivity. Simply append.
            actList.push_back(activep);
        }
    }

    // If the given SenTree has a SenItem equivalent to the given SenItem,
    // return that SenItem under the SenTree, otherwise return NULL.
    AstSenItem* findSenItem(const AstSenTree* treep, const AstSenItem* senItemp) {
        for (AstSenItem* itemp = treep->sensesp(); itemp;
             itemp = VN_CAST(itemp->nextp(), SenItem)) {
            if (itemp->sameTree(senItemp)) return itemp;
        }
        return NULL;
    }

    // Return any SenItem from the given SenTree that also exists in the
    // given senList, or NULL if no such SenItem exists in the SenTree.
    AstSenItem* findSenItem(const AstSenTree* treep, const SenList& senList) {
        for (SenList::const_iterator it = senList.begin(); it != senList.end(); ++it) {
            if (AstSenItem* const resultp = findSenItem(treep, *it)) { return resultp; }
        }
        return NULL;
    }

    AstNode* lowerActList(
        ActList::const_iterator curr,  // Start of remaining Active node list (inclusive)
        const ActList::const_iterator end,  // end of remaining Active node list (exclusive)
        const SenList knownTrue,  // SenItems known to be triggered in this branch
        const SenList knownFalse,  // SenItems known not to be triggered in this branch
        const bool knownDelayed,  // Known to be under a delayed clock branch
        const bool knownNonDelayed,  // Known to be under a non-delayed clock branch
        SenList toSpecialize,  // SenItems to specialize over when encountered
        const bool doClone  // Whether to clone the statements of Active nodes, or just move them
    ) {
        UASSERT(!(knownDelayed && knownNonDelayed), "Both knownDelayed and knownNonDelayed");
        UASSERT(toSpecialize.empty() || doClone, "Must be cloning when specializing");

        AstNode* resultp = NULL;  // The resulting lowered list

        // Lower the Active nodes to If statements
        while (curr != end) {
            const AstActive* const activep = *curr;
            // Clone the body if told to do so as we might be duplicating it.
            // Otherwise simply move it.
            AstNode* const stmtsp = doClone ? activep->stmtsp()->cloneTree(true)
                                            : activep->stmtsp()->unlinkFrBackWithNext();
//            int cnt = 0;
//            if (AstCCall *callp = VN_CAST(stmtsp, CCall)) {
//                EmitCBaseCounterVisitor c(callp->funcp());
//                cnt = c.count();
//            }
            UASSERT_OBJ(!activep->hasInitial() && !activep->hasSettle(), activep,
                        "Should have already converted initial and settle blocks");
            if (!activep->hasClocked()) {
                // Combinational block, append to result list
                resultp = resultp ? resultp->addNext(stmtsp) : stmtsp;
                // Move on to next item
                ++curr;
            } else if (findSenItem(activep->sensesp(), knownTrue)) {
                // This block is known to be triggered in this branch, append to result list
                resultp = resultp ? resultp->addNext(stmtsp) : stmtsp;
                // Move on to next item
                ++curr;
//            } else if (activep->sensesp()->isMulti() && !stmtsp->nextp() && cnt < 50) {
//                // This was a comb block and has only a single stmt, inline it..
//                resultp = resultp ? resultp->addNext(stmtsp) : stmtsp;
//                // Move on to next item
//                ++curr;
            } else {
                // Simplify condition
                AstSenTree* const senTreep = activep->sensesp()->cloneTree(false);
                // Remvoe knownFalse triggers
                while (AstSenItem* itemp = findSenItem(senTreep, knownFalse)) {
                    itemp->unlinkFrBack();
                    VL_DO_DANGLING(itemp->deleteTree(), itemp);
                }
                // Remove Delayed/Non-delayed triggers if knownNonDelayed/knownDelayed
                for (AstSenItem* itemp = senTreep->sensesp(); itemp;) {
                    AstSenItem* const nextp = VN_CAST(itemp->nextp(), SenItem);
                    UASSERT_OBJ(itemp->varrefp(), itemp, "Missing VarRef");
                    UASSERT_OBJ(itemp->varrefp()->varScopep(), itemp, "VarRef is not to VarScope");
                    const bool delayed = itemp->varrefp()->varScopep()->isDelayedClock();
                    if ((delayed && knownNonDelayed) || (!delayed && knownDelayed)) {
                        itemp->unlinkFrBack();
                        VL_DO_DANGLING(itemp->deleteTree(), itemp);
                    }
                    itemp = nextp;
                }
                if (!senTreep->sensesp()) {
                    // If no triggers left, we know it is not triggered.
                    // Move on to next item
                    ++curr;
                } else if (AstSenItem* senp = findSenItem(senTreep, toSpecialize)) {
                    // It has a SenItem we want to specialize over.
                    // Find the last Active conditional on this SenItem
                    ActList::const_iterator last = end;
                    while (--last != curr) {
                        if (findSenItem((*last)->sensesp(), senp)) { break; }
                    }
                    ++last;  // Make 'last' the exclusive end point of the sub-list
                    // Create if statement conditional on this SenItem only
                    AstSenItem* const uniquep = senp->cloneTree(false);
                    AstIf* const ifp = makeActiveIf(uniquep);
                    VL_DO_DANGLING(uniquep->deleteTree(), uniquep);
                    // Remove the SenItem being specialized over for the recursion
                    for (SenList::iterator it = toSpecialize.begin(); it != toSpecialize.end();) {
                        if (senp->sameTree(*it)) {
                            it = toSpecialize.erase(it);
                        } else {
                            ++it;
                        }
                    }
                    {  // Build the list assuming senp is true, add it to the then branch
                        SenList recKnownTrue = knownTrue;
                        recKnownTrue.push_back(senp);
                        SenList recKnownFalse = knownFalse;
                        if (AstSenItem* const complementp = complementEdge(senp)) {
                            recKnownFalse.push_back(complementp);
                        }
                        const bool delayed = senp->varrefp()->varScopep()->isDelayedClock();
                        AstNode* const thensp
                            = lowerActList(curr, last, recKnownTrue, recKnownFalse, delayed,
                                           !delayed, toSpecialize, doClone);
                        if (thensp) ifp->addIfsp(thensp);
                    }
                    {  // Build the list assuming senp is false, add it to the else branch
                        SenList recKnownFalse = knownFalse;
                        recKnownFalse.push_back(senp);
                        AstNode* const elsesp
                            = lowerActList(curr, last, knownTrue, recKnownFalse, knownDelayed,
                                           knownNonDelayed, toSpecialize, doClone);
                        if (elsesp) ifp->addElsesp(elsesp);
                    }
                    // Append to result list
                    resultp = resultp ? resultp->addNext(ifp) : ifp;
                    // Move on to rest if list
                    curr = last;
                } else {
                    // Ordinary block
                    AstIf* const ifp = makeActiveIf(senTreep->sensesp());
                    ifp->addIfsp(stmtsp);
                    resultp = resultp ? resultp->addNext(ifp) : ifp;
                    // Move on to next item
                    ++curr;
                }
                VL_DO_DANGLING(senTreep->deleteTree(), senTreep);
            }
        }
        return resultp;
    }

    // Remove and lower all Active nodes in the list starting at nodep.
    // Returns the start of the list of lowered nodes (may be NULL).
    AstNode* lowerActives(AstNode* nodep) {
        ActList actList;  // The merged Active nodes in the list starting at nodep

        bool haveExecGraph = false;  // Need to know if we have an ExecGrap

        // Extract active nodes, recursively process MTask bodies in ExecGraph.
        // Convert initial and settle blocks, merge consecutive nodes with
        // identical sensitivities.
        for (AstNode* nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (AstActive* const activep = VN_CAST(nodep, Active)) {
                activep->unlinkFrBack();
                if (!activep->stmtsp()) {
                    // Delete empty nodes immediately
                    VL_DO_DANGLING(activep->deleteTree(), activep);
                } else if (activep->hasInitial()) {
                    // Add statements to init function
                    m_initFuncp->addStmtsp(activep->stmtsp()->unlinkFrBackWithNext());
                    VL_DO_DANGLING(activep->deleteTree(), activep);
                } else if (activep->hasSettle()) {
                    // Add statements to settle function
                    m_settleFuncp->addStmtsp(activep->stmtsp()->unlinkFrBackWithNext());
                    VL_DO_DANGLING(activep->deleteTree(), activep);
                } else {
                    // Queue for processing
                    addActiveToList(activep, actList);
                }
            } else if (AstExecGraph* const egraphp = VN_CAST(nodep, ExecGraph)) {
                haveExecGraph = true;
                egraphp->unlinkFrBack();
                // Process MTask bodies recursively
                for (AstMTaskBody* mtaskp = egraphp->mTaskBody(); mtaskp;
                     mtaskp = VN_CAST(mtaskp->nextp(), MTaskBody)) {
                    AstNode* const loweredp = lowerActives(mtaskp->stmtsp());
                    if (loweredp) mtaskp->addStmtsp(loweredp);
                }
                // Move the ExecGraph into the body as a combinational block.
                // Its location marks the spot where the graph will execute,
                // relative to other (serial) logic in the cycle.
                FileLine* const flp = egraphp->fileline();
                AstSenItem* const senCombp = new AstSenItem(flp, AstSenItem::Combo());
                AstSenTree* const senTreep = new AstSenTree(flp, senCombp);
                const string name = "execgraph";
                AstActive* const combp = new AstActive(flp, name, senTreep);
                combp->addStmtsp(egraphp);
                // Queue for processing
                addActiveToList(combp, actList);
            }
        }

        // Choose the SenItems we will be specializing over. As ExecGraph is
        // not cloneable, we must not specialize triggers in this list if the
        // list contains an ExecGraph.
        const SenList toSpecialize = haveExecGraph ? SenList() : getSenItemsToSpecialize(actList);

        AstNode* const resultp = lowerActList(actList.begin(), actList.end(), SenList(), SenList(),
                                              false, false, toSpecialize, !toSpecialize.empty());

        // Delete the active nodes. They have already been unlinked above and
        // their content cloned and moved under resultp.
        while (!actList.empty()) {
            actList.back()->deleteTree();
            actList.pop_back();
        }

        return resultp;
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep) VL_OVERRIDE {
        UINFO(4, " TOPSCOPE   " << nodep << endl);
        m_topScopep = nodep;
        m_scopeTopp = nodep->scopep();
        UASSERT_OBJ(m_scopeTopp, nodep,
                    "No scope found on top level, perhaps you have no statements?");
        // VV*****  We reset all user1p()
        AstNode::user1ClearTree();
        // Make top functions
        {
            AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval", m_scopeTopp);
            funcp->argTypes(EmitCBaseVisitor::symClassVar());
            funcp->dontCombine(true);
            funcp->symProlog(true);
            funcp->isStatic(true);
            funcp->entryPoint(true);
            m_scopeTopp->addActivep(funcp);
            m_evalFuncp = funcp;
        }
        {
            AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval_initial", m_scopeTopp);
            funcp->argTypes(EmitCBaseVisitor::symClassVar());
            funcp->dontCombine(true);
            funcp->slow(true);
            funcp->symProlog(true);
            funcp->isStatic(true);
            funcp->entryPoint(true);
            m_scopeTopp->addActivep(funcp);
            m_initFuncp = funcp;
        }
        {
            AstCFunc* funcp = new AstCFunc(nodep->fileline(), "final", m_scopeTopp);
            funcp->skipDecl(true);
            funcp->dontCombine(true);
            funcp->slow(true);
            funcp->isStatic(false);
            funcp->entryPoint(true);
            funcp->protect(false);
            funcp->addInitsp(new AstCStmt(nodep->fileline(), EmitCBaseVisitor::symClassVar()
                                                                 + " = this->__VlSymsp;\n"));
            funcp->addInitsp(
                new AstCStmt(nodep->fileline(), EmitCBaseVisitor::symTopAssign() + "\n"));
            m_scopeTopp->addActivep(funcp);
            m_finalFuncp = funcp;
        }
        {
            AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval_settle", m_scopeTopp);
            funcp->argTypes(EmitCBaseVisitor::symClassVar());
            funcp->dontCombine(true);
            funcp->slow(true);
            funcp->isStatic(true);
            funcp->symProlog(true);
            funcp->entryPoint(true);
            m_scopeTopp->addActivep(funcp);
            m_settleFuncp = funcp;
        }
        // Process the top level Active nodes up front
        AstNode* const loweredp = lowerActives(m_scopeTopp->blocksp());
        if (loweredp) m_evalFuncp->addStmtsp(loweredp);
        // Process the children
        iterateChildren(nodep);
        // Done, clear so we can detect errors
        UINFO(4, " TOPSCOPEDONE " << nodep << endl);
        m_topScopep = NULL;
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        // UINFO(4, " MOD   " << nodep << endl);
        AstNodeModule* origModp = m_modp;
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
        m_modp = origModp;
    }
    virtual void visit(AstScope* nodep) VL_OVERRIDE {
        // UINFO(4, " SCOPE   " << nodep << endl);
        iterateChildren(nodep);
        if (AstNode* movep = nodep->finalClksp()) {
            UASSERT_OBJ(m_topScopep, nodep, "Final clocks under non-top scope");
            movep->unlinkFrBackWithNext();
            m_evalFuncp->addFinalsp(movep);
        }
    }
    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName(), true);
        nodep->replaceWith(cmtp);
        if (AstNode* stmtsp = nodep->bodysp()) {
            stmtsp->unlinkFrBackWithNext();
            cmtp->addNextHere(stmtsp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstAlwaysPost* nodep) VL_OVERRIDE {
        AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName(), true);
        nodep->replaceWith(cmtp);
        if (AstNode* stmtsp = nodep->bodysp()) {
            stmtsp->unlinkFrBackWithNext();
            cmtp->addNextHere(stmtsp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstCoverToggle* nodep) VL_OVERRIDE {
        // nodep->dumpTree(cout, "ct:");
        // COVERTOGGLE(INC, ORIG, CHANGE) ->
        //   IF(ORIG ^ CHANGE) { INC; CHANGE = ORIG; }
        AstNode* incp = nodep->incp()->unlinkFrBack();
        AstNode* origp = nodep->origp()->unlinkFrBack();
        AstNode* changep = nodep->changep()->unlinkFrBack();
        AstIf* newp = new AstIf(nodep->fileline(), new AstXor(nodep->fileline(), origp, changep),
                                incp, NULL);
        // We could add another IF to detect posedges, and only increment if so.
        // It's another whole branch though versus a potential memory miss.
        // We'll go with the miss.
        newp->addIfsp(
            new AstAssign(nodep->fileline(), changep->cloneTree(false), origp->cloneTree(false)));
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstInitial* nodep) VL_OVERRIDE {
        AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName(), true);
        nodep->replaceWith(cmtp);
        if (AstNode* stmtsp = nodep->bodysp()) {
            stmtsp->unlinkFrBackWithNext();
            cmtp->addNextHere(stmtsp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Link to global function
        if (nodep->formCallTree()) {
            UINFO(4, "    formCallTree " << nodep << endl);
            AstCCall* callp = new AstCCall(nodep->fileline(), nodep);
            callp->argTypes("vlSymsp");
            m_finalFuncp->addStmtsp(callp);
        }
    }
    virtual void visit(AstSenTree* nodep) VL_OVERRIDE {
        // Delete it later; Actives still pointing to it
        nodep->unlinkFrBack();
        pushDeletep(nodep);
    }
    virtual void visit(AstActive* nodep) VL_OVERRIDE {
        UASSERT_OBJ(!nodep->stmtsp(), nodep, "Non-empty active under non-top scope");
        nodep->unlinkFrBack();
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstExecGraph* nodep) VL_OVERRIDE {}  // Already processed

    //--------------------
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClockVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        m_evalFuncp = NULL;
        m_initFuncp = NULL;
        m_finalFuncp = NULL;
        m_settleFuncp = NULL;
        m_topScopep = NULL;
        m_scopeTopp = NULL;
        //
        iterate(nodep);
        // Allow downstream modules to find _eval()
        // easily without iterating through the tree.
        nodep->evalp(m_evalFuncp);
    }
    virtual ~ClockVisitor() {}
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ClockVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clock", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
