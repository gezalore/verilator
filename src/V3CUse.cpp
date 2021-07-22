// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3CUse's Transformations:
//
// Each module:
//   Each cell:
//      Create CUse for cell forward declaration
//   Search for dtypes referencing class, and create CUse for forward declaration
//   Each CFunc:
//      Create CUse for include files
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3CUse.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"

#include <set>

//######################################################################

// Visit within a CFunc to gather dependencies
class CUseFuncVisitor final : public AstNVisitor {
    // MEMBERS
    const AstNodeModule* const m_modp;  // Current module
    std::set<string> m_dependencies;  // Headers to include. Ordered set for deterministic output.

    // METHODS
    void addSymsDependency() { m_dependencies.insert(EmitCBaseVisitor::symClassName()); }
    void addModDependency(const AstNodeModule* modp) {
        if (const AstClass* const classp = VN_CAST_CONST(modp, Class)) {
            m_dependencies.insert(classp->classOrPackagep()->name());
        } else {
            m_dependencies.insert(modp->name());
        }
    }
    void addDTypeDependency(const AstNodeDType* nodep) {
        if (const AstClassRefDType* const dtypep = VN_CAST_CONST(nodep, ClassRefDType)) {
            m_dependencies.insert(dtypep->classp()->classOrPackagep()->name());
        }
    }
    void addSelfDependency(const string& selfPointer) {
        if (selfPointer.empty()) {
            // No self pointer (e.g.: function locals, const pool values, or static loose methods),
            // so no dependency required
        } else if (VString::startsWith(selfPointer, "this")) {
            // Dereferencing 'this', we need the definition of this module
            addModDependency(m_modp);
        } else {
            // Must be an absolute reference
            UASSERT(VString::startsWith(selfPointer, "(&vlSymsp->"),
                    "Unknown self pointer: '" << selfPointer << "'");
            // Dereferencing vlSymsp, so we need it's definition...
            m_dependencies.insert(EmitCBaseVisitor::symClassName());
        }
    }

    // VISITORS
    virtual void visit(AstCCall* nodep) override {
        addSelfDependency(nodep->selfPointer());
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstCNew* nodep) override {
        addDTypeDependency(nodep->dtypep());
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstCMethodCall* nodep) override {
        addDTypeDependency(nodep->fromp()->dtypep());
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstNewCopy* nodep) override {
        addDTypeDependency(nodep->dtypep());
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstMemberSel* nodep) override {
        addDTypeDependency(nodep->fromp()->dtypep());
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstNodeVarRef* nodep) override {
        addSelfDependency(nodep->selfPointer());
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstCoverDecl* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstCoverInc* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstDumpCtl* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstScopeName* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstPrintTimeScale* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstTimeFormat* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstNodeSimpleText* nodep) override {
        if (nodep->text().find("vlSymsp") != string::npos) {
            m_dependencies.insert(EmitCBaseVisitor::symClassName());
        }
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit CUseFuncVisitor(AstNodeModule* modp, AstCFunc* funcp)
        : m_modp{modp} {
        // Strictly speaking, for loose methods, we could get away with just a forward
        // declaration of the receiver class, but their body very likely includes at least one
        // relative reference, so we are probably not loosing much.
        addModDependency(modp);
        iterate(funcp);
        for (const string& dependency : m_dependencies) {
            AstCUse* const newp
                = new AstCUse{funcp->fileline(), VUseType::IMP_INCLUDE, dependency};
            funcp->addInitsp(newp);
        }
    }
    virtual ~CUseFuncVisitor() override = default;
    VL_UNCOPYABLE(CUseFuncVisitor);
};

// Visit within a module all nodes and data types they reference, finding
// any classes so we can make sure they are defined when Verilated code
// compiles
class CUseModVisitor final : public AstNVisitor {
    // NODE STATE
    //  AstNode::user1()     -> bool.  True if already visited
    AstUser1InUse m_inuser1;

    // MEMBERS
    bool m_impOnly = false;  // In details needed only for implementation
    AstNodeModule* const m_modp;  // Current module
    std::set<std::pair<VUseType, std::string>> m_didUse;  // What we already used

    // METHODS
    void addNewUse(AstNode* nodep, VUseType useType, const string& name) {
        if (m_didUse.emplace(useType, name).second) {
            AstCUse* const newp = new AstCUse{nodep->fileline(), useType, name};
            m_modp->addStmtp(newp);
            UINFO(8, "Insert " << newp << endl);
        }
    }

    // VISITORS
    virtual void visit(AstClassRefDType* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (!m_impOnly) addNewUse(nodep, VUseType::INT_FWD_CLASS, nodep->classp()->name());
        // Need to include extends() when we implement, but no need for pointers to know
        VL_RESTORER(m_impOnly);
        {
            m_impOnly = true;
            iterateChildren(nodep->classp());  // This also gets all extend classes
        }
    }
    virtual void visit(AstNodeDType* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (nodep->virtRefDTypep()) iterate(nodep->virtRefDTypep());
        if (nodep->virtRefDType2p()) iterate(nodep->virtRefDType2p());
    }
    virtual void visit(AstNode* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (nodep->dtypep() && !nodep->dtypep()->user1()) iterate(nodep->dtypep());
        iterateChildren(nodep);
    }
    virtual void visit(AstCell* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        // Currently no IMP_INCLUDE because we include __Syms which has them all
        addNewUse(nodep, VUseType::INT_FWD_CLASS, nodep->modp()->name());
        iterateChildren(nodep);
    }
    virtual void visit(AstCFunc* nodep) override {
        if (!(nodep->isMethod() && nodep->isLoose())) {
            // Non-loose methods are declared in the module, hence we need their argument types
            iterateAndNextConstNull(nodep->argsp());
        }
        CUseFuncVisitor{m_modp, nodep};
    }

public:
    // CONSTRUCTORS
    explicit CUseModVisitor(AstNodeModule* modp)
        : m_modp(modp) {
        iterate(modp);
    }
    virtual ~CUseModVisitor() override = default;
    VL_UNCOPYABLE(CUseModVisitor);
};

//######################################################################
// Class class functions

void V3CUse::cUseAll() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Call visitor separately for each module, so visitor state is cleared
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_CAST(modp->nextp(), NodeModule)) {
        // Insert under this module; someday we should e.g. make Ast
        // for each output file and put under that
        CUseModVisitor{modp};
    }
    V3Global::dumpCheckGlobalTree("cuse", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
