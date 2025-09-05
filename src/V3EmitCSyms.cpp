// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3ExecGraph.h"
#include "V3LanguageWords.h"
#include "V3StackCount.h"
#include "V3Stats.h"

#include <algorithm>
#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Symbol table emitting

// Some handy short-hands to reduce verbosity
static constexpr auto symClassName = &EmitCUtil::symClassName;
static constexpr auto topClassName = &EmitCUtil::topClassName;

class EmitCSyms final : EmitCBaseVisitorConst {
    // NODE STATE
    // Cleared on Netlist
    //  AstNodeModule::user1()  -> bool.  Set true __Vconfigure called
    const VNUser1InUse m_inuser1;

    // TYPES
    struct ScopeData final {
        const AstNode* m_nodep;
        const std::string m_symName;
        const std::string m_prettyName;
        const std::string m_defName;
        const int m_timeunit;
        std::string m_type;  // FIXME: this should be an enum
        ScopeData(const AstNode* nodep, const std::string& symName, const std::string& prettyName,
                  const std::string& defName, int timeunit, const std::string& type)
            : m_nodep{nodep}
            , m_symName{symName}
            , m_prettyName{prettyName}
            , m_defName{defName}
            , m_timeunit{timeunit}
            , m_type{type} {}
    };
    struct ScopeFuncData final {
        const AstScopeName* const m_scopep;
        const AstCFunc* const m_cfuncp;
        const AstNodeModule* const m_modp;
        ScopeFuncData(const AstScopeName* scopep, const AstCFunc* funcp, const AstNodeModule* modp)
            : m_scopep{scopep}
            , m_cfuncp{funcp}
            , m_modp{modp} {}
    };
    struct ScopeVarData final {
        const std::string m_scopeName;
        const std::string m_varBasePretty;
        const AstVar* const m_varp;
        const AstNodeModule* const m_modp;
        const AstScope* const m_scopep;
        ScopeVarData(const std::string& scopeName, const std::string& varBasePretty,
                     const AstVar* varp, const AstNodeModule* modp, const AstScope* scopep)
            : m_scopeName{scopeName}
            , m_varBasePretty{varBasePretty}
            , m_varp{varp}
            , m_modp{modp}
            , m_scopep{scopep} {}
    };
    using ScopeNames = std::map<const std::string, ScopeData>;
    using ScopeModPair = std::pair<const AstScope*, AstNodeModule*>;
    using ModVarPair = std::pair<const AstNodeModule*, const AstVar*>;

    // STATE
    AstCFunc* m_cfuncp = nullptr;  // Current function
    AstNodeModule* m_modp = nullptr;  // Current module
    std::vector<ScopeModPair> m_scopes;  // Every scope by module
    std::vector<AstCFunc*> m_dpis;  // DPI functions
    std::vector<ModVarPair> m_modVars;  // Each public {mod,var}
    std::map<const std::string, ScopeFuncData> m_scopeFuncs;  // Each {scope,dpi-export-func}
    std::map<const std::string, ScopeVarData> m_scopeVars;  // Each {scope,public-var}
    ScopeNames m_scopeNames;  // Each unique AstScopeName. Dpi scopes added later
    ScopeNames m_dpiScopeNames;  // Each unique AstScopeName for DPI export
    ScopeNames m_vpiScopeCandidates;  // All scopes for VPI
    // The actual hierarchy of scopes
    std::map<const std::string, std::vector<std::string>> m_vpiScopeHierarchy;
    int m_coverBins = 0;  // Coverage bin number
    const bool m_dpiHdrOnly;  // Only emit the DPI header
    int m_numStmts = 0;  // Number of statements output
    int m_funcNum = 0;  // CFunc split function number
    V3OutCFile* m_ofpBase = nullptr;  // Base (not split) C file
    std::unordered_map<int, bool> m_usesVfinal;  // Split method uses __Vfinal
    VDouble0 m_statVarScopeBytes;  // Statistic tracking

    // METHODS
    void emitSymHdr();
    void checkSplit(bool usesVfinal);
    void closeSplit();
    void emitSymImpPreamble();
    void emitScopeHier(bool destroy);
    void emitSymImp();
    void emitDpiHdr();
    void emitDpiImp();

    static void nameCheck(AstNode* nodep) {
        // Prevent GCC compile time error; name check all things that reach C++ code
        if (nodep->name().empty()) return;
        const AstCFunc* const cfuncp = VN_CAST(nodep, CFunc);
        if (!cfuncp || (!cfuncp->isConstructor() && !cfuncp->isDestructor())) {
            const std::string rsvd = V3LanguageWords::isKeyword(nodep->name());
            if (rsvd != "") {
                // Generally V3Name should find all of these and throw SYMRSVDWORD.
                // We'll still check here because the compiler errors
                // resulting if we miss this warning are SO nasty
                nodep->v3error("Symbol matching " + rsvd
                                   + " reserved word reached emitter,"
                                     " should have hit SYMRSVDWORD: "
                               << nodep->prettyNameQ());
            }
        }
    }

    static std::string scopeSymString(const std::string& scpname) {
        std::string out = scpname;
        std::string::size_type pos;
        while ((pos = out.find("__PVT__")) != std::string::npos) out.replace(pos, 7, "");
        if (VString::startsWith(out, "TOP__DOT__")) out.replace(0, 10, "");
        if (VString::startsWith(out, "TOP.")) out.replace(0, 4, "");
        while ((pos = out.find('.')) != std::string::npos) out.replace(pos, 1, "__");
        while ((pos = out.find("__DOT__")) != std::string::npos) out.replace(pos, 7, "__");
        return out;
    }

    static string scopeDecodeIdentifier(const std::string& scpname) {
        std::string::size_type pos = std::string::npos;

        // Remove hierarchy
        size_t i = 0;
        // always makes progress
        while (i < scpname.length()) {
            if (scpname[i] == '\\') {
                while (i < scpname.length() && scpname[i] != ' ') ++i;
                ++i;  // Proc ' ', it should always be there. Then grab '.' on next cycle
            } else {
                while (i < scpname.length() && scpname[i] != '.') ++i;
                if (i < scpname.length()) pos = i++;
            }
        }

        return pos != std::string::npos ? scpname.substr(pos + 1) : scpname;
    }

    /// (scp, m_vpiScopeCandidates, m_scopeNames) -> m_scopeNames
    /// Look for parent scopes of scp in m_vpiScopeCandidates (separated by __DOT__ or ".")
    /// Then add/update entry in m_scopeNames if not already there
    void varHierarchyScopes(std::string scp) {

        std::string::size_type prd_pos = scp.rfind('.');
        std::string::size_type dot_pos = scp.rfind("__DOT__");

        while (!scp.empty()) {
            // FIXME: What??
            const auto scpit = m_vpiScopeCandidates.find(scopeSymString(scp));
            if (scpit != m_vpiScopeCandidates.end()) {
                if (m_scopeNames.find(scp) == m_scopeNames.end()) {
                    // If not in m_scopeNames, add it, otherwise just update m_type
                    const auto pair = m_scopeNames.emplace(scpit->second.m_symName, scpit->second);
                    if (!pair.second) pair.first->second.m_type = scpit->second.m_type;
                }
            }

            // resize and advance pointers
            if ((prd_pos < dot_pos || prd_pos == string::npos) && dot_pos != string::npos) {
                scp.resize(dot_pos);
                dot_pos = scp.rfind("__DOT__");
            } else {
                if (prd_pos == string::npos) break;
                scp.resize(prd_pos);
                prd_pos = scp.rfind('.');
            }
        }
    }

    void varsExpand() {
        // We didn't have all m_scopes loaded when we encountered variables, so expand them now
        // It would be less code if each module inserted its own variables.
        // Someday.
        for (const ScopeModPair& smPair : m_scopes) {
            const AstScope* const scopep = smPair.first;
            const AstNodeModule* const smodp = smPair.second;
            for (const ModVarPair& mvPair : m_modVars) {
                const AstNodeModule* const modp = mvPair.first;
                const AstVar* const varp = mvPair.second;
                if (modp != smodp) continue;

                // Need to split the module + var name into the
                // original-ish full scope and variable name under that scope.
                // The module instance name is included later, when we
                // know the scopes this module is under
                std::string whole = scopep->name() + "__DOT__" + varp->name();
                std::string scpName;
                std::string varBase;
                if (VString::startsWith(whole, "__DOT__TOP")) whole.replace(0, 10, "");
                const std::string::size_type dpos = whole.rfind("__DOT__");
                if (dpos != std::string::npos) {
                    scpName = whole.substr(0, dpos);
                    varBase = whole.substr(dpos + std::strlen("__DOT__"));
                } else {
                    varBase = whole;
                }
                // UINFO(9, "For " << scopep->name() << " - " << varp->name() << "  Scp "
                // << scpName << "Var " << varBase);
                const std::string varBasePretty = AstNode::vpiName(VName::dehash(varBase));
                const std::string scpPretty = AstNode::prettyName(VName::dehash(scpName));
                const std::string scpSym = scopeSymString(VName::dehash(scpName));
                // UINFO(9, " scnameins sp " << scpName << " sp " << scpPretty << " ss "
                // << scpSym);
                if (v3Global.opt.vpi()) varHierarchyScopes(scpName);

                m_scopeNames.emplace(  //
                    std::piecewise_construct,  //
                    std::forward_as_tuple(scpSym),  //
                    std::forward_as_tuple(varp, scpSym, scpPretty, "<null>", 0, "SCOPE_OTHER"));

                m_scopeVars.emplace(  //
                    std::piecewise_construct,  //
                    std::forward_as_tuple(scpSym + " " + varp->name()),  //
                    std::forward_as_tuple(scpSym, varBasePretty, varp, modp, scopep));
            }
        }
    }

    void buildVpiHierarchy() {
        for (const auto& pair : m_scopeNames) {
            const std::string symName = pair.second.m_symName;
            std::string above = symName;
            if (VString::startsWith(above, "TOP.")) above.replace(0, 4, "");

            while (!above.empty()) {
                const std::string::size_type pos = above.rfind("__");
                if (pos == std::string::npos) break;
                above.resize(pos);
                if (m_vpiScopeHierarchy.find(above) != m_vpiScopeHierarchy.end()) {
                    m_vpiScopeHierarchy[above].push_back(symName);
                    break;
                }
            }
            // FIXME: yuck
            m_vpiScopeHierarchy[symName] = std::vector<string>();
        }
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // Collect list of scopes
        iterateChildrenConst(nodep);
        varsExpand();

        if (v3Global.opt.vpi()) buildVpiHierarchy();

        if (v3Global.dpi()) {
            // add dpi scopes to m_scopeNames if not already there
            for (const auto& scp : m_dpiScopeNames) m_scopeNames.emplace(scp.first, scp.second);
        }

        // Sort by names, so line/process order matters less
        std::stable_sort(m_scopes.begin(), m_scopes.end(),
                         [](const ScopeModPair& a, const ScopeModPair& b) {
                             return a.first->name() < b.first->name();
                         });
        std::stable_sort(m_dpis.begin(), m_dpis.end(),  //
                         [](const AstCFunc* ap, const AstCFunc* bp) {
                             if (ap->dpiImportPrototype() != bp->dpiImportPrototype()) {
                                 return bp->dpiImportPrototype();
                             }
                             return ap->name() < bp->name();
                         });

        // Output
        if (!m_dpiHdrOnly) {
            // Must emit implementation first to determine number of splits
            emitSymImp();
            emitSymHdr();
        }
        if (v3Global.dpi()) {
            emitDpiHdr();
            if (!m_dpiHdrOnly) emitDpiImp();
        }
    }
    void visit(AstConstPool* nodep) override {}  // Ignore
    void visit(AstNodeModule* nodep) override {
        nameCheck(nodep);
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstCellInlineScope* nodep) override {
        if (!v3Global.opt.vpi()) return;

        const std::string type = (nodep->origModName() == "__BEGIN__") ? "SCOPE_OTHER"  //
                                                                       : "SCOPE_MODULE";
        const std::string name = nodep->scopep()->shortName() + "__DOT__" + nodep->name();
        const int timeunit = m_modp->timeunit().powerOfTen();
        m_vpiScopeCandidates.emplace(  //
            std::piecewise_construct,  //
            std::forward_as_tuple(scopeSymString(name)),  //
            std::forward_as_tuple(nodep, scopeSymString(name), AstNode::vpiName(name),
                                  type == "SCOPE_MODULE" ? nodep->origModName() : "<null>",
                                  timeunit, type));
    }
    void visit(AstScope* nodep) override {
        if (VN_IS(m_modp, Class)) return;  // The ClassPackage is what is visible
        nameCheck(nodep);

        m_scopes.emplace_back(nodep, m_modp);

        if (v3Global.opt.vpi() && !nodep->isTop()) {
            const std::string type = VN_IS(nodep->modp(), Package) ? "SCOPE_PACKAGE"  //
                                                                   : "SCOPE_MODULE";
            const int timeunit = m_modp->timeunit().powerOfTen();
            m_vpiScopeCandidates.emplace(  //
                std::piecewise_construct,  //
                std::forward_as_tuple(scopeSymString(nodep->name())),  //
                std::forward_as_tuple(nodep, scopeSymString(nodep->name()),
                                      AstNode::vpiName(nodep->shortName()),
                                      nodep->modp()->origName(), timeunit, type));
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstScopeName* nodep) override {
        const std::string name = nodep->scopeSymName();
        // UINFO(9, "scnameins sp " << nodep->name() << " sp " << nodep->scopePrettySymName()
        // << " ss" << name);
        const int timeunit = m_modp ? m_modp->timeunit().powerOfTen() : 0;
        m_dpiScopeNames.emplace(  //
            std::piecewise_construct,  //
            std::forward_as_tuple(name),  //
            std::forward_as_tuple(nodep, name, nodep->scopePrettySymName(), "<null>", timeunit,
                                  "SCOPE_OTHER"));

        if (nodep->dpiExport()) {
            UASSERT_OBJ(m_cfuncp, nodep, "ScopeName not under DPI function");
            m_scopeFuncs.emplace(  //
                std::piecewise_construct,  //
                std::forward_as_tuple(name + " " + m_cfuncp->name()),  //
                std::forward_as_tuple(nodep, m_cfuncp, m_modp));
        } else {
            // Note emplace does not construct when duplicate key
            m_dpiScopeNames.emplace(  //
                std::piecewise_construct,  //
                std::forward_as_tuple(nodep->scopeDpiName()),  //
                std::forward_as_tuple(nodep, nodep->scopeDpiName(), nodep->scopePrettyDpiName(),
                                      "<null>", timeunit, "SCOPE_OTHER"));
        }
    }
    void visit(AstVar* nodep) override {
        nameCheck(nodep);
        iterateChildrenConst(nodep);
        // Ignore locals
        if (m_cfuncp) return;
        // Record if public
        if (nodep->isSigUserRdPublic() || nodep->isSigUserRWPublic()) {
            m_modVars.emplace_back(m_modp, nodep);
        }
    }
    void visit(AstVarScope* nodep) override {
        iterateChildrenConst(nodep);
        m_statVarScopeBytes += nodep->varp()->dtypep()->widthTotalBytes();
    }
    void visit(AstNodeCoverDecl* nodep) override {
        // Assign numbers to all bins, so we know how big of an array to use
        if (!nodep->dataDeclNullp()) {  // else duplicate we don't need code for
            nodep->binNum(m_coverBins);
            m_coverBins += nodep->size();
        }
    }
    void visit(AstCFunc* nodep) override {
        nameCheck(nodep);
        if (nodep->dpiImportPrototype() || nodep->dpiExportDispatcher()) m_dpis.push_back(nodep);
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        iterateChildrenConst(nodep);
    }

    //---------------------------------------
    void visit(AstConst*) override {}
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit EmitCSyms(AstNetlist* nodep, bool dpiHdrOnly)
        : m_dpiHdrOnly{dpiHdrOnly} {
        iterateConst(nodep);
    }
};

void EmitCSyms::emitSymHdr() {
    UINFO(6, __FUNCTION__ << ": ");
    const std::string filename = v3Global.opt.makeDir() + "/" + symClassName() + ".h";
    AstCFile* const cfilep = newCFile(filename, true /*slow*/, false /*source*/);
    V3OutCFile* const ofilep = optSystemC() ? new V3OutScFile{filename} : new V3OutCFile{filename};
    setOutputFile(ofilep, cfilep);

    ofp()->putsHeader();
    puts("// DESCRIPTION: Verilator output: Symbol table internal header\n");
    puts("//\n");
    puts("// Internal details; most calling programs do not need this header,\n");
    puts("// unless using verilator public meta comments.\n");

    ofp()->putsGuard();

    puts("\n");
    ofp()->putsIntTopInclude();
    puts("#include \"verilated.h\"\n");
    if (v3Global.needTraceDumper()) {
        puts("#include \"" + v3Global.opt.traceSourceLang() + ".h\"\n");
    }
    if (v3Global.opt.usesProfiler()) puts("#include \"verilated_profiler.h\"\n");

    puts("\n// INCLUDE MODEL CLASS\n");
    puts("\n#include \"" + topClassName() + ".h\"\n");

    puts("\n// INCLUDE MODULE CLASSES\n");
    for (AstNodeModule *nodep = v3Global.rootp()->modulesp(), *nextp; nodep; nodep = nextp) {
        nextp = VN_AS(nodep->nextp(), NodeModule);
        if (VN_IS(nodep, Class)) continue;  // Class included earlier
        putns(nodep, "#include \"" + EmitCUtil::prefixNameProtect(nodep) + ".h\"\n");
    }

    if (v3Global.dpi()) {
        puts("\n// DPI TYPES for DPI Export callbacks (Internal use)\n");
        std::set<std::string> types;  // Remove duplicates and sort
        for (const auto& pair : m_scopeFuncs) {
            const AstCFunc* const funcp = pair.second.m_cfuncp;
            if (!funcp->dpiExportImpl()) continue;
            const std::string cbtype
                = protect(v3Global.opt.prefix() + "__Vcb_" + funcp->cname() + "_t");
            const std::string functype = funcp->rtnTypeVoid() + " (*) (" + cFuncArgs(funcp) + ")";
            types.emplace("using " + cbtype + " = " + functype + ";\n");
        }
        for (const std::string& type : types) puts(type);
    }

    puts("\n// SYMS CLASS (contains all model state)\n");
    puts("class alignas(VL_CACHE_LINE_BYTES)" + symClassName()
         + " final : public VerilatedSyms {\n");
    ofp()->putsPrivate(false);  // public:

    puts("// INTERNAL STATE\n");
    puts(topClassName() + "* const __Vm_modelp;\n");

    if (v3Global.needTraceDumper()) {
        // __Vm_dumperp is local, otherwise we wouldn't know what design's eval()
        // should call a global dumpperp
        puts("bool __Vm_dumping = false;  // Dumping is active\n");
        puts("VerilatedMutex __Vm_dumperMutex;  // Protect __Vm_dumperp\n");
        puts(v3Global.opt.traceClassLang()
             + "* __Vm_dumperp VL_GUARDED_BY(__Vm_dumperMutex) = nullptr;"
               "  /// Trace class for $dump*\n");
    }
    if (v3Global.opt.trace()) {
        puts("bool __Vm_activity = false;"
             "  ///< Used by trace routines to determine change occurred\n");
        puts("uint32_t __Vm_baseCode = 0;"
             "  ///< Used by trace routines when tracing multiple models\n");
    }
    if (v3Global.hasEvents()) {
        if (v3Global.assignsEvents()) {
            puts("std::vector<VlAssignableEvent> __Vm_triggeredEvents;\n");
        } else {
            puts("std::vector<VlEvent*> __Vm_triggeredEvents;\n");
        }
    }
    if (v3Global.hasClasses()) puts("VlDeleter __Vm_deleter;\n");
    puts("bool __Vm_didInit = false;\n");

    if (v3Global.opt.mtasks()) {
        puts("\n// MULTI-THREADING\n");
        puts("VlThreadPool* __Vm_threadPoolp;\n");
        puts("bool __Vm_even_cycle__ico = false;\n");
        puts("bool __Vm_even_cycle__act = false;\n");
        puts("bool __Vm_even_cycle__nba = false;\n");
    }

    if (v3Global.opt.profExec()) {
        puts("\n// EXECUTION PROFILING\n");
        puts("VlExecutionProfiler* const __Vm_executionProfilerp;\n");
    }

    puts("\n// MODULE INSTANCE STATE\n");
    for (const ScopeModPair& pair : m_scopes) {
        const AstScope* const scopep = pair.first;
        const AstNodeModule* const modp = pair.second;
        if (VN_IS(modp, Class)) continue;
        const std::string name = EmitCUtil::prefixNameProtect(modp);
        ofp()->printf("%-30s ", name.c_str());
        putns(scopep, VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + ";\n");
    }

    if (m_coverBins) {
        puts("\n// COVERAGE\n");
        puts(v3Global.opt.threads() > 1 ? "std::atomic<uint32_t>" : "uint32_t");
        puts(" __Vcoverage[");
        puts(cvtToStr(m_coverBins));
        puts("];\n");
    }

    if (v3Global.opt.profPgo()) {
        puts("\n// PGO PROFILING\n");
        puts("VlPgoProfiler<" + std::to_string(ExecMTask::numUsedIds()) + "> _vm_pgoProfiler;\n");
    }

    if (!m_scopeNames.empty()) {  // Scope names
        puts("\n// SCOPE NAMES\n");
        for (const auto& pair : m_scopeNames) {
            const ScopeData& sd = pair.second;
            putns(sd.m_nodep, "VerilatedScope " + protect("__Vscope_" + sd.m_symName) + ";\n");
        }
    }

    if (v3Global.opt.vpi()) {
        puts("\n// SCOPE HIERARCHY\n");
        puts("VerilatedHierarchy __Vhier;\n");
    }

    puts("\n// CONSTRUCTORS\n");
    puts(symClassName() + "(VerilatedContext* contextp, const char* namep, " + topClassName()
         + "* modelp);\n");
    puts("~" + symClassName() + "();\n");

    for (const auto& i : m_usesVfinal) {
        puts("void " + symClassName() + "_" + cvtToStr(i.first) + "(");
        if (i.second) puts("int __Vfinal");
        puts(");\n");
    }

    puts("\n// METHODS\n");
    puts("const char* name() { return TOP.name(); }\n");

    if (v3Global.hasEvents()) {
        if (v3Global.assignsEvents()) {
            puts("void fireEvent(VlAssignableEvent& event) {\n");
        } else {
            puts("void fireEvent(VlEvent& event) {\n");
        }
        puts("if (VL_LIKELY(!event.isTriggered())) {\n");
        if (v3Global.assignsEvents()) {
            puts("__Vm_triggeredEvents.push_back(event);\n");
        } else {
            puts("__Vm_triggeredEvents.push_back(&event);\n");
        }
        puts("}\n");
        puts("event.fire();\n");
        puts("}\n");
        puts("void clearTriggeredEvents() {\n");
        if (v3Global.assignsEvents()) {
            puts("for (auto& event : __Vm_triggeredEvents) event.clearTriggered();\n");
        } else {
            puts("for (const auto eventp : __Vm_triggeredEvents) eventp->clearTriggered();\n");
        }
        puts("__Vm_triggeredEvents.clear();\n");
        puts("}\n");
    }

    if (v3Global.needTraceDumper()) {
        if (!optSystemC()) puts("void _traceDump();\n");
        puts("void _traceDumpOpen();\n");
        puts("void _traceDumpClose();\n");
    }

    if (v3Global.opt.savable()) {
        puts("void " + protect("__Vserialize") + "(VerilatedSerialize& os);\n");
        puts("void " + protect("__Vdeserialize") + "(VerilatedDeserialize& os);\n");
    }
    puts("};\n");

    ofp()->putsEndGuard();
    closeOutputFile();
}

void EmitCSyms::closeSplit() {
    if (!ofp() || ofp() == m_ofpBase) return;

    puts("}\n");
    closeOutputFile();
}

void EmitCSyms::checkSplit(bool usesVfinal) {
    if (ofp()
        && (!v3Global.opt.outputSplitCFuncs() || m_numStmts < v3Global.opt.outputSplitCFuncs())) {
        return;
    }

    // Splitting file, so using parallel build.
    v3Global.useParallelBuild(true);

    m_numStmts = 0;
    const std::string filename
        = v3Global.opt.makeDir() + "/" + symClassName() + "__" + cvtToStr(++m_funcNum) + ".cpp";
    AstCFile* const cfilep = newCFile(filename, true /*slow*/, true /*source*/);
    cfilep->support(true);
    m_usesVfinal[m_funcNum] = usesVfinal;
    closeSplit();

    V3OutCFile* const ofilep = optSystemC() ? new V3OutScFile{filename} : new V3OutCFile{filename};
    setOutputFile(ofilep, cfilep);

    m_ofpBase->puts(symClassName() + "_" + cvtToStr(m_funcNum) + "(");
    if (usesVfinal) m_ofpBase->puts("__Vfinal");
    m_ofpBase->puts(");\n");

    emitSymImpPreamble();
    puts("void " + symClassName() + "::" + symClassName() + "_" + cvtToStr(m_funcNum) + "(");
    if (usesVfinal) puts("int __Vfinal");
    puts(") {\n");
}

void EmitCSyms::emitSymImpPreamble() {
    ofp()->putsHeader();
    puts("// DESCRIPTION: Verilator output: Symbol table implementation internals\n");
    puts("\n");

    // Includes
    puts("#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
    puts("#include \"" + topClassName() + ".h\"\n");
    for (AstNodeModule *nodep = v3Global.rootp()->modulesp(), *nextp; nodep; nodep = nextp) {
        nextp = VN_AS(nodep->nextp(), NodeModule);
        if (VN_IS(nodep, Class)) continue;  // Class included earlier
        putns(nodep, "#include \"" + EmitCUtil::prefixNameProtect(nodep) + ".h\"\n");
    }
    puts("\n");
    // Declarations for DPI Export implementation functions
    bool needsNewLine = false;
    for (const auto& pair : m_scopeFuncs) {
        const AstCFunc* const funcp = pair.second.m_cfuncp;
        if (!funcp->dpiExportImpl()) continue;
        emitCFuncDecl(funcp, pair.second.m_modp);
        needsNewLine = true;
    }
    if (needsNewLine) puts("\n");
}

void EmitCSyms::emitScopeHier(bool destroy) {
    if (!v3Global.opt.vpi()) return;

    const std::string verb = destroy ? "Tear down" : "Set up";
    const std::string method = destroy ? "remove" : "add";
    puts("\n// " + verb + " scope hierarchy\n");
    for (const auto& pair : m_scopeNames) {
        if (pair.first == "TOP") continue;
        const ScopeData& sd = pair.second;
        const std::string& name = sd.m_prettyName;
        const std::string& scopeType = sd.m_type;
        if (name.find('.') != string::npos) continue;
        if (scopeType != "SCOPE_MODULE" && scopeType != "SCOPE_PACKAGE") continue;
        putns(sd.m_nodep,
              "__Vhier." + method + "(0, &" + protect("__Vscope_" + sd.m_symName) + ");\n");
    }

    for (const auto& pair : m_vpiScopeHierarchy) {
        const std::string fromname = scopeSymString(pair.first);
        const ScopeData& from = m_scopeNames.at(fromname);
        for (const std::string& name : pair.second) {
            const std::string toname = scopeSymString(name);
            const ScopeData& to = m_scopeNames.at(toname);
            puts("__Vhier." + method + "(");
            puts("&" + protect("__Vscope_" + from.m_symName) + ", ");
            puts("&" + protect("__Vscope_" + to.m_symName) + ");\n");
        }
    }
    puts("\n");
}

void EmitCSyms::emitSymImp() {
    UINFO(6, __FUNCTION__ << ": ");
    const std::string filename = v3Global.opt.makeDir() + "/" + symClassName() + ".cpp";
    AstCFile* const cfilep = newCFile(filename, true /*slow*/, true /*source*/);
    cfilep->support(true);

    V3OutCFile* const ofilep = optSystemC() ? new V3OutScFile{filename} : new V3OutCFile{filename};
    setOutputFile(ofilep, cfilep);

    m_ofpBase = ofp();
    emitSymImpPreamble();

    if (v3Global.opt.savable()) {
        for (const bool& de : {false, true}) {
            const std::string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
            const std::string funcname = protect(de ? "__Vdeserialize" : "__Vserialize");
            const std::string op = de ? ">>" : "<<";
            // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
            puts("void " + symClassName() + "::" + funcname + "(" + classname + "& os) {\n");
            puts("// Internal state\n");
            if (v3Global.opt.trace()) puts("os" + op + "__Vm_activity;\n");
            puts("os " + op + " __Vm_didInit;\n");
            puts("// Module instance state\n");
            for (const ScopeModPair& pair : m_scopes) {
                const AstScope* const scopep = pair.first;
                puts(VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + "."
                     + funcname + "(os);\n");
            }
            puts("}\n");
        }
        puts("\n");
    }

    puts("// FUNCTIONS\n");

    // Destructor
    puts(symClassName() + "::~" + symClassName() + "()\n");
    puts("{\n");
    emitScopeHier(true);
    if (v3Global.needTraceDumper()) {
        puts("#ifdef VM_TRACE\n");
        puts("if (__Vm_dumping) _traceDumpClose();\n");
        puts("#endif  // VM_TRACE\n");
    }
    if (v3Global.opt.profPgo()) {
        // Do not overwrite data during the last hierarchical stage.
        const std::string firstHierCall
            = (v3Global.opt.hierBlocks().empty() || v3Global.opt.hierChild()) ? "true" : "false";
        puts("_vm_pgoProfiler.write(\"" + topClassName()
             + "\", _vm_contextp__->profVltFilename(), " + firstHierCall + ");\n");
    }
    puts("}\n");

    if (v3Global.needTraceDumper()) {
        if (!optSystemC()) {
            puts("\nvoid " + symClassName() + "::_traceDump() {\n");
            // Caller checked for __Vm_dumperp non-nullptr
            puts("const VerilatedLockGuard lock{__Vm_dumperMutex};\n");
            puts("__Vm_dumperp->dump(VL_TIME_Q());\n");
            puts("}\n");
        }

        puts("\nvoid " + symClassName() + "::_traceDumpOpen() {\n");
        puts("const VerilatedLockGuard lock{__Vm_dumperMutex};\n");
        puts("if (VL_UNLIKELY(!__Vm_dumperp)) {\n");
        puts("__Vm_dumperp = new " + v3Global.opt.traceClassLang() + "();\n");
        puts("__Vm_modelp->trace(__Vm_dumperp, 0, 0);\n");
        puts("std::string dumpfile = _vm_contextp__->dumpfileCheck();\n");
        puts("__Vm_dumperp->open(dumpfile.c_str());\n");
        puts("__Vm_dumping = true;\n");
        puts("}\n");
        puts("}\n");

        puts("\nvoid " + symClassName() + "::_traceDumpClose() {\n");
        puts("const VerilatedLockGuard lock{__Vm_dumperMutex};\n");
        puts("__Vm_dumping = false;\n");
        puts("VL_DO_CLEAR(delete __Vm_dumperp, __Vm_dumperp = nullptr);\n");
        puts("}\n");
    }
    puts("\n");

    // Constructor
    puts(symClassName() + "::" + symClassName()
         + "(VerilatedContext* contextp, const char* namep, " + topClassName() + "* modelp)\n");
    puts("    : VerilatedSyms{contextp}\n");
    puts("    // Setup internal state of the Syms class\n");
    puts("    , __Vm_modelp{modelp}\n");

    if (v3Global.opt.mtasks()) {
        puts("    , __Vm_threadPoolp{static_cast<VlThreadPool*>(contextp->threadPoolp())}\n");
    }

    if (v3Global.opt.profExec()) {
        puts("    , "
             "__Vm_executionProfilerp{static_cast<VlExecutionProfiler*>(contextp->"
             "enableExecutionProfiler(&VlExecutionProfiler::construct))}\n");
    }

    puts("    // Setup module instances\n");
    for (const ScopeModPair& pair : m_scopes) {
        const AstScope* const scopep = pair.first;
        const AstNodeModule* const modp = pair.second;
        puts("    , ");
        putns(scopep, protect(scopep->nameDotless()));
        puts("{this");
        if (modp->isTop()) {
            puts(", namep");
        } else {
            // The "." is added by catName
            puts(", Verilated::catName(namep, ");
            putsQuoted(VIdProtect::protectWordsIf(scopep->prettyName(), scopep->protect()));
            puts(")");
        }
        puts("}\n");
        ++m_numStmts;
    }
    puts("{\n");

    {
        puts("    // Check resources\n");
        uint64_t stackSize = V3StackCount::count(v3Global.rootp());
        if (v3Global.opt.debugStackCheck()) stackSize += 1024 * 1024 * 1024;
        V3Stats::addStat("Size prediction, Stack (bytes)", stackSize);
        puts("    Verilated::stackCheck(" + cvtToStr(stackSize) + ");\n");
        V3Stats::addStat("Size prediction, Heap, from Var Scopes (bytes)", m_statVarScopeBytes);
        V3Stats::addStat(V3Stats::STAT_MODEL_SIZE, stackSize + m_statVarScopeBytes);
    }

    if (v3Global.opt.profPgo()) {
        puts("// Configure profiling for PGO\n");
        if (v3Global.opt.mtasks()) {
            v3Global.rootp()->topModulep()->foreach([&](const AstExecGraph* execGraphp) {
                for (const V3GraphVertex& vtx : execGraphp->depGraphp()->vertices()) {
                    const ExecMTask& mt = static_cast<const ExecMTask&>(vtx);
                    puts("_vm_pgoProfiler.addCounter(" + cvtToStr(mt.id()) + ", \"" + mt.hashName()
                         + "\");\n");
                }
            });
        }
    }

    puts("// Configure time unit / time precision\n");
    if (!v3Global.rootp()->timeunit().isNone()) {
        puts("_vm_contextp__->timeunit(");
        puts(cvtToStr(v3Global.rootp()->timeunit().powerOfTen()));
        puts(");\n");
    }
    if (!v3Global.rootp()->timeprecision().isNone()) {
        puts("_vm_contextp__->timeprecision(");
        puts(cvtToStr(v3Global.rootp()->timeprecision().powerOfTen()));
        puts(");\n");
    }

    puts("// Setup each module's pointers to their submodules\n");
    for (const auto& i : m_scopes) {
        const AstScope* const scopep = i.first;
        const AstNodeModule* const modp = i.second;
        const AstScope* const abovep = scopep->aboveScopep();
        if (!abovep) continue;

        checkSplit(false);
        const std::string protName = VIdProtect::protectWordsIf(scopep->name(), scopep->protect());
        if (VN_IS(modp, ClassPackage)) {
            // ClassPackage modules seem to be a bit out of place, so hard code...
            putns(scopep, "TOP");
        } else {
            putns(scopep, VIdProtect::protectIf(abovep->nameDotless(), abovep->protect()));
        }
        puts(".");
        puts(protName.substr(protName.rfind('.') + 1));
        puts(" = &");
        puts(VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + ";\n");
        ++m_numStmts;
    }

    puts("// Setup each module's pointer back to symbol table (for public functions)\n");
    for (const ScopeModPair& i : m_scopes) {
        const AstScope* const scopep = i.first;
        AstNodeModule* const modp = i.second;
        checkSplit(false);
        // first is used by AstCoverDecl's call to __vlCoverInsert
        const bool first = !modp->user1();
        modp->user1(true);
        putns(scopep, VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + "."
                          + protect("__Vconfigure") + "(" + (first ? "true" : "false") + ");\n");
        ++m_numStmts;
    }

    if (!m_scopeNames.empty()) {  // Setup scope names
        puts("// Setup scopes\n");
        for (const auto& pair : m_scopeNames) {
            checkSplit(false);
            const ScopeData& sd = pair.second;
            putns(sd.m_nodep, protect("__Vscope_" + sd.m_symName) + ".configure(this, name(), ");
            putsQuoted(VIdProtect::protectWordsIf(sd.m_prettyName, true));
            puts(", ");
            putsQuoted(protect(scopeDecodeIdentifier(sd.m_prettyName)));
            puts(", ");
            putsQuoted(sd.m_defName);
            puts(", ");
            puts(cvtToStr(sd.m_timeunit));
            puts(", VerilatedScope::" + sd.m_type + ");\n");
            ++m_numStmts;
        }
    }

    emitScopeHier(false);

    // Everything past here is in the __Vfinal loop, so start a new split file if needed
    closeSplit();

    if (v3Global.dpi()) {
        m_ofpBase->puts("// Setup export functions\n");
        m_ofpBase->puts("for (int __Vfinal = 0; __Vfinal < 2; ++__Vfinal) {\n");
        for (const auto& pair : m_scopeFuncs) {
            const ScopeFuncData& sfd = pair.second;
            const AstScopeName* const scopep = sfd.m_scopep;
            const AstCFunc* const funcp = sfd.m_cfuncp;
            const AstNodeModule* const modp = sfd.m_modp;

            if (!funcp->dpiExportImpl()) continue;

            checkSplit(true);
            putns(scopep,
                  protect("__Vscope_" + scopep->scopeSymName()) + ".exportInsert(__Vfinal, ");
            putsQuoted(funcp->cname());  // Not protected - user asked for import/export
            puts(", (void*)(&");
            puts(EmitCUtil::prefixNameProtect(modp));
            puts("__");
            puts(funcp->nameProtect());
            puts("));\n");
            ++m_numStmts;
        }
        // It would be less code if each module inserted its own variables.
        // Someday.  For now public isn't common.
        for (const auto& pair : m_scopeVars) {
            checkSplit(true);
            const ScopeVarData& svd = pair.second;

            const AstScope* const scopep = svd.m_scopep;
            const AstVar* const varp = svd.m_varp;
            int pdim = 0;
            int udim = 0;
            std::string bounds;
            if (const AstBasicDType* const basicp = varp->basicp()) {
                // Range is always first, it's not in "C" order
                for (AstNodeDType* dtypep = varp->dtypep(); dtypep;) {
                    // Skip AstRefDType/AstTypedef, or return same node
                    dtypep = dtypep->skipRefp();
                    if (const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                        bounds += " ,";
                        bounds += cvtToStr(adtypep->left());
                        bounds += ",";
                        bounds += cvtToStr(adtypep->right());
                        if (VN_IS(dtypep, PackArrayDType))
                            pdim++;
                        else
                            udim++;
                        dtypep = adtypep->subDTypep();
                    } else {
                        if (basicp->isRanged()) {
                            bounds += " ,";
                            bounds += cvtToStr(basicp->left());
                            bounds += ",";
                            bounds += cvtToStr(basicp->right());
                            pdim++;
                        }
                        break;  // AstBasicDType - nothing below, 1
                    }
                }
            }

            putns(scopep, protect("__Vscope_" + svd.m_scopeName));
            putns(varp, ".varInsert(__Vfinal,");
            putsQuoted(protect(svd.m_varBasePretty));

            const std::string varName
                = VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + "."
                  + protect(varp->name());

            if (varp->isParam()) {
                if (varp->vlEnumType() == "VLVT_STRING"
                    && !VN_IS(varp->subDTypep(), UnpackArrayDType)) {
                    puts(", const_cast<void*>(static_cast<const void*>(");
                    puts(varName);
                    puts(".c_str())), ");
                } else {
                    puts(", const_cast<void*>(static_cast<const void*>(&(");
                    puts(varName);
                    puts("))), ");
                }
            } else {
                puts(", &(");
                puts(varName);
                puts("), ");
            }

            puts(varp->isParam() ? "true" : "false");
            puts(", ");
            puts(varp->vlEnumType());  // VLVT_UINT32 etc
            puts(",");
            puts(varp->vlEnumDir());  // VLVD_IN etc
            puts(",");
            puts(cvtToStr(udim));
            puts(",");
            puts(cvtToStr(pdim));
            puts(bounds);
            puts(");\n");
            ++m_numStmts;
        }
        m_ofpBase->puts("}\n");
    }

    m_ofpBase->puts("}\n");

    closeSplit();
    setOutputFile(nullptr);
    VL_DO_CLEAR(delete m_ofpBase, m_ofpBase = nullptr);
}

//######################################################################

void EmitCSyms::emitDpiHdr() {
    UINFO(6, __FUNCTION__ << ": ");
    const std::string filename = v3Global.opt.makeDir() + "/" + topClassName() + "__Dpi.h";
    AstCFile* const cfilep = newCFile(filename, false /*slow*/, false /*source*/);
    cfilep->support(true);
    V3OutCFile hf{filename};
    setOutputFile(&hf, cfilep);

    ofp()->putsHeader();
    puts("// DESCR"
         "IPTION: Verilator output: Prototypes for DPI import and export functions.\n");
    puts("//\n");
    puts("// Verilator includes this file in all generated .cpp files that use DPI functions.\n");
    puts("// Manually include this file where DPI .c import functions are declared to ensure\n");
    puts("// the C functions match the expectations of the DPI imports.\n");

    ofp()->putsGuard();

    puts("\n");
    puts("#include \"svdpi.h\"\n");
    puts("\n");
    puts("#ifdef __cplusplus\n");
    puts("extern \"C\" {\n");
    puts("#endif\n");
    puts("\n");

    int firstExp = 0;
    int firstImp = 0;
    for (const AstCFunc* const nodep : m_dpis) {
        if (!nodep->dpiExportDispatcher() && !nodep->dpiImportPrototype()) continue;

        const std::string sourceLoc = VIdProtect::ifNoProtect(" at " + nodep->fileline()->ascii());
        if (nodep->dpiExportDispatcher()) {
            if (!firstExp++) puts("\n// DPI EXPORTS\n");
            putsDecoration(nodep, "// DPI export" + sourceLoc + "\n");
        } else {
            if (!firstImp++) puts("\n// DPI IMPORTS\n");
            putsDecoration(nodep, "// DPI import" + sourceLoc + "\n");
        }
        putns(nodep, "extern " + nodep->rtnTypeVoid() + " " + nodep->nameProtect() + "("
                         + cFuncArgs(nodep) + ");\n");
    }

    puts("\n");
    puts("#ifdef __cplusplus\n");
    puts("}\n");
    puts("#endif\n");

    ofp()->putsEndGuard();
    setOutputFile(nullptr);
}

//######################################################################

void EmitCSyms::emitDpiImp() {
    UINFO(6, __FUNCTION__ << ": ");
    const std::string filename = v3Global.opt.makeDir() + "/" + topClassName() + "__Dpi.cpp";
    AstCFile* const cfilep = newCFile(filename, false /*slow*/, true /*source*/);
    cfilep->support(true);
    V3OutCFile hf(filename);
    setOutputFile(&hf, cfilep);

    ofp()->putsHeader();
    puts("// DESCR"
         "IPTION: Verilator output: Implementation of DPI export functions.\n");
    puts("//\n");
    puts("// Verilator compiles this file in when DPI functions are used.\n");
    puts("// If you have multiple Verilated designs with the same DPI exported\n");
    puts("// function names, you will get multiple definition link errors from here.\n");
    puts("// This is an unfortunate result of the DPI specification.\n");
    puts("// To solve this, either\n");
    puts("//    1. Call " + topClassName() + "::{export_function} instead,\n");
    puts("//       and do not even bother to compile this file\n");
    puts("// or 2. Compile all __Dpi.cpp files in the same compiler run,\n");
    puts("//       and #ifdefs already inserted here will sort everything out.\n");
    puts("\n");

    puts("#include \"" + topClassName() + "__Dpi.h\"\n");
    puts("#include \"" + topClassName() + ".h\"\n");
    puts("\n");

    for (const AstCFunc* const nodep : m_dpis) {
        if (!nodep->dpiExportDispatcher()) continue;

        const std::string name = nodep->name();
        const std::string sourceLoc = VIdProtect::ifNoProtect(" at " + nodep->fileline()->ascii());

        // Prevent multi-definition if used by multiple models
        puts("#ifndef VL_DPIDECL_" + name + "_\n");
        puts("#define VL_DPIDECL_" + name + "_\n");
        putns(nodep, nodep->rtnTypeVoid() + " " + name + "(" + cFuncArgs(nodep) + ") {\n");
        puts("// DPI export" + sourceLoc + "\n");
        putns(nodep, "return " + topClassName() + "::" + name + "(");
        std::string comma;
        for (const AstNode* stmtp = nodep->argsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && !portp->isFuncReturn()) {
                    puts(comma);
                    comma = ", ";
                    putns(portp, portp->name());
                }
            }
        }
        puts(");\n");
        puts("}\n");
        puts("#endif\n");
        puts("\n");
    }
    setOutputFile(nullptr);
}

//######################################################################
// EmitC class functions

void V3EmitC::emitcSyms(bool dpiHdrOnly) {
    UINFO(2, __FUNCTION__ << ":");
    EmitCSyms{v3Global.rootp(), dpiHdrOnly};
}
