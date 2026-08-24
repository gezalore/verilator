// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCFunc.h"
#include "V3ThreadPool.h"
#include "V3UniqueNames.h"

#include <map>
#include <set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Internal EmitC implementation

class EmitCImp final : public EmitCFunc {
    // MEMBERS
    // Base module (For non-classes, same as m_modp. For classes, it's the ClassPackage.)
    const AstNodeModule* const m_fileModp;
    const bool m_slow;  // Creating __Slow file
    V3UniqueNames m_uniqueNames;  // Generates unique file names
    const std::string m_fileBaseName = EmitCUtil::prefixNameProtect(m_fileModp);

    // METHODS
    void openNextOutputFile(const std::string& fileName) {
        openNewOutputSourceFile(fileName, m_slow, false, "Design implementation internals");
        puts("// See " + EmitCUtil::topClassName() + ".h for the primary calling header\n");
        puts("\n");
        puts("#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        emitSystemCSection(m_fileModp, VSystemCSectionType::IMP_HDR);
        // Need to emit new lazy declarations
        m_lazyDecls.reset();
    }

    void emitStaticVarDefns(const AstNodeModule* modp) {
        // Emit static variable definitions
        const string modName = EmitCUtil::prefixNameProtect(modp);
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isStatic()) {
                    putns(varp, varp->vlArgType(true, false, false, modName));
                    puts(";\n");
                }
            }
        }
    }
    void emitParamDefns(const AstNodeModule* modp) {
        const string modName = EmitCUtil::prefixNameProtect(modp);
        bool first = true;
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isParam()) {
                    if (first) {
                        puts("\n");
                        putsDecoration(modp, "// Parameter definitions for " + modName + "\n");
                        first = false;
                    }
                    UASSERT_OBJ(varp->valuep(), nodep, "No init for a param?");
                    // Only C++ LiteralTypes can be constexpr
                    const bool canBeConstexpr = varp->dtypep()->isLiteralType();
                    putns(varp, canBeConstexpr ? "constexpr " : "const ");
                    const string scopedName = modName + "::" + varp->nameProtect();
                    putns(varp, varp->dtypep()->cType(scopedName, false, false));
                    if (!canBeConstexpr) {
                        puts(" = ");
                        emitConstInit(varp->valuep());
                    }
                    puts(";\n");
                }
            }
        }
        if (!first) puts("\n");
    }
    void emitCtorImp(const AstNodeModule* modp) {
        const std::string modName = EmitCUtil::prefixNameProtect(modp);

        puts("\n");
        if (modp->ctorVarReset())
            m_lazyDecls.emit("void " + modName + "__", protect("_ctor_var_reset"),
                             "(" + modName + "* vlSelf);");
        puts("\n");

        const std::string ctorArgs = EmitCUtil::symClassName() + "* symsp, const char* namep";

        // The root module needs a proper constuctor, everything else uses a
        // 'ctor' function in order to be able to split up constructors
        if (modp->isTop()) {
            putns(modp, modName + "::" + modName + "(" + ctorArgs + ")\n");

            ofp()->indentInc();
            const char* sepp = "  : ";
            for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                    if (const AstBasicDType* const dtypep
                        = VN_CAST(varp->dtypeSkipRefp(), BasicDType)) {
                        if (dtypep->keyword().isMTaskState()) {
                            puts(sepp);
                            putns(varp, varp->nameProtect());
                            puts("(");
                            iterateConst(varp->valuep());
                            puts(")\n");
                        } else if (varp->isIO() && varp->isSc()) {
                            puts(sepp);
                            putns(varp, varp->nameProtect());
                            puts("(");
                            putsQuoted(varp->nameProtect());
                            puts(")\n");
                        } else if (dtypep->isDelayScheduler()) {
                            puts(sepp);
                            putns(varp, varp->nameProtect());
                            puts("{*symsp->_vm_contextp__}\n");
                        } else {
                            continue;
                        }
                        sepp = ", ";
                    }
                }
            }
            ofp()->indentDec();
            puts(" {\n");
        } else {
            putns(modp, modName + "::" + modName + "() = default;\n");
            putns(modp, modName + "::~" + modName + "() = default;\n\n");
            putns(modp, "void " + modName + "::ctor(" + ctorArgs + ") {\n");
        }

        puts("vlSymsp = symsp;\n");
        if (modp->isTop()) {
            puts("vlNamep = strdup(namep);\n");
        } else {
            puts("vlNamep = strdup(Verilated::catName(vlSymsp->name(), namep));\n");
        }

        putsDecoration(modp, "// Reset structure values\n");
        if (modp->ctorVarReset()) puts(modName + "__" + protect("_ctor_var_reset") + "(this);\n");
        emitSystemCSection(modp, VSystemCSectionType::CTOR);

        puts("}\n");
    }
    void emitConfigureImp(const AstNodeModule* modp) {
        const string modName = EmitCUtil::prefixNameProtect(modp);

        if (v3Global.opt.coverage()) {
            puts("\n");
            m_lazyDecls.emit("void " + modName + "__", protect("_configure_coverage"),
                             "(" + modName + "* vlSelf, bool first);");
        }

        if (v3Global.opt.coverage()) {
            puts("\nvoid " + modName + "::" + protect("__Vconfigure") + "(bool first) {\n");
            puts("(void)first;  // Prevent unused variable warning\n");
            puts(modName + "__" + protect("_configure_coverage") + "(this, first);\n");
            puts("}\n");
        }
    }
    void emitCoverageImp() {
        // Rather than putting out VL_COVER_INSERT calls directly, we do it via this
        // function. This gets around gcc slowness constructing all of the template
        // arguments.
        if (v3Global.opt.coverage()) {
            puts("\n// Coverage\n");
            puts("void " + EmitCUtil::prefixNameProtect(m_modp) + "::__vlCoverInsert(");
            puts(v3Global.opt.threads() > 1 ? "std::atomic<uint32_t>" : "uint32_t");
            puts("* countp, bool enable, bool localCounter, const char* filenamep, int lineno, "
                 "int column,\n");
            puts("const char* hierp, const char* pagep, const char* commentp, const char* "
                 "linescovp,\n");
            puts("const char* fsmVarp, const char* fsmFromp, const char* fsmTop, const char* "
                 "fsmTagp) {\n");
            if (v3Global.opt.threads() > 1) {
                puts("assert(sizeof(uint32_t) == sizeof(std::atomic<uint32_t>));\n");
                puts("uint32_t* count32p = reinterpret_cast<uint32_t*>(countp);\n");
            } else {
                puts("uint32_t* count32p = countp;\n");
            }
            // static doesn't need save-restore as is constant
            puts("static uint32_t fake_zero_count = 0;\n");
            puts("std::string fullhier = std::string{vlNamep} + hierp;\n");
            puts("if (!fullhier.empty() && fullhier[0] == '.') fullhier = fullhier.substr(1);\n");
            // Global-counter users still redirect later duplicate instances
            // to fake_zero_count for default collapsed coverage. Object-local
            // counters must keep the real pointer so forcePerInstance can
            // report each hierarchy independently.
            puts("if (!enable && !localCounter) count32p = &fake_zero_count;\n");
            puts("*count32p = 0;\n");
            puts("VL_COVER_INSERT(vlSymsp->_vm_contextp__->coveragep(), vlNamep, count32p,");
            puts("  \"filename\",filenamep,");
            puts("  \"lineno\",lineno,");
            puts("  \"column\",column,\n");
            puts("\"hier\",fullhier.c_str(),");
            puts("  \"page\",pagep,");
            puts("  \"comment\",commentp,");
            puts("  (linescovp[0] ? \"linescov\" : \"\"), linescovp,");
            puts("  (fsmVarp[0] ? \"fsm_var\" : \"\"), fsmVarp,");
            puts("  (fsmFromp[0] ? \"fsm_from\" : \"\"), fsmFromp,");
            puts("  (fsmTop[0] ? \"fsm_to\" : \"\"), fsmTop,");
            puts("  (fsmTagp[0] ? \"fsm_tag\" : \"\"), fsmTagp);\n");
            puts("}\n");
        }
        if (v3Global.opt.coverageToggle()) {
            puts("\n// Toggle Coverage\n");
            puts("void " + EmitCUtil::prefixNameProtect(m_modp) + "::__vlCoverToggleInsert(");
            puts("int begin, int end, bool ranged, ");
            puts(v3Global.opt.threads() > 1 ? "std::atomic<uint32_t>" : "uint32_t");
            puts("* countp, bool enable, bool localCounter, const char* filenamep, int lineno, "
                 "int column,\n");
            puts("const char* hierp, const char* pagep, const char* commentp) {\n");
            if (v3Global.opt.threads() > 1) {
                puts("assert(sizeof(uint32_t) == sizeof(std::atomic<uint32_t>));\n");
            }
            puts("int step = (end >= begin) ? 1 : -1;\n");
            // range is inclusive
            puts("for (int i = begin; i != end + step; i += step) {\n");
            puts("for (int j = 0; j < 2; j++) {\n");
            if (v3Global.opt.threads() > 1) {
                puts("uint32_t* count32p = reinterpret_cast<uint32_t*>(countp);\n");
            } else {
                puts("uint32_t* count32p = countp;\n");
            }
            // static doesn't need save-restore as is constant
            puts("static uint32_t fake_zero_count = 0;\n");
            puts("std::string fullhier = std::string{vlNamep} + hierp;\n");
            puts("if (!fullhier.empty() && fullhier[0] == '.') fullhier = fullhier.substr(1);\n");
            puts("std::string commentWithIndex = commentp;\n");
            puts("if (ranged) commentWithIndex += '[' + std::to_string(i) + ']';\n");
            puts("commentWithIndex += j ? \":0->1\" : \":1->0\";\n");
            // Global-counter users still redirect later duplicate instances
            // to fake_zero_count for default collapsed coverage. Object-local
            // counters must keep the real pointer so forcePerInstance can
            // report each hierarchy independently.
            puts("if (!enable && !localCounter) count32p = &fake_zero_count;\n");
            puts("*count32p = 0;\n");
            puts("VL_COVER_INSERT(vlSymsp->_vm_contextp__->coveragep(), vlNamep, count32p,");
            puts("  \"filename\",filenamep,");
            puts("  \"lineno\",lineno,");
            puts("  \"column\",column,\n");
            puts("\"hier\",fullhier.c_str(),");
            puts("  \"page\",pagep,");
            puts("  \"comment\",commentWithIndex.c_str(),");
            puts("  \"\", \"\");\n");  //  linescov argument, but in toggle coverage it is always
                                       //  empty
            puts("++countp;\n");
            puts("}\n");
            puts("}\n");
            puts("}\n");
        }
    }
    void emitDestructorImp(const AstNodeModule* modp) {
        const std::string modName = EmitCUtil::prefixNameProtect(modp);
        puts("\n");
        if (modp->isTop()) {
            putns(modp, modName + "::~" + modName + "() {\n");
        } else {
            putns(modp, "void " + modName + "::dtor() {\n");
        }
        putns(modp, "VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);\n");
        emitSystemCSection(modp, VSystemCSectionType::DTOR);
        puts("}\n");
    }
    void emitSavableImp(const AstNodeModule* modp) {
        if (v3Global.opt.savable()) {
            puts("\n// Savable\n");
            for (int de = 0; de < 2; ++de) {
                const string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
                const string funcname = de ? "__Vdeserialize" : "__Vserialize";
                const string op = de ? ">>" : "<<";
                // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
                putns(modp, "void " + EmitCUtil::prefixNameProtect(modp) + "::" + protect(funcname)
                                + "(" + classname + "& os) {\n");
                // Place a computed checksum to ensure proper structure save/restore formatting
                // OK if this hash includes some things we won't dump, since
                // just looking for loading the wrong model
                VHashSha256 hash;
                for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                    if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                        hash.insert(varp->name());
                        hash.insert(varp->dtypep()->width());
                    }
                }
                ofp()->printf("uint64_t __Vcheckval = 0x%" PRIx64 "ULL;\n",
                              static_cast<uint64_t>(hash.digestUInt64()));
                if (de) {
                    puts("os.readAssert(__Vcheckval);\n");
                } else {
                    puts("os << __Vcheckval;\n");
                }

                // Save context
                // If multiple models save the same context we'll save it multiple
                // times, but is harmless, and doing it otherwise would break
                // backwards compatibility.
                puts("os " + op + " vlSymsp->_vm_contextp__;\n");

                // Save all members
                for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                    if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                        if (varp->isIO() && modp->isTop() && optSystemC()) {
                            // System C top I/O doesn't need loading, as the
                            // lower level subinst code does it.
                        } else if (varp->isParam()) {
                        } else if (varp->isStatic() && varp->isConst()) {
                        } else if (VN_IS(varp->dtypep(), NBACommitQueueDType)) {
                        } else {
                            int vects = 0;
                            AstNodeDType* elementp = varp->dtypeSkipRefp();
                            for (AstUnpackArrayDType* arrayp = VN_CAST(elementp, UnpackArrayDType);
                                 arrayp; arrayp = VN_CAST(elementp, UnpackArrayDType)) {
                                const int vecnum = vects++;
                                UASSERT_OBJ(arrayp->hi() >= arrayp->lo(), varp,
                                            "Should have swapped msb & lsb earlier.");
                                const string ivar = "__Vi"s + cvtToStr(vecnum);
                                puts("for (int __Vi" + cvtToStr(vecnum) + " = " + cvtToStr(0));
                                puts("; " + ivar + " < " + cvtToStr(arrayp->elementsConst()));
                                puts("; ++" + ivar + ") {\n");
                                elementp = arrayp->subDTypep()->skipRefp();
                            }
                            const AstBasicDType* const basicp = elementp->basicp();
                            // Do not save MTask state, only matters within an evaluation
                            if (basicp && basicp->keyword().isMTaskState()) continue;
                            // Want to detect types that are represented as arrays
                            // (i.e. packed types of more than 64 bits).
                            if (elementp->isWide()
                                && !(basicp && basicp->keyword() == VBasicDTypeKwd::STRING)) {
                                const int vecnum = vects++;
                                const string ivar = "__Vi"s + cvtToStr(vecnum);
                                puts("for (int __Vi" + cvtToStr(vecnum) + " = " + cvtToStr(0));
                                puts("; " + ivar + " < " + cvtToStr(elementp->widthWords()));
                                puts("; ++" + ivar + ") {\n");
                            }
                            putns(varp, "os" + op + varp->nameProtect());
                            for (int v = 0; v < vects; ++v) puts("[__Vi" + cvtToStr(v) + "]");
                            puts(";\n");
                            for (int v = 0; v < vects; ++v) puts("}\n");
                        }
                    }
                }

                puts("}\n");
            }
        }
    }
    // Predicate to check if we actually need to emit anything into the common implementation file.
    // Used to avoid creating empty output files.
    bool hasCommonImp(const AstNodeModule* modp) const {
        // Nothing to emit if no module!
        if (!modp) return false;
        // We always need the slow file
        if (m_slow) return true;
        // The fast file is only required when we have `systemc_implementation nodes
        if (v3Global.hasSystemCSections()) {
            for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (const AstSystemCSection* const ssp = VN_CAST(nodep, SystemCSection)) {
                    if (ssp->sectionType() == VSystemCSectionType::IMP) return true;
                }
            }
        }
        return false;
    }
    // Actually emit common implementation contents for given AstNodeModule
    void doCommonImp(const AstNodeModule* modp) {
        if (m_slow) {
            emitStaticVarDefns(modp);
            if (!VN_IS(modp, Class)) {
                emitParamDefns(modp);
                emitCtorImp(modp);
                emitConfigureImp(modp);
                emitDestructorImp(modp);
                emitCoverageImp();
            }
            emitSavableImp(modp);
        } else {
            // From `systemc_implementation
            emitSystemCSection(modp, VSystemCSectionType::IMP);
        }
    }
    void emitCommonImp(const AstNodeModule* modp) {
        const AstClass* const classp
            = VN_IS(modp, ClassPackage) ? VN_AS(modp, ClassPackage)->classp() : nullptr;

        if (hasCommonImp(modp) || hasCommonImp(classp)) {
            openNextOutputFile(m_fileBaseName);

            doCommonImp(modp);
            if (classp) {
                VL_RESTORER(m_modp);
                m_modp = classp;
                doCommonImp(classp);
            }

            closeOutputFile();
        }
    }
    void emitCFuncImp(const AstNodeModule* modp) {
        // Functions to be emitted here
        std::vector<AstCFunc*> funcps;

        const auto gather = [this, &funcps](const AstNodeModule* modp) {
            for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                AstCFunc* const funcp = VN_CAST(nodep, CFunc);
                if (!funcp) continue;
                // DPI handled elsewhere
                if (funcp->dpiImportPrototype()) continue;
                if (funcp->dpiExportDispatcher()) continue;
                if (funcp->slow() != m_slow) continue;
                funcps.push_back(funcp);
            }
        };

        gather(modp);
        VL_RESTORER(m_classOrPackage);
        if (const AstClassPackage* const packagep = VN_CAST(modp, ClassPackage)) {
            m_classOrPackage = packagep;
            gather(packagep->classp());
        }

        // Do not create empty files
        if (funcps.empty()) return;

        // Open output file
        openNextOutputFile(m_uniqueNames.get(m_fileBaseName));
        // Emit all functions
        for (AstCFunc* const funcp : funcps) {
            VL_RESTORER(m_modp);
            m_modp = EmitCParentModule::get(funcp);
            iterateConst(funcp);
        }
        // Close output file
        closeOutputFile();
    }

    // VISITORS
    void visit(AstCFunc* nodep) override {
        if (splitNeeded()) {
            // Splitting file, so using parallel build.
            v3Global.useParallelBuild(true);
            // Close old file
            closeOutputFile();
            // Open a new file
            openNextOutputFile(m_uniqueNames.get(m_fileBaseName));
        }

        EmitCFunc::visit(nodep);
    }

    explicit EmitCImp(const AstNodeModule* modp, bool slow)
        : m_fileModp{modp}
        , m_slow{slow} {
        UINFO(5, "  Emitting implementation of " << EmitCUtil::prefixNameProtect(modp));

        m_modp = modp;

        // Emit implementation of this module, if this is an AstClassPackage, then put the
        // corresponding AstClass implementation in the same file as often optimizations are
        // possible when both are seen by the compiler
        // TODO: is the above comment still true?

        // Emit implementations of common parts
        emitCommonImp(modp);

        // Emit implementations of all AstCFunc
        emitCFuncImp(modp);
    }
    ~EmitCImp() override = default;

public:
    static std::vector<AstCFile*> main(const AstNodeModule* modp, bool slow) VL_MT_STABLE {
        EmitCImp emitCImp{modp, slow};
        return emitCImp.getAndClearCfileps();
    }
};

//######################################################################
// Existing AstCFile emitter

class EmitCFile final : public EmitCFunc {
    explicit EmitCFile(AstCFile* cfilep) {
        openOutputFile(cfilep, "Generated C++");
        iterateConst(cfilep->tblockp());
        closeOutputFile();
    }
    ~EmitCFile() override = default;

public:
    static void main(AstCFile* cfilep) VL_MT_STABLE {
        if (!cfilep->tblockp()) return;
        EmitCFile{cfilep};
    }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcImp() {
    UINFO(2, __FUNCTION__ << ":");
    std::list<std::vector<AstCFile*>> cfiles;
    {
        // Make parent module pointers available.
        const EmitCParentModule emitCParentModule;
        V3ThreadScope threadScope;

        // Process each module in turn
        for (const AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, Class)) continue;  // Imped with ClassPackage
            const AstNodeModule* const modp = VN_AS(nodep, NodeModule);
            cfiles.emplace_back();
            std::vector<AstCFile*>& slow = cfiles.back();
            threadScope.enqueue([modp, &slow] { slow = EmitCImp::main(modp, /* slow: */ true); });
            cfiles.emplace_back();
            std::vector<AstCFile*>& fast = cfiles.back();
            threadScope.enqueue([modp, &fast] { fast = EmitCImp::main(modp, /* slow: */ false); });
        }
    }
    // Add files to netlist
    for (const std::vector<AstCFile*>& cfileps : cfiles) {
        for (AstCFile* const cfilep : cfileps) v3Global.rootp()->addFilesp(cfilep);
    }
}

void V3EmitC::emitcFiles() {
    UINFO(2, __FUNCTION__ << ":");
    for (AstNodeFile *filep = v3Global.rootp()->filesp(), *nextp; filep; filep = nextp) {
        nextp = VN_AS(filep->nextp(), NodeFile);
        if (AstCFile* const cfilep = VN_CAST(filep, CFile)) EmitCFile::main(cfilep);
    }
}
