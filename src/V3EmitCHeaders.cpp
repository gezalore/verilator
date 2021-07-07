// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3EmitC.h"
#include "V3EmitCFunc.h"

#include <algorithm>
#include <vector>

//######################################################################
// Internal EmitC implementation

class EmitCHeader final : public EmitCFunc {
    // METHODS
    void emitVarDecls(const AstNodeModule* modp) {
        // Output a list of variable declarations

        std::vector<std::pair<const AstVar*, VarClass>> varList;
        bool lastAnon = false;  // initial value is not important, but is used

        const auto emitCurrentList = [this, &varList, &lastAnon]() {
            if (varList.empty()) return;

            const auto emitDecl = [this](const std::pair<const AstVar*, VarClass>& pair) {
                static const char* prefix[]
                    = {"/* PORT      */ ", "/* SIGNAL    */ ", "/* INTERNAL  */ ",
                       "/* PARAMETER */ ", "@-ERROR-OTHER   "};
                puts(prefix[static_cast<uint8_t>(pair.second)]);
                emitVarDecl(pair.first);
            };

            if (lastAnon) {  // Output as anons
                const int anonMembers = varList.size();
                const int lim = v3Global.opt.compLimitMembers();
                int anonL3s = 1;
                int anonL2s = 1;
                int anonL1s = 1;
                if (anonMembers > (lim * lim * lim)) {
                    anonL3s = (anonMembers + (lim * lim * lim) - 1) / (lim * lim * lim);
                    anonL2s = lim;
                    anonL1s = lim;
                } else if (anonMembers > (lim * lim)) {
                    anonL2s = (anonMembers + (lim * lim) - 1) / (lim * lim);
                    anonL1s = lim;
                } else if (anonMembers > lim) {
                    anonL1s = (anonMembers + lim - 1) / lim;
                }
                if (anonL1s != 1)
                    puts("// Anonymous structures to workaround compiler member-count bugs\n");
                auto it = varList.cbegin();
                for (int l3 = 0; l3 < anonL3s && it != varList.cend(); ++l3) {
                    if (anonL3s != 1) puts("struct {\n");
                    for (int l2 = 0; l2 < anonL2s && it != varList.cend(); ++l2) {
                        if (anonL2s != 1) puts("struct {\n");
                        for (int l1 = 0; l1 < anonL1s && it != varList.cend(); ++l1) {
                            if (anonL1s != 1) puts("struct {\n");
                            for (int l0 = 0; l0 < lim && it != varList.cend(); ++l0) {
                                emitDecl(*it);
                                ++it;
                            }
                            if (anonL1s != 1) puts("};\n");
                        }
                        if (anonL2s != 1) puts("};\n");
                    }
                    if (anonL3s != 1) puts("};\n");
                }
                // Leftovers, just in case off by one error somewhere above
                for (; it != varList.cend(); ++it) { emitDecl(*it); }
            } else {  // Output as nonanons
                for (const auto& pair : varList) { emitDecl(pair); }
            }

            varList.clear();
        };

        // Emit variables in consecutive anon and non-anon batches
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST_CONST(nodep, Var)) {
                const VarClass vc = varClass(varp);

                // Emitted as enum instead
                if (vc == VarClass::Parameter && VN_IS(varp->valuep(), Const)) continue;
                // Emitted elsewhere
                if (vc == VarClass::Other) continue;

                const bool anon = isAnonOk(varp);

                if (anon != lastAnon) { emitCurrentList(); }

                lastAnon = anon;
                varList.emplace_back(varp, vc);
            }
        }

        // Emit final batch
        emitCurrentList();
    }
    void emitParamDecls(const AstNodeModule* modp) {
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isParam() && (varp->isUsedParam() || varp->isSigPublic())) {
                    UASSERT_OBJ(varp->valuep(), nodep, "No init for a param?");
                    // These should be static const values, however older MSVC++ did't
                    // support them; should be ok now under C++11, need to refactor.
                    if (varp->isWide()) {  // Unsupported for output
                        putsDecoration("// enum WData " + varp->nameProtect() + "  //wide");
                    } else if (varp->isString()) {
                        puts("static const std::string " + protect("var_" + varp->name()) + ";\n");
                    } else if (!VN_IS(varp->valuep(), Const)) {  // Unsupported for output
                        // putsDecoration("// enum ..... "+varp->nameProtect()
                        //               +"not simple value, see variable above instead");
                    } else if (VN_IS(varp->dtypep(), BasicDType)
                               && VN_CAST(varp->dtypep(), BasicDType)
                                      ->isOpaque()) {  // Can't put out e.g. doubles
                    } else {
                        // enum
                        puts(varp->isQuad() ? "enum _QData" : "enum _IData");
                        puts("" + varp->nameProtect() + " { " + varp->nameProtect() + " = ");
                        iterateAndNextNull(varp->valuep());
                        puts("};\n");
                        // var
                        puts(varp->isQuad() ? "static const QData " : "static const IData ");
                        puts(protect("var_" + varp->name()) + ";\n");
                    }
                }
            }
        }
    }
    void emitEnums(const AstNodeModule* modp) {
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            const AstTypedef* const tdefp = VN_CAST_CONST(nodep, Typedef);
            if (!tdefp) continue;
            if (!tdefp->attrPublic()) continue;
            const AstEnumDType* const edtypep
                = VN_CAST(tdefp->dtypep()->skipRefToEnump(), EnumDType);
            if (!edtypep) continue;
            if (edtypep->width() > 64) {
                putsDecoration("// enum " + tdefp->nameProtect() + " ignored: Too wide for C++\n");
            } else {
                puts("enum " + tdefp->name() + " {\n");
                for (const AstEnumItem* itemp = edtypep->itemsp(); itemp;
                     itemp = VN_CAST(itemp->nextp(), EnumItem)) {
                    puts(itemp->nameProtect());
                    puts(" = ");
                    iterate(itemp->valuep());
                    if (VN_IS(itemp->nextp(), EnumItem)) puts(",");
                    puts("\n");
                }
                puts("};\n");
            }
        }
    }
    void emitFuncDecls(const AstNodeModule* modp, bool inClassBody) {
        std::vector<const AstCFunc*> funcsp;

        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCFunc* const funcp = VN_CAST_CONST(nodep, CFunc)) {
                if (funcp->dpiImportPrototype())  // Declared in __Dpi.h
                    continue;
                if (funcp->dpiExportDispatcher())  // Declared in __Dpi.h
                    continue;
                if (funcp->isMethod() != inClassBody)  // Only methods go inside class
                    continue;
                if (funcp->isMethod() && funcp->isLoose())  // Loose methods are declared lazily
                    continue;
                funcsp.push_back(funcp);
            }
        }

        std::stable_sort(funcsp.begin(), funcsp.end(), [](const AstNode* ap, const AstNode* bp) {
            return ap->name() < bp->name();
        });

        for (const AstCFunc* const funcp : funcsp) {
            if (inClassBody) ofp()->putsPrivate(funcp->declPrivate());
            emitCFuncDecl(funcp, modp);
        }
    }
    void emitAll(const AstNodeModule* modp) {
        puts("\n//==========\n\n");

        if (const AstClass* const classp = VN_CAST_CONST(modp, Class)) {
            if (classp->extendsp())
                puts("#include \""
                     + prefixNameProtect(classp->extendsp()->classp()->classOrPackagep())
                     + ".h\"\n");
        }

        emitModCUse(modp, VUseType::INT_INCLUDE);

        // Declare foreign instances up front to make C++ happy
        puts("class " + symClassName() + ";\n");
        emitModCUse(modp, VUseType::INT_FWD_CLASS);

        puts("\n//----------\n\n");
        emitTextSection(modp, AstType::atScHdr);

        const string name = prefixNameProtect(modp);

        if (const AstClass* const classp = VN_CAST_CONST(modp, Class)) {
            puts("class ");
            puts(name);
            if (classp->extendsp()) {
                puts(" : public ");
                puts(prefixNameProtect(classp->extendsp()->classp()));
            }
            puts(" {\n");
        } else {
            puts("VL_MODULE(" + name + ") {\n");
        }
        ofp()->resetPrivate();
        ofp()->putsPrivate(false);  // public:

        putsDecoration("// CELLS\n");
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST_CONST(nodep, Cell)) {
                puts(prefixNameProtect(cellp->modp()) + "* " + cellp->nameProtect() + ";\n");
            }
        }

        putsDecoration("\n// DESIGN SPECIFIC STATE\n");
        emitVarDecls(modp);

        putsDecoration("\n// INTERNAL VARIABLES\n");
        if (!VN_IS(modp, Class)) puts(symClassName() + "* vlSymsp;  // Symbol table\n");

        putsDecoration("\n// PARAMETERS\n");
        emitParamDecls(modp);

        putsDecoration("\n// ENUMS (that were declared public)\n");
        emitEnums(modp);

        if (!VN_IS(modp, Class)) {  // Classes use CFuncs with isConstructor/isDestructor
            puts("\n// CONSTRUCTORS\n");
            puts(name + "(const char* name);\n");
            puts(name + "(const " + name + "& other) = delete;      // Non-copyable\n");
            puts(name + "& operator=(const " + name + "&) = delete; // Non-copyable\n");
            puts("~" + name + "();\n");
        }

        emitTextSection(modp, AstType::atScInt);

        puts("\n// INTERNAL METHODS\n");

        if (!VN_IS(modp, Class)) {
            puts("void " + protect("__Vconfigure") + "(" + symClassName()
                 + "* symsp, bool first);\n");
        }

        if (v3Global.opt.savable()) {
            puts("void " + protect("__Vserialize") + "(VerilatedSerialize& os);\n");
            puts("void " + protect("__Vdeserialize") + "(VerilatedDeserialize& os);\n");
        }

        if (v3Global.opt.coverage()) {
            puts("void __vlCoverInsert(");
            puts(v3Global.opt.threads() ? "std::atomic<uint32_t>" : "uint32_t");
            puts("* countp, bool enable, const char* filenamep, int lineno, int column,\n");
            puts("const char* hierp, const char* pagep, const char* commentp, const char* "
                 "linescovp);\n");
        }

        emitFuncDecls(modp, true);
        puts("}");
        if (!VN_IS(modp, Class)) puts(" VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES)");
        puts(";\n");

        puts("\n//----------\n\n");
        emitFuncDecls(modp, false);
    }

    explicit EmitCHeader(const AstNodeModule* modp) {
        UINFO(5, "  Emitting header for " << prefixNameProtect(modp) << endl);

        // Open output file
        const string filename = v3Global.opt.makeDir() + "/" + prefixNameProtect(modp) + ".h";
        newCFile(filename, /* slow: */ false, /* source: */ false);
        m_ofp = v3Global.opt.systemC() ? new V3OutScFile(filename) : new V3OutCFile(filename);

        ofp()->putsHeader();
        puts("// DESCRIPTION: Verilator output: Design internal header\n");
        puts("// See " + topClassName() + ".h for the primary model header\n");

        ofp()->putsGuard();

        // Include files
        puts("\n");
        ofp()->putsIntTopInclude();
        if (v3Global.needHeavy()) {
            puts("#include \"verilated_heavy.h\"\n");
        } else {
            puts("#include \"verilated.h\"\n");
        }
        if (v3Global.opt.mtasks()) puts("#include \"verilated_threads.h\"\n");
        if (v3Global.opt.savable()) puts("#include \"verilated_save.h\"\n");
        if (v3Global.opt.coverage()) puts("#include \"verilated_cov.h\"\n");

        emitAll(modp);

        if (const AstClassPackage* const packagep = VN_CAST_CONST(modp, ClassPackage)) {
            // Put the non-static class implementation in same h file for speed
            emitAll(packagep->classp());
        }

        ofp()->putsEndGuard();

        // Close output file
        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }
    virtual ~EmitCHeader() override = default;

public:
    static void main(const AstNodeModule* modp) { EmitCHeader emitCHeader(modp); }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcHeaders() {
    UINFO(2, __FUNCTION__ << ": " << endl);

    // Process each module in turn
    for (const AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep;
         nodep = VN_CAST(nodep->nextp(), NodeModule)) {
        if (VN_IS(nodep, Class)) continue;  // Declared with the ClassPackage
        EmitCHeader::main(nodep);
    }
}
