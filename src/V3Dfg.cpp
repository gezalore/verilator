// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Data flow graph (DFG) representation of logic
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

#include "V3Dfg.h"

#include "V3EmitV.h"
#include "V3File.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//------------------------------------------------------------------------------
// V3Dfg

// predicate for supported data types
static bool dfgGraphIsSupportedDTypePacked(const AstNodeDType* dtypep) {
    dtypep = dtypep->skipRefp();
    if (const AstBasicDType* const typep = VN_CAST(dtypep, BasicDType)) {
        return typep->keyword().isIntNumeric();
    }
    if (const AstPackArrayDType* const typep = VN_CAST(dtypep, PackArrayDType)) {
        return dfgGraphIsSupportedDTypePacked(typep->subDTypep());
    }
    if (const AstNodeUOrStructDType* const typep = VN_CAST(dtypep, NodeUOrStructDType)) {
        return typep->packed();
    }
    return false;
}

bool V3Dfg::isSupported(const AstNodeDType* dtypep) {
    dtypep = dtypep->skipRefp();
    // Support 1 dimensional unpacked arrays of packed types
    if (const AstUnpackArrayDType* const typep = VN_CAST(dtypep, UnpackArrayDType)) {
        return dfgGraphIsSupportedDTypePacked(typep->subDTypep());
    }
    // Support packed types
    return dfgGraphIsSupportedDTypePacked(dtypep);
}

//------------------------------------------------------------------------------
// DfgGraph

DfgGraph::DfgGraph(AstModule* modulep, const string& name)
    : m_modulep{modulep}
    , m_name{name} {}

DfgGraph::~DfgGraph() {
    forEachVertex([](DfgVertex& vtxp) { delete &vtxp; });
}

std::unique_ptr<DfgGraph> DfgGraph::clone() const {
    const bool scoped = !modulep();

    DfgGraph* const clonep = new DfgGraph{modulep(), name()};

    // Map from original vertex to clone
    std::unordered_map<const DfgVertex*, DfgVertex*> vtxp2clonep(size() * 2);

    // Clone constVertices
    for (const DfgConst& vtx : m_constVertices) {
        DfgConst* const cp = new DfgConst{*clonep, vtx.fileline(), vtx.num()};
        vtxp2clonep.emplace(&vtx, cp);
    }
    // Clone variable vertices
    for (const DfgVertexVar& vtx : m_varVertices) {
        const DfgVertexVar* const vp = vtx.as<DfgVertexVar>();
        DfgVertexVar* cp = nullptr;

        switch (vtx.type()) {
        case VDfgType::atVarArray: {
            if (scoped) {
                cp = new DfgVarArray{*clonep, vp->varScopep()};
            } else {
                cp = new DfgVarArray{*clonep, vp->varp()};
            }
            vtxp2clonep.emplace(&vtx, cp);
            break;
        }
        case VDfgType::atVarPacked: {
            if (scoped) {
                cp = new DfgVarPacked{*clonep, vp->varScopep()};
            } else {
                cp = new DfgVarPacked{*clonep, vp->varp()};
            }
            vtxp2clonep.emplace(&vtx, cp);
            break;
        }
        default: {
            vtx.v3fatalSrc("Unhandled variable vertex type: " + vtx.typeName());
            VL_UNREACHABLE;
            break;
        }
        }

        if (AstNode* const tmpForp = vp->tmpForp()) cp->tmpForp(tmpForp);
    }
    // Clone operation vertices
    for (const DfgVertex& vtx : m_opVertices) {
        switch (vtx.type()) {
#include "V3Dfg__gen_clone_cases.h"  // From ./astgen
        case VDfgType::atSel: {
            DfgSel* const cp = new DfgSel{*clonep, vtx.fileline(), vtx.dtypep()};
            cp->lsb(vtx.as<DfgSel>()->lsb());
            vtxp2clonep.emplace(&vtx, cp);
            break;
        }
        case VDfgType::atUnitArray: {
            DfgUnitArray* const cp = new DfgUnitArray{*clonep, vtx.fileline(), vtx.dtypep()};
            vtxp2clonep.emplace(&vtx, cp);
            break;
        }
        case VDfgType::atMux: {
            DfgMux* const cp = new DfgMux{*clonep, vtx.fileline(), vtx.dtypep()};
            vtxp2clonep.emplace(&vtx, cp);
            break;
        }
        case VDfgType::atSpliceArray: {
            DfgSpliceArray* const cp = new DfgSpliceArray{*clonep, vtx.fileline(), vtx.dtypep()};
            vtxp2clonep.emplace(&vtx, cp);
            break;
        }
        case VDfgType::atSplicePacked: {
            DfgSplicePacked* const cp = new DfgSplicePacked{*clonep, vtx.fileline(), vtx.dtypep()};
            vtxp2clonep.emplace(&vtx, cp);
            break;
        }
        case VDfgType::atLogic: {
            vtx.v3fatalSrc("DfgLogic cannot be cloned");
            VL_UNREACHABLE;
            break;
        }
        case VDfgType::atUnresolved: {
            vtx.v3fatalSrc("DfgUnresolved cannot be cloned");
            VL_UNREACHABLE;
            break;
        }
        default: {
            vtx.v3fatalSrc("Unhandled operation vertex type: " + vtx.typeName());
            VL_UNREACHABLE;
            break;
        }
        }
    }
    UASSERT(size() == clonep->size(), "Size of clone should be the same");

    // Constants have no inputs
    // Hook up inputs of cloned variables
    for (const DfgVertexVar& vtx : m_varVertices) {
        DfgVertexVar* const cp = vtxp2clonep.at(&vtx)->as<DfgVertexVar>();
        if (const DfgVertex* const srcp = vtx.srcp()) cp->srcp(vtxp2clonep.at(srcp));
        if (const DfgVertex* const defp = vtx.defaultp()) cp->defaultp(vtxp2clonep.at(defp));
    }
    // Hook up inputs of cloned operation vertices
    for (const DfgVertex& vtx : m_opVertices) {
        if (vtx.is<DfgVertexVariadic>()) {
            switch (vtx.type()) {
            case VDfgType::atSpliceArray: {
                const DfgSpliceArray* const vp = vtx.as<DfgSpliceArray>();
                DfgSpliceArray* const cp = vtxp2clonep.at(vp)->as<DfgSpliceArray>();
                vp->forDriver([&](const DfgVertex& src, uint32_t lo, FileLine* flp) {
                    cp->addDriver(flp, lo, vtxp2clonep.at(&src));
                    return false;
                });
                break;
            }
            case VDfgType::atSplicePacked: {
                const DfgSplicePacked* const vp = vtx.as<DfgSplicePacked>();
                DfgSplicePacked* const cp = vtxp2clonep.at(vp)->as<DfgSplicePacked>();
                vp->forDriver([&](const DfgVertex& src, uint32_t lo, FileLine* flp) {
                    cp->addDriver(flp, lo, vtxp2clonep.at(&src));
                    return false;
                });
                break;
            }
            default: {
                vtx.v3fatalSrc("Unhandled DfgVertexVariadic sub type: " + vtx.typeName());
                VL_UNREACHABLE;
                break;
            }
            }
            continue;
        }

        if (const DfgVertexUnary* const vp = vtx.cast<DfgVertexUnary>()) {
            DfgVertexUnary* const cp = vtxp2clonep.at(vp)->as<DfgVertexUnary>();
            cp->src0p(vtxp2clonep.at(vp->src0p()));
            continue;
        }

        if (const DfgVertexBinary* const vp = vtx.cast<DfgVertexBinary>()) {
            DfgVertexBinary* const cp = vtxp2clonep.at(vp)->as<DfgVertexBinary>();
            cp->src0p(vtxp2clonep.at(vp->src0p()));
            cp->src1p(vtxp2clonep.at(vp->src1p()));
            continue;
        }

        if (const DfgVertexTernary* const vp = vtx.cast<DfgVertexTernary>()) {
            DfgVertexTernary* const cp = vtxp2clonep.at(vp)->as<DfgVertexTernary>();
            cp->src0p(vtxp2clonep.at(vp->src0p()));
            cp->src1p(vtxp2clonep.at(vp->src1p()));
            cp->src2p(vtxp2clonep.at(vp->src2p()));
            continue;
        }
    }

    return std::unique_ptr<DfgGraph>{clonep};
}

void DfgGraph::mergeGraphs(std::vector<std::unique_ptr<DfgGraph>>&& otherps) {
    if (otherps.empty()) return;

    // NODE STATE
    // AstVar/AstVarScope::user2p() -> corresponding DfgVertexVar* in 'this' graph
    const VNUser2InUse user2InUse;

    // Set up Ast Variable -> DfgVertexVar map for 'this' graph
    for (DfgVertexVar& vtx : m_varVertices) vtx.nodep()->user2p(&vtx);

    // Merge in each of the other graphs
    for (const std::unique_ptr<DfgGraph>& otherp : otherps) {
        // Process variables
        for (DfgVertexVar* const vtxp : otherp->m_varVertices.unlinkable()) {
            // Variabels that are present in 'this', make them use the DfgVertexVar in 'this'.
            if (DfgVertexVar* const altp = vtxp->nodep()->user2u().to<DfgVertexVar*>()) {
                DfgVertex* const srcp = vtxp->srcp();
                DfgVertex* const defaultp = vtxp->defaultp();
                UASSERT_OBJ(!(srcp || defaultp) || (!altp->srcp() && !altp->defaultp()), vtxp,
                            "At most one alias should be driven");
                vtxp->replaceWith(altp);
                if (srcp) altp->srcp(srcp);
                if (defaultp) altp->defaultp(defaultp);
                VL_DO_DANGLING(vtxp->unlinkDelete(*otherp), vtxp);
                continue;
            }
            // Otherwise they will be moved
            vtxp->nodep()->user2p(vtxp);
            vtxp->m_userCnt = 0;
            vtxp->m_graphp = this;
        }
        m_varVertices.splice(m_varVertices.end(), otherp->m_varVertices);
        // Process constants
        for (DfgConst& vtx : otherp->m_constVertices) {
            vtx.m_userCnt = 0;
            vtx.m_graphp = this;
        }
        m_constVertices.splice(m_constVertices.end(), otherp->m_constVertices);
        // Process operations
        for (DfgVertex& vtx : otherp->m_opVertices) {
            vtx.m_userCnt = 0;
            vtx.m_graphp = this;
        }
        m_opVertices.splice(m_opVertices.end(), otherp->m_opVertices);
        // Update graph sizes
        m_size += otherp->m_size;
        otherp->m_size = 0;
    }
}

std::string DfgGraph::makeUniqueName(const std::string& prefix, size_t n) {
    // Construct the tmpNameStub if we have not done so yet
    if (m_tmpNameStub.empty()) {
        // Use the hash of the graph name (avoid long names and non-identifiers)
        const std::string hash = V3Hash{m_name}.toString();
        // We need to keep every variable globally unique, and graph hashed
        // names might not be, so keep a static table to track multiplicity
        static std::unordered_map<std::string, uint32_t> s_multiplicity;
        m_tmpNameStub += '_' + hash + '_' + std::to_string(s_multiplicity[hash]++) + '_';
    }
    // Assemble the globally unique name
    return "__Vdfg" + prefix + m_tmpNameStub + std::to_string(n);
}

DfgVertexVar* DfgGraph::makeNewVar(FileLine* flp, const std::string& name, AstNodeDType* dtypep,
                                   AstScope* scopep) {
    UASSERT_OBJ(!!scopep != !!modulep(), flp,
                "makeNewVar scopep should only be provided for a scoped DfgGraph");

    // Create AstVar
    AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, dtypep};

    if (scopep) {
        // Add AstVar to the scope's module
        scopep->modp()->addStmtsp(varp);
        // Create AstVarScope
        AstVarScope* const vscp = new AstVarScope{flp, scopep, varp};
        // Add to scope
        scopep->addVarsp(vscp);
        // Create and return the corresponding variable vertex
        if (VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) return new DfgVarArray{*this, vscp};
        return new DfgVarPacked{*this, vscp};
    } else {
        // Add AstVar to containing module
        modulep()->addStmtsp(varp);
        // Create and return the corresponding variable vertex
        if (VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) return new DfgVarArray{*this, varp};
        return new DfgVarPacked{*this, varp};
    }
}

static const std::string toDotId(const DfgVertex& vtx) { return '"' + cvtToHex(&vtx) + '"'; }

// Dump one DfgVertex in Graphviz format
static void dumpDotVertex(std::ostream& os, const DfgVertex& vtx) {

    if (const DfgVarPacked* const varVtxp = vtx.cast<DfgVarPacked>()) {
        const AstNode* const nodep = varVtxp->nodep();
        const AstVar* const varp = varVtxp->varp();
        os << toDotId(vtx);
        os << " [label=\"" << nodep->prettyName() << '\n';
        os << cvtToHex(varVtxp) << '\n';
        if (const AstNode* const tmpForp = varVtxp->tmpForp()) {
            os << "temporary for: " << tmpForp->prettyName() << "\n";
        }
        varVtxp->dtypep()->dumpSmall(os);
        os << " / F" << varVtxp->fanout() << '"';

        if (varp->direction() == VDirection::INPUT) {
            os << ", shape=box, style=filled, fillcolor=chartreuse2";  // Green
        } else if (varp->direction() == VDirection::OUTPUT) {
            os << ", shape=box, style=filled, fillcolor=cyan2";  // Cyan
        } else if (varp->direction() == VDirection::INOUT) {
            os << ", shape=box, style=filled, fillcolor=darkorchid2";  // Purple
        } else if (varVtxp->hasExtRefs()) {
            os << ", shape=box, style=filled, fillcolor=firebrick2";  // Red
        } else if (varVtxp->hasModRefs()) {
            os << ", shape=box, style=filled, fillcolor=darkorange1";  // Orange
        } else if (varVtxp->hasDfgRefs()) {
            os << ", shape=box, style=filled, fillcolor=gold2";  // Yellow
        } else if (varVtxp->tmpForp()) {
            os << ", shape=box, style=filled, fillcolor=gray80";
        } else {
            os << ", shape=box";
        }
        os << "]\n";
        return;
    }

    if (const DfgVarArray* const arrVtxp = vtx.cast<DfgVarArray>()) {
        const AstNode* const nodep = arrVtxp->nodep();
        const AstVar* const varp = arrVtxp->varp();
        os << toDotId(vtx);
        os << " [label=\"" << nodep->prettyName() << '\n';
        os << cvtToHex(arrVtxp) << '\n';
        if (const AstNode* const tmpForp = arrVtxp->tmpForp()) {
            os << "temporary for: " << tmpForp->prettyName() << "\n";
        }
        arrVtxp->dtypep()->dumpSmall(os);
        os << " / F" << arrVtxp->fanout() << '"';
        if (varp->direction() == VDirection::INPUT) {
            os << ", shape=box3d, style=filled, fillcolor=chartreuse2";  // Green
        } else if (varp->direction() == VDirection::OUTPUT) {
            os << ", shape=box3d, style=filled, fillcolor=cyan2";  // Cyan
        } else if (varp->direction() == VDirection::INOUT) {
            os << ", shape=box3d, style=filled, fillcolor=darkorchid2";  // Purple
        } else if (arrVtxp->hasExtRefs()) {
            os << ", shape=box3d, style=filled, fillcolor=firebrick2";  // Red
        } else if (arrVtxp->hasModRefs()) {
            os << ", shape=box3d, style=filled, fillcolor=darkorange1";  // Orange
        } else if (arrVtxp->hasDfgRefs()) {
            os << ", shape=box3d, style=filled, fillcolor=gold2";  // Yellow
        } else if (arrVtxp->tmpForp()) {
            os << ", shape=box3d, style=filled, fillcolor=gray80";
        } else {
            os << ", shape=box3d";
        }
        os << "]\n";
        return;
    }

    if (const DfgConst* const constVtxp = vtx.cast<DfgConst>()) {
        const V3Number& num = constVtxp->num();

        os << toDotId(vtx);
        os << " [label=\"";
        if (num.width() <= 32 && !num.isSigned()) {
            os << constVtxp->width() << "'d" << num.toUInt() << '\n';
            os << constVtxp->width() << "'h" << std::hex << num.toUInt() << std::dec << '\n';
        } else {
            os << num.ascii() << '\n';
        }
        os << cvtToHex(constVtxp) << '\n';
        os << '"';
        os << ", shape=plain";
        os << "]\n";
        return;
    }

    if (const DfgSel* const selVtxp = vtx.cast<DfgSel>()) {
        const uint32_t lsb = selVtxp->lsb();
        const uint32_t msb = lsb + selVtxp->width() - 1;
        os << toDotId(vtx);
        os << " [label=\"SEL _[" << msb << ":" << lsb << "]\n";
        os << cvtToHex(selVtxp) << '\n';
        vtx.dtypep()->dumpSmall(os);
        os << " / F" << vtx.fanout() << '"';
        if (vtx.hasMultipleSinks()) {
            os << ", shape=doublecircle";
        } else {
            os << ", shape=circle";
        }
        os << "]\n";
        return;
    }

    if (vtx.is<DfgVertexSplice>() || vtx.is<DfgUnitArray>() || vtx.is<DfgUnresolved>()) {
        os << toDotId(vtx);
        os << " [label=\"" << vtx.typeName() << '\n';
        os << cvtToHex(&vtx) << '\n';
        vtx.dtypep()->dumpSmall(os);
        os << " / F" << vtx.fanout() << '"';
        if (vtx.hasMultipleSinks()) {
            os << ", shape=doubleoctagon";
        } else {
            os << ", shape=octagon";
        }
        os << "]\n";
        return;
    }

    if (const DfgLogic* const logicp = vtx.cast<DfgLogic>()) {
        os << toDotId(vtx);
        std::stringstream ss;
        V3EmitV::debugVerilogForTree(logicp->nodep(), ss);
        os << " [label=\"";
        os << VString::replaceSubstr(VString::replaceSubstr(ss.str(), "\n", "\\l"), "\"", "\\\"");
        os << "\\n" << cvtToHex(&vtx);
        os << "\"\n";
        os << ", shape=box, style=\"rounded,filled\", fillcolor=cornsilk, nojustify=true";
        os << "]\n";
        return;
    }

    os << toDotId(vtx);
    os << " [label=\"" << vtx.typeName() << '\n';
    os << cvtToHex(&vtx) << '\n';
    vtx.dtypep()->dumpSmall(os);
    os << " / F" << vtx.fanout() << '"';
    if (vtx.hasMultipleSinks()) {
        os << ", shape=doublecircle";
    } else {
        os << ", shape=circle";
    }
    os << "]\n";
}

void DfgGraph::dumpDot(std::ostream& os, const std::string& label,
                       std::function<bool(const DfgVertex&)> p) const {
    // This generates a graphviz dump, https://www.graphviz.org

    // Header
    os << "digraph dfg {\n";
    os << "rankdir=LR\n";

    // If predicate not given, dump everything
    if (!p) p = [](const DfgVertex&) { return true; };

    std::unordered_set<const DfgVertex*> emitted;
    // Emit all vertices associated with a DfgLogic
    forEachVertex([&](const DfgVertex& vtx) {
        const DfgLogic* const logicp = vtx.cast<DfgLogic>();
        if (!logicp) return;
        if (logicp->synth().empty()) return;
        if (!p(vtx)) return;
        os << "subgraph cluster_" << cvtToHex(logicp) << " {\n";
        dumpDotVertex(os, *logicp);
        emitted.insert(logicp);
        for (DfgVertex* const vtxp : logicp->synth()) {
            if (!p(*vtxp)) continue;
            dumpDotVertex(os, *vtxp);
            emitted.insert(vtxp);
        }
        os << "}\n";
    });
    // Emit all remaining vertices
    forEachVertex([&](const DfgVertex& vtx) {
        if (emitted.count(&vtx)) return;
        if (!p(vtx)) return;
        dumpDotVertex(os, vtx);
    });
    // Emit all edges
    forEachVertex([&](const DfgVertex& vtx) {
        if (!p(vtx)) return;

        // Dump one DfgEdge in Graphviz format
        const auto dumpDotEdge = [&](const DfgVertex* srcp, size_t idx) {
            if (!p(*srcp)) return;
            os << toDotId(*srcp) << " -> " << toDotId(vtx);
            os << " [headlabel=\"" << vtx.srcName(idx) << "\"]";
            os << '\n';
        };

        if (const DfgVertexVar* const currp = vtx.cast<DfgVertexVar>()) {
            if (currp->srcp()) dumpDotEdge(currp->srcp(), 0);
            if (currp->defaultp()) dumpDotEdge(currp->defaultp(), 1);
            return;
        }
        if (vtx.is<DfgVertexNullary>()) return;
        if (const DfgVertexUnary* const currp = vtx.cast<DfgVertexUnary>()) {
            dumpDotEdge(currp->src0p(), 0);
            return;
        }
        if (const DfgVertexBinary* const currp = vtx.cast<DfgVertexBinary>()) {
            dumpDotEdge(currp->src0p(), 0);
            dumpDotEdge(currp->src1p(), 1);
            return;
        }
        if (const DfgVertexTernary* const currp = vtx.cast<DfgVertexTernary>()) {
            dumpDotEdge(currp->src0p(), 0);
            dumpDotEdge(currp->src1p(), 1);
            dumpDotEdge(currp->src2p(), 2);
            return;
        }
        if (const DfgVertexVariadic* const currp = vtx.cast<DfgVertexVariadic>()) {
            size_t n = currp->srcsSize();
            for (size_t i = 0; i < n; ++i) if (currp->srcp(i)) dumpDotEdge(currp->srcp(i), i);
            return;
        }
        vtx.v3fatalSrc("Unknown vertex type " << vtx.typeName());  // LCOV_EXCL_LINE
    });

    // Footer
    os << "label=\"" << name() + (label.empty() ? "" : "-" + label) << "\"\n";
    os << "labelloc=t\n";
    os << "labeljust=l\n";
    os << "}\n";
}

std::string DfgGraph::dumpDotString(const std::string& label,
                                    std::function<bool(const DfgVertex&)> p) const {
    std::stringstream ss;
    dumpDot(ss, label, p);
    return ss.str();
}

void DfgGraph::dumpDotFile(const std::string& filename, const std::string& label,
                           std::function<bool(const DfgVertex&)> p) const {
    const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(filename)};
    if (os->fail()) v3fatal("Can't write file: " << filename);
    dumpDot(*os.get(), label, p);
    os->close();
}

void DfgGraph::dumpDotFilePrefixed(const std::string& label,
                                   std::function<bool(const DfgVertex&)> p) const {
    std::string filename = name();
    if (!label.empty()) filename += "-" + label;
    dumpDotFile(v3Global.debugFilename(filename) + ".dot", label, p);
}

template <bool T_SinksNotSources>
static std::unique_ptr<std::unordered_set<const DfgVertex*>>
dfgGraphCollectCone(const std::vector<const DfgVertex*>& vtxps) {
    // Work queue for traversal starting from all the seed vertices
    std::vector<const DfgVertex*> queue = vtxps;
    // Set of already visited vertices
    std::unique_ptr<std::unordered_set<const DfgVertex*>> resp{
        new std::unordered_set<const DfgVertex*>{}};
    // Depth first traversal
    while (!queue.empty()) {
        // Pop next work item
        const DfgVertex* const vtxp = queue.back();
        queue.pop_back();
        // Mark vertex as visited, move on if already visited
        if (!resp->insert(vtxp).second) continue;
        // Enqueue all siblings of this vertex.
        if VL_CONSTEXPR_CXX17 (T_SinksNotSources) {
            vtxp->forEachSink([&](const DfgVertex& sink) { queue.push_back(&sink); });
        } else {
            vtxp->forEachSource([&](const DfgVertex& src) { queue.push_back(&src); });
        }
    }
    // Done
    return resp;
}

std::unique_ptr<std::unordered_set<const DfgVertex*>>
DfgGraph::sourceCone(const std::vector<const DfgVertex*>& vtxps) const {
    return dfgGraphCollectCone<false>(vtxps);
}

std::unique_ptr<std::unordered_set<const DfgVertex*>>
DfgGraph::sinkCone(const std::vector<const DfgVertex*>& vtxps) const {
    return dfgGraphCollectCone<true>(vtxps);
}

//------------------------------------------------------------------------------
// DfgEdge

void DfgEdge::unlinkSource() {
    if (!m_sourcep) return;
#ifdef VL_DEBUG
    {
        DfgEdge* currp = m_sourcep->m_sinksp;
        while (currp) {
            if (currp == this) break;
            currp = currp->m_nextp;
        }
        UASSERT(currp, "'m_sourcep' does not have this edge as sink");
    }
#endif
    // Relink pointers of predecessor and successor
    if (m_prevp) m_prevp->m_nextp = m_nextp;
    if (m_nextp) m_nextp->m_prevp = m_prevp;
    // If head of list in source, update source's head pointer
    if (m_sourcep->m_sinksp == this) m_sourcep->m_sinksp = m_nextp;
    // Mark source as unconnected
    m_sourcep = nullptr;
    // Clear links. This is not strictly necessary, but might catch bugs.
    m_prevp = nullptr;
    m_nextp = nullptr;
}

void DfgEdge::relinkSource(DfgVertex* newSourcep) {
    // Unlink current source, if any
    unlinkSource();
    // Link new source
    m_sourcep = newSourcep;
    // Prepend to sink list in source
    m_nextp = newSourcep->m_sinksp;
    if (m_nextp) m_nextp->m_prevp = this;
    newSourcep->m_sinksp = this;
}

//------------------------------------------------------------------------------
// DfgVertex

DfgVertex::DfgVertex(DfgGraph& dfg, VDfgType type, FileLine* flp, AstNodeDType* dtypep)
    : m_filelinep{flp}
    , m_dtypep{dtypep}
    , m_type{type} {
    dfg.addVertex(*this);
}

bool DfgVertex::equals(const DfgVertex& that, EqualsCache& cache) const {
    // If same vertex, then equal
    if (this == &that) return true;

    // If different type, then not equal
    if (this->type() != that.type()) return false;

    // If different data type, then not equal
    if (this->dtypep() != that.dtypep()) return false;

    // Check vertex specifics
    if (!this->selfEquals(that)) return false;

    // Check sources
    const auto key = (this < &that) ? EqualsCache::key_type{this, &that}  //
                                    : EqualsCache::key_type{&that, this};
    // Note: the recursive invocation can cause a re-hash but that will not invalidate references
    uint8_t& result = cache[key];
    if (!result) {
        const bool equal = [&]() -> bool {
            if (is<DfgVertexNullary>()) return true;
            if (const DfgVertexUnary* const thisp = cast<DfgVertexUnary>()) {
                const DfgVertexUnary* const thatp = that.as<DfgVertexUnary>();
                if (!thisp->src0p()->equals(*thatp->src0p(), cache)) return false;
                return true;
            }
            if (const DfgVertexBinary* const thisp = cast<DfgVertexBinary>()) {
                const DfgVertexBinary* const thatp = that.as<DfgVertexBinary>();
                if (!thisp->src0p()->equals(*thatp->src0p(), cache)) return false;
                if (!thisp->src1p()->equals(*thatp->src1p(), cache)) return false;
                return true;
            }
            if (const DfgVertexTernary* const thisp = cast<DfgVertexTernary>()) {
                const DfgVertexTernary* const thatp = that.as<DfgVertexTernary>();
                if (!thisp->src0p()->equals(*thatp->src0p(), cache)) return false;
                if (!thisp->src1p()->equals(*thatp->src1p(), cache)) return false;
                if (!thisp->src2p()->equals(*thatp->src2p(), cache)) return false;
                return true;
            }
            // TODO: splice
            if (const DfgVertexVariadic* const thisp = cast<DfgVertexVariadic>()) {
                const DfgVertexVariadic* const thatp = that.as<DfgVertexVariadic>();
                size_t n = thisp->srcsSize();
                for (size_t i = 0; i < n; ++i) {
                    if (!thisp->srcp(i)->equals(*thatp->srcp(i), cache)) return false;
                }
                return true;
            }
            v3fatalSrc("Unknown vertex type " << typeName());  // LCOV_EXCL_LINE
        }();
        result = (static_cast<uint8_t>(equal) << 1) | 1;
    }
    return result >> 1;
}

V3Hash DfgVertex::hash() {
    V3Hash& result = user<V3Hash>();
    if (!result.value()) {
        V3Hash hash{selfHash()};
        // Variables are defined by themselves, so there is no need to hash them further
        // (especially the sources). This enables sound hashing of graphs circular only through
        // variables, which we rely on.
        if (!is<DfgVertexVar>()) {
            hash += m_type;
            hash += size();
            forEachSource([&](DfgVertex& vtx) { hash += vtx.hash(); });
        }
        result = hash;
    }
    return result;
}

uint32_t DfgVertex::fanout() const {
    uint32_t result = 0;
    forEachSink([&](const DfgVertex&) { ++result; });
    return result;
}

DfgVertexVar* DfgVertex::getResultVar() {
    // It's easy if the vertex is already a variable ...
    if (DfgVertexVar* const varp = this->cast<DfgVertexVar>()) return varp;

    // Inspect existing variables written by this vertex, and choose one
    DfgVertexVar* resp = nullptr;
    // cppcheck-has-bug-suppress constParameter
    this->forEachSink([&resp](DfgVertex& sink) {
        DfgVertexVar* const varp = sink.cast<DfgVertexVar>();
        if (!varp) return;
        // First variable found
        if (!resp) {
            resp = varp;
            return;
        }

        // Prefer those variables that must be kept anyway
        if (resp->hasExtRefs() != varp->hasExtRefs()) {
            if (!resp->hasExtRefs()) resp = varp;
            return;
        }
        if (resp->hasModWrRefs() != varp->hasModWrRefs()) {
            if (!resp->hasModWrRefs()) resp = varp;
            return;
        }
        if (resp->hasDfgRefs() != varp->hasDfgRefs()) {
            if (!resp->hasDfgRefs()) resp = varp;
            return;
        }
        // Prefer those that already have module references
        if (resp->hasModRdRefs() != varp->hasModRdRefs()) {
            if (!resp->hasModRdRefs()) resp = varp;
            return;
        }
        // Prefer real variabels over temporaries
        if (!resp->tmpForp() != !varp->tmpForp()) {
            if (resp->tmpForp()) resp = varp;
            return;
        }
        // Prefer the earlier one in source order
        const FileLine& oldFlp = *(resp->fileline());
        const FileLine& newFlp = *(varp->fileline());
        if (const int cmp = oldFlp.operatorCompare(newFlp)) {
            if (cmp > 0) resp = varp;
            return;
        }
        // Prefer the one with the lexically smaller name
        if (const int cmp = resp->nodep()->name().compare(varp->nodep()->name())) {
            if (cmp > 0) resp = varp;
            return;
        }
        // 'resp' and 'varp' are all the same, keep using the existing 'resp'
    });
    return resp;
}

AstScope* DfgVertex::scopep(ScopeCache& cache, bool tryResultVar) VL_MT_DISABLED {
    // If this is a variable, we are done
    if (const DfgVertexVar* const varp = this->cast<DfgVertexVar>()) {
        return varp->varScopep()->scopep();
    }

    // Try the result var first if instructed (usully only in the recursive case)
    if (tryResultVar) {
        if (const DfgVertexVar* const varp = this->getResultVar()) {
            return varp->varScopep()->scopep();
        }
    }

    // Note: the recursive invocation can cause a re-hash but that will not invalidate references
    AstScope*& resultr = cache[this];
    if (!resultr) {
        // Mark to prevent infinite recursion on circular graphs - should never be called on such
        resultr = reinterpret_cast<AstScope*>(1);
        // Find scope based on sources, falling back on the root scope
        AstScope* const rootp = v3Global.rootp()->topScopep()->scopep();
        AstScope* foundp = nullptr;
        forEachSource([&](DfgVertex& src) {
            if (foundp) return;
            AstScope* const scp = src.scopep(cache, true);
            if (scp != rootp) foundp = scp;
        });
        resultr = foundp ? foundp : rootp;
    }

    // Die on a graph circular through operation vertices
    UASSERT_OBJ(resultr != reinterpret_cast<AstScope*>(1), this,
                "DfgVertex::scopep called on graph with circular operations");

    // Done
    return resultr;
}

void DfgVertex::unlinkDelete(DfgGraph& dfg) {
    // Unlink sink edges
    while (m_sinksp) m_sinksp->unlinkSource();
    // Remove from graph
    dfg.removeVertex(*this);
    // Delete - this will unlink sources
    delete this;
}

void DfgVertex::replaceWith(DfgVertex* newSorucep) {
    while (m_sinksp) m_sinksp->relinkSource(newSorucep);
}

//------------------------------------------------------------------------------
// DfgVisitor

#include "V3Dfg__gen_visitor_defns.h"  // From ./astgen
