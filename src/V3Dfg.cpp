// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Data flow graph data structures
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Dfg.h"
#include "V3File.h"

#include <cctype>
#include <unordered_map>

//------------------------------------------------------------------------------
// DfgGraph
//------------------------------------------------------------------------------

DfgGraph::DfgGraph(AstModule& module, const string& name)
    : m_modulep{&module}
    , m_name{name} {}

DfgGraph::~DfgGraph() {
    forEachVertex([](DfgVertex& vtxp) { delete &vtxp; });
}

std::vector<std::unique_ptr<DfgGraph>> DfgGraph::splitIntoComponents() {
    size_t componentNumber = 0;
    std::unordered_map<const DfgVertex*, unsigned> vertex2component;

    forEachVertex([&](const DfgVertex& vtx) {
        // If already assigned this vertex to a component, then continue
        if (vertex2component.count(&vtx)) return;

        // Work queue for depth first traversal starting from this vertex
        std::vector<const DfgVertex*> queue{&vtx};

        // Depth first traversal
        while (!queue.empty()) {
            // Pop next work item
            const DfgVertex& item = *queue.back();
            queue.pop_back();

            // Mark vertex as belonging to current component (if it's not marked yet)
            const bool isFirstEncounter = vertex2component.emplace(&item, componentNumber).second;

            // If we have already visited this vertex during the traversal, then move on.
            if (!isFirstEncounter) continue;

            // Enqueue all sources and sinks of this vertex.
            item.forEachSource([&](const DfgVertex& src, size_t) { queue.push_back(&src); });
            item.forEachSink([&](const DfgVertex& dst) { queue.push_back(&dst); });
        }

        // Done with this component
        ++componentNumber;
    });

    // Create the component graphs
    std::vector<std::unique_ptr<DfgGraph>> results{componentNumber};

    for (size_t i = 0; i < componentNumber; ++i) {
        results[i].reset(new DfgGraph{*m_modulep, name() + "-component-" + cvtToStr(i)});
    }

    // Move all vertices under the corresponding component graphs
    forEachVertex([&](DfgVertex& vtx) {
        this->removeVertex(vtx);
        results[vertex2component[&vtx]]->addVertex(vtx);
    });

    UASSERT(m_vertices.empty(), "'this' DfgGraph should have been emptied");

    return results;
}

static const string toDotId(const DfgVertex& vtx) {
    string str;
    str += '"';
    str += cvtToHex(&vtx);
    str += '"';
    return str;
}

// Dump one DfgVertex in Graphviz format
static void dumpDotVertex(std::ostream& os, const DfgVertex& vtx) {
    os << toDotId(vtx);
    if (const DfgVar* const varVtxp = vtx.cast<DfgVar>()) {
        AstVar* const varp = varVtxp->varp();
        os << " [label=\"" << varp->name() << "\nW" << varVtxp->width() << " / F"
           << varVtxp->fanout() << '"';
        if (varp->isIO()) {
            if (varp->direction() == VDirection::INPUT) {
                os << ", shape=invhouse";
            } else if (varp->direction() == VDirection::OUTPUT) {
                os << ", shape=house";
            } else {
                os << ", shape=star";
            }
        } else {
            os << ", shape=box";
            if (varVtxp->hasExtRefs()) os << ", style=diagonals";
        }
        os << "]";
    } else if (const DfgConst* const constVtxp = vtx.cast<DfgConst>()) {
        const V3Number& num = constVtxp->constp()->num();
        os << " [label=\"";
        if (num.width() <= 32 && !num.isSigned()) {
            os << constVtxp->width() << "'d" << num.toUInt() << "\n";
            os << constVtxp->width() << "'h" << std::hex << num.toUInt() << std::dec;
        } else {
            os << num.ascii();
        }
        os << '"';
        os << ", shape=plain";
        os << "]";
    } else {
        os << " [label=\"" << vtx.typeName() << "\nW" << vtx.width() << " / F" << vtx.fanout()
           << '"';
        if (vtx.hasMultipleSinks())
            os << ", shape=doublecircle";
        else
            os << ", shape=circle";
        os << "]";
    }
    os << endl;
}

// Dump one DfgEdge in Graphviz format
static void dumpDotEdge(std::ostream& os, const DfgEdge& edge, const string& headlabel) {
    os << toDotId(*edge.sourcep()) << " -> " << toDotId(*edge.sinkp());
    if (!headlabel.empty()) os << " [headlabel=\"" << headlabel << "\"]";
    os << endl;
}

// Dump one DfgVertex and all of its source DfgEdges in Graphviz format
static void dumpDotVertexAndSourceEdges(std::ostream& os, const DfgVertex& vtx) {
    dumpDotVertex(os, vtx);
    vtx.forEachSourceEdge([&](const DfgEdge& edge, size_t idx) {  //
        if (edge.sourcep()) {
            string headLabel;
            if (vtx.arity() > 1) headLabel = std::toupper(vtx.srcName(idx)[0]);
            dumpDotEdge(os, edge, headLabel);
        }
    });
}

void DfgGraph::dumpDot(std::ostream& os, const string& label) const {
    // Header
    os << "digraph dfg {" << endl;
    if (!label.empty()) os << "graph [label=\"" << label << "\", labelloc=t, labeljust=l]" << endl;
    os << "graph [rankdir=TB]" << endl;

    // Emit all vertices
    forEachVertex([&](const DfgVertex& vtx) { dumpDotVertexAndSourceEdges(os, vtx); });

    // Footer
    os << "}" << endl;
}

void DfgGraph::dumpDotFile(const string& fileName, const string& label) const {
    // This generates a file used by graphviz, https://www.graphviz.org
    // "hardcoded" parameters:
    const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(fileName)};
    if (os->fail()) v3fatal("Cannot write to file: " << fileName);
    dumpDot(*os.get(), label);
    os->close();
}

void DfgGraph::dumpDotFilePrefixed(const string& name) const {
    dumpDotFile(v3Global.debugFilename(name) + ".dot", name);
}

// Dump upstream logic cone starting from given vertex
static void dumpDotUpstreamConeFromVertex(std::ostream& os, const DfgVertex& vtx) {
    // Work queue for depth first traversal starting from this vertex
    std::vector<const DfgVertex*> queue{&vtx};

    // Set of already visited vertices
    std::unordered_set<const DfgVertex*> visited;

    // Depth first traversal
    while (!queue.empty()) {
        // Pop next work item
        const DfgVertex* const itemp = queue.back();
        queue.pop_back();

        // Mark vertex as visited
        const bool isFirstEncounter = visited.insert(itemp).second;

        // If we have already visited this vertex during the traversal, then move on.
        if (!isFirstEncounter) continue;

        // Enqueue all sources of this vertex.
        itemp->forEachSource([&](const DfgVertex& src, size_t) { queue.push_back(&src); });

        // Emit this vertex and all of its source edges
        dumpDotVertexAndSourceEdges(os, *itemp);
    }

    // Emit all DfgVar vertices that have external references driven by this vertex
    vtx.forEachSink([&](const DfgVertex& dst) {
        if (const DfgVar* const varVtxp = dst.cast<DfgVar>()) {
            if (varVtxp->hasExtRefs()) dumpDotVertexAndSourceEdges(os, dst);
        }
    });
}

void DfgGraph::dumpDotUpstreamCone(const string& fileName, const DfgVertex& vtx,
                                   const string& name) const {
    // Open output file
    const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(fileName)};
    if (os->fail()) v3fatal("Cannot write to file: " << fileName);

    // Header
    *os << "digraph dfg {" << endl;
    if (!name.empty()) *os << "graph [label=\"" << name << "\", labelloc=t, labeljust=l]" << endl;
    *os << "graph [rankdir=TB]" << endl;

    // Dump the cone
    dumpDotUpstreamConeFromVertex(*os, vtx);

    // Footer
    *os << "}" << endl;

    // Done
    os->close();
}

void DfgGraph::dumpDotAllVarConesPrefixed(const string& name) const {
    forEachVertex([&](const DfgVertex& vtx) {
        // Check if this node drives an externally referenced variable.
        const DfgVar* const sinkp = vtx.findSink<DfgVar>([](const DfgVar& sink) {  //
            return sink.hasExtRefs();
        });

        // We only dump cones driving an externally referenced variable
        if (!sinkp) return;

        // Open output file
        const string coneName{name + "-cone-" + sinkp->varp()->name()};
        const string fileName{v3Global.debugFilename(coneName) + ".dot"};
        const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(fileName)};
        if (os->fail()) v3fatal("Cannot write to file: " << fileName);

        // Header
        *os << "digraph dfg {" << endl;
        *os << "graph [label=\"" << coneName << "\", labelloc=t, labeljust=l]" << endl;
        *os << "graph [rankdir=TB]" << endl;

        // Dump this cone
        dumpDotUpstreamConeFromVertex(*os, vtx);

        // Footer
        *os << "}" << endl;

        // Done with this logic cone
        os->close();
    });
}

//------------------------------------------------------------------------------
// DfgEdge
//------------------------------------------------------------------------------

void DfgEdge::unlinkSource() {
    if (m_sourcep) {
#ifdef VL_DEBUG
        {
            DfgEdge* sinkp = m_sourcep->m_sinksp;
            while (sinkp) {
                if (sinkp == this) break;
                sinkp = sinkp->m_nextp;
            }
            UASSERT(sinkp, "'m_sourcep' does not have this edge as sink");
        }
#endif
        // Relink pointers of predecessor and successor
        if (m_prevp) m_prevp->m_nextp = m_nextp;
        if (m_nextp) m_nextp->m_prevp = m_prevp;
        // If head of list in source, update source's head pointer
        if (this == m_sourcep->m_sinksp) m_sourcep->m_sinksp = m_nextp;
        // Mark source as unconnected
        m_sourcep = nullptr;
        // Clear links is not strictly necessary, but might catch bugs
        m_prevp = nullptr;
        m_nextp = nullptr;
    }
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
//------------------------------------------------------------------------------

DfgVertex::DfgVertex(DfgGraph& dfg, FileLine* flp, uint32_t width, DfgType type)
    : m_filelinep{flp}
    , m_width{width}
    , m_type{type} {
    dfg.addVertex(*this);
}

bool DfgVertex::equals(const DfgVertex& that, EqualsCache& cache) const {
    const auto key = (this < &that) ? EqualsCache::key_type{this, &that}  //
                                    : EqualsCache::key_type{&that, this};
    const auto it = cache.find(key);
    if (it != cache.end()) return it->second;

    if (!this->selfEquals(that)) return false;
    auto thisPair = this->sourceEdges();
    const DfgEdge* const thisSrcEdgesp = thisPair.first;
    const size_t thisArity = thisPair.second;
    auto thatPair = that.sourceEdges();
    const DfgEdge* const thatSrcEdgesp = thatPair.first;
    const size_t thatArity = thatPair.second;
    UASSERT_OBJ(thisArity == thatArity, this, "Same type vertices must have same arity!");
    bool result = true;
    for (size_t i = 0; i < thisArity; ++i) {
        const DfgVertex* const thisSrcVtxp = thisSrcEdgesp[i].m_sourcep;
        const DfgVertex* const thatSrcVtxp = thatSrcEdgesp[i].m_sourcep;
        if (thisSrcVtxp) {
            if (!thatSrcVtxp || !thisSrcVtxp->equals(*thatSrcVtxp, cache)) {
                result = false;
                break;
            }
        } else {
            if (thatSrcVtxp) {
                result = false;
                break;
            }
        }
    }

    cache.emplace(key, result);
    return result;
}

V3Hash DfgVertex::hash(HashCache& cache) const {
    const auto key = this;
    const auto it = cache.find(key);
    if (it != cache.end()) return it->second;

    V3Hash result{selfHash()};
    forEachSource([&](const DfgVertex& src, size_t) { result += src.hash(cache); });

    cache.emplace(key, result);
    return result;
}

uint32_t DfgVertex::fanout() const {
    uint32_t result = 0;
    forEachSinkEdge([&](const DfgEdge&) { ++result; });
    return result;
}

void DfgVertex::unlinkDelete(DfgGraph& dfg) {
    // Unlink source edges
    forEachSourceEdge([](DfgEdge& edge, size_t) { edge.unlinkSource(); });
    // Unlink sink edges
    forEachSinkEdge([](DfgEdge& edge) { edge.unlinkSource(); });
    // Remove from graph
    dfg.removeVertex(*this);
    // Delete
    delete this;
}

void DfgVertex::replaceWith(DfgVertex* newSorucep) {
    while (m_sinksp) { m_sinksp->relinkSource(newSorucep); }
}

//------------------------------------------------------------------------------
// Vertex classes
//------------------------------------------------------------------------------

void DfgVar::accept(DfgVVisitor& visitor) { visitor.visit(this); }

bool DfgVar::selfEquals(const DfgVertex& that) const {
    if (const DfgVar* otherp = that.cast<DfgVar>()) {  //
        return varp() == otherp->varp();
    }
    return false;
}

V3Hash DfgVar::selfHash() const { return V3Hasher::uncachedHash(m_varp); }

void DfgConst::accept(DfgVVisitor& visitor) { visitor.visit(this); }

bool DfgConst::selfEquals(const DfgVertex& that) const {
    if (const DfgConst* otherp = that.cast<DfgConst>()) {
        return constp()->sameTree(otherp->constp());
    }
    return false;
}

V3Hash DfgConst::selfHash() const { return V3Hasher::uncachedHash(m_constp); }

//------------------------------------------------------------------------------
// DfgVVisitor
//------------------------------------------------------------------------------

void DfgVVisitor::visit(DfgVar* vtxp) { visit(static_cast<DfgVertex*>(vtxp)); }

void DfgVVisitor::visit(DfgConst* vtxp) { visit(static_cast<DfgVertex*>(vtxp)); }

//------------------------------------------------------------------------------
// 'astgen' generated definitions
//------------------------------------------------------------------------------

#include "V3Dfg__gen_definitions.h"
