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

#ifndef VERILATOR_V3DFG_H_
#define VERILATOR_V3DFG_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3List.h"
#include "V3Hash.h"
#include "V3Hasher.h"

#include <functional>
#include <type_traits>
#include <unordered_map>
#include <vector>

class DfgGraph;
class DfgVertex;
class DfgEdge;
class DfgVVisitor;

class DfgConst;

namespace {
// C++14 std::enable_if_t ...
template <bool c, typename T = void>  //
using enable_if_t = typename std::enable_if<c, T>::type;
}  // namespace

//------------------------------------------------------------------------------
// Dataflow graph
//------------------------------------------------------------------------------

class DfgGraph final {
    friend class DfgVertex;

    V3List<DfgVertex*> m_vertices;  // The vertices in the graph

    AstModule* m_modulep;  // Parent of the graph

    const string m_name;  // Name of graph (for debugging)

    // Add DfgVertex to this graph (assumes not yet contained)
    void addVertex(DfgVertex& vtx);
    // Remove DfgVertex form this graph (assume it is contained)
    void removeVertex(DfgVertex& vtx);

public:
    // Constructor. The given AstNodeModule is the module this graph lives under
    explicit DfgGraph(AstModule& module, const string& name = "");

    // Destructor. Destroys all contained vertices.
    ~DfgGraph();

    // DfgGraph is not copyable
    VL_UNCOPYABLE(DfgGraph);

    //
    AstModule* modulep() { return m_modulep; }

    //
    const string& name() { return m_name; }

    // Calls given function 'f' for each vertex in the graph. It is safe to manipulate any vertices
    // in the graph, or to delete/unlink the vertex passed to 'f' during iteration. It is however
    // not safe to delete/unlink any vertex in the same graph other than the one passed to 'f'.
    void forEachVertex(std::function<void(DfgVertex&)> f);

    // 'const' variant. No mutation allowed.
    void forEachVertex(std::function<void(const DfgVertex&)> f) const;

    // Iterates backwards
    void forEachVertexBackwards(std::function<void(DfgVertex&)> f);

    // Returns first vertex of type 'Vertex' that satisfies the given predicate 'p',
    // or nullptr if no such vertex
    template <typename Vertex>  //
    Vertex* findVertex(std::function<bool(const Vertex&)> p) const;

    // Split this graph into individual components (unique sub-graphs with no edges between them).
    // Leaves 'this' graph empty.
    std::vector<std::unique_ptr<DfgGraph>> splitIntoComponents();

    // Dump graph in Graphviz format into the given stream 'os'. 'name' is the name of the graph
    // which is included in the output.
    void dumpDot(std::ostream& os, const string& name = "") const;
    // Dump graph in Graphviz format into a new file with the given 'fileName'. 'name' is the name
    // of the graph which is included in the output.
    void dumpDotFile(const string& fileName, const string& name = "") const;
    // Dump graph in Graphviz format into a new automatically numbered debug file. 'name' is the
    // name of the graph, which is included in the file name and the output.
    void dumpDotFilePrefixed(const string& name) const;
    // Dump upstream (source) logic cone starting from given vertex into a file with the given
    // 'fileName'. 'name' is the name of the graph, which is included in the output.
    void dumpDotUpstreamCone(const string& fileName, const DfgVertex& vtx,
                             const string& name = "") const;
    // Dump all individual logic cones driving external variables in Graphviz format into separate
    // new automatically numbered debug files. 'name' is the name of the graph, which is included
    // in the file name and the output. This is useful for very large graphs that are otherwise
    // difficult to browse visually due to their size.
    void dumpDotAllVarConesPrefixed(const string& name) const;
};

//------------------------------------------------------------------------------
// Dataflow graph edge
//------------------------------------------------------------------------------

class DfgEdge final {
    friend class DfgVertex;
    template <size_t Arity> friend class DfgVertexWithArity;

    DfgEdge* m_nextp = nullptr;  // Next edge in sink list
    DfgEdge* m_prevp = nullptr;  // Previous edge in sink list
    DfgVertex* m_sourcep = nullptr;  // The source node driving this edge
    DfgVertex* const m_sinkp;  // The sink node. The sink owns the edge, so immutable

    explicit DfgEdge(DfgVertex* sinkp)  // The sink nodes own the edges, hence private
        : m_sinkp{sinkp} {}

public:
    // The source (driver) of this edge
    DfgVertex* sourcep() const { return m_sourcep; }

    // The sink (consumer) of this edge
    DfgVertex* sinkp() const { return m_sinkp; }

    // Remove driver of this edge
    void unlinkSource();

    // Relink this edge to be driven from the given new source node
    void relinkSource(DfgVertex* newSourcep);
};

//------------------------------------------------------------------------------
// Dataflow graph vertex
//------------------------------------------------------------------------------

// Reuse the generated type constants
using DfgType = VNType;

// Base data flow graph node
class DfgVertex VL_NOT_FINAL {
    friend class DfgGraph;
    friend class DfgEdge;
    friend class DfgVVisitor;

    V3ListEnt<DfgVertex*> m_vertices;  // V3List handle of this vertex, kept under the DfgGraph
protected:
    DfgEdge* m_sinksp = nullptr;  // List of sinks of this node
    FileLine* const m_filelinep;  // Source location
    uint32_t m_width = 0;  // Width of the result of this node
    const DfgType m_type;

    DfgVertex(DfgGraph& dfg, FileLine* flp, uint32_t width, DfgType type);

public:
    virtual ~DfgVertex() = default;

private:
    // Visitor accept method
    virtual void accept(DfgVVisitor& v) = 0;

    // Hash of keys to 'EqualsCache' below
    struct EqualsCacheHash {
        std::size_t
        operator()(const std::pair<const DfgVertex*, const DfgVertex*>& item) const noexcept {
            const size_t a = reinterpret_cast<std::uintptr_t>(item.first);
            const size_t b = reinterpret_cast<std::uintptr_t>(item.second);
            constexpr size_t halfWidth = 8 * sizeof(b) / 2;
            return a ^ ((b << halfWidth) | (b >> halfWidth));
        }
    };

    // Part of Vertex equality only dependent on this vertex
    virtual bool selfEquals(const DfgVertex& that) const {
        return (this == &that) || (this->m_type == that.m_type && this->width() == that.width());
    }

    // Part of Vertex hash only dependent on this vertex
    virtual V3Hash selfHash() const { return V3Hash{m_type} + m_width; }

public:
    // Source location
    FileLine* fileline() const { return m_filelinep; }

    // Width of result
    uint32_t width() const { return m_width; }

    // Cache type for 'equals' below
    using EqualsCache
        = std::unordered_map<std::pair<const DfgVertex*, const DfgVertex*>, bool, EqualsCacheHash>;

    // Vertex equality (depends on this vertex and all sources). Returns true, if the vertices
    // can be substituted for each other without changing the semantics of the logic.
    // The 'cache' argument is used to store results to avoid repeat evaluations, but it requires
    // that the upstream sources of the compared vertices do not change between invocations.
    bool equals(const DfgVertex& that, EqualsCache& cache) const;

    // Cache type for 'hash' below
    using HashCache = std::unordered_map<const DfgVertex*, V3Hash>;

    // Hash of vertex (depends on this vertex and all sources).
    // The 'cache' argument is used to store results to avoid repeat evaluations, but it requires
    // that the upstream sources of the vertex do not change between invocations.
    V3Hash hash(HashCache& cache) const;

    // Uncached version of 'equals'
    bool equals(const DfgVertex& that) const {
        EqualsCache cache;  // Still cache recursive calls within this invocation
        return equals(that, cache);
    }

    // Uncached version of 'hash'
    V3Hash hash() const {
        HashCache cache;  // Still cache recursive calls within this invocation
        return hash(cache);
    }

    // Source edges of this vertex
    virtual std::pair<DfgEdge*, size_t> sourceEdges() { return {nullptr, 0}; }

    // Source edges of this vertex
    virtual std::pair<const DfgEdge*, size_t> sourceEdges() const { return {nullptr, 0}; }

    // Arity (number of sources) of this node
    size_t arity() const { return sourceEdges().second; }

    // Predicate: has 0 sinks
    bool hasSinks() const { return m_sinksp != nullptr; }

    // Predicate: has 2 or more sinks
    bool hasMultipleSinks() const { return m_sinksp && m_sinksp->m_nextp; }

    // Fanout (number of sinks) of this node (expensive to compute)
    uint32_t fanout() const;

    // Unlink from container (graph or builder), then delete this vertex
    void unlinkDelete(DfgGraph& dfg);

    // Relink all sinks to be driven from the given new source
    void replaceWith(DfgVertex* newSourcep);

    // Calls given function 'f' for each source of this node. Also passes source index.
    // Unconnected sources are not iterated.
    void forEachSource(std::function<void(const DfgVertex&, size_t)> f) const;

    // Calls given function 'f' for each sink of this node
    void forEachSink(std::function<void(DfgVertex&)> f);

    // Calls given function 'f' for each sink of this node
    void forEachSink(std::function<void(const DfgVertex&)> f) const;

    // Calls given function 'f' for each source edge of this vertex. Also passes source index.
    void forEachSourceEdge(std::function<void(DfgEdge&, size_t)> f);

    // Calls given function 'f' for each source edge of this vertex. Also passes source index.
    void forEachSourceEdge(std::function<void(const DfgEdge&, size_t)> f) const;

    // Calls given function 'f' for each sink edge of this vertex.
    // Unlinking/deleting the given sink during iteration is safe, but not other sinks of this
    // vertex.
    void forEachSinkEdge(std::function<void(DfgEdge&)> f);

    // Calls given function 'f' for each sink edge of this vertex.
    void forEachSinkEdge(std::function<void(const DfgEdge&)> f) const;

    // Returns first sink node of type 'Vertex' which satisfies the given predicate 'p',
    // or nullptr if no such sink node
    template <typename Vertex>  //
    Vertex* findSink(std::function<bool(const Vertex&)> p) const;

    // Returns first sink node of type 'Vertex', or nullptr if no such sink node. This is
    // a special case of 'findSink' above with the predicate always true.
    template <typename Vertex>  //
    Vertex* findSink() const;

    // Is this a DfgConst that is all zeroes
    bool isZero() const;

    // Is this a DfgConst that is all ones
    bool isOnes() const;

    // Error reporting/messaging
    void v3errorEnd(std::ostringstream& str) const { m_filelinep->v3errorEnd(str); }
    void v3errorEndFatal(std::ostringstream& str) const VL_ATTR_NORETURN {
        m_filelinep->v3errorEndFatal(str);
    }
    string warnContextPrimary() const { return fileline()->warnContextPrimary(); }
    string warnContextSecondary() const { return fileline()->warnContextSecondary(); }
    string warnMore() const { return fileline()->warnMore(); }
    string warnOther() const { return fileline()->warnOther(); }

    // Subtype test
    template <typename T> constexpr bool is() const {
        static_assert(std::is_base_of<DfgVertex, T>::value, "'T' must be a subtype of DfgVertex");
        return m_type == T::dfgType();
    }

    // Ensure subtype, then cast to that type
    template <typename T> constexpr T* as() {
        UASSERT(is<T>(),
                "DfgVertex is not of expected type, but instead has type '" << typeName() << "'");
        return static_cast<T*>(this);
    }
    template <typename T> constexpr const T* as() const {
        UASSERT(is<T>(),
                "DfgVertex is not of expected type, but instead has type '" << typeName() << "'");
        return static_cast<const T*>(this);
    }

    // Cast to subtype, or null if different
    template <typename T> constexpr T* cast() {  //
        return is<T>() ? static_cast<T*>(this) : nullptr;
    }
    template <typename T> constexpr const T* cast() const {
        return is<T>() ? static_cast<const T*>(this) : nullptr;
    }

    // Human-readable node type as string for debugging
    const string typeName() const { return m_type.ascii(); }

    // Human-readable name for source operand with given index for debugging
    virtual const string srcName(size_t idx) const { return cvtToStr(idx); }
};

// DfgVertices are, well ... DfgVertices
template <> constexpr bool DfgVertex::is<DfgVertex>() const { return true; }
template <> constexpr DfgVertex* DfgVertex::as<DfgVertex>() { return this; }
template <> constexpr const DfgVertex* DfgVertex::as<DfgVertex>() const { return this; }
template <> constexpr DfgVertex* DfgVertex::cast<DfgVertex>() { return this; }
template <> constexpr const DfgVertex* DfgVertex::cast<DfgVertex>() const { return this; }

template <size_t Arity>  //
class DfgVertexWithArity VL_NOT_FINAL : public DfgVertex {
    static_assert(1 <= Arity && Arity <= 4, "Arity must be between 1 and 4 inclusive");

    // Uninitialized storage for source edges
    typename std::aligned_storage<sizeof(DfgEdge[Arity]), alignof(DfgEdge[Arity])>::type
        m_sourceEdges;

    constexpr inline DfgEdge& sourceEdge(size_t index) {
        return reinterpret_cast<DfgEdge*>(&m_sourceEdges)[index];
    }
    constexpr inline const DfgEdge& sourceEdge(size_t index) const {
        return reinterpret_cast<const DfgEdge*>(&m_sourceEdges)[index];
    }

protected:
    DfgVertexWithArity<Arity>(DfgGraph& dfg, FileLine* flp, uint32_t width, DfgType type)
        : DfgVertex{dfg, flp, width, type} {
        // Initialize source edges
        for (size_t i = 0; i < Arity; ++i) new (&sourceEdge(i)) DfgEdge{this};
    }

    virtual ~DfgVertexWithArity<Arity>() = default;

public:
    virtual std::pair<DfgEdge*, size_t> sourceEdges() override {  //
        return {&sourceEdge(0), Arity};
    }
    virtual std::pair<const DfgEdge*, size_t> sourceEdges() const override {
        return {&sourceEdge(0), Arity};
    }

    template <size_t Index>  //
    DfgVertex* source() const {
        return sourceEdge(Index).m_sourcep;
    }

    template <size_t Index>  //
    void relinkSource(DfgVertex* newSourcep) {
        static_assert(Index < Arity, "Source index out of range");
        UASSERT(sourceEdge(Index).m_sinkp == this, "Inconsistent");
        sourceEdge(Index).relinkSource(newSourcep);
    }

    // Named source getter/setter for unary vertices
    template <size_t A = Arity>  //
    typename std::enable_if<A == 1, DfgVertex*>::type srcp() const {
        static_assert(A == Arity, "Should not be changed");
        return source<0>();
    }
    template <size_t A = Arity>  //
    typename std::enable_if<A == 1, void>::type srcp(DfgVertex* vtxp) {
        static_assert(A == Arity, "Should not be changed");
        relinkSource<0>(vtxp);
    }

    // Named source getter/setter for binary vertices
    template <size_t A = Arity>  //
    typename std::enable_if<A == 2, DfgVertex*>::type lhsp() const {
        static_assert(A == Arity, "Should not be changed");
        return source<0>();
    }
    template <size_t A = Arity>  //
    typename std::enable_if<A == 2, void>::type lhsp(DfgVertex* vtxp) {
        static_assert(A == Arity, "Should not be changed");
        relinkSource<0>(vtxp);
    }

    template <size_t A = Arity>  //
    typename std::enable_if<A == 2, DfgVertex*>::type rhsp() const {
        static_assert(A == Arity, "Should not be changed");
        return source<1>();
    }
    template <size_t A = Arity>  //
    typename std::enable_if<A == 2, void>::type rhsp(DfgVertex* vtxp) {
        static_assert(A == Arity, "Should not be changed");
        relinkSource<1>(vtxp);
    }

    // Named source getter/setter for unary vertices
    virtual const string srcName(size_t idx) const {
        UASSERT(idx < Arity, "Out of range");
        if /* constexpr */ (Arity == 1) {
            return "srcp";
        } else if /* constexpr */ (Arity == 2) {
            const char* names[2] = {"lhsp", "rhsp"};
            return names[idx];
        } else {
            return DfgVertex::srcName(idx);
        }
    }
};

//------------------------------------------------------------------------------
// Vertex classes
//------------------------------------------------------------------------------

class DfgVar final : public DfgVertexWithArity<1> {
    friend class DfgVVisitor;

    AstVar* const m_varp;  // The AstVar associated with this vertex (not owned by this vertex)
    bool m_hasExtRefs = false;  // Whether this AstVar has references outside the DFG

    void accept(DfgVVisitor& visitor) override;
    bool selfEquals(const DfgVertex& that) const override;
    V3Hash selfHash() const override;

public:
    inline static constexpr DfgType dfgType() { return DfgType::atVar; };
    DfgVar(DfgGraph& dfg, AstVar* varp)
        : DfgVertexWithArity<1>(dfg, varp->fileline(), varp->width(), dfgType())
        , m_varp{varp} {}

    AstVar* varp() const { return m_varp; }
    void setHasExtRefs() { m_hasExtRefs = true; }
    bool hasExtRefs() const { return m_hasExtRefs; }

    DfgVertex* driverp() const { return source<0>(); }
};

class DfgConst final : public DfgVertex {
    friend class DfgVVisitor;

    AstConst* const m_constp;  // The AstConst associated with this vertex (owned by this vertex)

    void accept(DfgVVisitor& visitor) override;
    bool selfEquals(const DfgVertex& that) const override;
    V3Hash selfHash() const override;

public:
    inline static constexpr DfgType dfgType() { return DfgType::atConst; };
    DfgConst(DfgGraph& dfg, AstConst* constp)
        : DfgVertex(dfg, constp->fileline(), constp->width(), dfgType())
        , m_constp{constp} {}

    DfgConst(DfgGraph& dfg, FileLine* fileline, uint32_t value)
        : DfgVertex(dfg, fileline, 32, dfgType())
        , m_constp{new AstConst{fileline, AstConst::WidthedValue{}, 32, value}} {}

    DfgConst(DfgGraph& dfg, FileLine* fileline, const V3Number& value)
        : DfgVertex(dfg, fileline, 32, dfgType())
        , m_constp{new AstConst{fileline, value}} {}

    ~DfgConst() { VL_DO_DANGLING(m_constp->deleteTree(), m_constp); }

    AstConst* constp() const { return m_constp; }
    V3Number& num() const { return m_constp->num(); }

    uint32_t toU32() const { return num().toUInt(); }
    int32_t toI32() const { return num().toSInt(); }

    bool isZero() const { return num().isEqZero(); }
    bool isOnes() const { return num().isEqAllOnes(width()); }
};

// The following is parsed by 'astgen' and used to auto generate parts of DfgVertex subclasses
/* @@@ DFG START
{
    // Names of operand for accessors/dumping
    "operands": {
        "Cond":     ["condp",   "thenp",    "elsep"],
        "Sel":      ["fromp",   "lsbp",     "widthp"]
    }
}
@@@ DFG END */

#include "V3Dfg__gen_vertex_classes.h"

//------------------------------------------------------------------------------
// Dfg vertex visitor
//------------------------------------------------------------------------------

class DfgVVisitor VL_NOT_FINAL {
public:
    // Dispatch to most specific 'visit' method on 'vtxp'
    void iterate(DfgVertex* vtxp) { vtxp->accept(*this); }

    virtual void visit(DfgVar* vtxp);
    virtual void visit(DfgConst* vtxp);
#include "V3Dfg__gen_visitor_decls.h"
};

//------------------------------------------------------------------------------
// Inline method definitions
//------------------------------------------------------------------------------

inline void DfgGraph::addVertex(DfgVertex& vtx) { vtx.m_vertices.pushBack(m_vertices, &vtx); }

inline void DfgGraph::removeVertex(DfgVertex& vtx) { vtx.m_vertices.unlink(m_vertices, &vtx); }

inline void DfgGraph::forEachVertex(std::function<void(DfgVertex&)> f) {
    for (DfgVertex *vtxp = m_vertices.begin(), *nextp; vtxp; vtxp = nextp) {
        nextp = vtxp->m_vertices.nextp();
        f(*vtxp);
    }
}

inline void DfgGraph::forEachVertex(std::function<void(const DfgVertex&)> f) const {
    for (const DfgVertex* vtxp = m_vertices.begin(); vtxp; vtxp = vtxp->m_vertices.nextp()) {
        f(*vtxp);
    }
}

inline void DfgGraph::forEachVertexBackwards(std::function<void(DfgVertex&)> f) {
    for (DfgVertex *vtxp = m_vertices.rbegin(), *nextp; vtxp; vtxp = nextp) {
        nextp = vtxp->m_vertices.prevp();
        f(*vtxp);
    }
}

template <typename Vertex>  //
inline Vertex* DfgGraph::findVertex(std::function<bool(const Vertex&)> p) const {
    static_assert(std::is_base_of<DfgVertex, Vertex>::value,
                  "'Vertex' must be subclass of 'DfgVertex'");
    for (DfgVertex* vtxp = m_vertices.begin(); vtxp; vtxp = vtxp->m_vertices.nextp()) {
        if (Vertex* const vvtxp = vtxp->cast<Vertex>()) {
            if (p(*vvtxp)) return vvtxp;
        }
    }
    return nullptr;
}

inline void DfgVertex::forEachSource(std::function<void(const DfgVertex&, size_t)> f) const {
    const auto pair = sourceEdges();
    const DfgEdge* const edgesp = pair.first;
    const size_t arity = pair.second;
    for (size_t i = 0; i < arity; ++i) {
        if (DfgVertex* const sourcep = edgesp[i].m_sourcep) f(*sourcep, i);
    }
}

inline void DfgVertex::forEachSink(std::function<void(DfgVertex&)> f) {
    for (const DfgEdge* edgep = m_sinksp; edgep; edgep = edgep->m_nextp) f(*edgep->m_sinkp);
}

inline void DfgVertex::forEachSink(std::function<void(const DfgVertex&)> f) const {
    for (const DfgEdge* edgep = m_sinksp; edgep; edgep = edgep->m_nextp) f(*edgep->m_sinkp);
}

inline void DfgVertex::forEachSourceEdge(std::function<void(DfgEdge&, size_t)> f) {
    const auto pair = sourceEdges();
    DfgEdge* const edgesp = pair.first;
    const size_t arity = pair.second;
    for (size_t i = 0; i < arity; ++i) f(edgesp[i], i);
}

inline void DfgVertex::forEachSourceEdge(std::function<void(const DfgEdge&, size_t)> f) const {
    const auto pair = sourceEdges();
    const DfgEdge* const edgesp = pair.first;
    const size_t arity = pair.second;
    for (size_t i = 0; i < arity; ++i) f(edgesp[i], i);
}

inline void DfgVertex::forEachSinkEdge(std::function<void(DfgEdge&)> f) {
    for (DfgEdge *edgep = m_sinksp, *nextp; edgep; edgep = nextp) {
        nextp = edgep->m_nextp;
        f(*edgep);
    }
}

inline void DfgVertex::forEachSinkEdge(std::function<void(const DfgEdge&)> f) const {
    for (DfgEdge *edgep = m_sinksp, *nextp; edgep; edgep = nextp) {
        nextp = edgep->m_nextp;
        f(*edgep);
    }
}

template <typename Vertex>  //
inline Vertex* DfgVertex::findSink(std::function<bool(const Vertex&)> p) const {
    static_assert(std::is_base_of<DfgVertex, Vertex>::value,
                  "'Vertex' must be subclass of 'DfgVertex'");
    for (DfgEdge* edgep = m_sinksp; edgep; edgep = edgep->m_nextp) {
        if (Vertex* const sinkp = edgep->m_sinkp->cast<Vertex>()) {
            if (p(*sinkp)) return sinkp;
        }
    }
    return nullptr;
}

template <typename Vertex>  //
inline Vertex* DfgVertex::findSink() const {
    static_assert(!std::is_same<DfgVertex, Vertex>::value,
                  "'Vertex' must be proper subclass of 'DfgVertex'");
    return findSink<Vertex>([](const Vertex&) { return true; });
}

inline bool DfgVertex::isZero() const {
    if (const DfgConst* const constp = cast<DfgConst>()) return constp->isZero();
    return false;
}

inline bool DfgVertex::isOnes() const {
    if (const DfgConst* const constp = cast<DfgConst>()) return constp->isOnes();
    return false;
}

#endif
