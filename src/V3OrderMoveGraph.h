// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
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
//
//  Move graph builder for ordering
//
//*************************************************************************

#ifndef VERILATOR_V3ORDERMOVEGRAPH_H_
#define VERILATOR_V3ORDERMOVEGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Order.h"
#include "V3OrderGraph.h"

class OrderMoveDomScope;
class OrderMoveGraph;

//======================================================================
// Vertex types

class OrderMoveVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(OrderMoveVertex, V3GraphVertex)

    // The corresponding logic vertex, or nullptr if this MoveVertex stands for a variable vertex.
    OrderLogicVertex* const m_logicp;
    OrderMoveDomScope& m_domScope;  // DomScope this vertex is under
    V3ListLinks<OrderMoveVertex> m_links;  // List links to store instances of this class

    // METHODS
    std::string dotColor() const override { return logicp() ? logicp()->dotColor() : "yellow"; }

    std::string name() const override VL_MT_STABLE {
        std::string nm;
        if (!logicp()) {
            nm = "var";
        } else {
            nm = logicp()->name() + "\\n";
            nm += "MV:";
            nm += +" d=" + cvtToHex(logicp()->domainp());
            nm += +" s=" + cvtToHex(logicp()->scopep());
        }
        if (userp()) nm += "\nu=" + cvtToHex(userp());
        return nm;
    }

    V3ListLinks<OrderMoveVertex>& links() { return m_links; }

public:
    // List type to store instances of this class
    using List = V3List<OrderMoveVertex, &OrderMoveVertex::links>;

    // CONSTRUCTORS
    OrderMoveVertex(OrderMoveGraph& graph, OrderLogicVertex* lVtxp,
                    const AstSenTree* domainp) VL_MT_DISABLED;
    ~OrderMoveVertex() override = default;
    VL_UNCOPYABLE(OrderMoveVertex);

    OrderLogicVertex* logicp() const VL_MT_STABLE { return m_logicp; }
    OrderMoveDomScope& domScope() const { return m_domScope; }
};

//======================================================================
// Graph type

// OrderMoveGraph is constructed from the fine-grained OrderGraph.
// It is a slightly coarsened representation of dependencies used to drive serialization.
class OrderMoveGraph final : public V3Graph {
public:
    // Build an OrderMoveGraph from an OrderGraph
    static std::unique_ptr<OrderMoveGraph> build(OrderGraph&, const V3Order::TrigToSenMap&);
};

// Information stored for each unique (domain, scope) pair. Mainly a list of ready vertices under
// that (domain, scope). OrderMoveDomScope instances are themselves organized into a global ready
// list if they have ready vertices.
class OrderMoveDomScope final {
    // STATE
    OrderMoveVertex::List m_readyVertices;  // Ready vertices in this domain/scope
    V3ListLinks<OrderMoveDomScope> m_links;  // List links to store instances of this class
    bool m_isOnList = false;  // True if DomScope is already on a list through m_listEnt
    const AstSenTree* const m_domainp;  // Domain the vertices belong to
    const AstScope* const m_scopep;  // Scope the vertices belong to

    // Key type for map below
    class DomScopeMapKey final {
        const AstSenTree* const m_domainp;
        const AstScope* const m_scopep;

    public:
        DomScopeMapKey(const AstSenTree* domainp, const AstScope* scopep)
            : m_domainp{domainp}
            , m_scopep{scopep} {}

        struct Hash final {
            size_t operator()(const DomScopeMapKey& key) const {
                // cppcheck-suppress unreadVariable  // cppcheck bug
                V3Hash hash{reinterpret_cast<uint64_t>(key.m_domainp)};
                hash += reinterpret_cast<uint64_t>(key.m_scopep);
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const DomScopeMapKey& a, const DomScopeMapKey& b) const {
                return a.m_domainp == b.m_domainp && a.m_scopep == b.m_scopep;
            }
        };
    };

    using DomScopeMap = std::unordered_map<DomScopeMapKey, OrderMoveDomScope, DomScopeMapKey::Hash,
                                           DomScopeMapKey::Equal>;
    // Map from Domain/Scope to the corresponding DomScope instance
    static DomScopeMap s_dsMap;

    V3ListLinks<OrderMoveDomScope>& links() { return m_links; }

public:
    // List type to store instances of this class
    using List = V3List<OrderMoveDomScope, &OrderMoveDomScope::links>;

    // STATIC MEMBERS
    static OrderMoveDomScope& getOrCreate(const AstSenTree* domainp, const AstScope* scopep) {
        return s_dsMap
            .emplace(std::piecewise_construct,  //
                     std::forward_as_tuple(domainp, scopep),  //
                     std::forward_as_tuple(domainp, scopep))
            .first->second;
    }
    static void clear() { s_dsMap.clear(); }

    // CONSTRUCTOR
    OrderMoveDomScope(const AstSenTree* domainp, const AstScope* scopep)
        : m_domainp{domainp}
        , m_scopep{scopep} {}
    ~OrderMoveDomScope() = default;
    VL_UNCOPYABLE(OrderMoveDomScope);
    VL_UNMOVABLE(OrderMoveDomScope);

    // MEMBERS
    OrderMoveVertex::List& readyVertices() { return m_readyVertices; }
    const AstSenTree* domainp() const { return m_domainp; }
    const AstScope* scopep() const { return m_scopep; }

    bool isOnList() const { return m_isOnList; }
    void isOnList(bool value) { m_isOnList = value; }
};

//======================================================================
// Serializer for OrderMoveGraph

class OrderMoveGraphSerializer final {
    // STATE
    OrderMoveDomScope::List m_readyDomScopeps;  // List of DomScopes which have ready vertices
    std::vector<OrderMoveVertex*> m_vtxps;
    size_t m_nextVtxIndex = 0;

    // METHODS
    void order(const std::vector<OrderMoveVertex*>& rootps,
               const std::unordered_set<OrderMoveVertex*>& component) {
        enum state : int {  //
            UNSEEN = 0,
            ENQUEUED,
            VISITED,
            COMPLETED
        };

        std::vector<OrderMoveVertex*> stack{rootps.rbegin(), rootps.rend()};
        std::vector<OrderMoveVertex*> postOrder;

        std::unordered_map<OrderMoveVertex*, int> mark;
        for (OrderMoveVertex* const vtxp : stack) { mark[vtxp] = ENQUEUED; }

        while (!stack.empty()) {
            OrderMoveVertex* const vtxp = stack.back();

            if (mark[vtxp] == COMPLETED) {
                stack.pop_back();
                continue;
            }

            if (mark[vtxp] == VISITED) {
                mark[vtxp] = COMPLETED;
                stack.pop_back();
                postOrder.push_back(vtxp);
                continue;
            }

            UASSERT_OBJ(mark[vtxp] == ENQUEUED, vtxp, "Already visited and is on stack");
            mark[vtxp] = VISITED;

            for (auto it = vtxp->outEdges().rbegin(); it != vtxp->outEdges().rend(); ++it) {
                // The dependent variable
                OrderMoveVertex* const dVtxp = (*it).top()->as<OrderMoveVertex>();
                if (!component.count(dVtxp)) continue;
                if (mark[dVtxp] == COMPLETED) continue;
                UASSERT_OBJ(mark[dVtxp] == ENQUEUED || mark[dVtxp] == UNSEEN, dVtxp,
                            "Already visited and is on stack");

                mark[dVtxp] = ENQUEUED;
                stack.push_back(dVtxp);
            }
        }

        m_vtxps.insert(m_vtxps.end(), postOrder.rbegin(), postOrder.rend());
    }

    void ready(OrderMoveVertex* vtxp) {
        UASSERT_OBJ(!vtxp->user(), vtxp, "'ready' called on vertex with pending dependencies");
        // Add this vertex to the ready list of its DomScope
        OrderMoveDomScope& domScope = vtxp->domScope();
        domScope.readyVertices().linkBack(vtxp);
        // Add the DomScope to the global ready list if not there yet
        if (!domScope.isOnList()) {
            domScope.isOnList(true);
            m_readyDomScopeps.linkBack(&domScope);
        }
    }

public:
    // CONSTRUCTOR
    explicit OrderMoveGraphSerializer(OrderMoveGraph& moveGraph) {
        // Set V3GraphVertex::user() to the number of incoming edges (upstream dependencies)
        for (V3GraphVertex& vtx : moveGraph.vertices()) {
            const uint32_t nDeps = vtx.inEdges().size();
            vtx.user(nDeps);
        }
    }
    ~OrderMoveGraphSerializer() = default;
    VL_UNCOPYABLE(OrderMoveGraphSerializer);

    // Add a seed vertex to the ready lists
    void addSeed(OrderMoveVertex* vtxp) { ready(vtxp); }

    void doit() {
        m_nextVtxIndex = 0;
        m_vtxps.clear();

        //UASSERT(!m_readyDomScopeps.empty(), "??? empty ???");
        OrderMoveDomScope* nextDomScopep = m_readyDomScopeps.frontp();
        // If nothing is ready, we are done
        while (nextDomScopep) {
            OrderMoveDomScope& currDomScope = *nextDomScopep;
            OrderMoveVertex::List& currReadyList = currDomScope.readyVertices();
            UASSERT(!currReadyList.empty(), "DomScope on ready list, but has no ready vertices");

            std::vector<OrderMoveVertex*> rootps;
            for (OrderMoveVertex& vtx : currReadyList) rootps.emplace_back(&vtx);

            std::unordered_set<OrderMoveVertex*> component;

            while (!currReadyList.empty()) {
                // Remove vertex from ready list under the DomScope. This is the vertex we are
                // returning.
                OrderMoveVertex* const vtxp = currReadyList.unlinkFront();

                // Finally yield the selected vertex
                const bool newEntry = component.emplace(vtxp).second;
                UASSERT_OBJ(newEntry, vtxp, "Should be new");

                // Remove dependency on vertex we are returning. This might add vertices to
                // currReadyList.
                for (V3GraphEdge& edge : vtxp->outEdges()) {
                    // The dependent variable
                    OrderMoveVertex* const dVtxp = edge.top()->as<OrderMoveVertex>();
                    // Update number of dependencies
                    const uint32_t nDeps = dVtxp->user() - 1;
                    dVtxp->user(nDeps);
                    // If no more dependencies, mark it ready
                    if (!nDeps) ready(dVtxp);
                }
            }

            currDomScope.isOnList(false);
            m_readyDomScopeps.unlink(&currDomScope);

            order(rootps, component);

            // No more ready vertices in the current DomScope, prefer to continue with a new
            // scope under the same domain.
            nextDomScopep = m_readyDomScopeps.frontp();
            for (OrderMoveDomScope& domScope : m_readyDomScopeps) {
                if (domScope.domainp() == currDomScope.domainp()) {
                    nextDomScopep = &domScope;
                    break;
                }
            }
        }
    }

    OrderMoveVertex* getNext() {
        if (m_nextVtxIndex >= m_vtxps.size()) return nullptr;
        return m_vtxps[m_nextVtxIndex++];
    }
};

#endif  // Guard
