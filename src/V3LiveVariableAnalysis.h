// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Live variable analysis
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
//
//*************************************************************************

#ifndef VERILATOR_V3LIVEVARIABLEANALYSYS_H_
#define VERILATOR_V3LIVEVARIABLEANALYSYS_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3DataFlowAnalysis.h"

#include <unordered_map>
#include <unordered_set>

template <typename T>  //
class V3Set {
    // TYPES
    enum class Variant : bool {
        Inclusive,  // Inclusive sets are implemented as a set of elements they contain
        Exclusive  // Exclusive sets are implemented as a set of elements they do not contain
    };

    using Impl = std::unordered_set<T>;  // Type of the actual backing store

    // MEMBERS
    Impl m_impl;  // The set implementation
    Variant m_variant;  // The set variant

    explicit V3Set(Variant variant)
        : m_variant{variant} {}

    V3Set(std::unordered_set<T>&& impl, Variant variant)
        : m_impl{impl}
        , m_variant{variant} {}

    // METHODS
    bool isInclusive() const { return m_variant == Variant::Inclusive; }

public:
    // Factory methods
    static V3Set empty() { return V3Set{Variant::Inclusive}; }
    static V3Set universal() { return V3Set{Variant::Exclusive}; }

    // Returns true if value is in the set
    bool contains(T val) const {
        if (isInclusive()) {
            return m_impl.count(val) != 0;
        } else {
            return m_impl.count(val) == 0;
        }
    }

    // Insert value into set. Returns true if insertion did happen (i.e.: not already in the set)
    bool insert(T val) {
        if (isInclusive()) {
            return m_impl.insert(val).second;
        } else {
            return m_impl.erase(val) != 0;
        }
    }

    // Remove value from set. Returns true if removal did happen (i.e.: value was in the set)
    bool remove(T val) {
        if (isInclusive()) {
            return m_impl.erase(val) != 0;
        } else {
            return m_impl.insert(val).second;
        }
    }

    // Union
    V3Set<T> operator|(const V3Set<T>& rhs) const {
        const V3Set<T>& lhs = *this;

        const bool lhsImplIsSmaller = lhs.m_impl.size() < rhs.m_impl.size();
        const Impl& smallImpl = lhsImplIsSmaller ? lhs.m_impl : rhs.m_impl;
        const Impl& largeImpl = lhsImplIsSmaller ? rhs.m_impl : lhs.m_impl;

        if (lhs.isInclusive()) {
            if (rhs.isInclusive()) {
                // Inclusive | Inclusive -> union of implementations
                Impl impl{largeImpl};
                for (T val : smallImpl) impl.insert(val);
                return {std::move(impl), Variant::Inclusive};
            } else {
                // Inclusive | Exclusive -> RHS implementation minus LHS implementation
                Impl impl{rhs.m_impl};
                for (T val : lhs.m_impl) impl.erase(val);
                return {std::move(impl), Variant::Exclusive};
            };
        } else {
            if (rhs.isInclusive()) {
                // Exclusive | Inclusive -> LHS implementation minus RHS implementation
                Impl impl{lhs.m_impl};
                for (T val : rhs.m_impl) impl.erase(val);
                return {std::move(impl), Variant::Exclusive};
            } else {
                // Exclusive | Exclusive -> intersection of implementations
                Impl impl{smallImpl};
                for (T val : smallImpl) {
                    if (!largeImpl.count(val)) impl.erase(val);
                }
                return {std::move(impl), Variant::Exclusive};
            }
        }
    }

    bool operator==(const V3Set<T>& rhs) const {
        // Warning: For sets over finite domains, it is possible to represent the same set with
        // both an Inclusive and an Exclusive variant. Nevertheless, we pretend these are not the
        // same sets, which is good enough for our use here. Otherwise we would need to know the
        // size of the domain to answer this equivalence.
        if (m_variant != rhs.m_variant) return false;
        return *this == rhs;
    }

    bool operator!=(const V3Set<T>& rhs) const { return !(*this == rhs); }
};

using LiveVariableSet = V3Set<const AstVarScope*>;

class V3LiveVariableLattice final : public V3Semilattice<LiveVariableSet> {
public:
    LiveVariableSet meet(const LiveVariableSet& a, const LiveVariableSet& b) const {
        return a | b;
    }
    LiveVariableSet top() const { return LiveVariableSet::empty(); };
    LiveVariableSet bottom() const { return LiveVariableSet::universal(); };
    //    //
    //    virtual bool eq(const LiveVariableSet& x, const LiveVariableSet& y) const = 0;  //
    //    TODO: explain
};

class V3LiveVariableTrandferFunctions final : public V3TransferFunctions<LiveVariableSet> {

    static void removeKill(LiveVariableSet& set, const AstNode* nodep) {
        nodep->foreach<AstVarRef>([&](const AstVarRef* refp) {
            if (refp->access().isWriteOrRW()) set.remove(refp->varScopep());
        });
    }

    static void addGen(LiveVariableSet& set, const AstNode* nodep) {
        nodep->foreach<AstVarRef>([&](const AstVarRef* refp) {
            if (refp->access().isWriteOrRW()) set.remove(refp->varScopep());
        });
    }

    static LiveVariableSet removeKillAddGen(const LiveVariableSet& set, const AstNode* nodep) {
        LiveVariableSet result{set};
        removeKill(result, nodep);
        addGen(result, nodep);
        return result;
    }

public:
    LiveVariableSet initial() const { return LiveVariableSet::empty(); }

    LiveVariableSet apply(const AstIf* nodep, const LiveVariableSet& after) const {
        // This is only for the condition part of the if.
        // 'in' is the meet of the branches.
        return removeKillAddGen(after, nodep->condp());
    }

    LiveVariableSet apply(const AstWhile* nodep, const LiveVariableSet& after) const {
        // This is only for the condition part of the while.
        // 'in' is the meet of the continuation and the body.
        return removeKillAddGen(after, nodep->condp());
    }

    LiveVariableSet apply(const AstNodeAssign* nodep, const LiveVariableSet& after) const {
        return removeKillAddGen(after, nodep);
    }
};

class V3LiveVariableAnalysis final {
public:
    static std::unordered_map<const AstNode*, LiveVariableSet> apply(AstNode* nodep) {
        const V3LiveVariableLattice l;
        const V3LiveVariableTrandferFunctions t;
        return V3DataFlowAnalysis<V3DataFlowDirection::Backward, LiveVariableSet>{l, t}(nodep);
    }
};

#endif