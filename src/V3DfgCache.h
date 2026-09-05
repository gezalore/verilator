// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dfg vertex cache to find existing vertices
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
//
// A cache for DfgGraph, to find existing vertices with identical inputs.
//
// Beware that if you use this data-structure, you must invalidate the
// cache any time you change the inputs of an existing vertex, otherwise
// you will have a very bad day.
//
//*************************************************************************

#ifndef VERILATOR_V3DFGCACHE_H_
#define VERILATOR_V3DFGCACHE_H_

#include "V3Dfg.h"
#include "V3DfgDataType.h"
#include "V3HashMap.h"

#include <type_traits>

// Type predicate true for cached vertex types
template <typename Vertex>
using V3DfgCacheIsCached
    = std::integral_constant<bool, std::is_base_of<DfgVertexUnary, Vertex>::value
                                       || std::is_base_of<DfgVertexBinary, Vertex>::value
                                       || std::is_base_of<DfgVertexTernary, Vertex>::value>;

// Helper template to determine the cache type for a vertex type
template <typename Vertex, typename CacheBase, typename... Pairs>
struct V3DfgCacheType final {
    using Type = CacheBase;
};

template <typename Vertex, typename CacheBase, typename VertexBase, typename Cache,
          typename... Pairs>
struct V3DfgCacheType<Vertex, CacheBase, VertexBase, Cache, Pairs...> final {
    using Type = std::conditional_t<std::is_base_of<VertexBase, Vertex>::value, Cache,
                                    typename V3DfgCacheType<Vertex, CacheBase, Pairs...>::Type>;
};

class V3DfgCache final {
    // TYPES
    struct KeySel final {
        const DfgDataType* m_dtypep = nullptr;
        const DfgVertex* m_fromp = nullptr;
        uint32_t m_lsb = 0;

        KeySel() = default;
        KeySel(const DfgDataType& dtype, DfgVertex* fromp, uint32_t lsb)
            : m_dtypep{&dtype}
            , m_fromp{fromp}
            , m_lsb{lsb} {}
        explicit KeySel(const DfgSel* vtxp)
            : m_dtypep{&vtxp->dtype()}
            , m_fromp{vtxp->fromp()}
            , m_lsb{vtxp->lsb()} {}

        struct Hash final {
            size_t operator()(const KeySel& key) const {
                // cppcheck-suppress unreadVariable  // cppcheck bug
                V3Hash hash = key.m_dtypep->hash();
                hash += vertexHash(key.m_fromp);
                hash += key.m_lsb;
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const KeySel& a, const KeySel& b) const {
                return a.m_lsb == b.m_lsb && *a.m_dtypep == *b.m_dtypep
                       && vertexEqual(a.m_fromp, b.m_fromp);
            }
        };
    };

    struct KeyUnary final {
        const DfgDataType* m_dtypep = nullptr;
        const DfgVertex* m_source0p = nullptr;

        KeyUnary() = default;
        KeyUnary(const DfgDataType& dtype, DfgVertex* source0p)
            : m_dtypep{&dtype}
            , m_source0p{source0p} {}
        explicit KeyUnary(const DfgVertexUnary* vtxp)
            : m_dtypep{&vtxp->dtype()}
            , m_source0p{vtxp->inputp(0)} {}

        struct Hash final {
            size_t operator()(const KeyUnary& key) const {  //
                V3Hash hash = key.m_dtypep->hash();
                hash += vertexHash(key.m_source0p);
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const KeyUnary& a, const KeyUnary& b) const {
                return *a.m_dtypep == *b.m_dtypep && vertexEqual(a.m_source0p, b.m_source0p);
            }
        };
    };

    struct KeyBinary final {
        const DfgDataType* m_dtypep = nullptr;
        const DfgVertex* m_source0p = nullptr;
        const DfgVertex* m_source1p = nullptr;

        KeyBinary() = default;
        KeyBinary(const DfgDataType& dtype, DfgVertex* source0p, DfgVertex* source1p)
            : m_dtypep{&dtype}
            , m_source0p{source0p}
            , m_source1p{source1p} {}
        explicit KeyBinary(const DfgVertexBinary* vtxp)
            : m_dtypep{&vtxp->dtype()}
            , m_source0p{vtxp->inputp(0)}
            , m_source1p{vtxp->inputp(1)} {}

        struct Hash final {
            size_t operator()(const KeyBinary& key) const {
                V3Hash hash = key.m_dtypep->hash();
                hash += vertexHash(key.m_source0p);
                hash += vertexHash(key.m_source1p);
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const KeyBinary& a, const KeyBinary& b) const {
                return *a.m_dtypep == *b.m_dtypep && vertexEqual(a.m_source0p, b.m_source0p)
                       && vertexEqual(a.m_source1p, b.m_source1p);
            }
        };
    };

    struct KeyTernary final {
        const DfgDataType* m_dtypep = nullptr;
        const DfgVertex* m_source0p = nullptr;
        const DfgVertex* m_source1p = nullptr;
        const DfgVertex* m_source2p = nullptr;

        KeyTernary() = default;
        KeyTernary(const DfgDataType& dtype, DfgVertex* source0p, DfgVertex* source1p,
                   DfgVertex* source2p)
            : m_dtypep{&dtype}
            , m_source0p{source0p}
            , m_source1p{source1p}
            , m_source2p{source2p} {}
        explicit KeyTernary(const DfgVertexTernary* vtxp)
            : m_dtypep{&vtxp->dtype()}
            , m_source0p{vtxp->inputp(0)}
            , m_source1p{vtxp->inputp(1)}
            , m_source2p{vtxp->inputp(2)} {}

        struct Hash final {
            size_t operator()(const KeyTernary& key) const {
                V3Hash hash = key.m_dtypep->hash();
                hash += vertexHash(key.m_source0p);
                hash += vertexHash(key.m_source1p);
                hash += vertexHash(key.m_source2p);
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const KeyTernary& a, const KeyTernary& b) const {
                return *a.m_dtypep == *b.m_dtypep && vertexEqual(a.m_source0p, b.m_source0p)
                       && vertexEqual(a.m_source1p, b.m_source1p)
                       && vertexEqual(a.m_source2p, b.m_source2p);
            }
        };
    };

    class CacheBase VL_NOT_FINAL {
    protected:
        // These set the operands of a new vertex
        static void setOperands(DfgSel* vtxp, DfgVertex* fromp, uint32_t lsb) {
            vtxp->fromp(fromp);
            vtxp->lsb(lsb);
        }

        static void setOperands(DfgVertexUnary* vtxp, DfgVertex* src0p) {  //
            vtxp->inputp(0, src0p);
        }

        static void setOperands(DfgVertexBinary* vtxp, DfgVertex* src0p, DfgVertex* src1p) {
            vtxp->inputp(0, src0p);
            vtxp->inputp(1, src1p);
        }

        static void setOperands(DfgVertexTernary* vtxp, DfgVertex* src0p, DfgVertex* src1p,
                                DfgVertex* src2p) {
            vtxp->inputp(0, src0p);
            vtxp->inputp(1, src1p);
            vtxp->inputp(2, src2p);
        }

    public:
        // CacheBase does not cache anything
        virtual DfgVertex* cache(DfgVertex*) { return nullptr; }
        virtual void invalidate(const DfgVertex*) {}
    };

    template <typename T_Key, typename T_Vertex>
    class Cache final : public CacheBase {
        static_assert(std::is_base_of<DfgVertex, T_Vertex>::value, "T_Vertex must be a DfgVertex");
        // TYPES
        using Hash = typename T_Key::Hash;
        using Equal = typename T_Key::Equal;

        // STATE
        // The keys are not stored, they are recovered from the cached vertices
        V3HashMap<T_Vertex> m_table;

        // METHODS

        // Predicate matching the cached vertex holding the given key
        static auto keyEqual(const T_Key& key) {
            return [&key](const T_Vertex* vtxp) { return Equal{}(T_Key{vtxp}, key); };
        }

    public:
        // Add an existing vertex to the cache. If an equivalent exists,
        // it is returned and the cache is not updated.
        DfgVertex* cache(DfgVertex* vtxp) override {
            UASSERT_OBJ(vtxp->is<T_Vertex>(), vtxp, "Vertex is wrong type");
            const T_Key key{static_cast<const T_Vertex*>(vtxp)};
            const size_t hash = Hash{}(key);
            if (T_Vertex* const foundp = m_table.find(hash, keyEqual(key))) {
                return foundp != vtxp ? foundp : nullptr;
            }
            m_table.insert(hash, static_cast<T_Vertex*>(vtxp));
            return nullptr;
        }
        // Remove an existing vertex from the cache, if it is the cached vertex, otherwise no-op
        void invalidate(const DfgVertex* vtxp) override {
            UASSERT_OBJ(vtxp->is<T_Vertex>(), vtxp, "Vertex is wrong type");
            const T_Key key{static_cast<const T_Vertex*>(vtxp)};
            // Only the cached vertex itself is removed, an equivalent one is left alone
            m_table.erase(Hash{}(key),
                          [vtxp](const T_Vertex* cachedp) { return cachedp == vtxp; });
        }

        // Get vertex with given operands, return nullptr if not in cache
        template <typename Vertex, typename... Operands>
        Vertex* get(const DfgDataType& dtype, Operands... operands) {
            const T_Key key{dtype, operands...};
            return static_cast<Vertex*>(m_table.find(Hash{}(key), keyEqual(key)));
        }

        // Get or create (and insert) vertex with given operands
        template <typename Vertex, typename... Operands>
        Vertex* getOrCreate(DfgGraph& dfg, FileLine* flp, const DfgDataType& dtype,
                            Operands... operands) {
            const T_Key key{dtype, operands...};
            const size_t hash = Hash{}(key);
            if (T_Vertex* const foundp = m_table.find(hash, keyEqual(key))) {
                return static_cast<Vertex*>(foundp);
            }
            T_Vertex* const newp = new Vertex{dfg, flp, dtype};
            setOperands(newp, operands...);
            m_table.insert(hash, newp);
            return static_cast<Vertex*>(newp);
        }
    };

    // Map from Vertex type to cache type
    template <typename Vertex>
    using CacheType =
        typename V3DfgCacheType<Vertex, CacheBase,  //
                                DfgSel, Cache<KeySel, DfgSel>,  //
                                DfgVertexUnary, Cache<KeyUnary, DfgVertexUnary>,  //
                                DfgVertexBinary, Cache<KeyBinary, DfgVertexBinary>,  //
                                DfgVertexTernary, Cache<KeyTernary, DfgVertexTernary>  //
                                >::Type;
    // STATE
    DfgGraph& m_dfg;  // The DfgGraph we are caching the vertices of

    // The per type caches
#define VERTEX_CACHE_DECLARE_CACHE(t) CacheType<t> m_cache##t;
    FOREACH_DFG_VERTEX_TYPE(VERTEX_CACHE_DECLARE_CACHE)
#undef VERTEX_CACHE_DECLARE_CACHE

    // Map from vertex type to m_cache* instances for dynamic lookup
    std::array<CacheBase*, VDfgType::NUM_TYPES()> m_vtxType2Cachep{};

    // METHODS

    // Map from vertex type to m_cache* instances for static lookup
    template <typename Vertex>
    CacheType<Vertex>* cacheForType() {
#define VERTEX_CACHE_DECLARE_CACHE(t) \
    if VL_CONSTEXPR_CXX17 (std::is_same<Vertex, t>::value) \
        return reinterpret_cast<CacheType<Vertex>*>(&m_cache##t);
        FOREACH_DFG_VERTEX_TYPE(VERTEX_CACHE_DECLARE_CACHE)
#undef VERTEX_CACHE_DECLARE_CACHE
        return nullptr;  // LCOV_EXCL_LINE
    }

    // Hash constants by value, everything else by identity
    static V3Hash vertexHash(const DfgVertex* vtxp) {
        if (const DfgConst* const constp = vtxp->cast<DfgConst>()) return constp->num().toHash();
        return V3Hash{reinterpret_cast<uint64_t>(vtxp)};
    }

    // Constants are equal by value, everything else is equal by identity
    static bool vertexEqual(const DfgVertex* ap, const DfgVertex* bp) {
        if (ap == bp) return true;
        if (ap->type() != bp->type()) return false;
        if (const DfgConst* const aConstp = ap->cast<DfgConst>()) {
            const DfgConst* const bConstp = bp->as<DfgConst>();
            return aConstp->num().isCaseEq(bConstp->num());
        }
        return false;
    }

public:
    explicit V3DfgCache(DfgGraph& dfg)
        : m_dfg{dfg} {
        // Initialize the type to cache lookup table
#define VERTEX_CACHE_DECLARE_CACHE_PTR(t) m_vtxType2Cachep[t::dfgType()] = &m_cache##t;
        FOREACH_DFG_VERTEX_TYPE(VERTEX_CACHE_DECLARE_CACHE_PTR)
#undef VERTEX_CACHE_DECLARE_CACHE_PTR

        // Add all operation vertices to the cache
        for (DfgVertex& vtx : m_dfg.opVertices()) cache(&vtx);
    }

    // Add an existing vertex to the cache. If an equivalent (but different) already exists,
    // it is returned and the cache is not updated.
    DfgVertex* cache(DfgVertex* vtxp) { return m_vtxType2Cachep[vtxp->type()]->cache(vtxp); }

    // Remove an exiting vertex, it is the cached vertex.
    void invalidate(DfgVertex* vtxp) { m_vtxType2Cachep[vtxp->type()]->invalidate(vtxp); }

    // Find a vertex of type 'Vertex', with the given operands, or create a new one and add it.
    template <typename Vertex, typename... Operands>
    Vertex* getOrCreate(FileLine* flp, const DfgDataType& dtype, Operands... operands) {
        static_assert(std::is_final<Vertex>::value, "Must invoke on final vertex type");
        static_assert(V3DfgCacheIsCached<Vertex>::value, "Not a cached vertex type");
        return cacheForType<Vertex>()->template getOrCreate<Vertex>(m_dfg, flp, dtype,
                                                                    operands...);
    }

    // Find a vertex of type 'Vertex', with the given operands, return nullptr if not in cache.
    template <typename Vertex, typename... Operands>
    Vertex* get(const DfgDataType& dtype, Operands... operands) {
        static_assert(std::is_final<Vertex>::value, "Must invoke on final vertex type");
        static_assert(V3DfgCacheIsCached<Vertex>::value, "Not a cached vertex type");
        return cacheForType<Vertex>()->template get<Vertex>(dtype, operands...);
    }
};

#endif  // VERILATOR_V3DFGCACHE_H_
