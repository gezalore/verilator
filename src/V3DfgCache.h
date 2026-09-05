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

#include <algorithm>
#include <type_traits>
#include <vector>

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

        // The key is not stored, as it can be recovered from the cached vertex, which keeps
        // the table small enough that probing touches few cache lines
        struct Entry final {
            size_t m_hash = 0;  // Hash of the key of the cached vertex
            T_Vertex* m_vtxp = nullptr;  // The cached vertex - nullptr marks an empty slot
        };

        // STATE
        // Open-addressed, linear-probed hash table. Size is always a power of 2 (or 0).
        std::vector<Entry> m_table;
        size_t m_used = 0;  // Number of occupied slots

        // METHODS

        // Index of the entry with the given key, or of the empty slot to insert it at
        size_t findSlot(size_t hash, const T_Key& key) const {
            const size_t mask = m_table.size() - 1;
            size_t i = hash & mask;
            while (true) {
                const Entry& entry = m_table[i];
                if (!entry.m_vtxp || (entry.m_hash == hash && Equal{}(T_Key{entry.m_vtxp}, key))) {
                    return i;
                }
                i = (i + 1) & mask;
            }
        }

        // Grow the table if needed to insert one more entry, at most 75% load
        void maybeGrow() {
            if (VL_LIKELY((m_used + 1) * 4 <= m_table.size() * 3)) return;
            std::vector<Entry> oldTable{std::move(m_table)};
            m_table.clear();
            m_table.resize(std::max<size_t>(16, oldTable.size() * 2));
            const size_t mask = m_table.size() - 1;
            for (const Entry& entry : oldTable) {
                if (!entry.m_vtxp) continue;
                size_t i = entry.m_hash & mask;
                while (m_table[i].m_vtxp) i = (i + 1) & mask;
                m_table[i] = entry;
            }
        }

        // Insert entry known not to be in the table
        void insert(size_t hash, const T_Key& key, T_Vertex* vtxp) {
            maybeGrow();
            Entry& entry = m_table[findSlot(hash, key)];
            entry.m_hash = hash;
            entry.m_vtxp = vtxp;
            ++m_used;
        }

    public:
        // Add an existing vertex to the cache. If an equivalent exists,
        // it is returned and the cache is not updated.
        DfgVertex* cache(DfgVertex* vtxp) override {
            UASSERT_OBJ(vtxp->is<T_Vertex>(), vtxp, "Vertex is wrong type");
            const T_Key key{static_cast<const T_Vertex*>(vtxp)};
            const size_t hash = Hash{}(key);
            if (!m_table.empty()) {
                const Entry& entry = m_table[findSlot(hash, key)];
                if (entry.m_vtxp) return entry.m_vtxp != vtxp ? entry.m_vtxp : nullptr;
            }
            insert(hash, key, static_cast<T_Vertex*>(vtxp));
            return nullptr;
        }
        // Remove an existing vertex from the cache, if it is the cached vertex, otherwise no-op
        void invalidate(const DfgVertex* vtxp) override {
            UASSERT_OBJ(vtxp->is<T_Vertex>(), vtxp, "Vertex is wrong type");
            if (m_table.empty()) return;
            const T_Key key{static_cast<const T_Vertex*>(vtxp)};
            size_t i = findSlot(Hash{}(key), key);
            if (m_table[i].m_vtxp != vtxp) return;
            // Backward-shift deletion: move up entries the hole would break the probing of
            const size_t mask = m_table.size() - 1;
            size_t j = i;
            while (true) {
                j = (j + 1) & mask;
                const Entry& entry = m_table[j];
                if (!entry.m_vtxp) break;
                // Move back if its home position does not lie in the cyclic range (i, j]
                if (((j - (entry.m_hash & mask)) & mask) >= ((j - i) & mask)) {
                    m_table[i] = entry;
                    i = j;
                }
            }
            m_table[i] = Entry{};
            --m_used;
        }

        // Get vertex with given operands, return nullptr if not in cache
        template <typename Vertex, typename... Operands>
        Vertex* get(const DfgDataType& dtype, Operands... operands) {
            if (m_table.empty()) return nullptr;
            const T_Key key{dtype, operands...};
            const Entry& entry = m_table[findSlot(Hash{}(key), key)];
            return static_cast<Vertex*>(entry.m_vtxp);
        }

        // Get or create (and insert) vertex with given operands
        template <typename Vertex, typename... Operands>
        Vertex* getOrCreate(DfgGraph& dfg, FileLine* flp, const DfgDataType& dtype,
                            Operands... operands) {
            const T_Key key{dtype, operands...};
            const size_t hash = Hash{}(key);
            if (!m_table.empty()) {
                const Entry& entry = m_table[findSlot(hash, key)];
                if (entry.m_vtxp) return static_cast<Vertex*>(entry.m_vtxp);
            }
            T_Vertex* const newp = new Vertex{dfg, flp, dtype};
            setOperands(newp, operands...);
            insert(hash, key, newp);
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
    // Note: the cache starts out empty. If the caller wants existing vertices
    // to be found, it must add them itself by calling 'cache' on each.
    explicit V3DfgCache(DfgGraph& dfg)
        : m_dfg{dfg} {
    // Initialize the type to cache lookup table
#define VERTEX_CACHE_DECLARE_CACHE_PTR(t) m_vtxType2Cachep[t::dfgType()] = &m_cache##t;
              FOREACH_DFG_VERTEX_TYPE(VERTEX_CACHE_DECLARE_CACHE_PTR)
#undef VERTEX_CACHE_DECLARE_CACHE_PTR
          }

        // Add an existing vertex to the cache. If an equivalent (but different) already exists,
        // it is returned and the cache is not updated.
        DfgVertex
        * cache(DfgVertex * vtxp) {
        return m_vtxType2Cachep[vtxp->type()]->cache(vtxp);
    }

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
