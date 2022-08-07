// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scoreboards for thread partitioner
//
// Provides scoreboard classes:
//
//  * SortByValueMap
//  * V3Scoreboard
//
// See details below
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

#ifndef VERILATOR_V3SCOREBOARD_H_
#define VERILATOR_V3SCOREBOARD_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

#include <functional>
#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <vector>

// ######################################################################
//  SortByValueMap

// A generic key-value map, except iteration is in *value* sorted order. Values need not be unique.
// Uses T_KeyCompare to break ties in the sort when values collide. Note: Only const iteration is
// possible, as updating mapped values via iterators is not safe.

template <typename T_Key, typename T_Value, class T_KeyCompare = std::less<T_Key>>
class SortByValueMap final {
    // Current implementation is a std::set of key/value pairs, plus a std_unordered_map from keys
    // to iterators into the set. This keeps most operations fairly cheap and also has the benefit
    // of being able to re-use the std::set iterators.

    // TYPES

    using Pair = std::pair<T_Key, T_Value>;

    struct PairCmp final {
        bool operator()(const Pair& a, const Pair& b) const {
            // First compare values
            if (a.second != b.second) return a.second < b.second;
            // Then compare keys
            return T_KeyCompare{}(a.first, b.first);
        }
    };

    using PairSet = std::set<Pair, PairCmp>;

public:
    using const_iterator = typename PairSet::const_iterator;
    using const_reverse_iterator = typename PairSet::const_reverse_iterator;

private:
    // MEMBERS
    PairSet m_pairs;  // The contents of the map, stored directly as key-value pairs
    std::unordered_map<T_Key, const_iterator> m_kiMap;  // Key to iterator map

    VL_UNCOPYABLE(SortByValueMap);

public:
    // CONSTRUCTORS
    SortByValueMap() = default;

    // Only const iteration is possible
    const_iterator begin() const { return m_pairs.begin(); }
    const_iterator end() const { return m_pairs.end(); }
    const_iterator cbegin() const { m_pairs.cbegin(); }
    const_iterator cend() const { return m_pairs.cend(); }
    const_reverse_iterator rbegin() const { return m_pairs.rbegin(); }
    const_reverse_iterator rend() const { return m_pairs.rend(); }
    const_reverse_iterator crbegin() const { return m_pairs.crbegin(); }
    const_reverse_iterator crend() const { return m_pairs.crend(); }

    const_iterator find(const T_Key& key) const {
        const auto kiIt = m_kiMap.find(key);
        if (kiIt == m_kiMap.end()) return cend();
        return kiIt->second;
    }
    size_t erase(const T_Key& key) {
        const auto kiIt = m_kiMap.find(key);
        if (kiIt == m_kiMap.end()) return 0;
        m_pairs.erase(kiIt->second);
        m_kiMap.erase(kiIt);
        return 1;
    }
    void erase(const_iterator it) {
        m_kiMap.erase(it->first);
        m_pairs.erase(it);
    }
    void erase(const_reverse_iterator rit) {
        m_kiMap.erase(rit->first);
        m_pairs.erase(std::next(rit).base());
    }
    bool has(const T_Key& key) const { return m_kiMap.count(key); }
    bool empty() const { return m_pairs.empty(); }
    // Returns const reference.
    const T_Value& at(const T_Key& key) const { return m_kiMap.at(key)->second; }
    // Note this returns const_iterator
    template <typename... Args>
    std::pair<const_iterator, bool> emplace(const T_Key& key, Args&&... args) {
        const auto kiEmp = m_kiMap.emplace(key, end());
        if (kiEmp.second) {
            const auto result = m_pairs.emplace(key, std::forward<Args>(args)...);
#if VL_DEBUG
            UASSERT(result.second, "Should not be in set yet");
#endif
            kiEmp.first->second = result.first;
            return result;
        }
        return {kiEmp.first->second, false};
    }
    // Invalidates iterators
    void update(const_iterator it, T_Value value) {
        const auto kiIt = m_kiMap.find(it->first);
        m_pairs.erase(it);
        kiIt->second = m_pairs.emplace(kiIt->first, value).first;
    }
};

//======================================================================
// V3Scoreboard takes a set of Elem*'s, each having some score. Elem must derive from
// Scoreboardable and can only be added to a single V3Scoreboards. Scores are comptued via the
// 'score()' function of the elmenents. Elements with tied score are  sorted by a unique ID
// returned by the element 'id()' function.
//
// At any time, the V3Scoreboard can return the elem with the "best" score among those elements
// whose scores are known.
//
// The best score is the _lowest_ score. This makes sense in contexts where scores represent costs.
//
// The Scoreboard supports mutating element scores efficiently. The client must hint to the
// V3Scoreboard when an element's score may have changed. When it receives this hint, the
// V3Scoreboard will move the element into the set of elements whose scores are unknown. Later the
// client can tell V3Scoreboard to re-sort the list, which it does incrementally, by re-scoring all
// elements whose scores are unknown, and then moving these back into the score-sorted map. This is
// efficient when the subset of elements whose scores change is much smaller than the full set
// size.
//
// The implementation keep a std::set of ScoreboardEntry entries, sorted by score, then id. Removal
// is lazy and only actually happens when retrieving the best element. This allows
//
//

template <typename T_Elem, typename T_Score>
class V3Scoreboard;
template <typename T_Elem, typename T_Score>
class Scoreboardable;
template <typename T_Elem, typename T_Score>
struct ScoreboardHeapNode;

// Scoreboard heap node is a what... TODO: explain is a utility structure used by V3Scoreboard.
// Client code should never use it.
template <typename T_Elem, typename T_Score>
struct ScoreboardHeapNodeBase VL_NOT_FINAL {
    using HeapNode = ScoreboardHeapNode<T_Elem, T_Score>;

    // MEMBERS
    // Note: member ordering arranged to minimize structure padding
    T_Elem* m_elemp;  // The element (key)
    HeapNode* m_nextp;  // Next entry in lists
    HeapNode* m_kidsp;  // Child heaps of this node
    T_Score m_score;  // Score of the element
    bool m_known;  // Score is known
    bool m_removed;  // Element removed from scoreboard flag (for lazy deletion from maps)

    // METHODS
    bool operator<(const HeapNode& that) const {
#if VL_DEBUG
        UASSERT(!m_removed && !that.m_removed, "Should not be removed (need to access '->id()')");
#endif
        // First compare scores
        if (m_score != that.m_score) return m_score < that.m_score;
        // Then compare IDs
        return m_elemp->id() < that.m_elemp->id();
    }

    static constexpr size_t alignment() {
        using ThisType = ScoreboardHeapNodeBase<T_Elem, T_Score>;
        constexpr size_t size = sizeof(ThisType);
        // If power of 2, align to that
        if ((size & (size - 1)) == 0) return size;
        // Otherwise don't worry about it
        return alignof(ThisType);
    }
};

// Purely for alignment
template <typename T_Elem, typename T_Score>
struct alignas(ScoreboardHeapNodeBase<T_Elem, T_Score>::alignment()) ScoreboardHeapNode final
    : public ScoreboardHeapNodeBase<T_Elem, T_Score> {};

// Note: This is just an optimization so feel free to ignore if it fails
static_assert(sizeof(ScoreboardHeapNode<int, uint32_t>) != 32
                  || alignof(ScoreboardHeapNode<int, uint32_t>) == 32,
              "uint32_t score should yield aligned heap nodes on 64-bit platforms");

// Scoreboardable has some minimal state that V3Scoreboard uses to keep track of the key ->
// iterator association required by SortByValueMapBase. It is more efficient both in space and time
// to keep this inside the keys, if most keys in existence are expected to be in the map, and they
// can only be in one map, which holds for the usage of V3Scoreboard.
template <typename T_Elem, typename T_Score>
class Scoreboardable VL_NOT_FINAL {
    // Only V3Scorebard should access internals
    friend class V3Scoreboard<T_Elem, T_Score>;

    using HeapNode = ScoreboardHeapNode<T_Elem, T_Score>;

    // MEMBERS
    HeapNode* m_heapNodep = nullptr;

public:
    // The element is contained if there is an associated HeapNode
    bool isInScoreboard() const { return m_heapNodep; }

    // We also required duck-typed members:
    // uint64_t id();
    // T_Score score();
};

template <typename T_Elem, typename T_Score>
class V3Scoreboard final {
    // TYPES

    using HeapNode = ScoreboardHeapNode<T_Elem, T_Score>;

    using OurScoreboardable = Scoreboardable<T_Elem, T_Score>;
    static_assert(std::is_base_of<OurScoreboardable, T_Elem>::value,
                  "T_Elem must be a subtype of Scoreboardable<T_Elem, T_Score>");

    // We allocate this many heap nodes at once
    static constexpr size_t ALLOC_CHUNK_SIZE = 128;

    // MEMBERS
    HeapNode* m_freep = nullptr;  // List of free heap nodes
    HeapNode* m_knownp = nullptr;  // Pairing heap of elements with known scores
    HeapNode* m_unknonwp = nullptr;  // List of elements with unknown scores
    std::vector<std::unique_ptr<HeapNode[]>> m_allocated;  // Allocated heap nodes

    VL_UNCOPYABLE(V3Scoreboard);

    // METHODS

    // Allocate a HeapNode for the given element
    HeapNode* allocNode(T_Elem* elemp) {
        // If no free nodes available, then make some
        if (!m_freep) {
            // Allocate in chunks for efficiency
            m_allocated.emplace_back(new HeapNode[ALLOC_CHUNK_SIZE]);
            // Set up free list pointer
            m_freep = m_allocated.back().get();
            // Set up free list chain
            for (size_t i = 1; i < ALLOC_CHUNK_SIZE; ++i) m_freep[i - 1].m_nextp = &m_freep[i];
            // Clear the next pointer of the last entry
            m_freep[ALLOC_CHUNK_SIZE - 1].m_nextp = nullptr;
        }
        // Free nodes are available, pick up the first one
        HeapNode* const resultp = m_freep;
        m_freep = resultp->m_nextp;
        // Initialize the heap node (score is left un-initialized at this point)
        resultp->m_elemp = elemp;
        resultp->m_nextp = nullptr;
        resultp->m_kidsp = nullptr;
        resultp->m_known = false;
        resultp->m_removed = false;
        // Link it in the element
        elemp->m_heapNodep = resultp;
        //
        return resultp;
    }

    // Release a HeapNode (make it available for future allocation)
    void freeNode(HeapNode* hnp) {
        // simply prepend it to the free list
        hnp->m_nextp = m_freep;
        m_freep = hnp;
    }

    // Insert node newp into heapp pairing heap
    static HeapNode* insertHeap(HeapNode* newp, HeapNode* heapp) {
        // Mark as known
        newp->m_known = true;
        // Always clear next pointer on insertion
        // If very first element, then easy
        if (VL_UNLIKELY(!heapp)) {
            newp->m_nextp = nullptr;
            newp->m_kidsp = nullptr;
            return newp;
        }
        // Otherwise compare the nodes
        if (*newp < *heapp) {
            // The new node is better, the best goes under it
            newp->m_nextp = nullptr;
            newp->m_kidsp = heapp;
            return newp;
        } else {
            // The old best is better, it goes under the best
            newp->m_nextp = heapp->m_kidsp;
            newp->m_kidsp = nullptr;
            heapp->m_kidsp = newp;
            return heapp;
        }
    }

    // Merge two pairing heaps rooted at the given nodes
    static HeapNode* merge(HeapNode* ap, HeapNode* bp) {
        if (*ap < *bp) {
            // bp goes under ap
            bp->m_nextp = ap->m_kidsp;
            ap->m_kidsp = bp;
            return ap;
        } else {
            // ap goes under bp
            ap->m_nextp = bp->m_kidsp;
            bp->m_kidsp = ap;
            return bp;
        }
    }

    // Pop all removed elements from the top of the pairing heap
    HeapNode* popHeap(HeapNode* rootp) {
#if VL_DEBUG
        UASSERT(rootp->m_removed, "Should have been removed");
#endif
        // Grab the children of the heap
        HeapNode* kidsp = rootp->m_kidsp;
        // Free the root node, we are done with it
        freeNode(rootp);
        // Pairwise merge the child nodes, cleaning them up as we go
        HeapNode* resultp = nullptr;
        while (kidsp) {
            // Pop and clean up children until we have 2 clean heaps
            HeapNode* const ap = cleanHeap(kidsp);
            if (!ap) break;
            HeapNode* const bp = cleanHeap(ap->m_nextp);
            if (!bp) {
                // We have a leftover child, prepend to results
                ap->m_nextp = resultp;
                resultp = ap;
                break;
            }
            kidsp = bp->m_nextp;
            // Merge the pair
            HeapNode* const mergedp = merge(ap, bp);
            // Prepend to list
            mergedp->m_nextp = resultp;
            resultp = mergedp;
        }
        // If all child heaps were fully removed (or there were no children at all), then done
        if (!resultp) return nullptr;
        // Now merge reduce the merged pairs
        while (resultp->m_nextp) {
            // Pop first two results
            HeapNode* const ap = resultp;
            HeapNode* const bp = ap->m_nextp;
            resultp = bp->m_nextp;
            // Merge them
            HeapNode* const mergedp = merge(ap, bp);
            // Prepend back to list
            mergedp->m_nextp = resultp;
            resultp = mergedp;
        }
        // And we are done
        return resultp;
    }

    // Remove elements until the root is not removed. Follows nextp chain if whole heap is removed.
    HeapNode* cleanHeap(HeapNode* hnp) {
        // Empty is empty
        if (!hnp) return nullptr;
        // If the top is not removed, then there is nothing to be done
        if (!hnp->m_removed) return hnp;
        // Keep hold of next node
        HeapNode* const nextp = hnp->m_nextp;
        // Pop removed elements
        hnp = popHeap(hnp);
        // If we emptied it out return the next node cleaned
        if (!hnp) return cleanHeap(nextp);
        // Reset next node
        hnp->m_nextp = nextp;
        // Done
        return hnp;
    }

public:
    // CONSTRUCTORS
    explicit V3Scoreboard() = default;
    ~V3Scoreboard() = default;

    // Add an element to the scoreboard.
    // Note this cannot be returned until after the next call to 'rescore'.
    void addElem(T_Elem* elemp) {
#if VL_DEBUG
        UASSERT(!contains(elemp), "Adding element to scoreboard that was already in a scoreboard");
#endif
        // Just prepend it to the unknown list
        HeapNode* const hnp = allocNode(elemp);
        hnp->m_nextp = m_unknonwp;
        m_unknonwp = hnp;
    }

    // Remove element from scoreboard.
    static void removeElem(T_Elem* elemp) {
        // Just mark it as removed. It will actually get removed on 'best', if it has a known
        // score, or on 'rescore' if it has an unknown score.
        elemp->m_heapNodep->m_removed = true;
        elemp->m_heapNodep = nullptr;
    }

    // Returns true if the element is present in the scoreboard, false otherwise.Every other method
    // that takes an T_Elem* has undefined behavior if the element is not in this scoreboard.
    // Furthermore, this method is only valid if the element can only possibly be in this
    // scoreboard. That is: if the element might be in another scoreboard, the behaviour of this
    // method is undefined.
    static bool contains(const T_Elem* elemp) { return elemp->m_heapNodep; }

    // Get the best element, with the lowest score (lower is better), among elements whose scores
    // are known. Returns nullptr if no elements with known scores exist.
    //
    // This does not automatically rescore. Client must call 'rescore' appropriately to ensure all
    // elements in the scoreboard are reflected in the result of this method. Otherwise, this
    // method only considers elements that aren't pending rescore.
    T_Elem* best() {
        // Clean up removed elements
        m_knownp = cleanHeap(m_knownp);
        // Just return the top of the heap, if not empty
        return VL_LIKELY(m_knownp) ? m_knownp->m_elemp : nullptr;
    }

    // Tell the scoreboard that this element's score may have changed. At the time of this call,
    // the element's score becomes "unknown" to the V3Scoreboard. Unknown elements won't be
    // returned by 'best'. The element's score will remain unknown until the next call to
    // 'rescore'. The client must call this for each element whose score has changed. The client
    // may call this for elements whose score has not changed. Doing so makes the element
    // ineligible to be returned by 'best' until the next call to 'rescore'.
    void hintScoreChanged(T_Elem* elemp) {
        // If it's already in the unknown list, then nothing to do
        if (!elemp->m_heapNodep->m_known) return;
        // Otherwise it was in the heap, so mark as removed from the heap
        elemp->m_heapNodep->m_removed = true;
        // Prepend it to the unknown list via a new node
        HeapNode* const hnp = allocNode(elemp);
        hnp->m_nextp = m_unknonwp;
        m_unknonwp = hnp;
    }

    // True if we might have elements with unknown score. Conservative, 'rescore' might not
    // actually yield more elements, but eventually 'needsRescore' will become false.
    bool needsRescore() const { return m_unknonwp; }

    // False if the element's score is known to the scoreboard, else true if the element's score is
    // unknown until the next call to 'rescore'.
    static bool needsRescore(const T_Elem* elemp) { return !elemp->m_heapNodep->m_known; }

    // Retrieve the last known score for an element.
    static T_Score cachedScore(const T_Elem* elemp) { return elemp->m_heapNodep->m_score; }

    // For each element whose score is unknown, recompute the score and add to the known heap
    void rescore() {
        // Clean up the known heap so we can insert into it
        m_knownp = cleanHeap(m_knownp);
        // Rescore and insert all unknown elements
        while (m_unknonwp) {
            // Pop head of unknown list
            HeapNode* const hnp = m_unknonwp;
            m_unknonwp = m_unknonwp->m_nextp;
            // If removed, then free the node and move on
            if (hnp->m_removed) {
                freeNode(hnp);
                continue;
            }
            // Otherwise re-compute the score
            hnp->m_score = hnp->m_elemp->score();
            // Insert into known heap
            m_knownp = insertHeap(hnp, m_knownp);
        }
    }
};

// ######################################################################

namespace V3ScoreboardBase {
void selfTest();
}  // namespace V3ScoreboardBase

#endif  // Guard
