// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Open addressing hash table
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
// An open addressing, linear probing hash table of pointers.
//
// The keys are not held in the table. The caller passes in the hash of the
// entry it wants, together with a predicate deciding whether a stored entry
// is that entry. This keeps a slot down to a hash and a pointer, so probing
// touches few cache lines, and suits the common case where the key can be
// recovered from the value it belongs to.
//
// Entries with equal hashes are probed in the order they were inserted,
// which callers relying on the first match being the earliest inserted can
// depend on, but only if they never erase.
//
//*************************************************************************

#ifndef VERILATOR_V3HASHMAP_H_
#define VERILATOR_V3HASHMAP_H_

#include "config_build.h"
#include "verilatedos.h"

#include <algorithm>
#include <vector>

template <typename T_Value>
class V3HashMap final {
    // TYPES
    struct Entry final {
        size_t m_hash = 0;  // Hash of the entry
        T_Value* m_valuep = nullptr;  // The entry - nullptr marks a free slot
    };

    // CONSTANTS
    static constexpr size_t MIN_SIZE = 16;  // Smallest table allocated

    // STATE
    std::vector<Entry> m_table;  // The table, size is a power of two, or zero when unallocated
    size_t m_used = 0;  // Number of occupied slots

    // METHODS

    // Index of the free slot the given hash probes to. There must be one.
    size_t freeSlot(size_t hash) const {
        const size_t mask = m_table.size() - 1;
        size_t i = hash & mask;
        while (m_table[i].m_valuep) i = (i + 1) & mask;
        return i;
    }

    // Resize to the given number of slots, which must fit all entries
    void resize(size_t size) {
        std::vector<Entry> oldTable{std::move(m_table)};
        m_table.clear();
        m_table.resize(size);
        for (const Entry& entry : oldTable) {
            // Reinserting in slot order keeps entries with equal hashes in insertion order
            if (entry.m_valuep) m_table[freeSlot(entry.m_hash)] = entry;
        }
    }

public:
    // CONSTRUCTORS
    V3HashMap() = default;
    ~V3HashMap() = default;
    VL_UNCOPYABLE(V3HashMap);

    // METHODS
    size_t size() const { return m_used; }

    // Make room for the given number of entries, so inserting that many will not resize
    void reserve(size_t entries) {
        size_t size = MIN_SIZE;
        while (size * 3 < entries * 4) size *= 2;
        if (size > m_table.size()) resize(size);
    }

    // The entry with the given hash that 'equal' accepts, or nullptr if there is none
    template <typename T_Equal>
    T_Value* find(size_t hash, T_Equal&& equal) const {
        if (m_table.empty()) return nullptr;
        const size_t mask = m_table.size() - 1;
        for (size_t i = hash & mask; m_table[i].m_valuep; i = (i + 1) & mask) {
            const Entry& entry = m_table[i];
            if (entry.m_hash == hash && equal(entry.m_valuep)) return entry.m_valuep;
        }
        return nullptr;
    }

    // Add an entry that is known not to be in the table already
    void insert(size_t hash, T_Value* valuep) {
        // Grow at 3/4 load, which keeps the probes short without wasting much
        if (VL_UNLIKELY((m_used + 1) * 4 > m_table.size() * 3)) {
            resize(std::max<size_t>(MIN_SIZE, m_table.size() * 2));
        }
        Entry& entry = m_table[freeSlot(hash)];
        entry.m_hash = hash;
        entry.m_valuep = valuep;
        ++m_used;
    }

    // Remove the entry with the given hash that 'equal' accepts, if there is one.
    // Note this can reorder entries with equal hashes, see the file header.
    template <typename T_Equal>
    void erase(size_t hash, T_Equal&& equal) {
        if (m_table.empty()) return;
        const size_t mask = m_table.size() - 1;
        size_t i = hash & mask;
        while (true) {
            const Entry& entry = m_table[i];
            if (!entry.m_valuep) return;  // Not in the table
            if (entry.m_hash == hash && equal(entry.m_valuep)) break;
            i = (i + 1) & mask;
        }
        // Backward shift deletion: move up the entries the hole would break the probing of
        size_t j = i;
        while (true) {
            j = (j + 1) & mask;
            const Entry& entry = m_table[j];
            if (!entry.m_valuep) break;
            // Move back if its home position does not lie in the cyclic range (i, j]
            if (((j - (entry.m_hash & mask)) & mask) >= ((j - i) & mask)) {
                m_table[i] = entry;
                i = j;
            }
        }
        m_table[i] = Entry{};
        --m_used;
    }
};

#endif  // Guard
