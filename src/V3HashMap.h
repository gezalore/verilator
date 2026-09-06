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
// Entries with equal hashes are probed in the order they were inserted, so
// callers can depend on the first match being the earliest inserted. Erasing
// and growing both maintain this.
//
//*************************************************************************

#ifndef VERILATOR_V3HASHMAP_H_
#define VERILATOR_V3HASHMAP_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

#include <algorithm>
#include <array>
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
        const std::vector<Entry> oldTable{std::move(m_table)};
        m_table.clear();
        m_table.resize(size);
        if (oldTable.empty()) return;
        // Reinsert in probing order, which keeps entries with equal hashes in insertion
        // order. Start from a free slot, as a run of occupied slots that wraps around the
        // end of the table would otherwise be traversed tail first.
        const size_t oldMask = oldTable.size() - 1;
        size_t begin = 0;
        while (oldTable[begin].m_valuep) ++begin;  // Below full load, so this terminates
        for (size_t n = 1; n <= oldMask + 1; ++n) {
            const Entry& entry = oldTable[(begin + n) & oldMask];
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
    // The remaining entries keep their relative probing order.
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

    // SELF TEST
    static void selfTest() VL_MT_DISABLED;
};

//######################################################################

template <typename T_Value>
void V3HashMap<T_Value>::selfTest() {
    // Values are only ever compared by identity here, so any distinct addresses will do
    std::array<T_Value, 8> values;
    std::array<T_Value, 40> many;  // Enough entries to grow the smallest table twice
    const auto valuep = [&values](size_t i) { return &values[i]; };
    const auto isValue = [&values](size_t i) {
        return [&values, i](const T_Value* p) { return p == &values[i]; };
    };
    // The order the entries with the given hash are probed in
    const auto probeOrder = [](const V3HashMap<T_Value>& map, size_t hash) {
        std::vector<const T_Value*> result;
        map.find(hash, [&result](const T_Value* p) {
            result.push_back(p);
            return false;  // Never accept, so the whole probe sequence is visited
        });
        return result;
    };

    // Entries that are inserted are found, entries that are not are not
    {
        V3HashMap<T_Value> map;
        UASSERT_SELFTEST(size_t, map.size(), 0);
        UASSERT(!map.find(1, isValue(0)), "SelfTest: found entry in empty map");
        map.insert(1, valuep(0));
        UASSERT_SELFTEST(size_t, map.size(), 1);
        UASSERT(map.find(1, isValue(0)) == valuep(0), "SelfTest: inserted entry not found");
        UASSERT(!map.find(1, isValue(1)), "SelfTest: found entry never inserted");
        UASSERT(!map.find(2, isValue(0)), "SelfTest: found entry under wrong hash");
        map.erase(1, isValue(0));
        UASSERT_SELFTEST(size_t, map.size(), 0);
        UASSERT(!map.find(1, isValue(0)), "SelfTest: erased entry still found");
        map.erase(1, isValue(0));  // Erasing what is absent is a no-op
        UASSERT_SELFTEST(size_t, map.size(), 0);
    }

    // Entries with equal hashes are probed in insertion order, whichever is erased,
    // including when other hashes collide into the same slots
    for (size_t erase = 0; erase < 4; ++erase) {
        for (const size_t hash : {size_t{0}, size_t{7}, ~size_t{0}}) {  // Also wrap the table
            V3HashMap<T_Value> map;
            // Interleave entries of an unrelated hash landing on the same slots
            map.insert(hash, valuep(0));
            map.insert(hash + 1, valuep(4));
            map.insert(hash, valuep(1));
            map.insert(hash, valuep(2));
            map.insert(hash, valuep(3));
            const std::vector<const T_Value*> before = probeOrder(map, hash);
            UASSERT_SELFTEST(size_t, before.size(), 4);
            map.erase(hash, isValue(erase));
            UASSERT_SELFTEST(size_t, map.size(), 4);
            // The others keep their order, and the unrelated entry is still there
            std::vector<const T_Value*> expect;
            for (const T_Value* p : before) {
                if (p != valuep(erase)) expect.push_back(p);
            }
            UASSERT(probeOrder(map, hash) == expect, "SelfTest: erase changed probe order");
            UASSERT(map.find(hash + 1, isValue(4)) == valuep(4),
                    "SelfTest: erase lost a colliding entry");
        }
    }

    // Growing keeps entries with equal hashes in insertion order, including when their run
    // wraps around the end of the table. Note this only bites once there are enough
    // entries to actually grow the table, so do not reserve here.
    for (const size_t hash : {size_t{0}, size_t{7}, ~size_t{0}}) {
        V3HashMap<T_Value> map;
        for (size_t i = 0; i < many.size(); ++i) map.insert(hash, &many[i]);
        UASSERT_SELFTEST(size_t, map.size(), many.size());
        const std::vector<const T_Value*> order = probeOrder(map, hash);
        UASSERT_SELFTEST(size_t, order.size(), many.size());
        for (size_t i = 0; i < many.size(); ++i) {
            UASSERT(order[i] == &many[i], "SelfTest: resize changed probe order");
        }
    }

    // Reserving avoids growing, and all entries survive either way
    for (const bool doReserve : {false, true}) {
        V3HashMap<T_Value> map;
        if (doReserve) map.reserve(values.size());
        for (size_t i = 0; i < values.size(); ++i) map.insert(i * 1234567, valuep(i));
        for (size_t i = 0; i < values.size(); ++i) {
            UASSERT(map.find(i * 1234567, isValue(i)) == valuep(i), "SelfTest: entry lost");
        }
        UASSERT_SELFTEST(size_t, map.size(), values.size());
    }
}

#endif  // Guard
