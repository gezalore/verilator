// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Sorting routines for short fixed size sequences
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

#ifndef VERILATOR_V3FIXEDSORT_H_
#define VERILATOR_V3FIXEDSORT_H_

#include "config_build.h"
#include "verilatedos.h"

#include <algorithm>
#include <functional>

namespace vlt {

namespace batcher_network {

// Default Swap operator
template <typename T_Value>
struct DefaultSwap {
    void operator()(T_Value& a, T_Value& b) {
        if (std::less(b, a)) std::swap(a, b);
    }
};

// Sort step
template <typename Container, typename Swap, std::size_t Idx, std::size_t N>
struct Sort;

// Merge step
template <typename Container, typename Swap, std::size_t Idx, std::size_t Stride,  //
          std::size_t NA, std::size_t NB>
struct Merge;

// Final step
template <typename Container, typename Swap, std::size_t Idx, std::size_t Stride, std::size_t N>
struct Final;

constexpr size_t roundDownToPowerOf2(size_t i) {
    while (i & (i - 1)) i = i & (i - 1);
    return i;
}

// Generic sorting step
template <typename Container, typename Swap, std::size_t Idx, std::size_t N>
struct Sort final {
    static_assert(N >= 3, "This code path should not be sorting too small blocks");
    VL_ATTR_ALWINLINE Sort(Container& c) {
        constexpr std::size_t NA = roundDownToPowerOf2((N * 2) / 3);
        constexpr std::size_t NB = N - NA;
        // Sort first half
        Sort<Container, Swap, Idx, NA>{c};
        // Sort second half
        Sort<Container, Swap, Idx + NA, NB>{c};
        // Merge
        Merge<Container, Swap, Idx, 1, NA, NB>{c};
    }
};

// Base case sort 2
template <typename Container, typename Swap, std::size_t Idx>
struct Sort<Container, Swap, Idx, 2> final {
    VL_ATTR_ALWINLINE Sort(Container& c) { Swap{}(c[Idx], c[Idx + 1]); }
};

// Base case sort 1
template <typename Container, typename Swap, std::size_t Idx>
struct Sort<Container, Swap, Idx, 1> final {
    VL_ATTR_ALWINLINE Sort(Container&) {}
};

// Generic merging step
template <typename Container, typename Swap, std::size_t Idx, std::size_t Stride, std::size_t NA,
          std::size_t NB>
struct Merge final {
    static_assert(NA % 2 == 0, "A must be a multiple of 2");
    static_assert(NA <= 2 * NB && NB <= 2 * NA, "Must be balanced.");

    VL_ATTR_ALWINLINE Merge(Container& c) {
        Merge<Container, Swap, Idx, 2 * Stride, NA / 2, (NB + 1) / 2>{c};
        Merge<Container, Swap, Idx + Stride, 2 * Stride, NA / 2, NB / 2>{c};
        Final<Container, Swap, Idx + Stride, Stride, (NA + NB - 1) / 2>{c};
    }
};

// Base case of merging 1 and 2
template <typename Container, typename Swap, std::size_t Idx, std::size_t Stride>
struct Merge<Container, Swap, Idx, Stride, 1, 2> {
    VL_ATTR_ALWINLINE Merge(Container& c) {
        Swap{}(c[Idx], c[Idx + 2 * Stride]);
        Swap{}(c[Idx], c[Idx + Stride]);
    }
};

// Base case of merging 2 and 1
template <typename Container, typename Swap, std::size_t Idx, std::size_t Stride>
struct Merge<Container, Swap, Idx, Stride, 2, 1> {
    VL_ATTR_ALWINLINE Merge(Container& c) {
        Swap{}(c[Idx], c[Idx + 2 * Stride]);
        Swap{}(c[Idx + Stride], c[Idx + 2 * Stride]);
    }
};

// Base case of merging 1 and 1
template <typename Container, typename Swap, std::size_t Idx, std::size_t Stride>
struct Merge<Container, Swap, Idx, Stride, 1, 1> final {
    VL_ATTR_ALWINLINE Merge(Container& c) { Swap{}(c[Idx], c[Idx + Stride]); }
};

// Generic case for final step
template <typename Container, typename Swap, std::size_t Idx, std::size_t Stride, std::size_t N>
struct Final final {
    VL_ATTR_ALWINLINE Final(Container& c) {
        Swap{}(c[Idx], c[Idx + Stride]);
        Final<Container, Swap, Idx + 2 * Stride, Stride, N - 1>{c};
    }
};

// Base case for final step
template <typename Container, typename Swap, std::size_t Idx, std::size_t Stride>
struct Final<Container, Swap, Idx, Stride, 0> final {
    VL_ATTR_ALWINLINE Final(Container&) {}
};

}  // namespace batcher_network

// Entry point for fixed size sort using soring networks based on a compare and swap primitive
// operation.
template <std::size_t N,  // Number of entries to sort
          typename Container,  // Type of container
          typename Swap  // The compare and swap operator
          = batcher_network::DefaultSwap<typename Container::value_type>>
void fixedSort(Container& c) {
    batcher_network::Sort<Container, Swap, 0, N>{c};
}

}  // namespace vlt

#endif  // Guard
