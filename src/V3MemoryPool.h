// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Memory pool for fast dynamic allocations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2020 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3MEMORYPOOL_H_
#define _V3MEMORYPOOL_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

//============================================================================

class V3MemoryPool {

    const size_t m_block_size;

    void **m_free;

public:
    V3MemoryPool(size_t block_size) : m_block_size(block_size), m_free(NULL) {}

    void* allocate() {
        if (m_free) {
            void *result = m_free;
            m_free = reinterpret_cast<void**>(*m_free);
            return result;
        } else {
//            printf("Allocating %s\n", typeid(T).name());
            constexpr int n = 1024*128;
            char* p = new char[m_block_size*n];
            for (int i = 1 ; i < n - 1 ; i++) {
                *reinterpret_cast<void**>(p+ i*m_block_size) = p + (i+1)*m_block_size;
            }
            *reinterpret_cast<void**>(p + (n-1)*m_block_size) = NULL;
            m_free = reinterpret_cast<void**>(p + m_block_size);
            return p;
        }
    }

    void release(void *b) {
        void **block = reinterpret_cast<void**>(b);
        *block = reinterpret_cast<void*>(m_free);
        m_free = block;
    }
};

#endif  // Guard
