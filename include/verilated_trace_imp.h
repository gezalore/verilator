// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
//
// Verilated tracing implementation code template common to all formats.
// This file is included by the format-specific implementations and
// should not be used otherwise.
//
//=============================================================================

// clang-format off

#ifndef VL_CPPCHECK
#if !defined(VL_SUB_T) || !defined(VL_BUF_T)
# error "This file should be included in trace format implementations"
#endif

#include "verilated_intrinsics.h"
#include "verilated_trace.h"
#include "verilated_threads.h"
#include <algorithm>
#include <cstring>
#include <list>

// clang-format on

//=============================================================================
// Static utility functions

static double timescaleToDouble(const char* unitp) VL_PURE {
    char* endp = nullptr;
    double value = std::strtod(unitp, &endp);
    // On error so we allow just "ns" to return 1e-9.
    if (value == 0.0 && endp == unitp) value = 1;
    unitp = endp;
    for (; *unitp && std::isspace(*unitp); ++unitp) {}
    switch (*unitp) {
    case 's': value *= 1e0; break;
    case 'm': value *= 1e-3; break;
    case 'u': value *= 1e-6; break;
    case 'n': value *= 1e-9; break;
    case 'p': value *= 1e-12; break;
    case 'f': value *= 1e-15; break;
    case 'a': value *= 1e-18; break;
    }
    return value;
}

//=============================================================================
// Life cycle

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::closeBase() {}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::flushBase() {}

//=============================================================================
// Callbacks to run on global events

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::onFlush(void* selfp) {
    // This calls 'flush' on the derived class (which must then get any mutex)
    reinterpret_cast<VL_SUB_T*>(selfp)->flush();
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::onExit(void* selfp) {
    // This calls 'close' on the derived class (which must then get any mutex)
    reinterpret_cast<VL_SUB_T*>(selfp)->close();
}

//=============================================================================
// VerilatedTrace

template <>
VerilatedTrace<VL_SUB_T, VL_BUF_T>::VerilatedTrace() {
    set_time_unit(Verilated::threadContextp()->timeunitString());
    set_time_resolution(Verilated::threadContextp()->timeprecisionString());
}

template <>
VerilatedTrace<VL_SUB_T, VL_BUF_T>::~VerilatedTrace() {
    if (m_sigs_oldvalp) VL_DO_CLEAR(delete[] m_sigs_oldvalp, m_sigs_oldvalp = nullptr);
    if (m_sigs_enabledp) VL_DO_CLEAR(delete[] m_sigs_enabledp, m_sigs_enabledp = nullptr);
    Verilated::removeFlushCb(VerilatedTrace<VL_SUB_T, VL_BUF_T>::onFlush, this);
    Verilated::removeExitCb(VerilatedTrace<VL_SUB_T, VL_BUF_T>::onExit, this);
}

//=========================================================================
// Internals available to format-specific implementations

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::runInitCallback(size_t index,
                                                         bool rootInit) VL_MT_UNSAFE {
    if (m_initCbsCalled[index]) return;

    const CallbackRecord& cbr = m_initCbs[index];
    const uint32_t baseCode = nextCode();
    m_nextCode += cbr.m_nTraceCodes;

    void* const prevInitUserp = m_initUserp;
    const bool prevRootInit = m_rootInit;
    m_initUserp = cbr.m_userp;
    m_rootInit = rootInit;
    cbr.m_initCb(cbr.m_userp, self(), baseCode);
    m_initUserp = prevInitUserp;
    m_rootInit = prevRootInit;
    m_initCbsCalled[index] = true;
}

//=========================================================================
// RTMD based tracing

// Declare a value of the given type, recursing into unpacked arrays and structs
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::declareRtmdValue(const VlRtmdTables& tables,
                                                          uint32_t typeIdx, const char* name,
                                                          int arraynum, const VlRtmdScopeRow& row,
                                                          size_t addr) VL_MT_UNSAFE {
    const VlRtmdTypeRow& type = tables.m_typesp[typeIdx];
    const VlRtmdSignalType& sig = tables.m_signalsp[row.m_typeIdx];
    const VerilatedTraceSigDirection dir = vlRtmdToSigDirection(sig.m_direction);
    const VerilatedTraceSigKind kind = vlRtmdToSigKind(sig.m_varKind);
    // RTMD dumping uses a single buffer
    constexpr uint32_t fidx = 0;

    // Unpacked types open a naming level
    switch (type.m_op) {
    case VlRtmdTypeOp::UNPACKED_ARRAY: {
        const VlRtmdUnpackedArray& array = *type.m_unpackedArrayp;
        VL_TRACE_PUSH_PREFIX(self(), name, VerilatedTracePrefixType::UNPACKED_ARRAY, array.m_left,
                             array.m_right);
        const bool ascending = array.m_left <= array.m_right;
        // An unpacked element is named by its index, other elements take it as 'arraynum'
        const VlRtmdTypeOp elemOp = tables.m_typesp[array.m_elemIdx].m_op;
        const bool elemUnpacked
            = elemOp == VlRtmdTypeOp::UNPACKED_ARRAY || elemOp == VlRtmdTypeOp::UNPACKED_STRUCT;
        const uint32_t elements = vlRtmdElementsOf(array.m_left, array.m_right);
        for (uint32_t i = 0; i < elements; ++i) {
            const int index = ascending ? array.m_left + static_cast<int>(i)
                                        : array.m_left - static_cast<int>(i);
            const size_t elemAddr = addr + i * array.m_elemBytes;
            if (elemUnpacked) {
                const std::string elemName = '[' + std::to_string(index) + ']';
                declareRtmdValue(tables, array.m_elemIdx, elemName.c_str(), VL_RTMD_NO_INDEX, row,
                                 elemAddr);
            } else {
                declareRtmdValue(tables, array.m_elemIdx, "", index, row, elemAddr);
            }
        }
        VL_TRACE_POP_PREFIX(self());
        return;
    }
    case VlRtmdTypeOp::UNPACKED_STRUCT: {
        const VlRtmdUnpackedStruct& strct = *type.m_unpackedStructp;
        // Pass the member count as the range
        VL_TRACE_PUSH_PREFIX(self(), name, VerilatedTracePrefixType::UNPACKED_STRUCT,
                             static_cast<int>(strct.m_count), 0);
        for (uint32_t i = 0; i < strct.m_count; ++i) {
            const VlRtmdMember& member = strct.m_membersp[i];
            declareRtmdValue(tables, member.m_typeIdx, member.m_namep, VL_RTMD_NO_INDEX, row,
                             addr + member.m_offset);
        }
        VL_TRACE_POP_PREFIX(self());
        return;
    }
    default: break;
    }

    // A packed value
    const VlRtmdSigType rtmdSigType = vlRtmdSigTypeOf(tables, typeIdx);
    const VerilatedTraceSigType sigType = vlRtmdToSigType(rtmdSigType);
    const uint32_t bits = vlRtmdBitsOf(tables, typeIdx);
    const VlRtmdRange range = vlRtmdRangeOf(tables, typeIdx);
    const int dtypenum = type.m_op == VlRtmdTypeOp::ENUM ? type.m_enump->m_dtypenum : -1;

    // Allocate a code per word. Signals at the same address share the code. Constants never do.
    uint32_t code;
    bool firstName = true;  // First signal with this code
    if (row.m_op == VlRtmdScopeOp::SIGNAL_CONST) {
        code = m_nextCode;
        m_nextCode += VL_WORDS_I(bits);
    } else {
        const auto pair = m_rtmdValueCodes.emplace(std::make_pair(addr, bits), m_nextCode);
        code = pair.first->second;
        firstName = pair.second;
        if (firstName) m_nextCode += VL_WORDS_I(bits);
    }
    const int msb = range.m_left;
    const int lsb = range.m_right;
    // Record the value to dump, once per code
    if (firstName && row.m_op != VlRtmdScopeOp::SIGNAL_CONST) {
        const VlRtmdRead read = vlRtmdReadOf(rtmdSigType, bits);
        const void* const datap = static_cast<const uint8_t*>(tables.m_symsp) + addr;
        m_rtmdLeaves.push_back({datap, code, bits, row.m_actSetId, read});
    }
    if (firstName && row.m_op == VlRtmdScopeOp::SIGNAL_CONST && tables.m_constsp) {
        const VlRtmdRead read = vlRtmdReadOf(rtmdSigType, bits);
        m_rtmdConstLeaves.push_back({tables.m_constsp + row.m_dataOfs, code, bits, 0, read});
    }

    if (arraynum == VL_RTMD_NO_INDEX) {
        if (sigType == VerilatedTraceSigType::EVENT) {
            VL_TRACE_DECL_EVENT(self(), code, fidx, name, dtypenum, dir, kind, sigType);
        } else if (sigType == VerilatedTraceSigType::DOUBLE) {
            VL_TRACE_DECL_DOUBLE(self(), code, fidx, name, dtypenum, dir, kind, sigType);
        } else if (bits == 1 && vlRtmdIsScalar(tables, typeIdx)) {
            VL_TRACE_DECL_BIT(self(), code, fidx, name, dtypenum, dir, kind, sigType);
        } else if (bits <= 32) {
            VL_TRACE_DECL_BUS(self(), code, fidx, name, dtypenum, dir, kind, sigType, msb, lsb);
        } else if (bits <= 64) {
            VL_TRACE_DECL_QUAD(self(), code, fidx, name, dtypenum, dir, kind, sigType, msb, lsb);
        } else {
            VL_TRACE_DECL_WIDE(self(), code, fidx, name, dtypenum, dir, kind, sigType, msb, lsb);
        }
    } else {
        if (sigType == VerilatedTraceSigType::EVENT) {
            VL_TRACE_DECL_EVENT_ARRAY(self(), code, fidx, name, dtypenum, dir, kind, sigType,
                                      arraynum);
        } else if (sigType == VerilatedTraceSigType::DOUBLE) {
            VL_TRACE_DECL_DOUBLE_ARRAY(self(), code, fidx, name, dtypenum, dir, kind, sigType,
                                       arraynum);
        } else if (bits == 1 && vlRtmdIsScalar(tables, typeIdx)) {
            VL_TRACE_DECL_BIT_ARRAY(self(), code, fidx, name, dtypenum, dir, kind, sigType,
                                    arraynum);
        } else if (bits <= 32) {
            VL_TRACE_DECL_BUS_ARRAY(self(), code, fidx, name, dtypenum, dir, kind, sigType,
                                    arraynum, msb, lsb);
        } else if (bits <= 64) {
            VL_TRACE_DECL_QUAD_ARRAY(self(), code, fidx, name, dtypenum, dir, kind, sigType,
                                     arraynum, msb, lsb);
        } else {
            VL_TRACE_DECL_WIDE_ARRAY(self(), code, fidx, name, dtypenum, dir, kind, sigType,
                                     arraynum, msb, lsb);
        }
    }
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::declareRtmdSignal(const VlRtmdTables& tables,
                                                           const VlRtmdScopeRow& row)
    VL_MT_UNSAFE {
    const size_t addr = row.m_dataOfs;
    const VlRtmdSignalType& sig = tables.m_signalsp[row.m_typeIdx];
    declareRtmdValue(tables, sig.m_typeIdx, row.m_namep, VL_RTMD_NO_INDEX, row, addr);
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::declareRtmdTable(const VlRtmdTables& tables,
                                                          uint32_t tableIdx) VL_MT_UNSAFE {
    const VlRtmdScopeRow* const rowsp = tables.m_tablesp[tableIdx];
    const uint32_t nRows = tables.m_tableRowsp[tableIdx];
    for (uint32_t i = 0; i < nRows; ++i) {
        const VlRtmdScopeRow& row = rowsp[i];
        const char* const name = row.m_namep;
        switch (row.m_op) {
        case VlRtmdScopeOp::PUSH:
            VL_TRACE_PUSH_PREFIX(self(), name, vlRtmdToPrefixType(row.m_scopeKind), 0, 0);
            break;
        case VlRtmdScopeOp::POP: VL_TRACE_POP_PREFIX(self()); break;
        case VlRtmdScopeOp::SIGNAL:
        case VlRtmdScopeOp::SIGNAL_CONST: declareRtmdSignal(tables, row); break;
        case VlRtmdScopeOp::INSTANCE:
            VL_TRACE_PUSH_PREFIX(self(), name, vlRtmdToPrefixType(row.m_scopeKind), 0, 0);
            declareRtmdTable(tables, row.m_typeIdx);
            VL_TRACE_POP_PREFIX(self());
            break;
        case VlRtmdScopeOp::PARTITION: {
            // A --lib-create library registers its own tables, find them by instance name
            VL_TRACE_PUSH_PREFIX(self(), name, VerilatedTracePrefixType::SCOPE_MODULE, 0, 0);
            std::string libName{tables.m_namep};
            if (!libName.empty()) libName += '.';
            libName += row.m_libPathp;
            for (const VlRtmdTables& lib : m_rtmdTables) {
                // Absent if the library was compiled without tracing
                if (!lib.m_isLibInstance || libName != lib.m_namep) continue;
                declareRtmdTable(lib, lib.m_rootTable);
                break;
            }
            VL_TRACE_POP_PREFIX(self());
            break;
        }
        }
    }
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::elaborateRtmd() VL_MT_UNSAFE {
    m_rtmdLeaves.clear();
    m_rtmdConstLeaves.clear();
    m_rtmdGroups.clear();
    for (const VlRtmdTables& tables : m_rtmdTables) {
        // Libraries are walked from their PARTITION row
        if (tables.m_isLibInstance) continue;
        const size_t firstLeaf = m_rtmdLeaves.size();
        // Codes are only shared within a model
        m_rtmdValueCodes.clear();
        // Declare enums before the signals that reference them
        for (uint32_t i = 0; i < tables.m_nTypes; ++i) {
            const VlRtmdTypeRow& type = tables.m_typesp[i];
            if (type.m_op != VlRtmdTypeOp::ENUM) continue;
            const VlRtmdEnum* const enump = type.m_enump;
            VL_TRACE_DECL_DTYPE_ENUM(self(), enump->m_dtypenum, enump->m_namep, enump->m_count,
                                     vlRtmdBitsOf(tables, i), enump->m_namesp, enump->m_valuesp);
        }
        VL_TRACE_PUSH_PREFIX(self(), tables.m_namep, VerilatedTracePrefixType::SCOPE_MODULE, 0, 0);
        declareRtmdTable(tables, tables.m_rootTable);
        VL_TRACE_POP_PREFIX(self());
        // Group the leaves by activity set
        std::stable_sort(
            m_rtmdLeaves.begin() + firstLeaf, m_rtmdLeaves.end(),
            [](const RtmdLeaf& a, const RtmdLeaf& b) { return a.m_actSetId < b.m_actSetId; });
        for (size_t i = firstLeaf; i < m_rtmdLeaves.size();) {
            size_t j = i;
            while (j < m_rtmdLeaves.size()
                   && m_rtmdLeaves[j].m_actSetId == m_rtmdLeaves[i].m_actSetId) {
                ++j;
            }
            m_rtmdGroups.push_back({&tables, m_rtmdLeaves[i].m_actSetId, i, j - i});
            i = j;
        }
    }
    m_rtmdValueCodes.clear();
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::traceInit() VL_MT_UNSAFE {
    // Note: It is possible to re-open a trace file (VCD in particular),
    // so we must reset the next code here, but it must have the same number
    // of codes on re-open
    const uint32_t expectedCodes = nextCode();
    m_nextCode = 1;
    m_numSignals = 0;
    m_maxBits = 0;
    m_sigs_enabledVec.clear();
    m_initCbsCalled.assign(m_initCbs.size(), false);

    // Call all initialize callbacks for root instances, which will:
    // - Call decl* for each signal (these eventually call ::declCode)
    // - Call the initialize callbacks of library instances underneath
    // - Store the base code
    for (size_t i = 0; i < m_initCbs.size(); ++i) runInitCallback(i, true);

    // Declare the RTMD described models
    elaborateRtmd();

    if (expectedCodes && nextCode() != expectedCodes) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "Reopening trace file with different number of signals");
    }

    // Now that we know the number of codes, allocate space for the buffer
    // holding previous signal values.
    if (!m_sigs_oldvalp) m_sigs_oldvalp = new uint32_t[nextCode()];

    // Apply enables
    if (m_sigs_enabledp) VL_DO_CLEAR(delete[] m_sigs_enabledp, m_sigs_enabledp = nullptr);
    if (!m_sigs_enabledVec.empty()) {
        // Else if was empty, m_sigs_enabledp = nullptr to short circuit tests
        // But it isn't, so alloc one bit for each code to indicate enablement
        // We don't want to still use m_signs_enabledVec as std::vector<bool> is not
        // guaranteed to be fast
        m_sigs_enabledp = new uint32_t[1 + VL_WORDS_I(nextCode())]{0};
        m_sigs_enabledVec.reserve(nextCode());
        for (size_t code = 0; code < nextCode(); ++code) {
            if (m_sigs_enabledVec[code]) {
                m_sigs_enabledp[VL_BITWORD_I(code)] |= 1U << VL_BITBIT_I(code);
            }
        }
        m_sigs_enabledVec.clear();
    }

    // Set callback so flush/abort will flush this file
    Verilated::addFlushCb(VerilatedTrace<VL_SUB_T, VL_BUF_T>::onFlush, this);
    Verilated::addExitCb(VerilatedTrace<VL_SUB_T, VL_BUF_T>::onExit, this);
}

template <>
bool VerilatedTrace<VL_SUB_T, VL_BUF_T>::declCode(uint32_t code, const std::string& declName,
                                                  uint32_t bits) {
    if (VL_UNCOVERABLE(!code)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "Internal: internal trace problem, code 0 is illegal");
    }
    // To keep it simple, this is O(enables * signals), but we expect few enables
    bool enabled = false;
    if (m_dumpvars.empty()) enabled = true;
    for (const auto& item : m_dumpvars) {
        const int dumpvarsLevel = item.first;
        const char* dvp = item.second.c_str();
        const char* np = declName.c_str();
        while (*dvp && *dvp == *np) {
            ++dvp;
            ++np;
        }
        if (*dvp) continue;  // Didn't match dumpvar item
        if (*np && *np != ' ') continue;  // e.g. "t" isn't a match for "top"
        int levels = 0;
        while (*np) {
            if (*np++ == ' ') ++levels;
        }
        if (levels > dumpvarsLevel) continue;  // Too deep
        // We only need to set first code word if it's a multicode signal
        // as that's all we'll check for later
        if (m_sigs_enabledVec.size() <= code) m_sigs_enabledVec.resize((code + 1024) * 2);
        m_sigs_enabledVec[code] = true;
        enabled = true;
        break;
    }

    ++m_numSignals;
    m_maxBits = std::max(m_maxBits, bits);
    return enabled;
}

//=========================================================================
// Internals available to format-specific implementations

template <>
std::string VerilatedTrace<VL_SUB_T, VL_BUF_T>::timeResStr() const {
    return vl_timescaled_double(m_timeRes);
}

//=========================================================================
// External interface to client code

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_unit(const char* unitp) VL_MT_SAFE {
    m_timeUnit = timescaleToDouble(unitp);
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_unit(const std::string& unit) VL_MT_SAFE {
    set_time_unit(unit.c_str());
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_resolution(const char* unitp) VL_MT_SAFE {
    m_timeRes = timescaleToDouble(unitp);
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_resolution(const std::string& unit) VL_MT_SAFE {
    set_time_resolution(unit.c_str());
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpvars(int level, const std::string& hier) VL_MT_SAFE {
    if (level == 0) {
        m_dumpvars.clear();  // empty = everything on
    } else {
        // Convert Verilog . separators to trace space separators
        std::string hierSpaced = hier;
        for (auto& i : hierSpaced) {
            if (i == '.') i = ' ';
        }
        m_dumpvars.emplace_back(level, hierSpaced);
    }
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::parallelWorkerTask(void* datap, bool) {
    ParallelWorkerData* const wdp = reinterpret_cast<ParallelWorkerData*>(datap);
    // Run the task
    wdp->m_cb(wdp->m_userp, wdp->m_bufp);
    // Mark buffer as ready
    const VerilatedLockGuard lock{wdp->m_mutex};
    wdp->m_ready.store(true);
    if (wdp->m_waiting) wdp->m_cv.notify_one();
}

template <>
VL_ATTR_NOINLINE void VerilatedTrace<VL_SUB_T, VL_BUF_T>::ParallelWorkerData::wait() {
    // Spin for a while, waiting for the buffer to become ready
    for (int i = 0; i < VL_LOCK_SPINS; ++i) {
        if (VL_LIKELY(m_ready.load(std::memory_order_relaxed))) return;
        VL_CPU_RELAX();
    }
    // We have been spinning for a while, so yield the thread
    VerilatedLockGuard lock{m_mutex};
    m_waiting = true;
    m_cv.wait(m_mutex, [this] { return m_ready.load(std::memory_order_relaxed); });
    m_waiting = false;
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::runCallbacks(const std::vector<CallbackRecord>& cbVec) {
    if (parallel()) {
        // If tracing in parallel, dispatch to the thread pool
        VlThreadPool* threadPoolp = static_cast<VlThreadPool*>(m_contextp->threadPoolp());
        // List of work items for thread (std::list, as ParallelWorkerData is not movable)
        std::list<ParallelWorkerData> workerData;
        // We use the whole pool + the main thread
        const unsigned threads = threadPoolp->numThreads() + 1;
        // Main thread executes all jobs with index % threads == 0
        std::vector<ParallelWorkerData*> mainThreadWorkerData;
        // Enqueue all the jobs
        for (const CallbackRecord& cbr : cbVec) {
            // Always get the trace buffer on the main thread
            Buffer* const bufp = getTraceBuffer(cbr.m_fidx);
            // Create new work item
            workerData.emplace_back(cbr.m_dumpCb, cbr.m_userp, bufp);
            // Grab the new work item
            ParallelWorkerData* const itemp = &workerData.back();
            // Enqueue task to thread pool, or main thread
            if (unsigned rem = cbr.m_fidx % threads) {
                threadPoolp->workerp(rem - 1)->addTask(parallelWorkerTask, itemp);
            } else {
                mainThreadWorkerData.push_back(itemp);
            }
        }
        // Execute main thread jobs
        for (ParallelWorkerData* const itemp : mainThreadWorkerData) {
            parallelWorkerTask(itemp, false);
        }
        // Commit all trace buffers in order
        for (ParallelWorkerData& item : workerData) {
            // Wait until ready
            item.wait();
            // Commit the buffer
            commitTraceBuffer(item.m_bufp);
        }

        // Done
        return;
    }
    // Fall back on sequential execution
    for (const CallbackRecord& cbr : cbVec) {
        Buffer* const traceBufferp = getTraceBuffer(cbr.m_fidx);
        cbr.m_dumpCb(cbr.m_userp, traceBufferp);
        commitTraceBuffer(traceBufferp);
    }
}

// Defined at the end of this file, after the trace buffer methods
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpDescriptors(Buffer* bufp, bool full) VL_MT_UNSAFE;
template <>
bool VerilatedTrace<VL_SUB_T, VL_BUF_T>::rtmdGroupActive(const RtmdGroup&) const VL_MT_UNSAFE;
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpRtmdConsts(Buffer* bufp) VL_MT_UNSAFE;

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dump(uint64_t timeui) VL_MT_SAFE_EXCLUDES(m_mutex) {
    // Not really VL_MT_SAFE but more VL_MT_UNSAFE_ONE.
    // This does get the mutex, but if multiple threads are trying to dump
    // chances are the data being dumped will have other problems
    const VerilatedLockGuard lock{m_mutex};
    if (VL_UNCOVERABLE(m_didSomeDump && timeui <= m_timeLastDump)) {  // LCOV_EXCL_START
        VL_PRINTF_MT("%%Warning: previous dump at t=%" PRIu64 ", requesting t=%" PRIu64
                     ", dump call ignored\n",
                     m_timeLastDump, timeui);
        return;
    }  // LCOV_EXCL_STOP
    m_timeLastDump = timeui;
    m_didSomeDump = true;

    Verilated::quiesce();

    // Call hook for format-specific behaviour
    if (VL_UNLIKELY(m_fullDump)) {
        if (!preFullDump()) return;
    } else {
        if (!preChangeDump()) return;
    }

    // Update time point
    emitTimeChange(timeui);

    // Run the callbacks
    const bool fullDump = m_fullDump;
    if (VL_UNLIKELY(m_fullDump)) {
        m_fullDump = false;  // No more need for next dump to be full
        runCallbacks(m_fullCbs);
    } else {
        runCallbacks(m_chgCbs);
    }

    // Dump the RTMD described models
    if (!m_rtmdLeaves.empty()) {
        Buffer* const bufp = getTraceBuffer(0);
        dumpDescriptors(bufp, fullDump);
        commitTraceBuffer(bufp);
    }

    if (VL_UNLIKELY(m_constDump)) {
        m_constDump = false;
        runCallbacks(m_constCbs);
        if (!m_rtmdConstLeaves.empty()) {
            Buffer* const bufp = getTraceBuffer(0);
            dumpRtmdConsts(bufp);
            commitTraceBuffer(bufp);
        }
    }

    for (const CallbackRecord& cbr : m_cleanupCbs) cbr.m_cleanupCb(cbr.m_userp, self());
}

//=============================================================================
// Non-hot path internal interface to Verilator generated code

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addModel(VerilatedModel* modelp)
    VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};

    const bool newModel = m_models.insert(modelp).second;
    VerilatedContext* const contextp = modelp->contextp();

    // Validate
    if (!newModel) {  // LCOV_EXCL_START
        VL_FATAL_MT(
            __FILE__, __LINE__, "",
            "The same model has already been added to this trace file or VerilatedContext");
    }
    if (VL_UNCOVERABLE(m_contextp && contextp != m_contextp)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "A trace file instance can only handle models from the same VerilatedContext");
    }
    if (VL_UNCOVERABLE(m_didSomeDump)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "Cannot add models to a trace file if 'dump' has already been called");
    }  // LCOV_EXCL_STOP

    // Keep hold of the context
    m_contextp = contextp;

    // Get the desired trace config from the model
    const std::unique_ptr<VerilatedTraceConfig> configp = modelp->traceConfig();

    // Configure trace base class
    // If at least one model requests parallel tracing, then use it
    m_parallel |= configp->m_useParallel;

    // Configure format-specific sub class
    configure(*(configp.get()));
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addCallbackRecord(std::vector<CallbackRecord>& cbVec,
                                                           CallbackRecord&& cbRec)
    VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    cbVec.push_back(cbRec);
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addInitCb(initCb_t cb, void* userp,
                                                   const std::string& name, bool isLibInstance,
                                                   uint32_t nTraceCodes) VL_MT_SAFE {
    addCallbackRecord(m_initCbs, CallbackRecord{cb, userp, isLibInstance, name, nTraceCodes});
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addConstCb(dumpCb_t cb, uint32_t fidx,
                                                    void* userp) VL_MT_SAFE {
    addCallbackRecord(m_constCbs, CallbackRecord{cb, fidx, userp});
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addFullCb(dumpCb_t cb, uint32_t fidx,
                                                   void* userp) VL_MT_SAFE {
    addCallbackRecord(m_fullCbs, CallbackRecord{cb, fidx, userp});
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addChgCb(dumpCb_t cb, uint32_t fidx,
                                                  void* userp) VL_MT_SAFE {
    addCallbackRecord(m_chgCbs, CallbackRecord{cb, fidx, userp});
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addCleanupCb(cleanupCb_t cb, void* userp) VL_MT_SAFE {
    addCallbackRecord(m_cleanupCbs, CallbackRecord{cb, userp});
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::initLib(const std::string& name) VL_MT_SAFE {
    // Note it's possible the instance doesn't exist if the lib was compiled without tracing
    for (size_t i = 0; i < m_initCbs.size(); ++i) {
        if (m_initCbs[i].m_name != name) continue;
        runInitCallback(i, false);
    }
}

//=========================================================================
// Primitives converting binary values to strings...

// All of these take a destination pointer where the string will be emitted,
// and a value to convert. There are a couple of variants for efficiency.

inline void cvtCDataToStr(char* dstp, CData value) {
#ifdef VL_HAVE_SSE2
    // Similar to cvtSDataToStr but only the bottom 8 byte lanes are used
    const __m128i a = _mm_cvtsi32_si128(value);
    const __m128i b = _mm_unpacklo_epi8(a, a);
    const __m128i c = _mm_shufflelo_epi16(b, 0);
    const __m128i m = _mm_set1_epi64x(0x0102040810204080);
    const __m128i d = _mm_cmpeq_epi8(_mm_and_si128(c, m), m);
    const __m128i result = _mm_sub_epi8(_mm_set1_epi8('0'), d);
    _mm_storel_epi64(reinterpret_cast<__m128i*>(dstp), result);
#else
    dstp[0] = '0' | static_cast<char>((value >> 7) & 1);
    dstp[1] = '0' | static_cast<char>((value >> 6) & 1);
    dstp[2] = '0' | static_cast<char>((value >> 5) & 1);
    dstp[3] = '0' | static_cast<char>((value >> 4) & 1);
    dstp[4] = '0' | static_cast<char>((value >> 3) & 1);
    dstp[5] = '0' | static_cast<char>((value >> 2) & 1);
    dstp[6] = '0' | static_cast<char>((value >> 1) & 1);
    dstp[7] = '0' | static_cast<char>(value & 1);
#endif
}

inline void cvtSDataToStr(char* dstp, SData value) {
#ifdef VL_HAVE_SSE2
    // We want each bit in the 16-bit input value to end up in a byte lane
    // within the 128-bit XMM register. Note that x86 is little-endian and we
    // want the MSB of the input at the low address, so we will bit-reverse
    // at the same time.

    // Put value in bottom of 128-bit register a[15:0] = value
    const __m128i a = _mm_cvtsi32_si128(value);
    // Interleave bytes with themselves
    // b[15: 0] = {2{a[ 7:0]}} == {2{value[ 7:0]}}
    // b[31:16] = {2{a[15:8]}} == {2{value[15:8]}}
    const __m128i b = _mm_unpacklo_epi8(a, a);
    // Shuffle bottom 64 bits, note swapping high bytes with low bytes
    // c[31: 0] = {2{b[31:16]}} == {4{value[15:8}}
    // c[63:32] = {2{b[15: 0]}} == {4{value[ 7:0}}
    const __m128i c = _mm_shufflelo_epi16(b, 0x05);
    // Shuffle whole register
    // d[ 63: 0] = {2{c[31: 0]}} == {8{value[15:8}}
    // d[126:54] = {2{c[63:32]}} == {8{value[ 7:0}}
    const __m128i d = _mm_shuffle_epi32(c, 0x50);
    // Test each bit within the bytes, this sets each byte lane to 0
    // if the bit for that lane is 0 and to 0xff if the bit is 1.
    const __m128i m = _mm_set1_epi64x(0x0102040810204080);
    const __m128i e = _mm_cmpeq_epi8(_mm_and_si128(d, m), m);
    // Convert to ASCII by subtracting the masks from ASCII '0':
    // '0' - 0 is '0', '0' - -1 is '1'
    const __m128i result = _mm_sub_epi8(_mm_set1_epi8('0'), e);
    // Store the 16 characters to the un-aligned buffer
    _mm_storeu_si128(reinterpret_cast<__m128i*>(dstp), result);
#else
    cvtCDataToStr(dstp, value >> 8);
    cvtCDataToStr(dstp + 8, value);
#endif
}

inline void cvtIDataToStr(char* dstp, IData value) {
#ifdef VL_HAVE_AVX2
    // Similar to cvtSDataToStr but the bottom 16-bits are processed in the
    // top half of the YMM registers
    const __m256i a = _mm256_insert_epi32(_mm256_undefined_si256(), value, 0);
    const __m256i b = _mm256_permute4x64_epi64(a, 0);
    const __m256i s = _mm256_set_epi8(0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2,
                                      2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3);
    const __m256i c = _mm256_shuffle_epi8(b, s);
    const __m256i m = _mm256_set1_epi64x(0x0102040810204080);
    const __m256i d = _mm256_cmpeq_epi8(_mm256_and_si256(c, m), m);
    const __m256i result = _mm256_sub_epi8(_mm256_set1_epi8('0'), d);
    _mm256_storeu_si256(reinterpret_cast<__m256i*>(dstp), result);
#else
    cvtSDataToStr(dstp, value >> 16);
    cvtSDataToStr(dstp + 16, value);
#endif
}

inline void cvtQDataToStr(char* dstp, QData value) {
    cvtIDataToStr(dstp, value >> 32);
    cvtIDataToStr(dstp + 32, value);
}

#define cvtEDataToStr cvtIDataToStr

//=========================================================================
// VerilatedTraceBuffer

template <>
VerilatedTraceBuffer<VL_BUF_T>::VerilatedTraceBuffer(Trace& owner)
    : VL_BUF_T{owner}
    , m_sigs_oldvalp{owner.m_sigs_oldvalp}
    , m_sigs_enabledp{owner.m_sigs_enabledp} {}

// These functions must write the new value back into the old value store,
// and subsequently call the format-specific emit* implementations. Note
// that this file must be included in the format-specific implementation, so
// the emit* functions can be inlined for performance.

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullBit(uint32_t* oldp, CData newval) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    *oldp = newval;  // Still copy even if not tracing so chg doesn't call full
    if (VL_UNLIKELY(m_sigs_enabledp && !(VL_BITISSET_W(m_sigs_enabledp, code)))) return;
    emitBit(code, newval);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullEvent(uint32_t* oldp, const VlEventBase* newvalp) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    // No need to update *oldp
    if (newvalp->isTriggered()) emitEvent(code);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullEventTriggered(uint32_t* oldp) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    // No need to update *oldp
    emitEvent(code);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullCData(uint32_t* oldp, CData newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    *oldp = newval;  // Still copy even if not tracing so chg doesn't call full
    if (VL_UNLIKELY(m_sigs_enabledp && !(VL_BITISSET_W(m_sigs_enabledp, code)))) return;
    emitCData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullSData(uint32_t* oldp, SData newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    *oldp = newval;  // Still copy even if not tracing so chg doesn't call full
    if (VL_UNLIKELY(m_sigs_enabledp && !(VL_BITISSET_W(m_sigs_enabledp, code)))) return;
    emitSData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullIData(uint32_t* oldp, IData newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    *oldp = newval;  // Still copy even if not tracing so chg doesn't call full
    if (VL_UNLIKELY(m_sigs_enabledp && !(VL_BITISSET_W(m_sigs_enabledp, code)))) return;
    emitIData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullQData(uint32_t* oldp, QData newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    std::memcpy(oldp, &newval, sizeof(newval));
    if (VL_UNLIKELY(m_sigs_enabledp && !(VL_BITISSET_W(m_sigs_enabledp, code)))) return;
    emitQData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullWData(uint32_t* oldp, WDataInP newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    for (int i = 0; i < VL_WORDS_I(bits); ++i) oldp[i] = newval[i];
    if (VL_UNLIKELY(m_sigs_enabledp && !(VL_BITISSET_W(m_sigs_enabledp, code)))) return;
    emitWData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullDouble(uint32_t* oldp, double newval) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    std::memcpy(oldp, &newval, sizeof(newval));
    if (VL_UNLIKELY(m_sigs_enabledp && !(VL_BITISSET_W(m_sigs_enabledp, code)))) return;
    // cppcheck-suppress invalidPointerCast
    emitDouble(code, newval);
}

#endif  // VL_CPPCHECK

//=========================================================================
// RTMD based tracing: dumping

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpRtmdLeaf(Buffer* bufp, const RtmdLeaf& leaf,
                                                      bool full) VL_MT_UNSAFE {
    uint32_t* const oldp = bufp->oldp(leaf.m_code);
    const void* const datap = leaf.m_datap;
    const int bits = static_cast<int>(leaf.m_bits);
    switch (leaf.m_read) {
    case VlRtmdRead::BIT: {
        const CData val = *static_cast<const CData*>(datap);
        if (full) {
            bufp->fullBit(oldp, val);
        } else {
            bufp->chgBit(oldp, val);
        }
        break;
    }
    case VlRtmdRead::CDATA: {
        const CData val = *static_cast<const CData*>(datap);
        if (full) {
            bufp->fullCData(oldp, val, bits);
        } else {
            bufp->chgCData(oldp, val, bits);
        }
        break;
    }
    case VlRtmdRead::SDATA: {
        const SData val = *static_cast<const SData*>(datap);
        if (full) {
            bufp->fullSData(oldp, val, bits);
        } else {
            bufp->chgSData(oldp, val, bits);
        }
        break;
    }
    case VlRtmdRead::IDATA: {
        const IData val = *static_cast<const IData*>(datap);
        if (full) {
            bufp->fullIData(oldp, val, bits);
        } else {
            bufp->chgIData(oldp, val, bits);
        }
        break;
    }
    case VlRtmdRead::QDATA: {
        const QData val = *static_cast<const QData*>(datap);
        if (full) {
            bufp->fullQData(oldp, val, bits);
        } else {
            bufp->chgQData(oldp, val, bits);
        }
        break;
    }
    case VlRtmdRead::WDATA: {
        const WDataInP valp = WDataInP::external(static_cast<const EData*>(datap));
        if (full) {
            bufp->fullWData(oldp, valp, bits);
        } else {
            bufp->chgWData(oldp, valp, bits);
        }
        break;
    }
    case VlRtmdRead::DOUBLE: {
        const double val = *static_cast<const double*>(datap);
        if (full) {
            bufp->fullDouble(oldp, val);
        } else {
            bufp->chgDouble(oldp, val);
        }
        break;
    }
    case VlRtmdRead::EVENT: {
        const VlEventBase* const valp = static_cast<const VlEventBase*>(datap);
        if (full) {
            bufp->fullEvent(oldp, valp);
        } else {
            bufp->chgEvent(oldp, valp);
        }
        break;
    }
    }
}

template <>
bool VerilatedTrace<VL_SUB_T, VL_BUF_T>::rtmdGroupActive(const RtmdGroup& group) const
    VL_MT_UNSAFE {
    const VlRtmdTables& tables = *group.m_tablesp;
    // No activity information
    if (!tables.m_actSetsp || !tables.m_activityFlagsp) return true;
    const VlRtmdActSetRow& set = tables.m_actSetsp[group.m_actSetId];
    for (const uint32_t* flagp = set.m_firstFlagp; flagp != set.m_lastFlagp; ++flagp) {
        if (tables.m_activityFlagsp[*flagp]) return true;
    }
    return false;
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpDescriptors(Buffer* bufp, bool full) VL_MT_UNSAFE {
    for (const RtmdGroup& group : m_rtmdGroups) {
        if (!full && !rtmdGroupActive(group)) continue;
        const size_t end = group.m_first + group.m_count;
        for (size_t i = group.m_first; i < end; ++i) { dumpRtmdLeaf(bufp, m_rtmdLeaves[i], full); }
    }
    // Clear all activity flags
    for (const VlRtmdTables& tables : m_rtmdTables) {
        if (!tables.m_activityFlagsp) continue;
        uint8_t* const flagsp = const_cast<uint8_t*>(tables.m_activityFlagsp);
        std::fill(flagsp, flagsp + tables.m_nActivityFlags, 0);
    }
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpRtmdConsts(Buffer* bufp) VL_MT_UNSAFE {
    for (const RtmdLeaf& leaf : m_rtmdConstLeaves) { dumpRtmdLeaf(bufp, leaf, true); }
}
