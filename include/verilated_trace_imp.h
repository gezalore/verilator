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

#include "verilated.h"
#include "verilated_rtmd.h"
#ifndef VL_CPPCHECK
#if !defined(VL_SUB_T) || !defined(VL_BUF_T)
# error "This file should be included in trace format implementations"
#endif

#include "verilated_intrinsics.h"
#include "verilated_trace.h"
#include <algorithm>
#include <cstring>

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

//=========================================================================
// Hierarcy building

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addSignal(const char* namep,
                                                   const VlRtmdSignalType& sigType,
                                                   const VlRtmdDataType& dtype,
                                                   const VlRtmdActSet& actSet, const void* datap,
                                                   uint32_t lsb) VL_MT_UNSAFE {
    const uint32_t bits = dtype.width();

    // Aliases of the same value share the same code
    const auto pair = m_codes.emplace(std::make_tuple(datap, lsb, bits), m_nextCode);
    const uint32_t code = pair.first->second;

    // If the value is not already in the map, it is a new signal, allocate it
    if (pair.second) {
        // Need one code per word
        m_nextCode += VL_WORDS_I(bits);
        // Need to know max bits for buffer sizing
        m_maxBits = std::max(m_maxBits, bits);
        // Record the value to dump, with the others of the same activity set
        const StorageKind storage = dtype.storageKind();
        Group& group = m_groupMap[actSet][storage];
        group.m_storage = storage;
        // If a slice exactly fills its storage, which is aligned, then extraction is pointer math
        const auto sliceIsWhole = [bits, lsb]() {
            // A wide slice of whole words, starting on a word
            if (bits > VL_QUADSIZE) return (bits % VL_EDATASIZE == 0) && (lsb % VL_EDATASIZE == 0);
            // A narrow slice exactly filling its storage, starting on a byte. Loaded unaligned.
            const bool fills = bits == VL_BYTESIZE || bits == VL_SHORTSIZE || bits == VL_IDATASIZE
                               || bits == VL_QUADSIZE;
            return fills && lsb % VL_BYTESIZE == 0;
        };
        if (lsb == NOLSB) {
            group.m_wholes.push_back({datap, code, bits});
        } else if (sliceIsWhole()) {
            // Dumped as the whole value at the byte holding its lowest bit (little endian)
            const uint8_t* const bytep = static_cast<const uint8_t*>(datap) + lsb / VL_BYTESIZE;
            group.m_wholes.push_back({bytep, code, bits});
        } else {
            group.m_slices.push_back({datap, code, bits, lsb});
        }
    }

    self()->declareSignal(code, namep, sigType, dtype);
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::traceInit() VL_MT_UNSAFE {
    // Without VerilatedContext::trace, trace the context of the opening thread
    if (!m_contextp) m_contextp = Verilated::threadContextp();

    // Context needs to be set to calculate unused signals
    if (!m_contextp->calcUnusedSigs()) {
        VL_FATAL_MT("", 0, "",
                    "Turning on wave traces requires Verilated::traceEverOn(true) call before "
                    "time 0.");
    }

    // At least one model must be Verilated for tracing (though technically could still trace
    // whatever is available via the RTMD at this point, if present)
    bool anyTraced = false;
    for (const auto& pair : m_contextp->models()) {
        const VlRtmd* const rtmdp = pair.second->rtmd();
        anyTraced |= rtmdp && rtmdp->m_opt.m_trace;
    }
    if (!anyTraced) {
        VL_FATAL_MT("", 0, "",
                    "Testbench C call to 'VerilatedContext::trace()' requires model(s) "
                    "Verilated with --trace option");
    }

    // Note: It is possible to re-open a trace file (VCD in particular),
    // so we must reset the next code here, but it must have the same number
    // of codes on re-open
    const uint32_t expectedCodes = m_nextCode;
    m_nextCode = 1;
    m_maxBits = 0;

    m_groupVec.clear();
    m_activityFlags.clear();

    // Declare all enum types, in all models, before the signals that reference them
    for (const std::pair<const std::string, VerilatedModel*>& pair : m_contextp->models()) {
        const VlRtmd* const rtmdp = pair.second->rtmd();
        if (!rtmdp) continue;
        // Its activity flags are cleared after each dump
        if (rtmdp->m_activityFlagsp) {
            m_activityFlags.emplace_back(const_cast<CData*>(rtmdp->m_activityFlagsp),
                                         rtmdp->m_nActivityFlags);
        }
        for (uint32_t i = 0; !rtmdp->m_dataTypesTabp[i].isEnd(); ++i) {
            if (rtmdp->m_dataTypesTabp[i].enump()) self()->declareEnum(rtmdp->dataType(i));
        }
    }

    // Declare the hierarchy of all models, see the VlRtmdHierListener methods above
    walkContext(*m_contextp);
    m_codes.clear();

    // If reopen, check that the number of codes is the same as the previous dump
    if (expectedCodes && m_nextCode != expectedCodes) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "Reopening trace file with different number of signals");
    }

    // Keep the groups in the order of their activity sets, then how they are dumped
    for (auto& actSetPair : m_groupMap) {
        for (auto& storagePair : actSetPair.second) {
            m_groupVec.emplace_back(actSetPair.first, std::move(storagePair.second));
        }
    }
    m_groupMap.clear();

    // Dump the values of a group in address order, for better locality
    for (auto& group : m_groupVec) {
        std::vector<Whole>& wholes = group.second.m_wholes;
        std::sort(wholes.begin(), wholes.end(), [](const Whole& a, const Whole& b) {  //
            return a.m_datap < b.m_datap;
        });
        std::vector<Slice>& slices = group.second.m_slices;
        std::sort(slices.begin(), slices.end(), [](const Slice& a, const Slice& b) {
            if (a.m_datap != b.m_datap) return a.m_datap < b.m_datap;
            return a.m_lsb < b.m_lsb;
        });
    }

    // Room for extracting a wide slice, no wider than the widest signal
    m_wideSlice.resize(VL_WORDS_I(m_maxBits));

    // Now that we know the number of codes, allocate space for the buffer holding
    // previous signal values.
    if (!m_sigs_oldvalp) m_sigs_oldvalp = new uint32_t[m_nextCode];

    // Set callback so flush/abort will flush this file
    Verilated::addFlushCb(onFlush, this);
    Verilated::addExitCb(onExit, this);
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
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_unit(const char*) VL_MT_SAFE {}
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
    , m_sigs_oldvalp{owner.m_sigs_oldvalp} {}

// These functions must write the new value back into the old value store,
// and subsequently call the format-specific emit* implementations. Note
// that this file must be included in the format-specific implementation, so
// the emit* functions can be inlined for performance.

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullBit(uint32_t* oldp, CData newval) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    *oldp = newval;  // Still copy even if not tracing so chg doesn't call full
    emitBit(code, newval);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullEvent(uint32_t* oldp, const VlEventBase* newvalp) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    // No need to update *oldp
    if (newvalp->isTriggered()) emitEvent(code);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullCData(uint32_t* oldp, CData newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    *oldp = newval;  // Still copy even if not tracing so chg doesn't call full
    emitCData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullSData(uint32_t* oldp, SData newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    *oldp = newval;  // Still copy even if not tracing so chg doesn't call full
    emitSData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullIData(uint32_t* oldp, IData newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    *oldp = newval;  // Still copy even if not tracing so chg doesn't call full
    emitIData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullQData(uint32_t* oldp, QData newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    std::memcpy(oldp, &newval, sizeof(newval));
    emitQData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullWData(uint32_t* oldp, WDataInP newval, int bits) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    for (int i = 0; i < VL_WORDS_I(bits); ++i) oldp[i] = newval[i];
    emitWData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullDouble(uint32_t* oldp, double newval) {
    const uint32_t code = oldp - m_sigs_oldvalp;
    std::memcpy(oldp, &newval, sizeof(newval));
    // cppcheck-suppress invalidPointerCast
    emitDouble(code, newval);
}

#endif  // VL_CPPCHECK

//=========================================================================
// RTMD based tracing: dumping

template <>
template <bool T_Full>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpGroupDispatch(Buffer* bufp,
                                                           const Group& group) VL_MT_UNSAFE {
    // Dispatch on how the values are stored once for the whole group
    switch (group.m_storage) {
    case StorageKind::CDATA: dumpGroup<T_Full, StorageKind::CDATA>(bufp, group); break;
    case StorageKind::SDATA: dumpGroup<T_Full, StorageKind::SDATA>(bufp, group); break;
    case StorageKind::IDATA: dumpGroup<T_Full, StorageKind::IDATA>(bufp, group); break;
    case StorageKind::QDATA: dumpGroup<T_Full, StorageKind::QDATA>(bufp, group); break;
    case StorageKind::WDATA: dumpGroup<T_Full, StorageKind::WDATA>(bufp, group); break;
    case StorageKind::DOUBLE: dumpGroup<T_Full, StorageKind::DOUBLE>(bufp, group); break;
    case StorageKind::EVENT: dumpGroup<T_Full, StorageKind::EVENT>(bufp, group); break;
    }
}

template <>
template <bool T_Full, VlRtmdDataType::StorageKind T_Storage>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpGroup(Buffer* bufp, const Group& group) VL_MT_UNSAFE {
    // The whole values
    for (const Whole& whole : group.m_wholes) {
        dumpValue<T_Full, T_Storage>(bufp, whole.m_code, whole.m_datap,
                                     static_cast<int>(whole.m_bits));
    }

    // The slices of packed values
    for (const Slice& slice : group.m_slices) {
        // A slice is extracted into a temporary. A narrow one is read back as a value of its
        // width, which is little endian, so the low bytes of the widest. Loads start at the byte
        // holding the lowest bit, unaligned, and might read past the end of the packed value,
        // which is stored little endian.
        const uint8_t* const bytep
            = static_cast<const uint8_t*>(slice.m_datap) + slice.m_lsb / VL_BYTESIZE;
        const uint32_t shift = slice.m_lsb % VL_BYTESIZE;
        if VL_CONSTEXPR_CXX17 (T_Storage == StorageKind::WDATA) {
            // Each word is loaded as a quadword, covering it after the shift
            EData* const wordsp = m_wideSlice.data();
            const int words = VL_WORDS_I(slice.m_bits);
            for (int i = 0; i < words; ++i) {
                QData value;
                std::memcpy(&value, bytep + i * sizeof(EData), sizeof(value));
                wordsp[i] = static_cast<EData>(value >> shift);
            }
            // Clear the bits above the slice
            if (VL_BITBIT_E(slice.m_bits)) wordsp[words - 1] &= VL_MASK_E(slice.m_bits);
            dumpValue<T_Full, T_Storage>(bufp, slice.m_code, wordsp,
                                         static_cast<int>(slice.m_bits));
        } else {
            // Load two quadwords, and shift the slice down. The shift of 'hi' is split, so a
            // shift of 0 does not shift it by 64.
            QData lo;
            QData hi;
            std::memcpy(&lo, bytep, sizeof(lo));
            std::memcpy(&hi, bytep + sizeof(lo), sizeof(hi));
            QData value = (lo >> shift) | ((hi << 1) << (VL_QUADSIZE - 1 - shift));
            value &= VL_MASK_Q(slice.m_bits);
            dumpValue<T_Full, T_Storage>(bufp, slice.m_code, &value,
                                         static_cast<int>(slice.m_bits));
        }
    }
}

template <>
template <bool T_Full, VlRtmdDataType::StorageKind T_Storage>
VL_ATTR_ALWINLINE void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpValue(Buffer* bufp, uint32_t code,
                                                                     const void* datap,
                                                                     int bits) VL_MT_UNSAFE {
    uint32_t* const oldp = bufp->oldp(code);
    switch (T_Storage) {
    case StorageKind::CDATA: {
        const CData val = *static_cast<const CData*>(datap);
        // Single bits are dumped as scalars
        if (bits == 1) {
            if VL_CONSTEXPR_CXX17 (T_Full) {
                bufp->fullBit(oldp, val);
            } else {
                bufp->chgBit(oldp, val);
            }
        } else {
            if VL_CONSTEXPR_CXX17 (T_Full) {
                bufp->fullCData(oldp, val, bits);
            } else {
                bufp->chgCData(oldp, val, bits);
            }
        }
        break;
    }
    case StorageKind::SDATA: {
        SData val;
        std::memcpy(&val, datap, sizeof(val));  // Might be unaligned, see addSignal
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullSData(oldp, val, bits);
        } else {
            bufp->chgSData(oldp, val, bits);
        }
        break;
    }
    case StorageKind::IDATA: {
        IData val;
        std::memcpy(&val, datap, sizeof(val));  // Might be unaligned, see addSignal
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullIData(oldp, val, bits);
        } else {
            bufp->chgIData(oldp, val, bits);
        }
        break;
    }
    case StorageKind::QDATA: {
        QData val;
        std::memcpy(&val, datap, sizeof(val));  // Might be unaligned, see addSignal
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullQData(oldp, val, bits);
        } else {
            bufp->chgQData(oldp, val, bits);
        }
        break;
    }
    case StorageKind::WDATA: {
        const WDataInP valp = WDataInP::external(static_cast<const EData*>(datap));
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullWData(oldp, valp, bits);
        } else {
            bufp->chgWData(oldp, valp, bits);
        }
        break;
    }
    case StorageKind::DOUBLE: {
        const double val = *static_cast<const double*>(datap);
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullDouble(oldp, val);
        } else {
            bufp->chgDouble(oldp, val);
        }
        break;
    }
    case StorageKind::EVENT: {
        const VlEventBase* const valp = static_cast<const VlEventBase*>(datap);
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullEvent(oldp, valp);
        } else {
            bufp->chgEvent(oldp, valp);
        }
        break;
    }
    }
}

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

    // Dump the described models
    Buffer* const bufp = getTraceBuffer();
    if (VL_UNLIKELY(m_fullDump)) {
        m_fullDump = false;
        // Dump all values
        for (const auto& group : m_groupVec) { dumpGroupDispatch<true>(bufp, group.second); }
    } else {
        // Dump the changed values, skipping those that have not changed since the last dump.
        // The groups of an activity set are adjacent, so check each set only once.
        const VlRtmdActSet* lastActSetp = nullptr;
        bool active = false;
        for (const auto& group : m_groupVec) {
            const VlRtmdActSet& actSet = group.first;
            if (!lastActSetp || !(actSet == *lastActSetp)) {
                lastActSetp = &actSet;
                active = actSet.active();
            }
            if (!active) continue;
            dumpGroupDispatch<false>(bufp, group.second);
        }
    }
    commitTraceBuffer(bufp);

    // Clear all activity flags
    for (const std::pair<CData*, uint32_t>& flags : m_activityFlags) {
        std::fill(flags.first, flags.first + flags.second, 0);
    }
}
