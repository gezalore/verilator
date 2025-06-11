// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// - Ensures intermediate values (other than simple memory references or
//   constants) with multiple uses are assigned to variables
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"

VL_DEFINE_DEBUG_FUNCTIONS;

std::string V3DfgRegularizeContext::tmpNamePrefix(const DfgGraph& dfg) {
    // cppcheck-suppress unreadVariable  // cppcheck bug
    V3Hash hash{dfg.modulep()->name()};
    hash += m_label;
    std::string name = hash.toString();
    const uint32_t sequenceNumber = m_multiplicity[name]++;
    name += '_' + std::to_string(sequenceNumber);
    return name;
}

class DfgRegularize final {
    // Minimum width of concat trees that should be split up if possible.
    // Note we don't need to go too small, V3FuncOpt will further split them.
    // The goal here is to ensure we do not have *too* big single assignments
    // fed into scheduling, so we can do function splitting if necessary. This
    // avoids thing like
    //    'assign <32k-bit-wide-signal> = { ... 32k 1-bit signals ... };'
    // which can happen and would otherwise be impossible to split, and would
    // blow up C++ compilation time/memory use in GCC.
    static constexpr uint32_t WIDE_CONCAT_LIMIT = 4 * VL_QUADSIZE;

    // Used to keep track of drivers during concat splitting
    struct Driver final {
        FileLine* m_flp;
        DfgVertex* m_vtxp;
        uint32_t m_lsb;
        Driver() = default;
        Driver(FileLine* flp, uint32_t lsb, DfgVertex* vtxp)
            : m_flp{flp}
            , m_vtxp{vtxp}
            , m_lsb{lsb} {}
    };

    // Used to keep track of concatentation terms during concat splitting
    struct Term final {
        DfgVertex* m_vtxp = nullptr;
        size_t m_offset = 0;
        Term() = default;
        Term(DfgVertex* vtxp, size_t offset)
            : m_vtxp{vtxp}
            , m_offset{offset} {}
    };

    DfgGraph& m_dfg;  // The graph being processed
    V3DfgRegularizeContext& m_ctx;  // The optimization context for stats

    // Prefix of temporary variable names
    const std::string m_tmpNamePrefix = "__VdfgRegularize_" + m_ctx.tmpNamePrefix(m_dfg) + '_';
    size_t m_nTmps = 0;  // Number of temporaries added to this graph - for variable names only

    // Return canonical variable that can be used to hold the value of this vertex
    DfgVarPacked* getCanonicalVariable(DfgVertex& vtx) {
        // First gather all existing variables fully written by this vertex. Ignore SystemC
        // variables, those cannot act as canonical variables, as they cannot participate in
        // expressions or be assigned rvalues.
        std::vector<DfgVarPacked*> varVtxps;
        vtx.forEachSink([&](DfgVertex& sink) {
            if (DfgVarPacked* const varVtxp = sink.cast<DfgVarPacked>()) {
                if (varVtxp->isDrivenFullyByDfg() && !varVtxp->varp()->isSc()) {
                    varVtxps.push_back(varVtxp);
                }
            }
        });

        if (!varVtxps.empty()) {
            // There is at least one usable, existing variable. Pick the first one in source
            // order for deterministic results.
            std::stable_sort(varVtxps.begin(), varVtxps.end(),
                             [](const DfgVarPacked* ap, const DfgVarPacked* bp) {
                                 // Prefer those variables that must be kept anyway
                                 const bool keepA = ap->keep() || ap->hasDfgRefs();
                                 const bool keepB = bp->keep() || bp->hasDfgRefs();
                                 if (keepA != keepB) return keepA;
                                 // Prefer those that already have module references, so we don't
                                 // have to support recursive substitutions.
                                 if (ap->hasModRefs() != bp->hasModRefs()) return ap->hasModRefs();
                                 // Otherwise source order
                                 const FileLine& aFl = *(ap->fileline());
                                 const FileLine& bFl = *(bp->fileline());
                                 if (const int cmp = aFl.operatorCompare(bFl)) return cmp < 0;
                                 // Fall back on names if all else fails
                                 return ap->varp()->name() < bp->varp()->name();
                             });
            return varVtxps.front();
        }

        // We need to introduce a temporary
        ++m_ctx.m_temporariesIntroduced;

        // Add temporary AstVar to containing module
        FileLine* const flp = vtx.fileline();
        const std::string name = m_tmpNamePrefix + std::to_string(m_nTmps++);
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, vtx.dtypep()};
        m_dfg.modulep()->addStmtsp(varp);

        // Create and return a variable vertex for the temporary
        return new DfgVarPacked{m_dfg, varp};
    }

    // Gather concat terms right-to-left, delete the actual concat nodes, returns end offset
    uint32_t deconstructConcat(DfgVertex* vtxp, std::vector<Term>& terms, uint32_t offset) {
        if (DfgConcat* const catp = vtxp->cast<DfgConcat>()) {
            // Recursive case: gather sub terms
            offset = deconstructConcat(catp->rhsp(), terms, offset);
            offset = deconstructConcat(catp->lhsp(), terms, offset);
            VL_DO_DANGLING(catp->unlinkDelete(m_dfg), catp);
            return offset;
        }
        // Base case: different operation
        terms.emplace_back(vtxp, offset);
        return offset + vtxp->width();
    }

    // Split the given wide concatenation driver into multiple drivers
    void splitDriver(std::vector<Driver>& drivers, FileLine* flp, uint32_t lsb, DfgConcat& root) {
        // Gather all terms in the whole concat tree
        std::vector<Term> terms;
        uint32_t offset = lsb;
        offset = deconstructConcat(root.rhsp(), terms, offset);
        offset = deconstructConcat(root.lhsp(), terms, offset);
        // Sentinel value, m_vtxp is never dereferenced
        terms.emplace_back(nullptr, offset);

        // Build right leaning concat tree from terms between [begin, end), add it as driver
        const auto makeDriver = [&](const size_t begin, const size_t end) {
            UASSERT(end > begin, "Invalid range");
            DfgVertex* driverp = terms[begin].m_vtxp;
            for (size_t i = begin + 1; i < end; ++i) {
                DfgVertex* const vtxp = terms[i].m_vtxp;
                const uint32_t width = vtxp->width() + driverp->width();
                DfgConcat* const catp = new DfgConcat{m_dfg, flp, DfgVertex::dtypeForWidth(width)};
                catp->lhsp(vtxp);
                catp->rhsp(driverp);
                driverp = catp;
            }
            UASSERT_OBJ(end == begin + 1 || driverp->width() <= WIDE_CONCAT_LIMIT, driverp,
                        "Split term exceeds WIDE_CONCAT_LIMIT");
            drivers.emplace_back(flp, terms[begin].m_offset, driverp);
            lsb += driverp->width();
            ++m_ctx.m_splitConcats;
        };

        // Emit ranges not wider than WIDE_CONCAT_LIMIT (unless single term).
        // Attempt to split at VL_EDATASIZE boundaries to simplify later packing.
        size_t begin = 0;  // Range start index, inclusive
        size_t end = 0;  // Range end index, exclusive
        size_t boundary = 0;  // End index of last boundary since 'begin', or 0 if there isn't one
        while (++end < terms.size()) {
            // If this range still fits
            if (terms[end].m_offset - terms[begin].m_offset <= WIDE_CONCAT_LIMIT) {
                // Remember boundary
                if (terms[end].m_offset % VL_EDATASIZE == 0) boundary = end;
                // Move on
                continue;
            }

            // Current range doesn't fit. There are a couple of cases:
            if (end == begin + 1) {
                // 1. The range is a single element: We can't do much, just emit it below
            } else if (boundary) {
                // 2. There was a boundary earlier that still fits. Break there.
                end = boundary;
            } else {
                // 3. No boundary, but a one-smaller range fits. Break there.
                --end;
            }

            makeDriver(begin, end);
            begin = end;
            boundary = 0;
        }

        // Final chunk
        const size_t lastEnd = terms.size() - 1;
        if (begin < lastEnd) makeDriver(begin, lastEnd);
    }

    // Insert intermediate variables for vertices with multiple sinks (or use an existing one)
    DfgRegularize(DfgGraph& dfg, V3DfgRegularizeContext& ctx, bool lastRun)
        : m_dfg{dfg}
        , m_ctx{ctx} {

        // Ensure intermediate values are written to variables
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            const bool needsIntermediateVariable = [&]() {
                // Anything that drives an SC variable needs an intermediate,
                // as we can only assign simple variables to SC variables at runtime.
                const bool hasScSink = vtx.findSink<DfgVertexVar>([](const DfgVertexVar& var) {  //
                    return var.varp()->isSc();
                });
                if (hasScSink) return true;
                // Array selects need no variables, they are just memory references
                if (vtx.is<DfgArraySel>()) return false;
                // Operations with multiple sinks need an intermediate variables
                if (vtx.hasMultipleSinks()) return true;
                // Wide concatenation roots need an intermediate variable to enable splitting
                if (lastRun  // Only on last run
                    && vtx.is<DfgConcat>()  // Is a concat
                    && !vtx.singleSink().is<DfgConcat>()  // Is a root of a concat tree
                    && vtx.width() > WIDE_CONCAT_LIMIT)  // Is wider than limit
                    return true;
                // Otherwise needs no variable
                return false;
            }();

            if (!needsIntermediateVariable) continue;

            // This is an op which has multiple sinks. Ensure it is assigned to a variable.
            DfgVarPacked* const varp = getCanonicalVariable(vtx);
            if (varp->arity()) {
                // Existing variable
                FileLine* const flp = varp->driverFileLine(0);
                varp->sourceEdge(0)->unlinkSource();
                varp->resetSources();
                vtx.replaceWith(varp);
                varp->addDriver(flp, 0, &vtx);
            } else {
                // Temporary variable
                vtx.replaceWith(varp);
                varp->addDriver(vtx.fileline(), 0, &vtx);
            }
        }

        // Only split concats on last run, otherwise the next run would just coalesce them again
        if (!lastRun) return;

        // Now that variables have been inserted, split wide concatenations
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            DfgVarPacked* const varp = vtx.cast<DfgVarPacked>();
            if (!varp) continue;

            // Keep track of driving terms
            std::vector<Driver> drivers;

            // Gather and unlink all drivers, split wide concatentation drivers
            varp->forEachSourceEdge([this, varp, &drivers](DfgEdge& edge, size_t idx) {
                FileLine* const flp = varp->driverFileLine(idx);
                const uint32_t lsb = varp->driverLsb(idx);
                DfgVertex* const srcp = edge.sourcep();
                edge.unlinkSource();

                if (srcp->is<DfgConcat>() && srcp->width() > WIDE_CONCAT_LIMIT) {
                    // Driver is a wide concat, split it into multiple drivers
                    splitDriver(drivers, flp, lsb, *srcp->as<DfgConcat>());
                    VL_DO_DANGLING(srcp->unlinkDelete(m_dfg), srcp);
                } else {
                    // Driver is not a wide concat, just add it back
                    drivers.emplace_back(flp, lsb, srcp);
                }
            });

            // Link back the drivers, some of which might have been split into multiple drivers
            varp->resetSources();
            for (const Driver& driver : drivers) {
                varp->addDriver(driver.m_flp, driver.m_lsb, driver.m_vtxp);
            }
        }
    }

public:
    static void apply(DfgGraph& dfg, V3DfgRegularizeContext& ctx, bool lastRun) {
        DfgRegularize{dfg, ctx, lastRun};
    }
};

void V3DfgPasses::regularize(DfgGraph& dfg, V3DfgRegularizeContext& ctx, bool lastRun) {
    DfgRegularize::apply(dfg, ctx, lastRun);
}
