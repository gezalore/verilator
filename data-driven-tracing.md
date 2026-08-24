# Data-driven tracing — design document

Status: proposal / not implemented. All code references are against `master` at `ee8e2c0e1`.

Related issues: [#2259](https://github.com/verilator/verilator/issues/2259) (original data-driven
suggestion, icache measurements), [#6706](https://github.com/verilator/verilator/issues/6706)
(generated C++ size explosion), [#7001](https://github.com/verilator/verilator/issues/7001)
(V3TraceDecl placement / lost hierarchy information),
[#5813](https://github.com/verilator/verilator/issues/5813) (`traceClassBase` deprecated, multiple
trace formats), [#6707](https://github.com/verilator/verilator/issues/6707) (per-dtype trace
function dedup, landed as `7f571971c`).

---

## 1. Motivation

Tracing today generates C++ functions: `trace_init_top` / `trace_init_sub__*` /
`trace_init_dtype__*` for declarations, and `trace_const_*` / `trace_full_*` / `trace_chg_*` for
dumping. On large designs this is more than half of all generated code, and it has three distinct
costs:

1. **Object code size and link scaling.** Reported in #6706, up to and including
   `-mcmodel=large`-class linker relocation problems.
2. **Instruction cache.** Measured in #2259: 60 icache misses per thousand instructions and 64%
   frontend stall on a tracing SweRV run. Every byte of the dump code is touched exactly once per
   dump, so essentially every fetch is a miss. This is the dominant runtime cost, not the value
   comparisons or the formatting.
3. **Verilation time and memory.** Trace decls are built per scope and, with `--trace-structs`,
   materialise a `Sel`/`ArraySel`/`StructSel` tree plus an `AstTraceDecl` per struct member per
   instance, plus an `AstTraceInc` clone per signal per dump kind.

The incremental fixes have largely been played out: `60fe2c873` and `1af7fa92c` shrank declaration
object code (the latter added the `VL_TRACE_DECL_*` macro layer that discards unused arguments at
compile time), and `7f571971c` deduplicated per-dtype trace functions. The next structural step is
to stop generating code and generate data.

Two levels of sharing are available, and this design uses both:

- **Per data type.** One descriptor per unique data type, referenced by every signal of that type.
  A 100-member packed struct used by 1000 signals is one descriptor with 100 member entries plus
  1000 signal entries, not 100 000 leaf declarations. This is the largest single win and it
  generalises #6707 from "top-level aggregates get a shared function" to "every unique type,
  recursively, gets one shared descriptor".
- **Per module.** Instances whose descriptors end up identical after optimisation share one emitted
  table.

### Secondary wins

- The trace **format is currently fixed at verilate time** (`traceClassBase()`, itself deprecated
  pending #5813). A format-agnostic descriptor is a prerequisite for choosing VCD/FST/SAIF at
  runtime, and for tracing one model into several formats.
- Building descriptors before `V3Begin`/`V3Inline`/`V3Task`/`V3Scope` recovers the source-level
  information #7001 is about: real module type names, begin/generate block identity, function/task
  scopes for statics, and therefore precise FST scope types.
- The dump hierarchy becomes **structurally** independent of inlining, rather than reconstructed
  from `__DOT__`-joined names and repaired when it diverges (`a031dd1a2`).

---

## 2. Scope

### In scope for v1

- A parallel implementation, selected by a new option, coexisting with the current code-generating
  path so both can be run on the same design and their dumps compared.
- All three formats (VCD, FST, SAIF), C++ and SystemC.
- Every traced value is a plain address in model state, or a compile-time constant.

### Deferred

- **Arbitrary traced expressions.** v1 keeps every traced signal as real model state by pinning it
  (§8). Later ("option 2") the values that only tracing needs move into a trace-only prologue
  function writing a `__VtraceTmp` struct, so they are computed only when dumping. The cost of not
  having this yet is measurable and should be measured (§12).
- Threaded/offloaded tracing (#2259). A contiguous entry range is a natural work unit for a
  consumer thread, and the design should not preclude it, but it is not part of this work.
- Runtime format selection. Enabled by this design, not delivered by it.
- Letting `V3SplitVar` split traced variables (§8, item 4).

### Explicitly not reused, and not added

The existing tracing nodes — `AstTraceDecl`, `AstTraceInc`, `AstTracePushPrefix`,
`AstTracePopPrefix` — and the `V3TraceDecl` / `V3Trace` code generators are left untouched for the
legacy path and **deleted** when this supersedes it (§13, Stage 7). The new work shares no
representation with them.

Ten new AST nodes are added: `AstRtmdType` and `AstRtmdScope` under a common
`AstNodeRtmd` base, and six entry kinds under `AstNodeRtmdItem` (see §4). No `Ast*DType` node is added: that suffix denotes an actual data
type by convention, and a descriptor is not a data type — it *describes* one. No new container node
is added either; type descriptors live in the existing `AstTypeTable`.

---

## 3. Architecture

Three representations, in order:

```
   AST                                   generated tables (.rodata)      runtime table
   ───                                   ──────────────────────────      ─────────────
   AstRtmdScope per scope     →     entry rows, relative      →     flat entries,
     entries reference                    offsets, dtype indices          absolute pointers,
   AstRtmdType per data type        + one shared type              expanded per leaf
     (uniqued, in AstTypeTable)           descriptor table
```

**Rtmds** are a compact *description*: fixed-size POD rows once emitted, no relocations,
offsets relative to the enclosing scope object, hierarchy expressed by instance entries, and
aggregate structure expressed by a reference into the shared data type descriptors.

**The runtime table** is built once at trace-open time by walking the emitted descriptors, expanding
instance entries per instance and data type descriptors per leaf, allocating codes, partitioning by
thread, and resolving each entry to an absolute data pointer. The hot loop walks only this.

This split is what makes the hot path cheap: the generated description can be as indirect and shared
as it likes, because nothing walks it during simulation.

### Hot path

The dump loop iterates activity groups; each group is one flag test followed by a contiguous run of
self-contained entries:

```c
for (const VlTraceGroup& g : groups) {
    if (!g.always && !anyActive(g)) continue;
    for (const VlTraceEntry* e = g.begin; e != g.end; ++e) {
        // op-tagged switch; datap already absolute
    }
}
```

Compared with today's generated code this is *fewer* operations per signal, not more: no `vlSymsp`
indirection (the pointer is pre-resolved), and the per-signal specialisation that generated code
provides is exactly reproduced by the op tag.

The one thing that could have been lost — compile-time-constant widths — turns out not to be a
factor. `VerilatedVcdBuffer::emitCData/emitSData/emitIData/emitQData`
(`include/verilated_vcd_c.cpp:639-668`) already take `bits` as a runtime `int`; it only affects a
shift and the write-pointer advance, because `cvtCDataToStr` and friends always convert a full
8/16/32/64 characters. FST ignores `bits` entirely
(`VerilatedFstBuffer::emitIData(uint32_t, IData, int)`). So the only compile-time specialisation in
today's codegen is *which* `chg*`/`emit*` variant is called, and that is what the op tag encodes.

### Three things only the runtime table makes possible

- **`$dumpvars` filtering moves to table-build time.** Disabled signals are simply not
  materialised, instead of every `full*` testing `m_sigs_enabledp`
  (`include/verilated_trace_imp.h:550-619`). Partial dumps get strictly faster rather than paying
  full sweep cost.
- **Activity groups become contiguous ranges** — one test, then a linear, prefetchable stream. The
  always-active group needs no test at all, replacing today's per-group
  `if (activity[a] || activity[b])`.
- **Aggregates and arrays stop being unrolled at compile time.** `EmitCTrace::visit(AstTraceInc*)`
  (`src/V3EmitCImp.cpp:870-879`) unrolls `arrayRange().elements()` iterations "because it traces
  faster", and `V3TraceDecl` unrolls every struct member and array element into its own decl; that
  is why `t_trace_huge_array` needs `--output-split-ctrace 10` and still emits ten-plus files. With
  data type descriptors the unrolling happens once, at init, in the runtime.

### Memory cost

An entry is roughly 16 bytes, on top of the existing 4 bytes per code in `m_sigs_oldvalp`. On a
design with millions of trace codes that is hundreds of megabytes of runtime table. This is the one
axis where the design is clearly worse than generated code — note that the compile-time sharing
(per type, per module) does *not* reduce it, because the runtime table is fully expanded.
Mitigations: keep `code` rather than a second resolved `oldp` pointer; never materialise
filtered-out signals. **Measure this early.**

---

## 4. AST representation

Two abstract bases and six concrete nodes. Splitting them means each node carries exactly the fields
its role needs, rather than one node carrying the union of all of them, and the `broken()` checks
become type-based rather than kind-based.

```
AstNodeRtmd                 base of the two descriptors
  AstRtmdType               describes a data type; held by AstTypeTable
  AstRtmdScope              describes a design scope; held by the module or scope
AstNodeRtmdItem            base of the six entry kinds; no data of its own
  AstRtmdMember        member of a described data type
  AstRtmdSignal        traced signal under a described scope
  AstRtmdInstance      sub-instance under a described scope
  AstRtmdPartition     separately verilated partition under a described scope
  AstRtmdPush          opens a naming level within the described scope
  AstRtmdPop           closes it
```

`AstNodeRtmd` holds no data of its own; it exists so passes and future code can handle "a
descriptor" without caring which kind, and so the two share one place to document the contract.

`AstRtmdType` describes a data type. It is held by the existing `AstTypeTable`, which gains
`op2 := rtmdTypesp : List[AstRtmdType]`, so one descriptor is shared by every signal of that
type however many instances use it. `dtypep()` is the described type and is required.

```cpp
class AstRtmdType final : public AstNode {
    // @astgen op1 := membersp : List[AstRtmdMember]  // Members, in declared order
    //
    // @astgen ptr := m_subp : Optional[AstRtmdType]  // Element type of an array type
    uint32_t m_stride = 0;      // Array element stride; bits if packed, else bytes
};
```

It takes one of three shapes: a **leaf** has neither members nor `subp`, and its width and signal
type are read from `dtypep()`; an **array** has `subp` and `stride`, with the range read from
`dtypep()`; a **struct or union** lists its members, with packedness read from `dtypep()`.

`AstRtmdScope` describes a design scope. It is held by the `AstNodeModule` it describes,
cloned into each `AstScope` by `V3Scope`, and moved back to the module by `V3Descope`.

```cpp
class AstRtmdScope final : public AstNode {
    // @astgen op1 := entriesp : List[AstNodeRtmdItem]  // Items found, in trace order
    const VRtmdScopeKind m_kind;
    string m_name;
};
```

The six entry kinds share an abstract base, `AstNodeRtmdItem`, which like
`AstNodeRtmd` holds no data -- it exists to be the element type of the scope's entry list:

| Node | Holds | Listed by |
|---|---|---|
| `AstRtmdMember` | name, `m_offset`, `ptr m_typeDescp` (required) | `AstRtmdTypeAtom` | `m_enumName`, `m_keyword`, `m_bits`, `m_left`, `m_right`, `m_signed`, `m_ranged`, `op1 enumItemsp` | `TYPETABLE` |
| `AstRtmdTypePackedArray` | `op1 valuep`, `ptr m_elemp`, `m_elemBits`, `m_left`, `m_right` | `TYPETABLE` |
| `AstRtmdTypeUnpackedArray` | `ptr m_elemp`, `m_elemBytes`, `m_left`, `m_right` | `TYPETABLE` |
| `AstRtmdTypePackedStruct` / `AstRtmdTypePackedUnion` | `op1 valuep`, `op2 membersp` | `TYPETABLE` |
| `AstRtmdTypeUnpackedStruct` | `op1 membersp` | `TYPETABLE` |
| `AstRtmdSignal` | name, `ptr m_typeDescp` (required), `op1 valuep`, `m_valueId`, `ptr m_actSetp`, direction, var type | `AstRtmdScope` |
| `AstRtmdInstance` | name, `ptr m_cellp`, `ptr m_scopeDescp` | `AstRtmdScope` |
| `AstRtmdPartition` | name | `AstRtmdScope` |
| `AstRtmdPush` | name, `VRtmdScopeKind` | `AstRtmdScope` |
| `AstRtmdPop` | nothing | `AstRtmdScope` |

Only `AstRtmdMember` stores an offset, because only a packed member's bit offset is a
number Verilator has to compute and keep. A signal's offset is `offsetof(ScopeClass, member)`
recovered from its `AstVarRef` at emit, an instance's base likewise from its cell, and an unpacked
member's offset comes from the C++ layout -- so storing an offset on those would be storing
something already derivable. Names, by contrast, must be captured here rather than re-derived at
emit: `V3Begin` and `V3Inline` rename variables and cells downstream, and the trace name is the one
from before those passes ran.

Because the two descriptors are distinct node types, every reference is precisely typed: a member
and a signal point at an `AstRtmdType`, an instance points at an `AstRtmdScope`, and the
type table holds only type descriptors. No node needs a kind field to say which it is.

`VRtmdScopeKind` goes in `V3AstAttr.h` alongside the other `V*` attribute enums, and holds
`MODULE`, `INTERFACE`, `GENERATE`, `BLOCK`, `FUNCTION`, `TASK`. These must map onto the runtime's
`VerilatedTracePrefixType` (`include/verilated_trace.h:50-60`), which needs the
generate/block/function/task values added -- that addition *is* the #7001 win.

Nesting comes in two forms, because the two things being nested are different. A sub-instance is a
reference: `AstRtmdInstance` points at *another* module's `AstRtmdScope`, which is
what allows one descriptor per module rather than per instance. A naming level *within* one module --
a generate or begin block, or a function or task whose statics are traced -- has no separate
descriptor to point at, so it is bracketed inline by an `AstRtmdPush` and a matching
`AstRtmdPop`.

The push/pop form is deliberate rather than a leftover from `AstTracePushPrefix`: it maps 1:1 onto
the emitted row stream, so emission is a flat walk and `V3Inline` splicing an inlined child is a list
splice between a push and a pop rather than construction of a wrapper node. The cost is that
unbalanced pairs are representable, so balance is an invariant `V3Rtmd` must maintain and check
rather than one the node types enforce.

Note no `Ast*DType` node is introduced: that suffix denotes an actual data type by convention, and a
descriptor is not a data type -- it *describes* one.

### Offset units: the packed root boundary

`m_offset` and `m_stride` change unit at one well-defined boundary. A packed type can only ever
contain packed types, so any descriptor tree is *unpacked levels on the outside, packed levels on
the inside*, with exactly one crossing. Call the outermost packed object the **packed root**: it is a
single contiguous storage object (a `CData`/`SData`/`IData`/`QData` scalar, or a `VlWide` word array)
at a known byte offset.

- Above the packed root — unpacked arrays, unpacked structs, and the signal itself — offsets and
  strides are **bytes**, taken from C++ layout (`offsetof` / `sizeof`).
- At and below the packed root — packed structs, packed unions, packed arrays — offsets and strides
  are **bits** within that root, computed by Verilator, and they accumulate across nesting levels.
  This is what `V3TraceDecl` computes today, e.g. `declPackedArray`'s
  `const int lsb = (i - nodep->lo()) * subtypep->width();` and `AstMemberDType::lsb()`.

So the expansion state carried by the runtime is
`(byte offset of the packed root, bit offset within it, packed root width)`. All three are
type-relative, so this does not affect descriptor sharing.

Note also that a leaf has **two** distinct bit ranges that must not be conflated: its *declared*
range (msb/lsb from its own data type, which is what `declBus(code, name, msb, lsb)` reports) and
its *storage* bit offset within the packed root (which drives extraction). Today these are
`AstTraceDecl::bitRange()` and the `AstSel` lsb respectively.

### Rtmds are policy-free

Rtmds describe the type completely and make **no** tracing decisions. In particular they do
not apply `--trace-structs`, `--trace-max-width` or `--trace-max-array`, and they do not decide
whether a packed aggregate is dumped per member or as one flat bus. All of that is emitted in full
and decided by the runtime (§7.2).

This falls out of the representation rather than needing extra data: a packed root descriptor already
carries both views. Its `dtypep()` gives the total width, so "dump the whole thing as one bus" is
just treating the root as a leaf; its `entriesp` gives the members, so "dump per member" is
expanding them. An array descriptor already carries `elements`, so a size limit is a runtime
comparison. Nothing is added to support either choice — the earlier draft of this document had the
descriptor store the *outcome* of these decisions, which was strictly less information for the same
bytes.

Three consequences:

- **Rtmds are option-independent**, so a descriptor is valid for any trace configuration.
  Sharing improves, and the descriptor's identity depends only on the data type, which is what makes
  "identical type ⇒ identical descriptor" hold unconditionally.
- **`--trace-structs`, `--trace-max-width` and `--trace-max-array` stop requiring re-verilation.**
  They become runtime policy with the command-line values passed through as defaults, in the same
  way `$dumpvars` filtering is already a runtime concern.
- **The `--trace-max-array` default of 32 largely loses its purpose.** That limit exists because
  today an array is *unrolled into generated code*, so a large one explodes the C++. A descriptor
  represents an array in constant space regardless of element count, and the runtime skips it before
  materialising any entries, so nothing explodes at any layer. Whether to keep the default is a
  separate user-facing decision, but the technical reason for it is gone.

So what the descriptor stores is only what cannot be read back from `dtypep()`: the **C++ layout
constants** (`m_offset` / `m_stride` for unpacked aggregates and arrays of aggregates, where the
layout belongs to the C++ compiler rather than to Verilator) and the trace code count. Widths,
msb/lsb, signal types, array ranges, member names and packed member offsets are all read from the
data type at emit time.

Genuinely untraceable constructs are a separate matter from policy. Strings have no fixed-width
representation and are ignored today ("Unsupported: strings"), as are unpacked unions; these should
be emitted as an explicitly-marked unsupported entry rather than silently omitted, so the runtime
knows something was skipped and a future format can support it without a descriptor change.

Signal kind and direction are deliberately **not** part of a type descriptor — they are properties of
the signal entry and are propagated down during expansion. This is an improvement over today's
`DtypeFuncKey{dtypep, varType}` (`src/V3TraceDecl.cpp:120-134`), which must key its shared function
on variable kind because the kind is baked into the emitted declaration. Keeping type descriptors
purely type-derived is what makes "identical type ⇒ identical descriptor" true rather than nearly
true.

### Three properties this gets for free

- **Type descriptors are never cloned.** `AstTypeTable::cloneRelink()` is `V3ERROR_NA` — "Not
  cloneable" (`src/V3AstNodeOther.h:1963`) — so anything owned by the type table is inherently
  shared. Cloning a scope descriptor relinks its internal `entriesp`/`valuep` but leaves
  `m_targetp` pointing at the same shared type descriptor, which is exactly what we want.
- **Data type liveness.** `V3Dead::checkAll` increments `user1` on `nodep->dtypep()`
  (`src/V3Dead.cpp:97-105`), so a descriptor keeps its data type alive through
  `deadifyDTypesScoped` (which runs downstream of descriptor creation) via the standard mechanism,
  with no special casing.
- **Null `dtypep()` is legal.** `V3Broken` only requires a null `dtypep()` on nodes *without*
  `hasDType()`; when `hasDType()` is true it imposes nothing (`src/V3Broken.cpp:191-198`). So the
  two-role design needs no exemption.

### Uniquing

Rtmds are canonicalized **bottom up**: a type's element and member descriptors are
canonicalized before the type that references them, so a `m_subp` or `m_typeDescp` always points at
the one canonical descriptor for that type. That is what lets `sameNode` compare referenced
descriptors by pointer and still be exact -- comparing them structurally instead would be both
slower and, because `AstRtmdType::sameNode` does not itself recurse into members, wrong.

During construction, a map keyed by `AstNodeDType::skipRefp()` gives one descriptor per dtype node
in O(1). Because structurally identical types can still be distinct `AstNodeDType` nodes, a second
structural dedup pass over descriptor subtrees (`V3Hasher` / `V3DupFinder`, the same mechanism as
`V3CoverageJoin` and `V3Trace::detectDuplicates`) collapses those and redirects `m_targetp`
references, leaving one canonical descriptor per structurally distinct type. A canonical descriptor's
`dtypep()` is then one representative of possibly several structurally identical data types.

Two constraints on how far that dedup reaches, both discovered while implementing it:

- **The hash must not iterate into the described data type.** `V3Hasher` hashes struct and union
  types by `uniqueNum()` and deliberately hashes neither their children nor their dtype
  (`visit(AstNodeUOrStructDType)`), to break the circularity described at `src/V3Hasher.cpp:88-93`.
  Hashing a descriptor *through* its dtype would therefore give two clones of one struct declaration
  different hashes, so `V3DupFinder` would never even offer them for comparison — defeating the
  sharing the hash exists to find. `visit(AstRtmdType)` instead hashes the descriptor's own fields
  plus a summary of the type (width, and the basic keyword and signedness at leaves), and leaves the
  exact structural comparison to `AstRtmdType::sameNode`.
- **Struct dedup is limited to clones of one declaration.**
  `AstNodeUOrStructDType::similarDTypeNode` (`src/V3AstNodes.cpp:2273-2285`) compares packedness,
  member names, member widths and recurses into member types, but it also requires
  `fileline()->tokenNum()` to match. So a struct type in a module that `V3Param` cloned a hundred
  times deduplicates to one descriptor -- which is the #6706 case -- while two textually separate but
  identical struct declarations do not. Packed and unpacked arrays have no such restriction
  (`AstNodeArrayDType::similarDTypeNode` compares ranges and recurses), so they dedup structurally.
  Widening the struct case would mean relaxing `similarDTypeNode`, which is out of scope here.

### `broken()` checks

- a `TYPE` node has `dtypep()`, everything else does not;
- a `SIGNAL`'s `valuep` is an `AstVarRef` or an `AstConst`, and nothing else has a `valuep`;
- `m_targetp` of a `MEMBER`/`SIGNAL` is a `TYPE`; of an `INSTANCE` is a scope descriptor;
- `entriesp` of a `TYPE` contains only `MEMBER`s; of a scope only `SCOPE_*`/`SIGNAL`/`INSTANCE`/
  `LIBINIT`.

### Why `AstVarRef` / `AstConst` for the value

Holding a real `AstVarRef` means the entry participates in machinery that would otherwise all need
reimplementing:

- **`V3Scope`** relinks for free. The new `visit(AstRtmdScope*)` copies the `AstCoverToggle` shape
  (`src/V3Scope.cpp:232-239`): `cloneTree(false)` → `nodep->user2p(clonep)` →
  `m_scopep->addBlocksp(clonep)` → `iterateChildren(clonep)` ("we iterate under the *clone*"), and
  the existing `m_varRefScopes` / `AstVar::user1p -> AstVarScope*` fixup rewrites each clone's refs.
- **`V3Inline`** renames for free via `InlineRelinkVisitor`.
- **`V3Descope`** descopes for free: `visit(AstScope*)` at `src/V3Descope.cpp:215`, generic
  `visit(AstNode*)` at `:284`, and `visit(AstNodeVarRef*)` at `:224`.
- **`V3Dead`** keeps the variable alive for free, because a real `AstVarRef` is a real reference.
- **Emit** reuses the existing VarRef emission to produce the member-designator path (§5, emit).

`AstConst` covers parameters and anything else constant-folded; the `V3Number` is directly
available, including wide values and doubles, and an aggregate constant decomposes through its type
descriptor exactly like a variable does. Parameters are a large fraction of the #6706 bulk and must
**not** be materialised as pinned runtime variables.

---

## 5. Pipeline integration

`V3Coverage` is the anchor, and it is a principled one rather than an arbitrary one:
`src/Verilator.cpp:182` runs `V3Param::param` with the comment *"No more AstGenCase/AstGenFor/AstGenIf
after this"*, so the instance tree is fully elaborated; `V3WidthCommit` then commits
`widthMin == width` with `assertDTypesResolved(true)`; and the "End of elaboration" marker sits
immediately above the coverage block. Everything a descriptor needs is final, and nothing structural
has been lost yet.

| Line | Pass | What happens to the descriptors |
|---|---|---|
| 240-245 | `V3Coverage` / `V3Covergroup` | **`V3Rtmd` runs here**, after the whole coverage block (note `V3Coverage` is conditional on `coverageNonFsm()`, so placement must be unconditional). Builds the data type descriptors into `AstTypeTable` and one scope descriptor per module. Must be after coverage because `--trace-coverage` creates traced mirror vars (`src/V3Coverage.cpp:194`). |
| 258 | `V3Undriven` | Needs `visit(AstRtmdScope*) override {}` — see §9. |
| 286 | `V3SplitVar` | Runs *after* descriptor creation. v1 relies on its existing traced-variable handling (§8 item 4). |
| 280 | `V3LinkLevel::wrapTop` | Creates the `$root` wrapper *after* `V3Rtmd` has run, so the wrapper gets a descriptor of its own from `V3Rtmd::rtmdTopWrapper`, called immediately after. Its primary IOs go under a `$rootio` naming level (matching `V3TraceDecl`'s `$rootio` path, `src/V3TraceDecl.cpp:181`), and its cells — the design top(s) and every package — become instance entries. Without this the design would have no root descriptor to walk from, and `V3Inline` would have nothing to inline the top module's descriptor into. |
| 294 | `V3Inst::dearrayAll` | An arrayed instance or interface-reference-array entry is replaced by one entry per element, using a map from de-arrayed cell/port var to its element list recorded as the arrays are expanded. |
| 302 | `V3Begin` | Rtmds already captured begin/generate structure; variable names inside get flattened, descriptor names do not. |
| 326 | `V3Inline` | **Inlines descriptors**: the parent's instance entry for the inlined cell is replaced by `PUSH` *(named for the entry, not the cell — a de-arrayed element is named for its array position)* + the child descriptor's entries + `POP`. No `__DOT__` surgery on descriptor names — the dump path comes from the entry nesting; the child's descriptor rides along in the module body being moved, so its VarRefs and nested cell pointers are relinked by the existing clone/relink machinery. A cell with `!isTrace()` has no instance entry, in which case the child descriptor is simply dropped. Interface-reference entries are exempted from pin substitution (`InlineRelinkVisitor::visit(AstRtmdIfaceRef*)`), so they keep naming the port variable and resolve through the port's `AstAliasScope` in `V3LinkDot` exactly as they do without inlining. |
| 331 | `V3Interface` | Runs `if (opt.trace())` only, and exists solely to populate `AstCell::intfRefsp` for trace decls. Interface-ref entries stay unresolved until `V3Scope`; interfaces are never inlined (`src/V3Inline.cpp:268`) so the target always survives as a real instance (§14). |
| 358 | `V3Scope` | **Duplicates scope descriptors per scope** via the new visitor. `INSTANCE` entries resolve through the existing `AstCell::user2p -> AstScope*` ("The scope created inside the cell", `src/V3Scope.cpp:39`, set at `:144`). Type descriptors are shared, not cloned. |
| 366 | `V3LinkDot::linkDotScope` | **Resolves interface-reference entries**, deferred to the end of `LinkDotScopeVisitor` so every `AstAliasScope` has been processed first (depth-sorted outer-to-inner, so a port connected to another port resolves transitively). An entry is resolved to the descriptor of the scope of `getAliasVarScopep(varRefp()->varScopep())`, and must resolve — asserted, not left dangling. |
| 368 | `V3Rtmd::pruneAll` | **The prune pass**, immediately after `linkDotScope` so every instance and interface-reference link is resolved. Three things, in order: (1) mark what is reachable from the top scope's descriptor by following instance and interface-reference links, and delete every descriptor nothing names — that is what keeps a `tracing_off` instance's state from being pinned; (2) drop each signal for which `V3Control::getScopeTraceOn(path)` is false, i.e. `.vlt` `tracing_off -scope`; (3) drop naming levels left empty. This settles the pin set (§8). |
| 441 | `V3Gate` | Needs the pinning hook (§8). |
| 517 | `V3DepthBlock` | — |
| 524 | `V3Localize` | Needs a skip and a filter conjunct (§9). |
| 527 | `V3Descope` | Needs an explicit visitor: `V3Descope` deletes *every* `AstVarScope`, so descriptor entry VarRefs must be descoped too, but with an empty self-pointer rather than the `vlSymsp->TOP.x` form a CFunc reference would get — the emitted descriptor locates state by offset from `vlSymsp`, not by a C++ expression. Also relocates the scope descriptor from scope to module, as it does for `AstCFunc` (`src/V3Descope.cpp:260-273`). |
| 530 | `V3Combine` | Data, not code. Not applicable. |
| 507 | `V3Trace` | Activity analysis (shared with the legacy path, §10), then descriptor finalisation instead of CFunc construction. |
| emit | new `EmitCRtmd` | Resolves offsets, dedups descriptors, writes rows and pools. |

### The path a `.vlt` scope rule matches

`tracing_off -scope` matching is string matching, and `-levels` counts dots, so the string handed to
`V3Control::getScopeTraceOn` has to be exactly the one the legacy path uses or the rules behave
differently. Legacy passes `AstVarScope::prettyName()`, which is the flattened variable name — it
works only because `prettyName` decodes `__DOT__` back to `.` and strips the leading `TOP.`, so
`t__DOT__u__DOT__bar` in scope `TOP` reads back as `t.u.bar`.

The prune pass does not use the variable at all. It builds the path from the descriptor structure:
`AstNode::prettyName(scopep->name() + "->")` as the base, plus the naming levels currently open,
plus the entry name. That reproduces legacy's string in every case and is right in one case where
reading it off the variable is not: an inlined port entry's `AstVarRef` names the *parent's*
variable, so `u.i` would be matched as `din`. Two further properties fall out of using the
instance's own path:

- an interface is decided under its own instance path, once, however many ports reference it —
  which is what legacy does too, since it builds one init function per interface scope and calls it
  from each reference;
- a synthetic level like `$rootio` is excluded from the path, matching legacy, which applies scope
  rules to a wrapper primary IO under its bare name.

### What the reachability walk replaces

`AstVarScope::isTrace()` needs no check of its own. It is only ever cleared at
`src/V3Scope.cpp:296`, for the varscopes of a scope whose instantiating cell was `tracing_off` — and
`V3Rtmd` already emits no instance entry for such a cell, so that scope's descriptor is
exactly what the reachability walk finds unreachable and deletes. The pass asserts the implication
rather than re-testing it. Deleting the descriptor, rather than emptying it, is what matters:
otherwise the pinning hooks would still walk it and hold the whole subtree's state live.

### Empty levels are not all the same

An instance level with nothing traced inside it must stay: `VerilatedVcd` emits `$scope`/`$upscope`
for it, and the legacy goldens contain those empty scopes (`t_trace_scope_no_inline.out` has an
empty `mid_a`). A *naming* level with nothing in it must go: legacy pushes a prefix only on the way
to a real entry, so an empty generate block or `$rootio` never appears. Hence pruning removes empty
`PUSH`/`POP` pairs and leaves empty instance entries alone.

### Precedent

Create-early-per-module → clone-per-scope → dedup-later is not a new shape in this codebase. It is
exactly the toggle-coverage flow, anchored at the same point: `V3Coverage` creates `AstCoverToggle`
per module, `V3Scope` clones it per scope (`src/V3Scope.cpp:232-239`), and `V3CoverageJoin` dedups
with `V3DupFinder` (`src/V3CoverageJoin.cpp:24,49`).

### Per-instance divergence

This is the reason for per-scope duplication of the *scope* descriptors, even though *type*
descriptors are shared. After `V3Scope`, each instance's entries are optimised independently: if
instance A's signal folds to a constant and instance B's does not, A's `valuep` becomes an `AstConst`
(const entry, never-changing activity set) while B's stays an `AstVarRef`. A shared per-module
descriptor cannot express that. Size is recovered at the end by deduplicating *final* descriptors,
which is strictly better than sharing up front because it only merges what genuinely stayed
identical. Type descriptors are unaffected, since a type's structure does not depend on which
instance uses it.

### Emit

Offsets are three-level, and each level is relative so that dedup remains possible:

- an `INSTANCE` entry carries `offsetof(SymsClass, scopeMember)` — the instance base;
- a `SIGNAL` entry carries `offsetof(ScopeClass, member)` — scope-relative;
- within a signal, the type descriptor supplies bit offsets for packed types and
  `offsetof`/`sizeof` constants for unpacked ones.

The runtime composes all three. This works because `V3EmitCSyms` emits all module instance state
**by value** as members of the Syms class (`src/V3EmitCSyms.cpp:949-957`, "MODULE INSTANCE STATE"),
so every traceable signal has a fixed offset. `V3TraceDecl` already excludes class members, function
locals and automatics, which are the things that would not.

One new emitter capability is required: emit an `AstVarRef` as a bare member-designator path
(`__PVT__i`, or `a.b.c` for nested aggregates) without the `vlSymsp->` / `vlSelfRef.` prefix, so it
can be placed inside `offsetof(...)`. This keeps Verilator from having to model C++ struct layout
itself.

Caveat: the Syms class is `alignas(VL_CACHE_LINE_BYTES) ... final : public VerilatedSyms`
(`src/V3EmitCSyms.cpp:899-900`), so it is not standard-layout and `offsetof` is only
conditionally-supported — accepted by GCC/Clang/MSVC including nested member designators, but warns
under `-Winvalid-offsetof`. Needs a wrapper macro with pragma suppression, a
`static_assert(sizeof(Syms) <= UINT32_MAX)` (or a 64-bit offset fallback), and a debug-mode
self-check comparing a computed offset against a real address.

---

## 6. Generated data

Invariants that matter more than the exact packing (which is Stage 0 tuning work):

- fixed-size op-tagged POD rows, so they are indexable and prefetchable;
- **no relocations** — strings are `uint32_t` offsets into a pool, type descriptors and sub-tables
  are indices into their tables, constants are offsets into a word pool. This keeps everything in
  `.rodata` and is directly relevant to the #6706 linker relocation reports;
- signal offsets are scope-relative and type offsets are type-relative, so identical modules and
  identical types produce identical rows;
- rows are chunked across translation units, subsuming `--output-split-ctrace` for the tabled part.

Per model:

**Type descriptor table** — one row per descriptor, with the fields that were derived from
`dtypep()` now materialised: `LEAF {bits, msb, lsb, sigType, flags, enumIdx}`,
`ARRAY {kind, left, right, elements, stride, subIdx}`,
A row is just `{op, pointer to the descriptor of that kind}`, and the descriptor names its own
fields: `VlRtmdAtom {sigType, flags, bits, left, right, enump}`, `VlRtmdPackedArray {value, count,
elemBits, elemIdx, left, right}`, `VlRtmdUnpackedArray {count, elemBytes, elemIdx, left, right}`,
`VlRtmdPackedStruct {value, count, membersp}`, `VlRtmdUnpackedStruct {count, membersp}`, and
`VlRtmdEnum {nameOfs, bits, count, namesOfs, valuesOfs, dtypenum}`. Every kind a dump shows as a
single value carries a `VlRtmdAtom` describing that value, so nothing has to reconstruct it.

Only a SystemVerilog builtin is an atom. A ranged scalar such as `logic [7:0]` is a `PACKED_ARRAY`
of `logic` with `elemBits` 1, and `logic [0:0]` is one too, distinct from `logic [1:1]`. Verilator
holds a single packed dimension on the `AstBasicDType` itself rather than as an `AstPackArrayDType`,
which is a detail of how it stores the type, not of the type as written, so it is not carried into
the descriptors. A builtin whose keyword gives its own width, `int` and the like, stays an atom when
ranged; so does an enum, whatever its base, since what a dump shows is the item name of the whole
value. The one bit element is canonicalized, so every ranged scalar in a design shares it, and the
signedness of `logic signed [7:0]` sits on the array rather than on one of its bits.

Each descriptor is its own object with external linkage, not an element of a per kind array, so the
descriptors split across as many `<prefix>__RtmdDefs__N__Slow.cpp` files as they need while the
table that indexes them stays one contiguous array. A struct's members go with its descriptor, as
they are read by index and cannot be split away from it.

**Scope tables** — one per unique scope descriptor: `PUSH {nameOfs, scopeKind}`, `POP {}`,
`SIGNAL {nameOfs, typeIdx, dataOfs, direction, kind, valueId, actSetId}`,
`SIGNAL_CONST {nameOfs, typeIdx, constOfs, direction, kind}`,
`INSTANCE {nameOfs, scopeKind, tableIdx, offsetBase}`, `PARTITION {nameOfs}`. The push and pop rows
mirror the `AstRtmdPush`/`Pop` pair one for one, so emission needs no restructuring.

**Activity set tables** — a pair serving the whole design, in a generated file of their own
(`<prefix>__RtmdActSets__Slow.cpp`). The set table is indexed by the set id a `SIGNAL` row
carries; each row is a `VlRtmdActSetRow {firstFlag, lastFlag}`, a half open range over the
flag side table, which holds the activity flag numbers. Because a row carries both indices the sets
need not be laid out in order, so flag runs can later be shared between sets. Set 0 is the set of signals nothing was
worked out about, which is what a row names when it names no set of its own, so a zeroed row is read
rather than silently skipped; it holds `V3Trace::EVAL_FLAG` alone, so those signals are read whenever
anything at all can have changed. An empty set at any other index is one whose signals never change,
which the full dump reads and the change dump does not. The set table has external linkage, named
`<prefix>__RtmdActSets` to keep two linked models apart, as the constant pool does; the flag
table is `static`, since only the set table points into it.

The sets live in the tree: `V3Trace` makes one `AstRtmdActSets` under the netlist, holding one
`AstRtmdActSet` per distinct set, and points each signal's `m_actSetp` at the entry that
covers it (none meaning always check). The emitter numbers the entries from 1 and lays out both
tables, so the analysis stays free of the table format.

**Pools** — strings, constant words, enum item names and values. A row indexes a pool by offset
rather than pointing at one, so the pools never leave the file the registration function is in.

Each table is emitted into a file of its own: `<prefix>__RtmdTypes__Slow.cpp` for the type table,
`<prefix>__RtmdScopes__Slow.cpp` for the per instance scope tables and the table of tables,
`<prefix>__RtmdActSets__Slow.cpp` for the activity sets, and `<prefix>__Rtmd__Slow.cpp` for the
pools and the registration function that hands the lot over. Only the registration function needs
all of them, so only the three tables it names have external linkage; the per scope arrays and the
pools are `static`. The type table needs no model header, as nothing in it is an `offsetof`.

Name strings must be run through `VIdProtect::protectWordsIf` at emit, as
`emitTraceInitOne` does today (`src/V3EmitCImp.cpp:688`), including the member names inside type
descriptors — otherwise `--protect-ids` leaks identifiers into the dump. The `protect()` flag rides
on the descriptor node as it does on `AstTraceDecl`.

One set of tables serves declarations, full dumps and change dumps. Today the full and chg functions
are two copies of the same body (`createNonConstTraceFunctions`, `src/V3Trace.cpp:909-1028`); the
descriptor form halves that on top of everything else.

Note the three formats consume *different* subsets of the declaration fields — VCD's `decl*` drops
`fidx`/`dtypenum`/`dir`/`kind`/`type` (`include/verilated_vcd_c.h:161-188`), FST drops `fidx`
(`include/verilated_fst_c.h:156-183`), SAIF drops `dtypenum`/`dir`/`kind`/`type`
(`include/verilated_saif_c.h:174-201`), and only FST's `pushPrefix` takes `left`/`right`. The macro
layer exists precisely to discard them at compile time. A format-agnostic descriptor carries the
union: slightly more data, in exchange for the format no longer being baked in.

---

## 7. Runtime

### Registration

The runtime needs no knowledge of generated types. Everything is reachable from a small record:

```c
struct VlRtmdTables {
    void*           symsp;            // base for offset resolution
    uint8_t*        activityFlagsp;   // &vlSymsp->__Vm_traceActivity[0]; flag 0 is coarse
    uint32_t        nActivityFlags;   // also drives the generic cleanup
    const VlRtmdDTypeRow* dtypesp;  uint32_t nDtypes;
    const VlRtmdRow*      rootp;    uint32_t nRootRows;
    const VlRtmdRow* const* tablesp;   // table-of-tables for INSTANCE rows
    const char*     stringPoolp;
    const uint32_t* constPoolp;
};
```

`__Vm_traceActivity` is a Syms member, sized by the flag count on the `AstRtmdActSets`.
`V3Trace::EVAL_FLAG` is the flag the model sets on every eval, replacing the separate
`__Vm_activity` bool. Nothing in the runtime treats it specially: it is simply the only flag in the
activity set of the signals nothing was worked out about, so `rtmdGroupActive` is one loop
over the group's own flags with no early outs. Passing their addresses means
the generic interpreter never dereferences a generated type. The generated `trace_cleanup` function
(`src/V3Trace.cpp:1030-1062`) becomes a generic runtime loop over `activityFlagsp`.

### Elaboration

At trace-open, per model, in one recursive walk:

1. descend `SCOPE` and `INSTANCE` rows, maintaining the name prefix stack and a composed base
   offset;
2. for each `SIGNAL`, expand its type descriptor recursively, composing the leaf name (`name`,
   `.member`, `[idx]`) and the leaf address (instance base + signal offset + type offset), and
   propagating the signal's direction and kind down to each leaf;
3. apply the tracing policy (§7.2), dropping filtered leaves without materialising them;
4. group the surviving leaves by the signal's activity set, then allocate codes in that order
   (§7.3), then partition into fidx ranges (§7.4);
5. second pass: declare, calling the format's `pushPrefix` / `decl*` / `declDTypeEnum`.

**Code allocation must follow dump order, not declaration order.** Today `V3Trace` allocates codes
while iterating the activity-sorted `traces` multimap in `createConstTraceFunctions`, deliberately:
*"Our keys are now sorted to have same activity number adjacent, then by trace order... Last are
constants and non-changers, as then the last value vector is more compact"*
(`src/V3Trace.cpp:1089-1092`). That ordering is what makes each change-dump function walk
`m_sigs_oldvalp` roughly sequentially. A runtime elaborator that allocated codes during the
descriptor walk would allocate in *declaration* order instead, scattering `oldp` accesses within
every activity group and giving up cache locality that today's code has. Hence the grouping happens
before allocation, and the declaration pass runs afterwards once codes are known.

This is also why the activity set must be carried in the descriptor (`m_actSetId`): the runtime
cannot derive it, and it needs it before it can allocate a single code. `V3Trace`'s analysis assigns
a dense set id per distinct activity set, emitted as a small side table of flag-index lists.

Two declaration-time passes are needed anyway because SAIF consumes `fidx` at declaration time
(`declBit(uint32_t code, uint32_t fidx, const char* name)`). All cold path.

Two ordering invariants to preserve: FST keys enum tables per model
(`m_local2fstdtype.at(initUserp())`) so enums must be declared before the signals referencing them,
and FST's `pushPrefix` assumes "a signal at a given prefix level is declared before any pushPrefix
at that same level". Both fall out of preserving entry order.

The interpreter is instantiated per format in `verilated_trace_imp.h`, next to
`VerilatedTraceBuffer::full*`, so the `emit*` calls still inline. That is the icache win: one or two
kilobytes of loop, once per format, in place of megabytes of generated functions.

`WDataInP::external(const EData*)` (`include/verilated_types.h:188`) already exists for
constructing a wide handle from a raw pointer. Events work directly: the entry points at the
`VlEventBase` and the runtime calls `isTriggered()`, since it is the same library.

### 7.1 Extracting packed leaves

A leaf inside a packed root is not addressable on its own — it lives at an arbitrary bit offset and
may straddle word boundaries — so the runtime has to extract it. This is the work that V3Expand does
at compile time today, and it is the one place where the interpreter genuinely has to do more than
load and compare. The good news is that the runtime already has every primitive needed, all
`VL_MT_SAFE` and inline in `include/verilated_funcs.h`:

| Case | Extraction | Primitive |
|---|---|---|
| Packed root ≤ 64 bits (scalar storage) | shift, then mask | `VL_SEL_IIII` (`:2755`), i.e. `>> lsb` |
| Wide root, leaf ≤ 32 bits | may span two words | `VL_SEL_IWII` (`:2795-2806`) |
| Wide root, leaf 33-64 bits | may span three words | `VL_SEL_QWII` (`:2808-2828`) |
| Wide root, leaf > 64 bits, word-aligned | none — point directly at the parent's words | zero copy |
| Wide root, leaf > 64 bits, unaligned | assemble into a scratch buffer | `VL_SEL_WWII` (`:2830+`) |

So the entry op tag needs to distinguish these, and each maps onto one existing call. Three
consequences:

- **The entry's `datap` is the packed root's storage, not the leaf's**, because a cross-word span
  needs access to the neighbouring word. The exception is the word-aligned wide case, where `datap`
  can be pre-advanced and the leaf compared and emitted in place with no copy at all — worth having
  as its own op, since word-aligned wide members are common and it is the cheapest path in the whole
  design. A useful encoding refinement: for the non-wide cases pre-advance `datap` to the containing
  word and store only `lsb % 32`, which fits in 5 bits, since `VL_SEL_IWII`/`VL_SEL_QWII` only touch
  words at or above `VL_BITWORD_E(lsb)`. That needs the primitives' bounds check adjusting or
  skipping, since offsets are known valid by construction.
- **The runtime needs a scratch buffer** for the unaligned wide case, to hold the assembled value
  before comparing it against `oldp` and emitting it. It is bounded by `--trace-max-width`
  (default 4096) and there is precedent: FST already allocates `m_strbufp` sized by `maxBits()`.
- **The `VL_SEL_*` primitives do not mask the upper bits** — they return the shifted value and
  Verilator's generated code follows them with an `AND` where needed. The interpreter must do the
  same, which is the concrete form of the cleanliness requirement in §9.

There is also an optimisation here that only the data-driven form makes practical, and which is
worth noting for later rather than v1: a packed root with many leaves can be **pre-checked as a
whole**. One comparison of the root against a saved copy can skip every leaf under it, where today's
generated code must compare each member separately. For a 100-member struct that is one wide compare
instead of a hundred narrow ones. It costs a second copy of the root's storage, which is redundant
with the leaves' `oldp` words, so it is a space/time trade to measure rather than an obvious win.

### 7.2 Policy applied at runtime

Because descriptors are policy-free (§4), the runtime decides during expansion:

| Decision | Today | Runtime rule |
|---|---|---|
| Expand a packed aggregate per member, or dump it as one bus | `--trace-structs` at verilate time | on reaching a packed root: expand `entriesp`, or emit the root as a single leaf of its full width |
| Skip an unpacked array that is too large | `--trace-max-array` at verilate time | compare the descriptor's `elements` before expanding; nothing is materialised if skipped |
| Skip a signal that is too wide | `--trace-max-width` at verilate time | compare the width before materialising |
| Skip by name / hierarchy | `--trace-underscore`, `--trace-depth`, `.vlt` scope trace-off | the runtime has names, paths and depth, so these are expressible too — see the caveat below |
| Skip by `$dumpvars` | already runtime | unchanged |

The existing command-line options remain, and their values are passed through so behaviour matches
today by default. `VerilatedTraceConfig` (`include/verilated_trace.h:103-109`) currently carries only
`m_useParallel` and is produced per model by `traceConfig()`, consumed in `addModel`, which is the
natural channel — though these are really trace-*file* policy rather than per-model, so they may be
better as trace-file settings with the model supplying defaults, in the way
`VerilatedVcdC::dumpvars` already works. Note `addModel` currently resolves the one existing
config field by OR-ing (`m_parallel |= configp->m_useParallel`), so a conflict rule is needed if two
models in one file disagree.

**Caveat: filters that drop signals interact with pinning.** A decision that changes *whether a
signal is dumped at all* changes whether the compiler must keep that signal alive (§8). Since v1
emits everything and lets the runtime choose, the compiler cannot know, so it must pin everything
described — which is more pinning than today, where `--trace-max-width` and `--trace-max-array` drop
signals before they are ever pinned. In practice the delta should be modest, because wide signals and
large memories are almost always real state that was never eliminable anyway, but it is a real cost
and belongs in the measurements (§12). The name- and path-based filters are listed above as
*expressible* at runtime rather than as v1 work, for the same reason.

This tension disappears with option 2 (§2): once trace-only values are computed in a prologue rather
than pinned, nothing needs pinning, the compiler no longer needs to know the filter outcome, and
fully runtime-configurable filtering becomes coherent. That is the endpoint; v1 gets the descriptor
completeness without yet getting the freedom.

### 7.3 Codes assigned at runtime

Runtime allocation removes the compile-time `nTraceCodes` contract passed to `addInitCb`
(`src/V3EmitCModel.cpp:611-617`) and makes the reopen check
(`include/verilated_trace_imp.h:137-140`, "Reopening trace file with different number of signals")
true by construction.

It loses one thing that is currently compile-time: **value dedup**. `V3DupFinder` in
`detectDuplicates` (`src/V3Trace.cpp:256-326`) finds decls that trace the same value and gives the
duplicate the canonical's code. A runtime elaborator cannot see that two entries read the same
storage, so each signal entry carries a **`valueId`**: either "allocate fresh codes" or "reuse the
codes already allocated for value id N". Because a signal's leaves are allocated contiguously in
descriptor order, an alias only needs the base — the leaf offset within the type is implied. This is
the same shape as today's `TraceTraceVertex::m_dtypeAliasOffset` (`src/V3Trace.cpp:144-145`), and it
also subsumes the `--lib-create` root/top aliasing, which today is a post-hoc match on
name/direction/width/range (`sameRootInitAlias`, `src/V3Trace.cpp:244-254`).

The format side is already prepared for aliased codes — FST's `declare()` does
`m_code2symbol.find(code)` and calls `createVar` with the existing handle for aliases.

### 7.4 fidx assigned at runtime

**Deferred.** Rtmd dumping uses a single buffer, so fidx is 0 everywhere and dumping is
sequential. That costs parallel dump throughput and nothing else: fidx reaches no output except
SAIF's declarations, which take it at face value. Picking this up later needs nothing undone —
just a partition of the flat leaf list and a range per buffer. The rest of this section is the
plan for when that happens.

Today `useTraceParallel()` (`src/V3Options.h:662-664`) bakes the verilate-time `--threads` into the
partition count via `m_parallelism` (`src/V3Trace.cpp:209-210`). Runtime partitioning follows the
actual thread pool, so one binary is well-partitioned for any thread count. The existing
`CallbackRecord` / `runCallbacks` / `getTraceBuffer(fidx)` machinery
(`include/verilated_trace_imp.h:272-318`) is reused by registering generic trampolines over entry
ranges, so parallel dispatch, buffer commit ordering and `initLib` behaviour are unchanged.

### 7.5 Sharing summary

| Level | Mechanism | Shared when |
|---|---|---|
| Data type | one descriptor per unique type, referenced by index | always — structure is instance-independent |
| Scope | dedup identical final descriptors | entries *and* activity groups match after optimisation |
| Runtime entries | none — fully expanded | never |

Activity is derived from the call statement, and `V3Trace` groups consecutive `CCall`s in one
statement list into a single activity vertex — which is exactly the #6706 case where two instances
are called from the same `if` body, so they do share. But scope sharing is a measured outcome, not a
guarantee; type sharing is unconditional, which is why it carries the bulk of the win.

---

## 8. Pinning

With the trace CFuncs gone, the incidental pinning they provided disappears, and `V3Gate` would not
merely substitute traced signals — it would delete them as unconsumed. v1 requires every traced
value to be an address, so pinning becomes explicit. All three hooks follow established idioms.

1. **`V3Gate`** — `makeVarVertex` (`src/V3Gate.cpp:156-180`) already pins for this class of reason
   three times over:
   ```cpp
   if (vscp->varp()->isSigPublic()) {
       // Public signals shouldn't be changed, pli code might be messing with them
       vVtxp->clearReducibleAndDedupable("SigPublic");
       vVtxp->setConsumed("SigPublic");
   }
   ```
   Rtmd-traced variables get the same treatment (`"Traced"`), next to
   `VirtIface`/`SigPublic`/`isTop`. `setConsumed` prevents the "Remove unconsumed" path at
   `:1273-1277` from deleting it; `clearReducibleAndDedupable` prevents substitution-and-elimination
   and matches the conservative `SigPublic` choice.
2. **`V3Localize`** — marks each described `AstVarScope` as not optimizable (`user1`), the same
   mechanism the pass already uses for a variable it must not localize. Today localization is
   blocked only as a side effect of the trace CFunc's read references (`:201-222`).
3. **`V3Dead`** — `mightElimVar` (`src/V3Dead.cpp:422`) already reads
   `if (nodep->isTemp() && !nodep->isTrace()) return true;`, so temps are covered; the non-temp path
   falls through to `m_elimUserVars` and wants checking. Real `AstVarRef`s in the entries may make
   this a no-op.
4. **`V3SplitVar`** — **no change for v1.** `src/V3SplitVar.cpp:1209` and `:1228-1240` already keep a
   traced variable whole and reconstruct it via `Concat`. That is exactly the v1 behaviour we want.
   Letting it split and carrying per-piece entries belongs with option 2.

### The pin set

The pin set is "every variable that produced a descriptor entry", and both hooks above read it
straight off the descriptors: each iterates the `AstRtmdScope`s and pins exactly the variables
the entry VarRefs name. That is definitionally the right set and needs no separate marking pass —
`V3Gate` and `V3Localize` both run after the prune pass, so what they see is already settled. Do not
pin on `varp()->isTrace()` — that flag is set well before any of the filtering, so it both over-pins
(described-then-pruned signals) and, being per-variable rather than per-instance, cannot express a
per-scope decision at all.

Note this set is *larger* than today's traced set, because descriptors are policy-free (§4) and the
size filters now run at runtime: a signal that `--trace-max-width` or `--trace-max-array` would have
dropped is still described, so it must still be pinned. `vscIgnoreTrace`
(`src/V3TraceDecl.cpp:242-266`) is the list of things that are no longer decided at this point. Of
that list, only `--trace-max-width` is left to the runtime; the name- and path-based filters do not
depend on runtime policy, so they are applied and keep the pin set tighter — `--trace-underscore`
per name component in `V3Rtmd`, `.vlt` scope trace-off in the prune pass.

### The cost being accepted

Today `V3Gate` *can* eliminate a traced signal and have its value recomputed inside the trace
function — that is where arbitrary traced expressions come from in the first place. Pinning removes
that, so v1 will have more live model state and possibly slower `eval` than `--trace` on the same
design. Dumps must match exactly; `eval` performance, model size and `--stats` legitimately will
not. The A/B gate is therefore **dump equality only**, and the eval delta is a number to hand to
option 2 rather than a regression to fix. Capture it per RTLMeter design from the first working
build, since it is the entire justification for doing option 2.

### Cases that are not plain addresses

- **Parameters / localparams** → `AstConst` entries with the value in the constant pool. In scope
  for v1; materialising them as variables would be strictly worse.
- **SystemC top IOs** → already handled upstream, no work needed. `V3LinkLevel::wrapTopCell`
  (`src/V3LinkLevel.cpp:290-305`) clones each top IO into the wrapper and, for SystemC, does
  `varp->sc(true); varp->trace(false);` with the comment *"User can see trace one level down from the
  wrapper / Avoids packing & unpacking SC signals a second time"*. The wrapper var is the SC one and
  is not traced; the inner original is a plain Verilated variable on the same net. So `--sc` stays in
  scope for v1.
  Open: whether any *other* SC-typed variable can still reach a traced signal — that is what
  `emitTraceIsScBv` / `emitTraceIsScUint` / `emitTraceIsScBigUint` (`src/V3EmitCImp.cpp:622-641`)
  serve. `t_trace_scstruct` (`--sc --trace-vcd --trace-structs --pins-bv 2`) and the ten
  `t_var_pins_*` tests are the probes; the bring-up assert below answers it definitively.
- **Forced signals** → a code force keeps the value in a `VlForceVec`, so there is no address to
  point at. `V3Force` materialises one (`__VforceTrace`, §9), which is pinning by another name.
- **Events** → entry points at the `VlEventBase`; the runtime calls `isTriggered()`.
- **Strings and unpacked unions** → not traceable in any supported format; described but marked
  unsupported so the runtime skips them (§4).

### Bring-up guardrail

At descriptor finalisation, assert that every `SIGNAL`'s `valuep` is `AstVarRef` or `AstConst` —
`v3fatalSrc`, not a silent fallback. During bring-up this converts "we missed a case" from a subtly
wrong dump into an immediate localized failure, and whatever trips it becomes the precise work list
for option 2.

---

## 9. Required changes elsewhere

Putting real `AstVarRef`s in a container that is **not** an `AstCFunc` breaks an invariant several
passes rely on. Two confirmed instances, found by inspection rather than by test failure:

- **`V3Undriven`** — `visit(AstTraceDecl*) { v3fatalSrc("Should not exist yet"); }`
  (`src/V3Undriven.cpp:899-900`), and it runs at `src/Verilator.cpp:258`, downstream of the anchor.
  Needs `visit(AstRtmdScope*) override {}`. This matters for behaviour, not just for the assert:
  V3Undriven deliberately skips `AstNodeCoverDecl`/`AstCoverInc`/`AstCoverToggle` as sinks
  (`:897-899`, "Coverage artifacts etc shouldn't count as a sink"). If descriptor reads counted as
  sinks, UNDRIVEN/UNUSED warnings that fire today would start being suppressed, because today trace
  decls do not exist yet at that point.
- **`V3Localize`** — `UASSERT_OBJ(m_cfuncp, nodep, "AstVarRef not under function")`
  (`src/V3Localize.cpp:202`), with `m_cfuncp` set only in `visit(AstCFunc*)` (`:147`) and a generic
  `visit(AstNode*)` (`:224`) that walks everything. Needs a skip for `AstRtmdScope`.

Passes that only walk logic under CFuncs — `V3Clean`, `V3Premit`, `V3Expand`, `V3Subst`,
`V3MergeCond`, `V3Reloop` — will not see the descriptors, which is correct for v1 since bare VarRefs
need no cleaning or expansion.

### The audit

Every pass from the anchor (`Verilator.cpp:249`) to emit, checked against six failure modes. What
determines whether a pass is even exposed is *where the descriptor lives*: under
`AstNodeModule::stmtsp` from `V3Rtmd` to `V3Scope`, under `AstScope::blocksp` from `V3Scope` to
`V3Descope`, and back under `AstNodeModule::stmtsp` after that. A pass that walks module statements
or scope blocks generically reaches it; a pass that walks only CFuncs, `AstActive` contents, or an
explicit logic list does not.

**1. Asserts a statement or function context.** Recipe:
`grep -rn "not under function\|UASSERT.*m_cfuncp\|UASSERT.*m_modp" src/`. One real hit,
`V3Localize.cpp:217` (`"AstVarRef not under function"`), fixed by the descriptor visit that also
does the pinning. Checked and clear: `V3Depth:112` (fires on `AstCExprUser`/`AstCStmtUser` only),
`V3CCtors:202`, `V3Trace:1255`, `V3EmitCSyms:804`, `V3SplitVar:454-466` (`m_modp` is set, since
descriptors are under a module).

**2. Fatals on nodes it does not expect.** One real hit, `V3Undriven.cpp:899-900`, fixed with
`visit(AstRtmdScope*) override {}`. The other generic-visit fatals do not apply:
`V3SchedPartition:263` sees only `AstActive` contents, `V3Subst:193` only expression trees,
`V3EmitCPch`/`V3Randomize`/`V3WidthSel` only their own controlled entry points. `V3EmitV`'s default
visit is not fatal but emits `???? // ...` and a `%Error` — fixed with
`visit(AstNodeRtmd*) override {}` next to its existing `AstTraceDecl`/`AstTraceInc` skips.

**3. Newly sees VarRefs it previously could not.** The interesting mode, and the one that produced
findings no amount of reading the pass list would have suggested. Three hits, all of them a pass
*rewriting* the descriptor's reference rather than merely observing it:

- **`V3DfgAstToDfg`** — `AstToDfgVisitor`'s unhandled-node case calls `markReferenced`, so
  `AstToDfgAddAstRefs` walks the descriptor and builds a `DfgAstRd` vertex for its read. On
  writeback `V3DfgDfgToAst.cpp:330` replaces every `DfgAstRd` reference with its driving
  expression, so entries became `SEL`s and `CONCAT`s. This was ~350 of the 356 designs the
  whole-suite sweep flagged, i.e. **the DFG optimizer, not `V3Gate`, is the dominant pinning site**
  — §8 named `V3Gate` and missed this. Fixed by marking a descriptor read as `setHasExtRdRefs`, the
  DFG's own "a read I cannot see into" flag, and creating no vertex: the variable stays observed and
  the reference is left alone.
- **`V3SplitVar`** — collects every `AstVarRef` for the packed splitter
  (`SplitUnpackedVarVisitor::visit(AstVarRef*)`), then `updateReferences` rewrites them to the
  pieces. The `varp->isTrace()` branch at `:1228-1240` does keep the original variable and drive it
  from the pieces, so §8 item 4 was right that no *splitting* change is needed for the packed
  case — but it only helps if something still names the original, and our reference had been
  rewritten. The unpacked path is worse: it deletes the original variable outright (`:768`). v1
  therefore **refuses to split any variable a descriptor names**, as one more entry in
  `cannotSplitVarCommonReason` beside `isSigPublic` and `isForceable`. That supersedes §8 item 4:
  the cost is losing the optimisation on traced variables, and a `SPLITVAR` warning wherever the
  user asked for a split explicitly (39 of them in `t_split_var_0`) — both visible only in
  descriptor mode. Letting it split and carrying per-piece entries stays with option 2.
- **`V3Tristate`** — subtler than it looks. The graphing phase is safe on its own
  (`associateLogic` is a no-op when `m_logicp` is null, `V3Tristate.cpp:478-480`), but the
  enable-propagation phase hangs an enable expression off a read via `user1p`, and `checkUnhandled`
  (`:697-712`) then rejects any node whose child carries one — reported as
  `Unsupported tristate construct: DESCRIPTORENTRYSIGNAL`. Fixed by not visiting descriptors at
  all: the reference already reads the resolved value, which is what the dump wants.
- **`V3Force`** — see the unresolved item below.

Observing passes are fine: `V3Dead` counting a descriptor read as a use is exactly what is wanted,
and it is also what keeps a type descriptor's `dtypep()` alive, through the generic
`checkAll(nodep)` (`V3Dead.cpp:97-104`) that every node gets — which works only because
`AstRtmdType::hasDType()` is true. `V3Tristate` is safe by its own gating: `associateLogic` is
a no-op when `m_logicp` is null (`V3Tristate.cpp:478-480`), and a descriptor read never satisfies
`feedsTri`, so neither the graphing nor the enable-propagation path touches it.

**4. Counts or measures nodes.** Narrower than feared. `V3InstrCount` is only ever called on
`rootp()->evalp()`, an order-logic vertex, or an MTask function, so **MTask partitioning inputs are
unaffected**. `V3StackCount` short-circuits `AstNodeExpr` and counts variables only under a CFunc,
so descriptors add nothing. That leaves `--stats` node counts, which do change.

**5. Needs a new visitor for the new node.** `V3Broken` via the `broken()` implementations,
`V3Hasher` (needed anyway for type-descriptor dedup), `dump()`/`dumpJson()`, and `V3EmitV` as above.

**6. Deletes or moves what a descriptor points at.** Not in the original list, and in practice the
mode that cost the most work: `V3Inst::dearrayAll` deletes the cell an instance entry names,
`V3Inline` deletes the cell and moves the module body, `V3Descope` deletes every `AstVarScope`, and
`V3Localize`/`V3Dead` would remove a variable only a descriptor reads. Each is handled at the pass
that does the damage — see the §5 table. The general lesson is that a pointer from a descriptor to
a cell or variable is a maintenance obligation on every pass that restructures those, which is the
argument for the `broken()` checks being as strict as they are.

Two hits here are consequences of the anchor rather than of any one pass, and are listed as
unresolved below: a module that does not exist yet at the anchor, and a variable in dead code that
is deleted before the first pinning hook runs.

**7. Creates a module after the anchor.** `V3LinkLevel::wrapTop` was the known case (§5), but it is
not the only one: a later pass creates the `$unit` package on demand — `t_sys_monitor` and six
siblings do it — and the wrapper instantiates it, so its instance entry had nothing to resolve to.
Fixed by having `rtmdTopWrapper` describe *any* module that lacks a descriptor, not just the
wrapper, which is the natural catch-up point since it already runs after `wrapTop`. Note this made
a second `RtmdTypeBuilder` load-bearing, and a fresh `V3DupFinder` does not know about the
first invocation's descriptors: the builder now seeds itself from `AstTypeTable::rtmdTypesp`, or
type sharing silently splits in two.

#### The guardrail that found modes 3 and 6

`AstRtmdSignal::broken()` asserts that `valuep()` is an `AstVarRef` or an `AstConst`.
Under `--debug-check` this fires in the pass that breaks the invariant rather than as a wrong dump
much later, which is what turned "the DFG substitutes expressions" from a subtle golden mismatch
into a one-line diagnosis. It also confirms the design's claim that constant folding gives const
entries for free: `t_trace_scope_vlt`'s parameters arrive at emit as `AstConst` entries with
`origParamName` intact, with no work on our side.

#### Method

Whole-suite sweeps of all 3397 `test_regress/t/t_*.v*` designs with `--debug-check`, one baseline
and one with `--trace-vcd`, comparing which designs fail to verilate. That is what found
modes 3, 6 and 7; targeted sweeps over the trace and interface tests had been clean for days. The
first comparison flagged **356** new failures. After the fixes above and the four below, **2**
remain out of 3397 designs. The groups were:

| Designs | Cause | Status |
|---|---|---|
| ~45 | `V3Force`: no address for a forced value | Fixed: materialise the shadow |
| 4 | `V3SplitVar`: unpacked split deletes the variable | Fixed: refuse to split a described variable |
| 3 | Variable in dead code, or in a construct lowered later | Fixed: gate the deleting transforms |
| 2 | Declining an optimisation exposes a real error | Expected, see below |

Two remain, both of the last kind.

#### Resolved: variables in dead code

`t_var_nonamebegin` and `t_lint_unusedloop_removed_bad` left a dangling `AstVarRef::m_varp`: the
variable is declared in code that `V3Const` removes as dead, at `Verilator.cpp:290` — before any
pinning hook runs and before the prune pass could drop the entry. Legacy never meets this because
`V3TraceDecl` runs at 438, long after the dead code is gone.

`V3Const` deletes variables in three places, each by deleting a statement subtree that happens to
contain declarations:

- **`visit(AstNodeIf*)`** (`src/V3Const.cpp:3786-3829`) — a constant condition folds the `if` to
  the taken branch and the untaken branch is deleted. This is `t_var_nonamebegin`.
- **`visit(AstLoop*)`** (`:4109-4122`) — a loop whose first `AstLoopTest` is always false is
  deleted whole, with the `UNUSEDLOOP` warning. This is `t_lint_unusedloop_removed_bad`.
- **`visit(AstExprStmt*)`** (`:3429`) — statements dropped when the result folds to a constant.

All three call `deleteVarScopesUnder` (`:962-974`), which exists for exactly this hazard — its
comment is *"If we delete a branch that contains variable declarations, also delete the
corresponding varscopes so we don't leave dangling AstVarScope::m_varp pointers"*. It cleans up
varscopes and nothing else, so any other pointer to the variable is left dangling. It is also a
no-op pre-scope (`if (!m_scopep) return`), which is where these failures happen.

The invariant, and the fix: **a transform that deletes variables must only run once static
variables have been lifted to module scope.** Until then a statement subtree still holds model
state, so deleting it deletes state. `V3Begin` lifts the statics of blocks and `V3Task` those of
functions and tasks, so `v3Global.staticsLifted(true)` is set immediately after `V3Task::taskAll`
(`Verilator.cpp:403`), alongside the existing `assertDTypesResolved`/`assertScoped` phase flags. All
three sites above now consult `deletableSubtree`, which permits the fold either once statics are
lifted or when the subtree declares nothing. A dead branch that declares something is simply left
for a later `constifyAll` — of which there are eight past the lifting point — to fold.

This is a general correctness fix, not a tracing one: the hazard is that anything else pointing at
such a variable is left dangling, and a tracing descriptor is merely the first thing to have
pointed. Verified inert for existing behaviour: **368 designs across `t_var_*`, `t_lint_*`,
`t_const_*`, `t_case_*`, `t_for*`, `t_func_*` and `t_gen_*` emit byte-identical C++ before and
after**, the whole-suite baseline failure set is unchanged, and `t_lint_unusedloop_removed_bad`
still produces its eleven `UNUSEDLOOP` warnings verbatim.

#### Resolved: forced variables have no address

A variable forced by RTL code has no plain location holding its current value: `V3Force` keeps the
value in a `VlForceVec` and rewrites reads to `forceVec.read(rawVar)`
(`createForceReadExpression`), which it applied to the descriptor's reference too. Legacy tracing
dumps exactly that call — `bufp->chgBit(oldp+0, (t__DOT__zeroize__VforceVec__TOP.read(...)))` — so
it is the clearest real example of the arbitrary-expression tracing that §8 defers to option 2, and
about 45 designs met it. Not only `force`/`release`: procedural `assign`/`deassign` uses the same
machinery, so `t_assign_dff` and friends were in this group too.

The fix materialises the shadow, which is the same trade §8 already accepts for pinning, paid in a
second place. `V3Force` already keeps a plain `__VforceRd` variable in step for `isForceable()`
variables and retargets reads to it, but that is the public force API's en/val machinery and does
not cover a code force. So for a variable a descriptor names that has no `__VforceRd`,
`finalizeRhsVars` now creates `<name>__VforceTrace` plus

```
always_comb <name>__VforceTrace = forceVec.read(<name>);
```

and `ForceReplaceVisitor` retargets a descriptor reference to it — `__VforceRd` when that exists,
`__VforceTrace` otherwise — instead of substituting the expression. The assigned expression is
character-for-character the one legacy computes in its trace change function, so the dumped value is
the same by construction; the `forceVec.touch()` ordering edge is still emitted, since that is
keyed on `__VforceRd`, so the update path is scheduled exactly as before. Value equality still wants
an execution test, which is the Stage 3 gate.

Cost: one variable and one combinational assignment per forced described variable, in descriptor
mode only. Verified inert for existing behaviour — 63 designs across `t_force*`, `t_forceable*`,
`t_assign*`, `t_vpi_force`, `t_verilated_all`, `t_dfg_inline_forced` and `t_alias_force` emit
byte-identical C++ with and without the change at baseline.

#### Deferred: matching a split dump

Refusing to split (above) keeps v1 correct but not identical to legacy, which dumps the pieces
individually — `tmp(-1)`, `tmp(-2)`, … in `t_split_var_0`. Matching that means replacing the array's
descriptor entry with one entry per piece, the same shape as the `V3Inst::dearrayAll` fixup already
in place. Worth doing only if the eval cost of not splitting traced variables turns out to matter,
which is a measurement, not a guess.

#### Noted: declining an optimisation can change what verilates

Two designs verilate at baseline and error in descriptor mode, both because an optimisation was
declined rather than because anything is broken:

- `t_gate_loop` reports `Wire inputs its own output, creating circular logic (wire x=x)`. Keeping a
  variable the DFG would have optimised away is exactly what the pinning hook is for, and the cycle
  it exposes is real.
- `t_func_ref_bad` passes `ref a[1]`, which is only legal because splitting rewrites the
  bit-select into a whole-variable reference; refusing to split leaves the `Sel` and
  `V3Task.cpp:612` rejects it as *"Function/task ref argument is not of allowed type"*.

So **declining an optimisation can turn a design that verilates into one that errors.** Worth
remembering before reading a descriptor-mode failure as a descriptor bug, and worth a line in the
release notes when this becomes the default.

### Cleanliness

`V3Clean` cleans traced values only in `visit(AstTraceInc*)` → `ensureCleanAndNext(valuep)`
(`src/V3Clean.cpp:255-258`), and there will be no `AstTraceInc`s. This is safe because
`AstVarRef::cleanOut()` is `true` (`src/V3AstNodeExpr.h:6413`), i.e. Verilator maintains variable
storage with zero upper bits, so a whole-variable read from raw storage is already clean.

Leaves extracted from inside a packed root are a different matter: the `VL_SEL_*` primitives return
the shifted value without masking, exactly as they do for generated code, which is then followed by
the `AstAnd` that `insertClean` (`src/V3Clean.cpp:124-136`) inserts. The interpreter must apply the
same mask — see §7.1. Getting this wrong is not a crash: the change-detection compare is full-word,
so a stray upper bit produces a spurious value change, visible as a golden mismatch rather than as
an obvious failure. Worth an explicit test with a packed struct whose members are not multiples of
8 bits and whose root exceeds 64 bits, since that combination exercises masking and cross-word spans
together.

### Simplifications this enables

- `PathAdjustor` (`src/V3TraceDecl.cpp:49-102`) and the `AstNode::vcdName()` string-splitting
  disappear — hierarchy becomes structural instead of parsed back out of `__DOT__` names.
- `V3Combine`'s hard `v3fatalSrc` on `AstAddrOfCFunc` (`src/V3Combine.cpp:209-217`) stops being
  load-bearing for tracing.
- `V3InlineCFuncs`' "Contains TraceDecl" `setNoInline` (`src/V3InlineCFuncs.cpp:419-426`) and the
  `isTrace()` inlining budget (`:299`) become moot.
- `splitTraceDeclFuncs` (`src/V3Trace.cpp:368-417`), the sub-function/baseCode plumbing, and the
  whole `m_dtypeFuncs` / `m_dtypeNonConstFuncs` / `createNonConstDtypeTraceFunctions` machinery
  (#6707) are subsumed by data type descriptors.

---

## 10. Parallel world

The two implementations coexist in tree for the whole of the bring-up, and the mode is chosen per
verilation by `--trace-vcd`. The legacy path is untouched and remains the
default until the new one is proven. The option needs a documentation entry or
`t/t_dist_docs_options.py` fails.

This is coexistence *in the compiler*, not two tracing implementations inside one generated model.
Emitting both into a single model would allow one simulation to produce two dumps from identical
stimulus, which is the ideal differential, but it needs two trace file objects bound to the same
model and `traceBaseModel` is a single entry point that would have to grow a mode argument.
`VerilatedTrace::addModel` only rejects a model already added to *that* file
(`m_models.insert(modelp).second`) so it may well be permitted, but this is unverified — worth a
quick experiment during Stage 0, because if it works it is a much sharper bring-up tool than
comparing two separate runs.

Wiring: when set, run `V3Rtmd` after the coverage block and skip `V3TraceDecl`
(`src/Verilator.cpp:426`); both worlds converge at `V3Trace` (`:507`).

**Fork at codegen, not at analysis.** `V3Trace`'s activity analysis — the graph build
(`TraceActivityVertex`, `TraceCFuncVertex`, `graphSimplify`, `graphOptimize`), activity flag
allocation and setter insertion including the coroutine `CAwait` handling
(`src/V3Trace.cpp:59-102, 419-584, 618-669`) — is the subtlest code in the file and both worlds need
it identically. Duplicating it is where silent divergence would hide: a fix applied to one path and
not the other surfaces as a dump mismatch nobody can localize. Split `V3Trace` into an analysis
component plus two codegen backends.

On the runtime side, a new `verilated_trace_table.*` needs at least one test that compiles it,
because `t/t_verilated_all.py` asserts every `include/*.cpp` is compiled by some test.

---

## 11. Testing

The suite is well shaped for a differential. 289 drivers in `test_regress/t/` are tracing-related
(202 named `t_trace*`), of which 201 golden-compare a produced dump. Comparison is *logical*, not
textual: `vcd_identical` (`test_regress/driver.py:2597`) shells out to `wavediff` with
`--epsilon 0.0000001`, `fst_identical` delegates to it (so FST is compared against a VCD-text
golden), and `saif_identical` (`:2611`) runs `nodist/verilator_saif_diff`. `trace_identical`
(`:2622`) dispatches on the produced file's extension. Goldens are 132 VCD-text and 38 SAIF `.out`
files; `copy_if_golden` (`:2591`) with `HARNESS_UPDATE_GOLDEN=1` is the bulk regolden lever.

### The requirement: every trace test runs both ways, outputs match

Three tiers, because "all trace tests" covers more than the commons-structured ones:

1. **A global driver flag for whole-suite sweeps.** There is exact precedent: `driver.py --trace`
   (declared at `:3038`) appends `--trace-vcd` to *every* test's verilator flags at `:1170`. A
   `--trace-vcd` flag slots into the same place, so a single command runs the entire regression in
   descriptor mode. This is the mechanism that makes "all trace tests, both ways" a one-liner in CI
   rather than 289 per-test edits.
2. **A `_descriptor` variant in the commons for always-on coverage.** The trace commons already fan out
   over `{cc,sc} × {vcd,fst,saif} ×` variants via `parse_name`, and variants share one golden:
   ```python
   test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"
   ```
   so `_noinl`, `_portable` and `_cmake` all compare against the same file. A `_descriptor` variant that
   flips the option and compares to the *same* golden gives a direct A/B over ~200 golden dumps for
   a few lines per common module, running in normal CI rather than only in sweeps.
3. **An explicit opt-out list** for the tests that cannot match by construction — the ~15 that grep
   generated C++ for functions the descriptor path does not emit (table below). These need
   mode-awareness or exclusion; regoldening cannot help them.

### What "outputs match" actually requires

Dump comparison is *logical*, not textual, in both formats: `vcd_identical` shells out to `wavediff`
(which is why an FST can be compared against a VCD-text golden at all), and `saif_identical` runs
`nodist/verilator_saif_diff`, which compares the INSTANCE/NET/SIGNAL tree and toggle counts
structurally. No test does `files_identical` on a dump.

So the requirement reduces to: **the same set of signals, at the same hierarchical names, with the
same widths and the same values at the same times.** Declaration order and VCD identifier codes are
free, and scope *kinds* are probably free too.

**This corrects an earlier claim in this document that a bulk regolden should be expected.** Because
the comparison is logical, the declaration-order change from building descriptors early costs
nothing. What is *not* free is any change to the signal set or to hierarchical names — and that is
exactly what the #7001 fidelity improvements (proper generate/begin/function/task scope kinds, real
module type names) would touch. Two consequences:

- **v1 must reproduce today's hierarchy exactly**, using the early anchor for access to the
  information without yet changing what is emitted. Today's hierarchy is already largely correct:
  `PathAdjustor` reconstructs nested scopes by splitting `__DOT__`-derived names
  (`src/V3TraceDecl.cpp:49-102`), so what #7001 fixes is mainly scope *kind* (everything is
  `SCOPE_MODULE` today) rather than scope structure. Keeping v1 output-identical is what makes the
  differential interpretable: any mismatch is a bug, never an intended improvement.
- **The #7001 improvements get their own stage** with their own deliberate golden update
  (§13, Stage 7). Whether `wavediff` tolerates scope-kind differences determines whether that stage
  needs a regolden at all, and that is worth establishing empirically in Stage 0 — `wavediff` is an
  external prerequisite (hudson-trading/wavetools, per `docs/internals.rst:1572`), not in-tree, so
  its exact tolerance cannot be read off the source.

**Roughly 15 drivers need rewriting, not regoldening**, because they grep generated C++ for
structures that cease to exist:

| Test(s) | Assertion |
|---|---|
| 8 × `t_trace_complex_structs_*` | `trace_complex_common.py:38-39` greps `__Trace__0.cpp` for `Vt_.*trace_chg_dtype.*v_strp2` |
| 3 × `t_trace_split_struct_*` | `trace_split_struct_common.py:21-23` asserts **zero** `trace_chg_dtype` |
| `t_mem_trace_split` | `:17-21` counts `void Vt.*trace_chg_.*sub.*{` (3 if vltmt else 1) |
| `t_trace_ena_cc` | `:20-21` greps `__Trace__0__Slow.cpp` for signal-name strings |
| `t_trace_huge_array` | `:17-19` requires ≥10 `*Trace*.cpp` files |
| `t_trace_decoration` | `:18` `--no-decoration` check |

**Order-sensitive tests to watch.** These bypass the logical comparison and inspect dump text
directly, so they *are* sensitive to declaration order and code allocation even though the golden
compares are not:

- `trace_hier_block_common.py:74-86` — a line-by-line `$var` header diff between hierarchical and
  non-hierarchical builds, normalising only the id code. This asserts exact `$var` ordering, so it
  constrains v1 more tightly than the goldens do.
- `t_trace_vif_class_clk{,_multi}` — `file_grep_count(trace_filename, r'(?m)^1[!-~]$', 5)` counts
  single-bit value-change lines, so it depends on which codes got the short identifiers.
- The dump-content greps: `t_trace_max`, `t_trace_depth`, `t_trace_empty`, `t_var_escape*`,
  `t_time_vpi_*`.

Because runtime code allocation (§7.3) walks the descriptors in declaration order, matching today's
allocation means matching today's declaration order — which is a stronger constraint than "the
waveforms are logically equal", and it is these tests that will enforce it. The runtime policy
decisions (§7.2) must also reproduce today's outcomes exactly for the differential to hold: the
descriptor-mode defaults have to make `--trace-structs`, `--trace-max-width` and `--trace-max-array`
behave identically to the verilate-time versions, including edge cases like which level of a nested
packed aggregate gets collapsed.

**Cross-cutting equivalences the shared goldens encode**, all of which must continue to hold: cc ==
sc, vcd/fst/saif from one source, `-fno-inline` == inlined, cmake == gmake, `VL_PORTABLE_ONLY` ==
optimised, vlt == vltmt, hierarchical == non-hierarchical, `--lib-create` == monolithic, and split
(`--output-split-ctrace N`) == unsplit.

### Rtmd-specific tests to add

The existing suite exercises these constructs, but only through the legacy path, and it checks
dumps rather than descriptors. Each case below wants a test that runs in descriptor mode and
asserts on the descriptors themselves, which `--dump-tree` makes checkable without waiting for
emission to exist. Checking descriptors rather than generated C++ also keeps these tests useful
after the legacy path is deleted.

- **Type sharing.** Two signals of an identical multi-dimensional packed array type must reference
  one `AstRtmdType`, as must two signals of one struct type. The suite probes this only
  indirectly today via `t_trace_type_dupes_*`, `t_trace_struct_alias_*`,
  `t_trace_struct_array_multi_inst_*` and `t_trace_type_alias`.
- **Interface reference arrays.** An array of interface references, either as a port
  (`module sub(ifc i[2])`) or as a variable, is currently described as *nothing*: the data type is
  an unpacked array of `AstIfaceRefDType`, which the type builder cannot describe, so the variable
  is dropped as untraceable and the interface contents never appear. The scalar cases are covered
  (a direct reference, a port, a modport port, and a port chain), so this is the gap. Note
  `t_interface_ar3.v` and `t_interface_dearray_bad.v` currently fail in Verilator *before*
  reaching any of this (`V3Inst.cpp:484: No interface varref under array`), so the test must use a
  shape that elaborates, and the fix belongs with whatever makes arrays of interfaces work
  generally.
- **Arrayed instances.** `V3Inst::dearrayAll` must replace the one entry naming an arrayed cell
  with one entry per element, each linked to its own element's descriptor. Worth asserting the
  element names are the trace-visible `arr[0]`/`arr[1]` rather than the internal
  `arr__BRA__0__KET__`.
- **Per-instance interface resolution.** Two instances of one module connected to different
  interfaces must have their descriptors linked to different interface descriptors. A module-level
  answer cannot express this, so it is the case that proves the linking happens per instance.
- **Generate and begin blocks.** A named generate block must produce a push/pop pair around its
  contents rather than a flattened name, which is what the early anchor buys.
- **Inlining invariance.** The trace hierarchy a descriptor set describes must be identical with
  and without `-fno-inline`, for every construct above. This is the sharpest available check on the
  `V3Inline` splice, and unlike the others it needs no golden file — the two runs check each other.
- **Design ports.** A design with top-level ports must place the wrapper's primary IOs under a
  `$rootio` level, and a design with none must not emit an empty `$rootio` level at all.
- **`.vlt` scope rules.** `t_trace_scope_vlt` and `t_trace_scope_no_inline` are the two designs whose
  goldens turn on `-levels` counting, re-enabling a subtree, and disabling one variable in one
  instance path (`*.sub2a.ADD`). Both must come out of the prune pass matching their legacy golden
  exactly, inlined and not — the `-levels` cases fail loudly if the matched path string is off by a
  component. A `tracing_off` region around one instance is the companion case, since it is the one
  that must leave *no* descriptor rather than an empty one.

Until emission exists, a cheap and broad check is to run the existing `t_*.v` sources through
`--trace-vcd` and require no internal errors. That sweep is what found the port-chain and
arrayed-instance gaps, and it costs nothing to keep running as the pass grows. Its stronger form —
worth automating early — is to flatten the final descriptors from `--dump-tree` into a path list
(walking push/pop and following instance and interface-reference links, with a canonical string per
data type) and diff the inlined against the `-fno-inline` run of the same design. Over the 187
`t_interface*`/`t_trace*` designs that verilate today those lists are byte-identical, which
exercises the splice, the de-array fixup, the per-instance interface links and type sharing all at
once. The same flattener is what will diff a descriptor dump against a legacy VCD's scope tree once
emission exists.

---

## 12. Measurement

RTLMeter is checked out at `/home/glore/work/rtlmeter` with BlackParrot, Caliptra, NVDLA, OpenPiton,
OpenTitan, Servant, VeeR-EH1/EH2/EL2, Vortex, XiangShan and XuanTie-C906/C910/E902/E906.

**It has no tracing configuration** — no design or runner option mentions tracing — so building one
is a prerequisite task, not free. `rtlmeter run` does accept `--compileArgs` / `--executeArgs`, so
trace-enabled cases can be injected, but actually enabling dumping needs per-design harness work.

Mechanics worth remembering: use `--nCompile` (repeating `--nExecute` does not repeat compiles, so
verilate and C++ compile times would be n=1 noise), and put `--workRoot` under `/home/glore/work`
rather than `/tmp`.

Metrics per design, legacy vs descriptor mode, VCD and FST, single-threaded and `--threads`:

- generated trace `.cpp` line count and file count; `.o`/binary size
- verilation wall time and peak RSS; C++ compile wall time
- trace-on simulation throughput
- **runtime table memory** (§3)
- **eval throughput and model state size** — expected to regress from pinning (§8); this is the
  number that justifies option 2
- sharing effectiveness: unique type descriptors vs signal entries; unique scope descriptors vs
  instances
- anything that trips the bring-up assert

Validate `--threads` tracing under TSAN; OpenTitan is a good signal there since its cycle counts are
deterministic again after #7913.

---

## 13. Milestones

1. **Stage 0 — baselines, encoding prototype, and harness questions.** Build the RTLMeter tracing
   configuration and capture baselines. Hand-write a runtime interpreter against a hand-built table
   for one small design and diff the VCD, to settle row packing and the type-expansion rules before
   touching any pass. Two harness questions to settle here because they shape later stages: whether
   `wavediff` tolerates scope-kind differences (§11), and whether one model can be bound to two
   trace files so a single run can dump both ways (§10).
2. **Stage 1 — option, nodes, `V3Rtmd`, plumbing.** The option; the descriptor nodes and
   `VRtmdScopeKind`; `AstTypeTable::rtmdTypesp`; `V3Rtmd` building type descriptors (with
   uniquing and structural dedup) and scope descriptors; the top wrapper descriptor; the
   `V3Inst::dearrayAll` fixup; `V3Inline` splicing; the `V3Scope` visitor and `V3LinkDot`
   interface-reference resolution; the prune pass; the `V3Undriven`/`V3Descope`/`V3EmitV` guards;
   the pinning hooks in `V3Gate`, `V3Localize` and the DFG; `broken()` checks; the pass audit (§9).
   No emit yet — validate by dumping the tree, diffing the derived hierarchy inlined against
   `-fno-inline`, and comparing it against what `V3TraceDecl` produces for the same design. Closes
   with the two items the audit left open: forced variables and split unpacked arrays.
3. **Stage 2 — declarations end to end.** Generated type and scope tables, enum descriptors,
   `PARTITION`, runtime elaboration and expansion, runtime code allocation with `valueId` aliasing,
   declaration replay.
4. **Stage 3 — dumping end to end.** Entry materialisation, packed extraction (§7.1), activity
   groups, const entries, generic cleanup, the hot loop (fidx partitioning deferred, §7.4). Gate:
   the whole
   trace suite passing in both modes, via the global flag *and* the always-on `_descriptor` variants
   (§11), with no golden changes; RTLMeter perf and memory within agreed bounds. Output must be
   hierarchy-identical to the legacy path at this stage — no fidelity improvements yet.
5. **Stage 4 — scope dedup.** Hashing and sharing of identical scope descriptors (type sharing is
   already in from Stage 1). Gate: object-size improvement measured; dumps unchanged.
6. **Stage 5 — option 2.** Trace-only prologue writing `__VtraceTmp`, removing the pinning and
   recovering the eval regression; then let `V3SplitVar` split traced variables.
7. **Stage 6 — hierarchy fidelity (#7001).** Only now start *using* the source-level information the
   early anchor made available: proper generate / begin / function / task scope kinds, real module
   type names, statics inside functions and tasks. This is the first stage that may deliberately
   change dump content, so it carries its own golden update and cannot be mixed into the
   differential stages above. Requires extending the runtime `VerilatedTracePrefixType`
   (`include/verilated_trace.h:50-60`).
8. **Stage 7 — retire the legacy path** once the differential has been clean for a release cycle.
   Delete `AstTraceDecl`, `AstTraceInc`, `AstTracePushPrefix`, `AstTracePopPrefix`, `VTraceType`,
   `V3TraceDecl`, `V3Trace`'s codegen half, `EmitCTrace`, `EmitCTraceTypes`, the `VL_TRACE_DECL_*` /
   `VL_TRACE_PUSH_PREFIX` macro layers, and the trace-specific special cases in `V3Clean`,
   `V3Hasher`, `V3InlineCFuncs`, `V3Combine`, `V3Undriven` and `V3EmitV`. The descriptor nodes are then
   the only tracing-related ones.

---

## 14. Open questions

### Decided

- **The scope descriptor is a bare node**, not hung under an `AstCFunc`. The pass audit in §9 is
  therefore committed work rather than an alternative, and is enumerated there.
- **Interface references are not a special problem.** Interfaces are never inlined —
  `V3Inline.cpp:268` hard-marks them: `if (VN_IS(nodep, Iface)) vtxp->setNoInlineHard("Interface");`
  — so an interface instance always survives as a distinct module with its own struct in the Syms
  class, and Emit can address it with the ordinary `offsetof(SymsClass, scopeMember)` that every
  other instance entry uses. That removes the addressing half of the problem entirely, and with it
  the reason today's code reconstructs a path string and looks it up.
  What remains is identification: which interface instance a given reference resolves to in a given
  scope. `AstIfaceRefDType` carries both `ifacep()` and `cellp()`, with *"cellp() should override"*
  (`src/V3AstNodeDType.h:898`), and `V3LinkDot` already treats `ifaceRefp->cellp()` as authoritative
  (`:975`). So the sub-question for Stage 1 is narrow: whether `cellp()` is populated for every
  traced interface-ref VarScope after `linkDotScope` (359), or whether module-*port* references —
  where `cellp()` can be null, per the `if (!ifacerefp->cellp())` guard in
  `V3LinkLevel::wrapTopCell` — still need the name-based `AstIntfRef` mapping that `V3Interface`
  builds. Pointer-based where possible is strictly more robust than today's string paths, which is
  what makes the `src/V3TraceDecl.cpp:766-772` TODO about upward and sideways propagation moot.
  Virtual interfaces resolve to nothing today (the synthesised path matches no scope, so
  `fixupPlaceholder` deletes the placeholder), so emitting nothing for them preserves behaviour.
  Probes: `t_trace_interface_ref_*` (8 drivers, all four inline permutations) and
  `t_trace_vif_class_clk*`.

### Multi-model init: what `initLib` needs

This is the one remaining area needing design before Stage 1, and it is also where the current
mechanism has a latent fragility worth fixing rather than porting.

**How it works today.** Every model registers a `traceBaseModelCb` on the context when constructed
(`src/V3EmitCModel.cpp:315-317`), and `VerilatedContext::trace()` invokes all of them
(`include/verilated.cpp:3802`), each doing `addModel` + `addInitCb(cb, userp, name(), isLibInstance,
nTraceCodes)` + `trace_register`. Then `traceInit` runs *every* registered init callback as a root:
`for (size_t i = 0; i < m_initCbs.size(); ++i) runInitCallback(i, true);`
(`include/verilated_trace_imp.h:135`). A parent's walk reaches its child via generated code emitting
`tracep->initLib(__VlibName)` (`V3TraceDecl::fixupLibStub`), which matches on
`m_initCbs[i].m_name` and runs that callback with `rootInit=false`
(`include/verilated_trace_imp.h:437-444`). The `m_initCbsCalled` guard then makes the outer loop
skip it.

So nesting is correct **only if the parent is registered before the child**: whoever gets there
first decides whether the child is traced nested or as a root. `CallbackRecord::m_isLibInstance`
looks like it was meant to disambiguate this, but it is **dead — stored in the constructor and never
read anywhere in `src/` or `include/`**. It also could not simply mean "skip in the root loop",
because `t_trace_lib_as_top_*` requires a library to be traceable *as* a root when nobody claims it.

**What the descriptor design needs.**

1. **A name-to-tables registry** replacing the name-to-callback match. The runtime must compose the
   same string the generated code does today (parent instance name, `'.'`, cell pretty name) from
   the `PARTITION` row and the parent's instance name.
2. **Resolve root-vs-nested up front, not by arrival order.** Because every parent's `PARTITION` rows
   are *data*, the runtime can scan all registered models before walking any of them, collect the
   set of names claimed by some parent, and then walk as roots only the models nobody claimed. That
   is order-independent, handles as-top and embedded use with the same rule, and lets
   `m_isLibInstance` be deleted rather than reimplemented. This is a small behavioural improvement
   over today, so it wants its own test — two libraries, or a library constructed before its parent.
3. **Per-model context during the walk.** `m_initUserp` is not just bookkeeping: FST keys its
   enum-type map on it (`m_local2fstdtype.at(initUserp())`). The walk must maintain an equivalent
   current-model handle, or enum references break for multi-model traces.
4. **`rootInit` logic must move from code into data.** It currently lives in the generated
   `trace_init` (`src/V3EmitCModel.cpp:561-580`): when rooted, push the instance name, call
   `trace_init_root`, then push the library's top name. In descriptor form that is a root-phase entry
   range and a top-phase entry range plus conditional scope entries — the existing
   `trace_init_leaf_root__*` / `trace_init_leaf_top__*` split (`src/V3TraceDecl.cpp:313-316`)
   expressed as data.
5. **`sameRootInitAlias` becomes `valueId` aliasing.** Today the wrapper IO codes are matched to the
   top module's by name, direction, width and range (`src/V3Trace.cpp:244-254`); with explicit value
   ids the root-phase and top-phase entries for one IO simply share an id. Intra-model, so no
   cross-model code sharing is needed.
6. **`m_nTraceCodes` and `__Vm_baseCode` disappear.** `runInitCallback` currently pre-reserves each
   model's code range before invoking it; with runtime allocation each model's codes are allocated
   when that model is processed. Determinism across reopen is preserved because the walk is
   deterministic, which is what the reopen check relied on.
7. **A library compiled without tracing must stay a silent no-op** — today `initLib` simply finds no
   matching name ("Note it's possible the instance doesn't exist if the lib was compiled without
   tracing").

Probes: `t_trace_lib_*` (6), `t_trace_lib_as_top_*` (3), plus `t_trace_hier_block_*` (12) and
`t_trace_hier_*` (6), since hierarchical blocks are separate models reaching the same machinery.

### Tuning and smaller items

- Row packing: single tagged union vs per-op arrays; 16 vs 24 bytes; chunk size. Stage 0.
- Whether `AstRtmdScope` should reuse and extend `VTracePrefixType` rather than introducing
  `VRtmdScopeKind` — the runtime `VerilatedTracePrefixType` has to grow the
  generate/block/function/task values either way.
- Whether any non-wrapper SC-typed variable can reach a traced signal (§8).
- Whether `V3Randomize`/`V3Assert` (`src/Verilator.cpp:250-269`, now downstream of the anchor)
  introduce user-visible traced signals that would be missed. Probes: `t_cover_sva_trace`,
  `t_cover_line_trace`, `t_cover_trace_always`.
- Interface references remain the messiest corner. `V3Interface` runs after `V3Inline` and only for
  tracing, and today's `m_pathToScopep` carries a TODO admitting it is "not actually correct" for
  interfaces propagated via downward hierarchical refs (`src/V3TraceDecl.cpp:766-772`).
- 32-bit vs 64-bit offsets for very large Syms.
- `--output-split-ctrace` semantics for the tabled part (chunking) vs the legacy path.
- Docs: `docs/guide/files.rst` lists generated file names; `docs/internals.rst` describes the trace
  flow in passing.
