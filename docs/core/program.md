# The program, its values and the launch

How the model represents a kernel before it runs: the parsed PTX source, its decoding into typed instructions, the values and bytes that registers and memory hold, and the launch that fixes the grid. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [Source and decoding](#source-and-decoding)
    - [`Syntax.Module`](#c-syntax-module)
    - [`Syntax.Function`](#c-syntax-function)
    - [`Syntax.Statement`](#c-syntax-statement)
    - [`Syntax.Operand`](#c-syntax-operand)
    - [`module`](#c-module)
  - [Kernel and instructions](#kernel-and-instructions)
    - [`Kernel`](#c-kernel)
    - [`Instr`](#c-instr)
    - [`Op`](#c-op)
    - [`Opnd`](#c-opnd)
    - [`FloatFmt`](#c-floatfmt)
    - [`Space`](#c-space)
    - [`SReg`](#c-sreg)
    - [`Op.isLocal`](#c-op-islocal)
    - [`Op.aligned`](#c-op-aligned)
    - [`Op.uniform`](#c-op-uniform)
    - [`UniformScope`](#c-uniformscope)
  - [Values and bytes](#values-and-bytes)
    - [`Value`](#c-value)
    - [`FVal`](#c-fval)
    - [`Layout`](#c-layout)
    - [`PtrTarget`](#c-ptrtarget)
    - [`Value.bytes`](#c-value-bytes)
    - [`Value.byteAt`](#c-value-byteat)
    - [`Value.toBytes`](#c-value-tobytes)
    - [`Byte`](#c-byte)
    - [`ClcResponse`](#c-clcresponse)
    - [`Fault`](#c-fault)
    - [`Exec`](#c-exec)
  - [Locations, launch and initial memory](#locations-launch-and-initial-memory)
    - [`Loc`](#c-loc)
    - [`Acc`](#c-acc)
    - [`Acc.Overlap`](#c-acc-overlap)
    - [`Launch`](#c-launch)
    - [`Launch.threads`](#c-launch-threads)
    - [`Mem0`](#c-mem0)
- [Rules](#rules)
  - [The program text](#the-program-text)
    - [the parsed PTX source](#prog-syntax) (`PROG-SYNTAX`)
    - [modifier tokens and slots](#prog-isa-token) (`PROG-ISA-TOKEN`)
    - [instruction entries](#prog-isa-entry) (`PROG-ISA-ENTRY`)
    - [legal modifier combinations](#prog-isa-constraint) (`PROG-ISA-CONSTRAINT`)
    - [recognizing an instruction](#prog-isa-grammar) (`PROG-ISA-GRAMMAR`)
    - [from source to instructions](#prog-decode) (`PROG-DECODE`)
      - [shared memory layout](#ext-shared) (`EXT-SHARED`)
      - [local and constant variable layout](#ext-local-const-layout) (`EXT-LOCAL-CONST-LAYOUT`)
  - [Instructions](#instructions)
    - [the supported instruction forms](#prog-instr-forms) (`PROG-INSTR-FORMS`)
    - [which instructions perform events](#prog-instr-events) (`PROG-INSTR-EVENTS`)
  - [Values and bytes](#values-and-bytes)
    - [register values](#thread-value) (`THREAD-VALUE`)
    - [floating and fixed-point layouts](#thread-float-format) (`THREAD-FLOAT-FORMAT`)
    - [memory bytes](#mem-byte) (`MEM-BYTE`)
      - [byte order](#ext-endian) (`EXT-ENDIAN`)
    - [opaque cancellation response](#obj-clc-response) (`OBJ-CLC-RESPONSE`)
    - [undefined behaviour of one instruction](#err-fault-reason) (`ERR-FAULT-REASON`)
  - [Locations and the launch](#locations-and-the-launch)
    - [locations and footprints](#mem-location) (`MEM-LOCATION`)
    - [the launch](#prog-launch) (`PROG-LAUNCH`)
    - [memory at launch](#prog-launch-memory) (`PROG-LAUNCH-MEMORY`)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### Source and decoding

The parsed PTX source and the decoder that turns it into a kernel.

<a id="c-syntax-module"></a>
#### `Syntax.Module`

*structure*

A parsed PTX module: its directives, global declarations and functions.

- `sourceSha256`
- `directives`
- `globals`: Module-scope declarations other than functions, e.g. `.extern .shared` arrays.
- `functions`

[Lean source: `Core/Source/Syntax.lean` L67-L74](../../Core/Source/Syntax.lean#L67-L74)

<a id="c-syntax-function"></a>
#### `Syntax.Function`

*structure*

A function of the module: its name, header tokens and body statements.

- `name`
- `header`
- `body`

[Lean source: `Core/Source/Syntax.lean` L60-L65](../../Core/Source/Syntax.lean#L60-L65)

<a id="c-syntax-statement"></a>
#### `Syntax.Statement`

*inductive*

One statement of a function body: an instruction with its optional guard predicate, a label,
a declaration, a directive, or a nested scope.

- `instruction`: `predicate = some (register, negated)`.
- `label`
- `declaration`
- `directive`
- `scope`

[Lean source: `Core/Source/Syntax.lean` L49-L58](../../Core/Source/Syntax.lean#L49-L58)

<a id="c-syntax-operand"></a>
#### `Syntax.Operand`

*inductive*

An instruction operand as spelled in the source: a register, a symbol, a literal, the sink `_`,
an address, a vector, a base with a signed offset, a negation, or a pair.

- `register`
- `symbol`
- `literal`
- `sink`
- `address`
- `vector`
- `offset`
- `negate`
- `pair`

[Lean source: `Core/Source/Syntax.lean` L35-L47](../../Core/Source/Syntax.lean#L35-L47)

<a id="c-module"></a>
#### `module`

*def*

Decode kernel `f` of module `m`: the module's target, then the kernel.

[Lean source: `Core/Source/Decode.lean` L867-L870](../../Core/Source/Decode.lean#L867-L870)

### Kernel and instructions

The typed program that the model executes.

<a id="c-kernel"></a>
#### `Kernel`

*structure*

A decoded kernel: parameters, static shared memory size, parameter objects, launch
constraints, register names and the instruction list, whose indices are the source positions.

- `name`
- `params`: Parameter names and their widths in bits.
- `sharedBytes`: Bytes of statically declared `.shared` memory per CTA.
- `paramObjects`: By-value array parameters, separate from scalar parameter values.
- `ptrParams`: The `.ptr` attributes of pointer parameters that constrain a launch (a state space or an alignment above 1), by parameter name.
- `maxThreads`: `.maxntid` bound on the CTA size (the product of its extents), if declared.
- `reqThreads`: `.reqntid` CTA shape `(nx, ny, nz)`, if declared; an extent not written is 1.
- `minPerCtaMemory`: `.minperctamemory` size in bytes, if declared (§11.5.10); the `%perctamemory` registers decode only when it is.
- `regNames`: The source name of each register, by id; for diagnostics only.
- `code`

[Lean source: `Core/Source/Instr.lean` L292-L315](../../Core/Source/Instr.lean#L292-L315)

<a id="c-instr"></a>
#### `Instr`

*structure*

One instruction of a kernel: an optional guard predicate and the operation.

- `guard`: `some (p, negated)`: execute only when predicate `p` is true (or false if negated).
- `op`

[Lean source: `Core/Source/Instr.lean` L272-L277](../../Core/Source/Instr.lean#L272-L277)

<a id="c-op"></a>
#### `Op`

*inductive*

The supported instruction forms with their decoded qualifiers and operands: local arithmetic,
moves and branches, memory accesses, barriers, mbarrier and bulk-copy operations, tensor copies,
cluster launch control and `tcgen05`.

- `prefetchTensorMap`: Prefetch a tensormap through a generic or explicit parameter-space address.
- `prefetchTensor`: `cp.async.bulk.prefetch.tensor.<n>d.L2.global{.tile, .tile::gather4}{.L2::cache_hint} [map, coords]{, cachePolicy}`: an L2 prefetch of tensor data.
- `setMaxReg`
- `int`: An integer, bit, logic, comparison or selection instruction (PROG-ISA-INT).
- `move`: A register move, pack or unpack (PROG-ISA-MOVE).
- `cvt`: A conversion (PROG-ISA-CVT).
- `mem`: A load, store, atomic or reduction (PROG-ISA-MEM).
- `addr`: An address conversion or query (PROG-ISA-MEM).
- `warp`: A warp collective (PROG-ISA-WARP).
- `matrix`: A warp-level matrix instruction (PROG-ISA-MATRIX).
- `misc`: `createpolicy`, `nanosleep` or `pmevent` (PROG-ISA-MISC).
- `float`: A floating-point, half-precision or mixed-precision instruction (PROG-ISA-FLOAT).
- `barSync`: `bar.sync a` / `barrier.sync{.aligned} a` without a thread count: the whole CTA. `aligned` is set for `bar.sync` and `barrier.sync.aligned` (§9.7.15.1: `bar.sync` is `barrier.sync.aligned`).
- `barSyncN`: `bar.sync a, b` / `barrier.sync{.aligned} a, b` with an explicit thread count `b`.
- `barArrive`: `bar.arrive a, b` / `barrier.arrive{.aligned} a, b`: arrival at barrier `a` with thread count `b`, without waiting for the other participating warps (§9.7.15.1: `bar.arrive` is `barrier.arrive.aligned`).
- `cluster`
- `bra`: `bra{.uni} target`; `uni` records the `.uni` qualifier (§9.7.14.3: the branch is non-divergent).
- `brx`: `brx.idx{.uni} index, tlist`: a branch to entry `index` of the `.branchtargets` table.
- `ret`: `ret`.
- `exit`: `exit`.
- `trap`: `trap`.
- `cpTensor`: `cp.async.bulk.tensor.<n>d` global-to-shared load: `.tile` with `n` coordinates (inner first), or `.2d.tile::gather4` with `{x, y0, y1, y2, y3}`; `multicast` is `.multicast::cluster`'s ctaMask operand and its width in bits (16 or 32); `cachePolicy` is the 64-bit operand of `.L2::cache_hint`.
- `cpTensorStore`: `n`-D shared-to-global store: `.tile` with `n` coordinates, or `.2d.tile::scatter4` with `{x, y0, y1, y2, y3}`; cache policy is an optional 64-bit hint. With `reduce`, `cp.reduce.async.bulk.tensor.<n>d.global.shared::cta.<redOp>{.tile}.bulk_group`: each element is reduced into the tensor instead of stored.
- `bulkCommit`
- `bulkWait`
- `clcTryCancel`
- `clcQuery`
- `mbarInit`: `mbarrier.init.shared::cta.b64 [base + offset], count`.
- `mbarInval`: `mbarrier.inval.shared::cta.b64 [base + offset]`.
- `fence`: A thread fence (also `membar`) or a proxy fence (PROG-ISA-FENCE).
- `fenceMbarInit`: Restricted release of this thread's preceding local mbarrier initialization.
- `mbarArrive`: `mbarrier.arrive{.sem}{.scope}{.expect_tx}.shared{::cta,::cluster}.b64 state, [base + offset]` with optional count and transaction operands: `count` arrivals after expecting `tx` bytes. `cluster` selects a `shared::cluster` address. `state` is the destination register, `none` for the sink `_`. Defaults are the PTX defaults.
- `cpBulk`: `cp.async.bulk{.sem.scope}.dst.src.completion{...} [dstMem], [srcMem], size, ...` in any direction, and `cp.reduce.async.bulk` (`BulkCopy`).
- `asyncStore`: `st.async` and `red.async` (`AsyncStore`).
- `cpAsync`: `cp.async.{ca,cg}.shared{::cta}.global [dst], [src], cp-size{, src-size | ignore-src}{, cache_policy}` with `cp-size` 4, 8 or 16; the cache operator and prefetch-size hints are dropped.
- `cpAsyncCommit`: `cp.async.commit_group`.
- `cpAsyncWait`: `cp.async.wait_group N` (`all` false) or `cp.async.wait_all` (`all` true, `remaining` 0).
- `cpAsyncArrive`: `cp.async.mbarrier.arrive{.noinc}{.shared{::cta}}.b64 [base + offset]`; `generic` when no state space is written.
- `prefetchBulk`: `cp.async.bulk.prefetch.L2.global{.L2::cache_hint, .L2::evict_last} [src], size{, cachePolicy}`.
- `mbarWait`: `mbarrier.try_wait.parity{.sem}{.scope}.shared{::cta}.b64 p, [base + offset], parity{, hint}`. The suspend-time hint is dropped. Defaults are the PTX defaults (`.acquire.cta`).
- `tcAlloc`: `tcgen05.alloc.cta_group::{1,2}.sync.aligned.shared::cta.b32 [base + offset], n`.
- `tcDealloc`: `tcgen05.dealloc.cta_group::{1,2}.sync.aligned.b32 taddr, n`.
- `tcRelinquish`: `tcgen05.relinquish_alloc_permit.cta_group::{1,2}.sync.aligned`.
- `tcMma`: `tcgen05.mma` in every form of the instruction table (PROG-ISA-TC-MMA).
- `tcCommit`: `tcgen05.commit.cta_group::{1,2}.mbarrier::arrive::one.shared::cluster{.multicast::cluster}.b64 [base + offset]{, mask}`.
- `tcFenceBefore`: `tcgen05.fence::before_thread_sync`.
- `tcFenceAfter`: `tcgen05.fence::after_thread_sync`.
- `tcLd`: `tcgen05.ld.sync.aligned.<shape>.x<num>.b32 {d0, ...}, [taddr]{, immHalfSplitoff}`. The shape is last and defaults to `.32x32b`, so a program written before shapes existed keeps its text. With `red`, `tcgen05.ld.red` (PROG-ISA-TC-LD-RED).
- `tcWaitLd`: `tcgen05.wait::ld.sync.aligned`.
- `tcSt`: `tcgen05.st.sync.aligned.<shape>.x<num>.b32 [taddr], {immHalfSplitoff,} {s0, ...}`; the shape as for `tcLd`.
- `tcWaitSt`: `tcgen05.wait::st.sync.aligned`.
- `tcCp`: `tcgen05.cp.cta_group::{1,2}.<shape>{.<multicast>}{.b8x16.<src_fmt>} [taddr], s-desc` (PROG-ISA-TC-CP); `fmt` is the decompression, none when not written.
- `tcShift`: `tcgen05.shift.cta_group::{1,2}.down [taddr]` (§9.7.18.9.3).
- `unmodeled`: An instruction recognized by the grammar that has no family representation this round (PROG-DECODE); no rule gives it semantics.

[Lean source: `Core/Source/Instr.lean` L127-L270](../../Core/Source/Instr.lean#L127-L270)

<a id="c-opnd"></a>
#### `Opnd`

*inductive*

A source operand of an instruction: a register, an integer or binary32 literal, a special
register, or the address of a `.shared` variable, `.local` variable or kernel parameter.

- `reg`: A register, by its id: its index in the kernel's declared-register order (`Kernel.regNames`).
- `imm`
- `f32imm`: A `0fXXXXXXXX` literal: raw binary32 pattern, decoded exactly.
- `sreg`
- `sharedSym`: Address of a `.shared` variable: the launch's shared window base plus `offset`.
- `localSym`: Address of a `.local` variable: the launch's local base plus `offset`.
- `paramSym`: Address of a kernel parameter object, not the value stored in it.

[Lean source: `Core/Source/Operand.lean` L56-L72](../../Core/Source/Operand.lean#L56-L72)

<a id="c-floatfmt"></a>
#### `FloatFmt`

*inductive*

A floating-point format of a data type: `f16`, `bf16`, `f32`, `f64`, `e4m3` or `e5m2`.

- `f16`
- `bf16`
- `f32`
- `f64`
- `e4m3`
- `e5m2`

[Lean source: `Core/Isa/Types.lean` L47-L50](../../Core/Isa/Types.lean#L47-L50)

<a id="c-space"></a>
#### `Space`

*inductive*

State spaces of memory locations in this model: global, shared, a thread's local memory and
constant memory.

- `global`
- `shared`
- `const`

[Lean source: `Core/Isa/Types.lean` L64-L68](../../Core/Isa/Types.lean#L64-L68)

<a id="c-sreg"></a>
#### `SReg`

*structure*

A special register operand: its name and, for a vector register, the component.

- `name`
- `dim`

[Lean source: `Core/Isa/SReg.lean` L64-L68](../../Core/Isa/SReg.lean#L64-L68)

<a id="c-op-islocal"></a>
#### `Op.isLocal`

*def*

The instruction only reads and writes the thread's registers and source position, and
performs no event.

[Lean source: `Core/Source/Instr.lean` L381-L398](../../Core/Source/Instr.lean#L381-L398)

<a id="c-op-aligned"></a>
#### `Op.aligned`

*def*

The instruction carries `.aligned`: all threads of the warp execute it together.

[Lean source: `Core/Source/Instr.lean` L471-L477](../../Core/Source/Instr.lean#L471-L477)

<a id="c-op-uniform"></a>
#### `Op.uniform`

*def*

The instruction requires a warp-uniform guard: `bra.uni`, `brx.idx.uni`, `shfl.sync`,
`vote.sync`, `redux.sync`, `match.sync` or an `.aligned` instruction.

[Lean source: `Core/Sync/WarpUniform.lean` L219-L226](../../Core/Sync/WarpUniform.lean#L219-L226)

<a id="c-uniformscope"></a>
#### `UniformScope`

*inductive*

The threads that must evaluate a uniform instruction's guard identically.

- `warp`
- `warpgroup`

[Lean source: `Core/Sync/WarpUniform.lean` L208-L211](../../Core/Sync/WarpUniform.lean#L208-L211)

### Values and bytes

What a register holds, what a memory byte holds, and how undefined behaviour is reported.

<a id="c-value"></a>
#### `Value`

*inductive*

A value held in a register or stored in memory (THREAD-VALUE).

- `bits`: A `width`-bit integer stored zero-extended in 64 bits.
- `float`
- `pred`
- `ptr`: A `width`-bit symbolic pointer to byte `offset` of the memory `target` names, in its generic representation when `generic` holds and in its state-space representation otherwise.
- `clc`: An opaque 16-byte response, with its request identity preserved.
- `policy`: The opaque 64-bit cache eviction policy that `createpolicy` writes (THREAD-CACHE-POLICY).
- `nan`: A NaN of format `fmt` whose pattern is unspecified (THREAD-FLOAT).
- `pair`: Two values packed into one register or vector element; `lo` is the low half.
- `slice`: A byte slice of an opaque payload, preserving its origin across register moves.

[Lean source: `Core/Data/Value.lean` L101-L120](../../Core/Data/Value.lean#L101-L120)

<a id="c-fval"></a>
#### `FVal`

*inductive*

A floating datum as IEEE 754 classifies it: a zero with its sign, a finite nonzero number, an
infinity with its sign, or NaN with its pattern when the pattern is known.

- `zero`
- `fin`
- `inf`
- `nan`

[Lean source: `Core/Float/Format.lean` L79-L86](../../Core/Float/Format.lean#L79-L86)

<a id="c-layout"></a>
#### `Layout`

*inductive*

A data layout: a binary floating layout with `eb` exponent and `mb` mantissa bits, a sign
bit above them when `signed`, and its special encodings; or a two's complement fixed-point layout
of `w` bits with `frac` fraction bits.

- `binary`
- `fixed`

[Lean source: `Core/Float/Format.lean` L111-L117](../../Core/Float/Format.lean#L111-L117)

<a id="c-ptrtarget"></a>
#### `PtrTarget`

*inductive*

The memory a symbolic pointer names (THREAD-VALUE).

- `shared`: The shared memory of CTA `cta`, in a pointer that a thread of CTA `issuer` produced.
- `param`: The kernel parameter object `name`, shared by the whole launch.
- `const`: The constant memory.

[Lean source: `Core/Data/Value.lean` L89-L99](../../Core/Data/Value.lean#L89-L99)

<a id="c-value-bytes"></a>
#### `Value.bytes`

*def*

The size of a value in bytes.

[Lean source: `Core/Data/Value.lean` L122-L132](../../Core/Data/Value.lean#L122-L132)

<a id="c-value-byteat"></a>
#### `Value.byteAt`

*def*

Byte `k` of `v` in memory, little-endian: a packed pair stores `lo` first.

[Lean source: `Core/Data/Value.lean` L172-L182](../../Core/Data/Value.lean#L172-L182)

<a id="c-value-tobytes"></a>
#### `Value.toBytes`

*def*

The `v.bytes` bytes a write of `v` stores.

[Lean source: `Core/Data/Value.lean` L184-L185](../../Core/Data/Value.lean#L184-L185)

<a id="c-byte"></a>
#### `Byte`

*abbrev*

The content of one memory byte: byte `k` of the stored scalar value `v`.

[Lean source: `Core/Data/Value.lean` L169-L170](../../Core/Data/Value.lean#L169-L170)

<a id="c-clcresponse"></a>
#### `ClcResponse`

*structure*

The response of a `clusterlaunchcontrol.try_cancel` request: the identity of the request and,
on success, the coordinates of the first CTA that was cancelled.

- `request`
- `firstCta`

[Lean source: `Core/Data/Value.lean` L39-L44](../../Core/Data/Value.lean#L39-L44)

<a id="c-fault"></a>
#### `Fault`

*inductive*

Undefined behaviour detected by an instruction rule.

- `pcOutOfRange`
- `uninitialized`
- `typeMismatch`
- `badParam`
- `misaligned`
- `badValue`
- `badBarrier`
- `noRule`: An instruction form for which neither the core nor a kernel assumption has a rule.
- `trap`: A `trap` instruction (THREAD-RUN). No assumption gives it a rule.

[Lean source: `Core/Data/Value.lean` L212-L220](../../Core/Data/Value.lean#L212-L220)

<a id="c-exec"></a>
#### `Exec`

*abbrev*

A rule either returns a result or reports undefined behaviour.

[Lean source: `Core/Data/Value.lean` L222-L223](../../Core/Data/Value.lean#L222-L223)

### Locations, launch and initial memory

Where bytes live, how threads are launched, and what memory holds at launch.

<a id="c-loc"></a>
#### `Loc`

*structure*

A byte location: a state space, its owner and a byte address.

- `space`
- `cta`: The CTA owning a shared location, the thread owning a local location; always `0` for global and constant memory.
- `addr`

[Lean source: `Core/Data/Value.lean` L253-L260](../../Core/Data/Value.lean#L253-L260)

<a id="c-acc"></a>
#### `Acc`

*structure*

The bytes a memory operation accesses: `size` bytes from `loc` (§8.2).

- `loc`
- `size`
- `acquire`: Generic-proxy memory semantics; footprint ignores these qualifiers.
- `release`
- `scope`
- `elem`: Position of this scalar operation among the elements of its vector access (EXT-VECTOR-ELEM); `0` for a scalar access.
- `relaxed`: The `.relaxed` qualifier: with `acquire` and `release` it records the memory semantics, and the access is strong when one of the three is set (`Acc.Strong`).

[Lean source: `Core/Data/Value.lean` L270-L284](../../Core/Data/Value.lean#L270-L284)

<a id="c-acc-overlap"></a>
#### `Acc.Overlap`

*def*

Two accesses overlap when some byte is in both (§8.2.1).

[Lean source: `Core/Data/Value.lean` L294-L295](../../Core/Data/Value.lean#L294-L295)

<a id="c-launch"></a>
#### `Launch`

*structure*

The launch configuration: the counts and shapes of the grid, the CTA and the cluster, kernel
parameters, shared memory base, tensor maps and by-value parameter objects (PROG-LAUNCH).

- `grid`: The number of CTAs of the grid.
- `block`: The number of threads of a CTA.
- `params`: Raw parameter bits, zero-extended.
- `sharedBase`: Address of the first byte of static shared memory in the shared window.
- `localBase`: Address of the first `.local` variable in each thread's local memory (EXT-LOCAL-CONST-LAYOUT).
- `constBase`: Address of the first `.const` variable in the constant memory (EXT-LOCAL-CONST-LAYOUT).
- `clusterSize`: The number of CTAs of a cluster; implicit clusters have size one.
- `tensorMaps`: Host-created, immutable tensor maps of rank `outer + 1`, published before launch. Device updates and descriptors read dynamically through the tensormap proxy need separate rules.
- `tensorLargeAllocMinBytes`: Actual CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE, when supplied. An unknown attribute cannot justify a large-class out-of-bounds operation.
- `paramObjects`: Actual by-value parameter declarations and their generic base addresses. This is launch/ABI data, not the scalar bits stored in a parameter. The immutable tensorMaps entry at such an address describes that parameter's actual contents.
- `paramBytes`: Byte `k` of by-value parameter object `name` as passed by the host, if supplied.
- `sregInit`: The value of special register `s` that the driver or the machine fixes for thread `g` before it starts, for the registers THREAD-SREG leaves unconstrained (`SRegKind.initial`).
- `ntid`: The CTA shape `%ntid`; one-dimensional unless given.
- `nctaid`: The grid shape in CTAs, `%nctaid`; one-dimensional unless given.
- `clusterNctaid`: The regular cluster shape in CTAs (the CUDA cluster dimension); one-dimensional unless given.
- `preferredNctaid`: The preferred cluster shape in CTAs (EXT-PREFERRED-CLUSTER); the regular shape unless given.
- `nclusters`: The number of clusters.
- `clusterPlaces`: The place of each cluster, by the model's cluster number (PROG-CLUSTER); clusters of the regular shape tiling the grid unless given.
- `explicitCluster`: The cluster dimensions were given at launch (`%is_explicit_cluster`, §2.2.2).

[Lean source: `Core/Data/Value.lean` L399-L448](../../Core/Data/Value.lean#L399-L448)

<a id="c-launch-threads"></a>
#### `Launch.threads`

*def*

The number of threads of the launch.

[Lean source: `Core/Data/Value.lean` L450-L451](../../Core/Data/Value.lean#L450-L451)

<a id="c-mem0"></a>
#### `Mem0`

*abbrev*

Memory at launch, as written by `W0` (§8.2.6): `none` = not allocated (any access is
undefined); `some none` = allocated with an unknown constant value; `some (some b)` =
byte `b`.

[Lean source: `Core/Data/Value.lean` L495-L498](../../Core/Data/Value.lean#L495-L498)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### The program text

How the parsed source becomes a kernel.

<a id="prog-syntax"></a>
#### the parsed PTX source (`PROG-SYNTAX`)

*Rule* · [Lean comment: `Core/Source/Syntax.lean` L14-L30](../../Core/Source/Syntax.lean#L14-L30)

The model starts from the syntax tree of the kernel's PTX file. The tree keeps opcode strings, operand spellings and declaration tokens exactly as written, and the decoder gives them their meaning.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: every definition of [`Core/Source/Syntax.lean`](../../Core/Source/Syntax.lean).

<details>
<summary>Details for reviewers</summary>

- §4 (syntax)
- §11 (directives)

**Effect:** The model's source is the syntax tree the Python parser exports. That the tree is the `.ptx` file is external fact EXT-IMPORT.

</details>

<a id="prog-isa-token"></a>
#### modifier tokens and slots (`PROG-ISA-TOKEN`)

*Rule* · [Lean comment: `Core/Source/Isa/Token.lean` L11-L31](../../Core/Source/Isa/Token.lean#L11-L31)

The grammar layer names every modifier token of the instruction table, every segment of a mnemonic and every operand type token by a constructor of `Token`, and every modifier position of an entry by a constructor of `Slot`. The file is generated from the vendored instruction table by `Tools/isa/gen_lean.py`.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: every definition of [`Core/Source/Isa/Token.lean`](../../Core/Source/Isa/Token.lean).

<details>
<summary>Details for reviewers</summary>

- the TIRx PTX table `tvm/python/tvm_tirx/backend/cuda/ptx/table.py` at commit
    ce11dfe1e30433491b5ee035d2f59b54fa95c914 (sha256 e1e0b138c5119b41...), vendored as
    `Tools/isa/data/table.json`
- PTX ISA 9.5 §9.7 (instruction syntax, modifiers and operand lists)

**Effect:** A dot-free segment of an opcode is looked up by its key, the number whose base-128 digits are the segment's ASCII codes (`Token.ofKey?`, a balanced comparison tree). Tokens that contain dots are composites of two or three segments (`Token.comp2?`, `Token.comp3?`). `Slot.code s t` is the position of `t` in the union of the choices of slot `s` over all entries, counted from 1; 0 means that `t` is no choice of `s`.

</details>

<a id="prog-isa-entry"></a>
#### instruction entries (`PROG-ISA-ENTRY`)

*Rule* · [Lean comment: `Core/Source/Isa/Entry.lean` L11-L93](../../Core/Source/Isa/Entry.lean#L11-L93)

Every instruction entry of the vendored table that is decoded, and every entry added for instructions the table lacks, is a constructor of `Entry`, with its mnemonic, family, effect class, PTX ISA section, modifier slots and operands. The file is generated from the vendored instruction table by `Tools/isa/gen_lean.py`; the assignment of entries to families is `Tools/isa/families.py`.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: every definition of [`Core/Source/Isa/Entry.lean`](../../Core/Source/Isa/Entry.lean).

<details>
<summary>Details for reviewers</summary>

- the TIRx PTX table `tvm/python/tvm_tirx/backend/cuda/ptx/table.py` at commit
    ce11dfe1e30433491b5ee035d2f59b54fa95c914 (sha256 e1e0b138c5119b41...), vendored as
    `Tools/isa/data/table.json`
- PTX ISA 9.5 §9.7 (instruction syntax, modifiers and operand lists)
- the entries added and the corrections made in `Tools/isa/extra.py`
- §9.7.7.2: "The sink symbol ‘_’ may be used in place of any one of the destination operands."
- §9.7.10.8: ".ss = { .const, .global, .local, .param{::entry, ::func}, .shared{::cta, ::cluster}
    };"
- §9.7.10.3: "mov.type d, avar+imm; // get address of variable with offset"
- §9.7.10.27: "getctarank.shared::cluster.type d, var + imm;"
- §9.7.10.23: ".size = { .u32, .u64 };"
- §9.7.10.23: "cvta.space.size p, var+imm; // generic address of var+offset"
- §9.7.10.26: ".type = { .u32, .u64 }"
- §9.7.10.26: "mapa.shared::cluster.type d, sh + imm, b;"
- §9.7.10.28.6.2: "cp.async.bulk.wait_group.sync_restrict::proxy::async N;"
- §9.7.15.11: "The sink symbol ‘_’ may be used in place of any one of the destination operands."
- §9.7.15.15: "The sink symbol ‘_’ can be used for destination operand d ."
- §9.7.18.10.10.1: "tcgen05.mma.cta_group::1.kind::f16 [taddr0], a-desc, b-desc, idesc, p;"
- §9.7.18.10.10.2: "tcgen05.mma.cta_group::1.kind::f16 [taddr0], a-desc, b-desc, idesc, p;"
- §9.7.18.10.10.3: "tcgen05.mma.ws.cta_group::1.kind{.collector_usage} [d-tmem], a-desc, b-desc,
    idesc, enable-input-d {, zero-column-mask-desc };"
- §9.7.10.8: "ld{.weak}{.ss}{.cop}{.level::cache_hint}{.level::prefetch_size}{.vec}.type d,
    [a]{.unified}{, cache_policy};"
- §9.7.10.8: "The .v4 ( .vec ) qualifier with type .b64 or .s64 or .u64 or .f64 is supported if:
    State space is .global or with generic addressing where address points to .global state space"
- §9.7.14.3: "bra{.uni} tgt; // unconditional branch"
- §9.7.14.4: "brx.idx{.uni} index, tlist;"
- §9.7.14.4: "The index operand is a .u32 register."
- §9.7.2.1: "add.cc.type d, a, b;"
- §9.7.2.1: ".type = { .u32, .s32, .u64, .s64 };"
- §9.7.2.2: "addc{.cc}.type d, a, b;"
- §9.7.2.2: ".type = { .u32, .s32, .u64, .s64 };"
- §9.7.2.3: "sub.cc.type d, a, b;"
- §9.7.2.3: ".type = { .u32, .s32, .u64, .s64 };"
- §9.7.2.4: "subc{.cc}.type d, a, b;"
- §9.7.2.4: ".type = { .u32, .s32, .u64, .s64 };"
- §9.7.2.5: "mad{.hi,.lo}.cc.type d, a, b, c;"
- §9.7.2.5: ".type = { .u32, .s32, .u64, .s64 };"
- §9.7.2.6: "madc{.hi,.lo}{.cc}.type d, a, b, c;"
- §9.7.2.6: ".type = { .u32, .s32, .u64, .s64 };"
- §9.7.21.2: "nanosleep.u32 t;"
- §9.7.21.2: "t may be a register or an immediate value."
- §9.7.21.3: "pmevent.mask a; // trigger one or more performance monitor events"
- §9.7.21.3: "pmevent a; // trigger a single performance monitor event"
- §9.7.15.4: "membar.level;"
- §9.7.15.4: ".level = { .cta, .gl, .sys };"
- §9.7.15.4: "fence.proxy.proxykind{.sem}.scope;"
- §9.7.15.4: ".sem = { .sc, .acq_rel, .acquire, .release };"
- §9.7.15.4: ".scope = { .cta, .cluster, .gpu, .sys };"
- §9.7.15.4: ".proxykind = { .alias, .async, .async.global, .async.shared::{cta, cluster} };"
- §9.7.14.6: "ret{.uni};"
- §9.7.14.7: "Syntax exit;"
- §9.7.21.4: "Syntax trap;"
- §9.7.18.9.3: "tcgen05.shift.cta_group.down [taddr];"
- §9.7.18.9.3: ".cta_group = { .cta_group::1, .cta_group::2 }"

**Effect:** An entry's slots are its modifier positions in syntax order; `optional` slots may be omitted. The mask of a slot has bit `Slot.code s t` set for every choice `t`. An operand's lanes (number of registers), type token and whether a lane may be the sink `_` are `Fact`s: a constant, the token of a slot, or a table keyed by the codes of the slots the fact depends on (base-128 digits in slot order). The effect class is `event` for an entry with an address operand or one that orders memory, `ctl` for control flow and `local` otherwise. Excluded table entries (wgmma) have no constructor. A table entry whose PTX spelling is that of another entry (mapa with a pointer or an integer address; the `.b8` and `.b16` TMA override tensor sizes) has no constructor either and decodes as that entry (`ALIASES` in `Tools/isa/families.py`); an operand whose type differs between the two has no type token. Corrections of the table: `elect.sync`'s `d` may be the sink, and every `tcgen05.mma` entry with a `disable-output-lane` vector has a sibling `<name>_nomask` without it, the form of the ISA's examples. `mapa` is split by its `.space` qualifier: `mapa` (with `.shared::cluster`) takes a variable `var` or `var+imm` as `a`, and `mapa_generic` (without `.space`) takes a register. `getctarank` takes a variable as `a`; `mov`'s `a` may be a variable with an offset (`regvar`); `ld` and `ld_vec` accept the `.const` space.

</details>

<a id="prog-isa-constraint"></a>
#### legal modifier combinations (`PROG-ISA-CONSTRAINT`)

*Rule* · [Lean comment: `Core/Source/Isa/Constraint.lean` L11-L29](../../Core/Source/Isa/Constraint.lean#L11-L29)

For every decoded entry, the legal combinations of modifier values are a union of cubes, each cube giving one set of allowed values per slot. The cubes are computed by `Tools/isa/constraints.py` from the table's `check` function, evaluated over all slot combinations when the table was vendored, and their union is verified to equal the legal set exactly. The file is generated by `Tools/isa/gen_lean.py`.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: every definition of [`Core/Source/Isa/Constraint.lean`](../../Core/Source/Isa/Constraint.lean).

<details>
<summary>Details for reviewers</summary>

- the TIRx PTX table `tvm/python/tvm_tirx/backend/cuda/ptx/table.py` at commit
    ce11dfe1e30433491b5ee035d2f59b54fa95c914 (sha256 e1e0b138c5119b41...), vendored as
    `Tools/isa/data/table.json`
- PTX ISA 9.5 §9.7 (instruction syntax, modifiers and operand lists)

**Effect:** A cube is a list of masks aligned with `Entry.slotSpecs`; bit 0 of a mask allows the omitted value and bit `Slot.code s t` allows token `t`.

</details>

<a id="prog-isa-grammar"></a>
#### recognizing an instruction (`PROG-ISA-GRAMMAR`)

*Rule* · [Lean comment: `Core/Source/Isa/Grammar.lean` L11-L46](../../Core/Source/Isa/Grammar.lean#L11-L46)

`Grammar.parse` recognizes a PTX instruction, given its opcode string and its operands as written, as one instruction entry with the value of every modifier slot and its operands; when no entry or more than one entry accepts the instruction it fails, so decoding is never ambiguous. The dispatch tables are generated from the vendored instruction table by `Tools/isa/gen_lean.py`.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: every definition of [`Core/Source/Isa/Grammar.lean`](../../Core/Source/Isa/Grammar.lean).

<details>
<summary>Details for reviewers</summary>

- the TIRx PTX table `tvm/python/tvm_tirx/backend/cuda/ptx/table.py` at commit
    ce11dfe1e30433491b5ee035d2f59b54fa95c914 (sha256 e1e0b138c5119b41...), vendored as
    `Tools/isa/data/table.json`
- PTX ISA 9.5 §9.7 (instruction syntax, modifiers and operand lists)
- PTX ISA 9.5 §6.4.3 (Vectors as Operands): "A brace-enclosed list is used for pattern matching to
    pull apart vectors."

**Effect:** The opcode is split at dots; the first segment selects the candidate entries (`candidates`), a wgmma mnemonic fails with its reason (`excluded?`). For each candidate the remaining segments must follow the mnemonic's own segments and then align with the entry's slots left to right, each slot taking a composite of three or two segments, a single token, or nothing when it is optional. PTX writes qualifiers in syntax order; the one exception is `.cta_group` and `.level::cache_hint` of cp.async.bulk.tensor, which ptxas accepts in either order, so an entry with both slots is also tried with the two swapped (`Entry.orders`). The slot values must lie in one cube of `Entry.cubes`. The operands must match the entry's operand groups: a register group is a vector of exactly its lanes, `_` only where the table allows the sink, `p|q` pairs and composite addresses `[m0, ...]` member by member, an address `[r]`, `[sym]`, `[imm]`, `[r+imm]` or `[r-imm]`, an operand with no registers under the modifiers absent. A register operand may be written as a name without `%`, and a scalar register operand as a brace list of that one register, `{ %r }`, which stands for the register (a reading: the manual defines the brace list only for vectors, and ptxas accepts the one-element list). Register names and widths are left to the family layer, which resolves them with the decoder's environment, with one exception: cp.async's `src-size` and `ignore-src` are told apart only by whether the register is a predicate, so for operands with `predCheck` the grammar asks the caller's oracle `isPred`. Strings are read through their UTF-8 bytes, which kernel reduction handles much faster than `String.toList`.

</details>

<a id="prog-decode"></a>
#### from source to instructions (`PROG-DECODE`)

*Rule* · [Lean comment: `Core/Source/Decode.lean` L17-L201](../../Core/Source/Decode.lean#L17-L201)

The decoder turns the parsed source of a kernel into the typed program that the model executes. The grammar recognizes each instruction as an instruction entry, and the layer of the entry's family builds the instruction's representation; headers, parameters, the shared, local and constant variable layouts, labels, branch tables and register numbering are decoded here. An instruction the grammar does not recognize or its family layer rejects fails decoding, so no code is dropped silently. A module decodes only for a single `.target` of `sm_70` or later.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: every definition of [`Core/Source/Decode.lean`](../../Core/Source/Decode.lean).

<details>
<summary>Details for reviewers</summary>

- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "Integer constants are 64-bits in
    size and are either signed or unsigned, i.e., every integer constant has type .s64 or .u64"
- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "Integer literals may be followed
    immediately by the letter U to indicate that the literal is unsigned."
- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "literals are signed ( .s64 )
    unless the value cannot be fully represented in .s64 or the unsigned suffix is specified, in
    which case the literal is unsigned ( .u64 )"
- §4.5.5: "Unary plus and minus preserve the type of the input operand."
- §4.5.5: "-1U , -0xfabc123400000000 are unsigned."
- §4.5.2 (0f binary32 constants)
- §9.4 Table 26 (an `.sX`/`.uX` operand of an `.fX` instruction type is): "invalid"
- §6.4.3: "when specified as destination operand, all elements in vector expression must be unique,
    otherwise behavior is undefined"
- §9.7.14.1: "any variable declared within a scope is not available outside the scope"
- §9.7 (instruction syntax, modifiers and `.type` lists)
- §5.1.7 (shared variables)
- §11 (`.target`)
- §9.7.15.1
- §9.7.15.2
- §9.7.10.6 (sm_6x notes)
- §9.3: "predicate registers can be declared as .reg .pred p, q, r;"
- §5.1.6.1 (kernel parameters)
- §5.1.6.4: "ld.param.s32 %y, [buffer+8];"
- §6.4.1: "[var+immOff] a sum of address of addressable variable var containing a byte address plus
    a constant integer byte offset (signed, 32-bit)."
- §6.4.1: "The address must be naturally aligned to a multiple of the access size. If an address is
    not properly aligned, the resulting behavior is undefined."
- §5.4.5: "The variable will be aligned to an address which is an integer multiple of byte-count."
- §9.7.10.8 (ld `.vec` restrictions)
- §9.4.1 Table 28 (wider destination registers)
- §9.7.1.3 (mul): ".mode = { .hi, .lo, .wide };"
- §9.7.1.3 (mul): "The .wide suffix is supported only for 16- and 32-bit integer types."
- §9.7.1.13
- §9.7.1.14 (min, max): "min{.relu}.type2 d, a, b;"
- §9.7.9.1–§9.7.9.4 (and, or, xor, not): ".type = { .pred, .b16, .b32, .b64 };"
- §9.7.9.1–§9.7.9.4 (and, or, xor, not): "Allowed types include predicate registers."
- §9.7.9.9 (shr): ".type = { .b16, .b32, .b64, .u16, .u32, .u64, .s16, .s32, .s64 };"
- §9.7.3.3
- §9.7.3.4: "sub{.rnd}{.ftz}.f32x2 d, a, b;"
- §9.7.3.4: "The default value of rounding modifier is .rn ."
- §9.7.3.6: "fma.rnd{.ftz}.f32x2 d, a, b, c;"
- §9.7.3.6: "Rounding modifiers (no default):"
- §9.7.3.11
- §9.7.3.12: "max{.ftz}{.NaN}{.abs}.f32 d, a, b, c;"
- §9.7.3.13: "rcp.approx{.ftz}.f32 d, a;"
- §9.7.3.21: "ex2.approx{.ftz}.f32 d, a;"
- §9.7.7.2: "setp.CmpOp{.ftz}.type p[|q], a, b;"
- §9.3.1.2 (Tables 23 and 24)
- §9.7.10.28.5.3 (cp.async.bulk.tensor syntax)
- §9.7.18.10.10.1 (tcgen05.mma syntax)
- §9.7.18.8.3 and §9.7.18.8.4 (tcgen05.ld and tcgen05.st syntax, Tables 59 and 61)
- §4.5.3: "In PTX, integer constants may be used as predicates."
- §11.8.3: "Declare the maximum number of thread blocks (CTAs) allowed to be part of the cluster."
- §11.8.3: "Product of the number of CTAs in each cluster dimension specified in any invocation of
    the kernel is required to be less or equal to that specified in this directive. Otherwise
    invocation will result in a runtime error or kernel launch failure."

**Effect:** The decoder works in two layers: `Isa.Grammar.parse` recognizes it as one instruction entry with its modifier values and operands (PROG-ISA-GRAMMAR), and the layer of the entry's family (`Entry.family`) builds the `Op`: `IntInstr.ofRaw` (PROG-ISA-INT), `MoveInstr.ofRaw` (PROG-ISA-MOVE), `CvtInstr.ofRaw` (PROG-ISA-CVT), `MemAccess.ofRaw` and `AddrInstr.ofRaw` (PROG-ISA-MEM), `WarpInstr.ofRaw` (PROG-ISA-WARP), `MatrixInstr.ofRaw` (PROG-ISA-MATRIX), `FloatInstr.ofRaw` (PROG-ISA-FLOAT), `ctlOp` for control flow, and `keptOp` for the barrier, mbarrier, fence, copy, cluster launch control, `setmaxnreg` and `tcgen05` forms (PROG-ISA-SYNC-FORMS). An entry of the `multimem`, `texture` or `unmodeled` family, and an instruction a family layer has no representation for, decodes to `Op.unmodeled`, which has no rule. Each kernel's `decode_eq` checks, by evaluation, that its source decodes to the kernel its theorem is about, so a decoding error changes which program is proved, never the proof. Registers are numbered once, here: a register's id is its position in the kernel's declared-register order (declarations in statement order, scoped ones after hygienic renaming; `pre<n>` declares `pre0` … `pre(n-1)`), and `Kernel.regNames` lists the names by id. Control flow is decoded as follows. `bra{.uni}` takes a label of the function; `brx.idx{.uni}` takes a `.branchtargets` table, a label followed by the directive, declared before the instruction (§9.7.14.4: "The .branchtargets directive must be defined in the local function scope before it is used."), whose targets are labels of the function; a table label is not a branch target. `ret.uni` is not decoded. `.loc` source-location directives (§11.6.4) are checked and dropped. The target check is stricter. A module decodes only for `.target sm_70` or later (`target`, `module`). For `.target sm_6x or below` the ISA gives `barrier{.cta}` without `.aligned`, `bar.warp.sync` and `shfl.sync` convergence requirements (§9.7.15.1: "For .target sm_6x or below, barrier{.cta} instruction without .aligned modifier is equivalent to .aligned variant and has the same restrictions as of .aligned variant."; §9.7.15.2 and §9.7.10.6 likewise) that the model's sm_70 rules do not check, so such modules are rejected. A module without exactly one `.target` directive is rejected too (§11.1.2: "A .target directive specifies a single target architecture, but subsequent .target directives can be used to change the set of target features allowed during parsing"; a module with several is rejected rather than checking each). The directive names exactly one architecture, spelled `sm_n[a|f]` as in the §11.1.2 list or as its synonym `compute_n` ("Targets of the form compute_xx are also accepted as synonyms for sm_xx targets."), with the same sm_70 floor, and otherwise only the options `texmode_unified`, `texmode_independent` and `debug`; other spellings (`sm_70junk`), two architectures and unknown options are rejected. The option `map_f64_to_f32` is rejected too: it changes the meaning of every double-precision instruction (§11.1.2: "map_f64_to_f32 indicates that all double-precision instructions map to single-precision regardless of the target architecture."), and the model executes `.f64` instructions in double precision. Each kernel's module passes this check; its `decode_eq` decodes the kernel's function. Parameters are decoded as follows. A scalar kernel parameter is `.param .t name` or a pointer `.param .t .ptr [.space] [.align N] name` (§5.1.6.3, `.space` one of `.const`, `.global`, `.local`, `.shared`, N an integer literal (§4.5.1, `U` suffix allowed) that is a power of two, 4 when not written, `.t` 32 or 64 bits); `name` may be a parameterized name `p<n>` declaring `p0` … `p(n-1)` (§5.4.6: "This shorthand syntax may be used with any of the fundamental types and with any state space"); any other attribute token is rejected. A scalar parameter with a storage alignment (`.param .align N .t name`, §5.4.5) is legal PTX that the decoder does not support, so it is rejected (stricter). A `.ptr` attribute with a state space or an alignment above 1 is kept in `Kernel.ptrParams` (alignment 1 with a generic address constrains nothing the launch check reads). A register declaration declares one name, a parameterized name `pre<n>` or a comma list of plain names (`.reg .t a, b, c`, §9.3), each a register of type `.t`, in source order; a list that mixes in a parameterized name is rejected (stricter). The directives `.maxntid` (1 to 3 extents, kept as their product, §11.5.2), `.reqntid` (1 to 3 extents, kept per dimension with an extent not written being 1: the directive declares a 1D, 2D or 3D CTA and §10.2 gives "%ntid.y == %ntid.z == 1 in 1D CTAs. %ntid.z ==1 in 2D CTAs."; not both, §11.5.3) are kept for CORRECT-LAUNCH; `.minperctamemory size` (§11.5.10, a 32-bit unsigned size) is kept in `Kernel.minPerCtaMemory`, and only a kernel with it may use `%perctamemoryoffset` and `%perctamemorysize` (§11.5.10: "Only entry functions specifying this directive are allowed to use special registers %perctamemoryoffset or %perctamemorysize ."; PROG-OPERAND). `.maxnreg`, `.minnctapersm` and `.maxclusterrank` are checked and dropped: the model represents no register counts (EXT-SETMAXNREG-EFFECTIVE), no residency, and the cluster's size comes from the launch (§11.8.3: "Product of the number of CTAs in each cluster dimension specified in any invocation of the kernel is required to be less or equal to that specified in this directive."). Parameter objects are decoded as follows. `ld.param{.v2,.v4}.t d, [obj]` or `[obj+off]` on a by-value parameter object `obj` (`.param .align N .t obj[n]`) reads `count` elements of `.t` from byte `off` of the object (THREAD-MOVE). It is rejected (stricter, `MemAccess.paramChecks`) when the access leaves the object (`off` negative or `off + size` beyond its bytes: the ISA gives such a read no meaning), when the access size does not divide both `off` and the declared alignment (then the address is aligned for no placement, or only for some placements, the declaration allows; a misaligned address is undefined), and for a `.vec`/`.type` pair `ld` admits only in the global space. A `.b128` element is read as two 64-bit halves (THREAD-MOVE). The destination registers have one width: the element width or a wider one (PROG-ISA-MEM); THREAD-MOVE applies to a wider destination of at most 64 bits of a bit-size `.t` only (Table 28 zero-extends every wider destination of a bit-size type). `ld.param` on a scalar parameter is `[p]` at the parameter's own width. Variables are decoded as follows. A kernel's `.shared .align A .b8 name[N]` and `.local .align A .b8 name[N]` variables and the module's `.shared` and `.const .align A .b8 name[N]` variables are laid out by the decoder (EXT-SHARED, EXT-LOCAL-CONST-LAYOUT); a `.const` variable with an initializer and every other `.local` or `.const` declaration form are rejected. Scopes and types are decoded as follows. Every name declared in a `{}` scope (register, label, `.shared` or `.local` variable) is bound in that scope only, under a hygienic name, so equal names in different scopes are different objects; names declared twice in one scope are errors. Each instruction accepts only the modifier combinations of its entry (PROG-ISA-GRAMMAR), and its registers must be declared at the widths of the operand types the family layer reads (PROG-OPERAND). The kept forms (`keptOp`) are described next. A form of those families that the description calls not decoded is recognized by the grammar and decodes to `Op.unmodeled` when the table has it. Tensor loads are decoded as follows. `.L2::cache_hint` stands after an optional `.multicast::cluster`, before or after `.cta_group` (§9.7.10.28.5.3 lists `{.cta_group}{.level::cache_hint}`; the text gives qualifier order no meaning, and ptxas accepts both), each qualifier at most once; its 64-bit `cache_policy` is the last operand, after `ctaMask`. Other qualifier orders are rejected (scope). The MMA operands are decoded as follows. `tcgen05.mma` takes its A operand as a shared descriptor or as a Tensor Memory address `[a-tmem]` or `[a-tmem+imm]` (THREAD-TC), the lane-mask vector or no mask (then `4 * group size` zero words, THREAD-TC), and `enable-input-d` as a predicate register or an integer constant (§4.5.3); a floating constant there is rejected. The destination `[d-tmem]` is a register. Tensor Memory loads and stores are decoded as follows. `tcgen05.ld` and `tcgen05.st` decode every `.shape1` and `.shape2` of §9.7.18.8.3 and §9.7.18.8.4 (`TcShape`), with `.num` from `.x1` to `.x128` and a vector of `num` repetitions of the shape's registers, an entry Tables 59 and 61 give (not NA). The address is `[taddr]` or `[taddr+0]`; `.16x32bx2` takes its `immHalfSplitoff` as a non-negative integer constant below `2 ^ 32`, after the address. `.pack::16b`, `.unpack::16b`, `.red`, `.spcompress` and a nonzero address offset are not decoded (scope). The rejected forms are as follows. Static undefined behaviour is rejected: a destination vector naming a register twice (every instruction with a destination list, PROG-OPERAND `rdsts`, `dstRegs`). Forms with no stated meaning are rejected too: an integer constant at a floating-point instruction type (Table 26), an integer constant wider than 64 bits (§4.5.1 gives constants 64 bits and does not say how one is widened to 128), a scalar kernel parameter wider than 64 bits (the launch supplies a scalar parameter as 64 bits), and an integer literal whose value is not representable in `.u64` (§4.5.1: every integer constant is `.s64` or `.u64`, so no wider value is a constant). Other integer constant expressions (§4.5.4: unary plus, repeated unary operators, `!`, `~`, binary and ternary operators, parentheses, casts, `WARP_SZ`) are legal PTX that the decoder does not support, so they are rejected (stricter). Integer constants are decoded as follows. A constant is decoded with its §4.5.1 type: a literal is `.s64` unless its value is not representable in `.s64` or it has the `U` suffix, and then `.u64`; one unary minus applied to a literal keeps that type (§4.5.5), so it negates an `.s64` literal as an integer and a `.u64` literal modulo `2^64` (`-1U` is `2^64 - 1`, `-9223372036854775808` is the `.u64` value `2^63`). The operand holds the constant's value; data operands and address offsets use its 64-bit pattern, truncated to the width of the use (§4.5.1: "each integer constant is converted to the appropriate size based on the data or instruction type at its use").

</details>

<a id="ext-shared"></a>
##### shared memory layout (`EXT-SHARED`)

*Interpretation (EXT)* · [Lean comment: `Core/Source/Decode.lean` L203-L224](../../Core/Source/Decode.lean#L203-L224)

The model places each `.shared` variable at the decoder's offset from the shared base, in disjoint and aligned bytes of the CTA's shared memory. The PTX ISA does not say where variables are placed, so a kernel whose behaviour depends on the addresses beyond disjointness and alignment is outside the claim.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** Distinct `.shared` variables occupy disjoint, aligned bytes of the CTA's shared memory. The model places them at the decoder's offsets from `Launch.sharedBase`; a kernel whose behaviour depends on the actual addresses beyond disjointness and alignment is outside the claim. Obligations on the launch, not checked: `Launch.sharedBase` is aligned to the largest alignment of the kernel's shared variables, and an `extern` shared variable starts after the static ones at its own alignment.

**Evidence:** PTX ISA §5.1.7 ("Variables declared in .shared state space refer to the memory addresses in the current CTA") and §5.4.5 (alignment). Neither gives the placement of variables or the base address of the shared window, which the compiler and the driver choose.

**Effect:** Disclosed by every kernel whose statement names `Opnd.sharedSym`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm, TmaCopy.

</details>

<a id="ext-local-const-layout"></a>
##### local and constant variable layout (`EXT-LOCAL-CONST-LAYOUT`)

*Interpretation (EXT)* · [Lean comment: `Core/Source/Decode.lean` L226-L255](../../Core/Source/Decode.lean#L226-L255)

The model places each `.local` variable at the decoder's offset from the local base in every thread's local memory, and each `.const` variable at the decoder's offset from the constant base, in disjoint and aligned bytes. The PTX ISA does not say where variables are placed, so a kernel whose behaviour depends on the addresses beyond disjointness and alignment is outside the claim.

Source:

- - §5.1.5: "The local state space ( .local ) is private memory for each thread to keep its own data." - §5.1.3: "Statically-sized constant variables have an optional variable initializer; constant variables with no explicit initializer are initialized to zero by default." - §5.4.5 (alignment)

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text gives neither the placement of the variables nor the base addresses, which the compiler and the driver choose. A kernel's `.local .align A .b8 name[N]` variables are laid out in declaration order from `Launch.localBase` at their alignments, the same offsets in every thread's local memory, and the module's `.const .align A .b8 name[N]` variables in declaration order from `Launch.constBase` (`varLayout`). Obligations on the launch, not checked: each base is aligned to the largest alignment of its variables, and the bytes of the variables are allocated in `mem0`. The contents of a `.const` variable at launch are `mem0`'s bytes at its location (EXT-LAUNCH), which covers the zero default and a value the host wrote before the launch. A `.const` variable with an initializer is rejected at decoding: the model would need `mem0` to agree with the initializer, which the launch interface does not state.

**Effect:** If it does not hold, a kernel that computes with the numeric address of a local or constant variable may reach other bytes than the model's. Disclosed by every kernel whose statement names `AddrBase.localSym`, `Opnd.localSym` or `AddrBase.constSym`: none.

</details>

### Instructions

The instruction forms that exist, and which of them perform events.

<a id="prog-instr-forms"></a>
#### the supported instruction forms (`PROG-INSTR-FORMS`)

*Rule* · [Lean comment: `Core/Source/Instr.lean` L28-L53](../../Core/Source/Instr.lean#L28-L53)

A decoded instruction is a family constructor (integer, floating, move, conversion, memory access, address, warp collective, warp-level matrix instruction, `createpolicy`, `nanosleep` and `pmevent`), one of the kept constructors of the barrier, mbarrier, fence, copy, cluster launch control, `setmaxnreg` and `tcgen05` forms, a control-flow constructor, or `Op.unmodeled` for a recognized instruction without a representation this round. A kernel is a list of instructions in source order; each has an optional guard, branch targets are instruction indices, and registers are numbered by declaration order.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`ClcDim`](../../Core/Source/Instr.lean#L56-L59), [`ClcQuery`](../../Core/Source/Instr.lean#L61-L64), [`ClusterOp`](../../Core/Source/Instr.lean#L66-L70), [`ClusterOp.aligned`](../../Core/Source/Instr.lean#L72-L73), [`TensorMode`](../../Core/Source/Instr.lean#L75-L79), [`TensorMode.coordinates`](../../Core/Source/Instr.lean#L81-L84), [`TcShape`](../../Core/Source/Instr.lean#L86-L98) ([concept](tcgen05.md#c-tcshape)), [`TcShape.lanes`](../../Core/Source/Instr.lean#L100-L107), [`TcShape.regs`](../../Core/Source/Instr.lean#L109-L114), [`TcShape.countOk`](../../Core/Source/Instr.lean#L122-L125), [`TcShape.singleAccess`](../../Core/Source/Instr.lean#L116-L120), [`Op`](../../Core/Source/Instr.lean#L127-L270) ([concept](#c-op)), [`Op.aligned`](../../Core/Source/Instr.lean#L471-L477) ([concept](#c-op-aligned)), [`Instr`](../../Core/Source/Instr.lean#L272-L277) ([concept](#c-instr)), [`PtrSpace`](../../Core/Source/Instr.lean#L279-L283), [`PtrDecl`](../../Core/Source/Instr.lean#L285-L290), [`Kernel`](../../Core/Source/Instr.lean#L292-L315) ([concept](#c-kernel))

<details>
<summary>Details for reviewers</summary>

- §9.7 (instruction descriptions)
- §9.3 (predicated execution)

**Effect:** An instruction the grammar does not recognize, or whose family layer rejects it, fails decoding, so no theorem is about a kernel that uses it. `Op.unmodeled` keeps the recognized instruction (`Isa.Raw`); no rule gives it semantics (THREAD-LOCAL, THREAD-RUN). Branch targets are instruction indices; a guard is a predicate register, possibly negated. A register is a number, its index in the kernel's declared-register order (PROG-DECODE); `Kernel.regNames` keeps the source names for printing, and no rule reads them.

</details>

<a id="prog-instr-events"></a>
#### which instructions perform events (`PROG-INSTR-EVENTS`)

*Rule* · [Lean comment: `Core/Source/Instr.lean` L317-L364](../../Core/Source/Instr.lean#L317-L364)

An instruction that accesses memory, synchronizes with other threads, issues an asynchronous operation, ends the thread or has another effect outside the thread's registers performs an event, and so does an instruction that reads a special register whose value changes while the thread runs. Every other instruction only reads and writes the thread's own registers and source position.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`Opnd.varying?`](../../Core/Source/Instr.lean#L367-L371), [`Op.varyingSregs`](../../Core/Source/Instr.lean#L373-L379), [`Op.isLocal`](../../Core/Source/Instr.lean#L381-L398) ([concept](#c-op-islocal)), [`Op.isLocal_of_varyingSregs`](../../Core/Source/Instr.lean#L400-L404)

<details>
<summary>Details for reviewers</summary>

- §10.4: "Note that %warpid returns the location of a thread at the moment when read, but its value
    may change during execution"
- §8.2 (memory operations)
- §9.7.15.1 (bar)
- §9.7.15.3 (barrier.cluster)
- §9.7.10.6 (shfl.sync)
- §9.7.15.10 (vote.sync)
- §9.7.14.6 (ret)
- §9.7.15.16 (mbarrier)
- §9.7.10.28.4.1 (cp.async.bulk)
- §9.7.10.28.3 (cp.async and its groups)
- §9.7.10.28.4.3 (cp.async.bulk.prefetch)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)
- §9.7.10.28.5.5 (cp.async.bulk.prefetch.tensor)
- §9.7.18 (tcgen05)

**Effect:** Exactly these instructions perform an event (`Op.isLocal` is false): `setmaxnreg`, every memory access (`Op.mem`: `ld`, `st`, `atom`, `red`) except `ld.param`, every warp collective (`Op.warp`: `shfl.sync`, `vote.sync`, `match.sync`, `redux.sync`, `activemask`, `elect.sync`, `bar.warp.sync`), every warp-level matrix instruction (`Op.matrix`: `ldmatrix`, `stmatrix`, `movmatrix`, `mma`, `mma.sp`), `barrier{.cta}` (`sync` with and without a thread count, `arrive`), `barrier.cluster`, `ret`, `exit`, `trap`, every fence (`Op.fence`: thread fences, `membar` and proxy fences), the mbarrier-initialization fence, the mbarrier instructions (`init`, `inval`, arrive, wait), the copies (`cp.async`, `cp.async.bulk`, `cp.reduce.async.bulk` and the tensor loads and stores), `st.async`, `red.async`, bulk-group and `cp.async`-group commit and wait, `cp.async.mbarrier.arrive`, the data prefetches (`cp.async.bulk.prefetch` and `cp.async.bulk.prefetch.tensor`), the cluster launch control `try_cancel` and response query, every `tcgen05` instruction (alloc, dealloc, relinquish, mma in every form, commit, both fences, ld, st, their waits, cp), and an `Op.unmodeled` instruction whose entry has the effect class `event` (PROG-ISA-ENTRY: an address operand or memory ordering). An integer, move or conversion instruction with a source operand that reads `%warpid`, `%smid`, `%clock`, `%clock_hi`, `%clock64` or a `%globaltimer` register (`Op.varyingSregs`) performs the read event of THREAD-SREG. `ld.param` reads the launch's parameters (THREAD-MOVE) and is local. Every other instruction, including the tensormap prefetch and the cache instructions `prefetch`, `prefetchu` and `applypriority` (`Op.addr`, THREAD-PREFETCH), only reads and writes this thread's registers and `pc`, so an instruction marked local never touches memory or another thread.

</details>

### Values and bytes

The data that registers and memory hold.

<a id="thread-value"></a>
#### register values (`THREAD-VALUE`)

*Rule* · [Lean comment: `Core/Data/Value.lean` L46-L86](../../Core/Data/Value.lean#L46-L86)

A register value is an integer bit vector of its width, a floating payload as an ideal real number in its format, a predicate, a pair of packed values, a symbolic pointer, an opaque cancellation response, or a slice of one of these. Every data value has a bit pattern, so integer instructions read a float as its bits. A symbolic pointer is a generic or state-space address that remembers the memory it names: the target CTA and the producing CTA of a shared address, the name of a kernel parameter object, the thread that owns a local address, or the constant memory. A cache eviction policy is an opaque 64-bit value, and a NaN whose pattern the manual leaves unspecified is an opaque value of its format's width.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`PtrTarget`](../../Core/Data/Value.lean#L89-L99) ([concept](#c-ptrtarget)), [`Value`](../../Core/Data/Value.lean#L101-L120) ([concept](#c-value)), [`Value.bytes`](../../Core/Data/Value.lean#L122-L132) ([concept](#c-value-bytes))

<details>
<summary>Details for reviewers</summary>

- §5.1.7 (shared windows, quoted in THREAD-SHARED-POINTER)
- §6.4.1.1 (generic address windows, quoted in THREAD-CVTA)
- §5.1.1: "Registers may be typed (signed integer, unsigned integer, floating point, predicate) or
    untyped."
- §5.2 (fundamental types)
- §5.2.5 (packed data types); numeric interpretation selected through ASM-INTERFACE

**Effect:** A register value is an integer bit vector of its width; a float payload is the number it denotes in its format (an ideal real number under an ideal profile); a predicate is a Boolean; a packed value is a pair, low half first. Every data value has a bit pattern (`Value.bitPattern`, THREAD-BITS): a float payload's is its encoding in its format, so a register is read as bits by integer instructions and as a number by floating ones. A value's size in bytes is its width. A symbolic pointer `.ptr w generic sp off` is a `w`-bit address of byte `off` of the memory that `sp` names, in its generic representation (`generic = true`) or its state-space one (THREAD-CVTA). It assumes no encoding of window bases or CTA-rank bits and has no bit pattern, so arbitrary integer inspection of a pointer has no rule, and moves preserve its representation. A shared pointer (a generic or `.shared::cluster` address, THREAD-SHARED-POINTER) retains its target CTA and the CTA whose thread produced it. A parameter pointer retains the launch-wide parameter name, independent of the parameter contents, and its offset is 0, since no rule moves it. A generic local pointer retains the thread whose local memory it addresses, and a generic constant pointer names the constant memory; local and constant pointers are generic only. A cache eviction policy is an opaque 64-bit value without a bit pattern (THREAD-CACHE-POLICY). `.nan fmt` is a NaN of format `fmt` whose pattern the manual leaves unspecified (§9.7.3: "Single-precision instructions return an unspecified NaN"): it has the format's size and no bit pattern, so a floating instruction reads it as NaN (THREAD-NUM), a store and reload keep it, and every reader that needs its bits faults.

</details>

<a id="thread-float-format"></a>
#### floating and fixed-point layouts (`THREAD-FLOAT-FORMAT`)

*Rule* · [Lean comment: `Core/Float/Format.lean` L21-L76](../../Core/Float/Format.lean#L21-L76)

A floating datum is a zero with a sign, a finite nonzero number, an infinity with a sign, or NaN, with its pattern when the pattern is known. A binary layout reads a pattern as a sign bit, an exponent field and a mantissa field, with subnormal numbers at the zero exponent field, and gives each format's encodings of infinity and NaN. The fixed-point layout of `.s2f6` reads a pattern as a two's complement integer times `2^-6`.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`FVal`](../../Core/Float/Format.lean#L79-L86) ([concept](#c-fval)), [`FVal.num`](../../Core/Float/Format.lean#L88-L92), [`FVal.ofRat`](../../Core/Float/Format.lean#L94-L95), [`Specials`](../../Core/Float/Format.lean#L97-L109), [`Layout`](../../Core/Float/Format.lean#L111-L117) ([concept](#c-layout)), [`Layout.width`](../../Core/Float/Format.lean#L119-L122), [`Layout.bias`](../../Core/Float/Format.lean#L124-L125), [`Layout.magnitude`](../../Core/Float/Format.lean#L127-L133), [`Layout.fieldVal`](../../Core/Float/Format.lean#L135-L139), [`Layout.decode`](../../Core/Float/Format.lean#L141-L162), [`Layout.encode`](../../Core/Float/Format.lean#L164-L167), [`Layout.minNormal`](../../Core/Float/Format.lean#L169-L173), [`Layout.topField`](../../Core/Float/Format.lean#L175-L183), [`Layout.maxNorm`](../../Core/Float/Format.lean#L185-L189), [`Layout.subnormal`](../../Core/Float/Format.lean#L191-L193), [`Layout.flush`](../../Core/Float/Format.lean#L195-L199), [`Layout.signPattern`](../../Core/Float/Format.lean#L201-L202), [`Layout.infPattern`](../../Core/Float/Format.lean#L204-L208), [`FloatFmt.layout`](../../Core/Float/Format.lean#L210-L217), [`FType.layout?`](../../Core/Float/Format.lean#L219-L229), [`FloatFmt.expBits`](../../Core/Float/Format.lean#L231-L235), [`FloatFmt.mantBits`](../../Core/Float/Format.lean#L237-L241), [`FloatFmt.bias`](../../Core/Float/Format.lean#L243-L244), [`FloatFmt.magnitude`](../../Core/Float/Format.lean#L246-L248), [`FloatFmt.decode`](../../Core/Float/Format.lean#L250-L253), [`f32Value`](../../Core/Float/Format.lean#L255-L256), [`FloatFmt.representable`](../../Core/Float/Format.lean#L258-L261), [`Layout.magnitude_zero`](../../Core/Float/Format.lean#L267-L268), [`Layout.magnitude_lt_succ`](../../Core/Float/Format.lean#L270-L309), [`Layout.magnitude_strictMono`](../../Core/Float/Format.lean#L311-L312), [`Layout.magnitude_pos`](../../Core/Float/Format.lean#L314-L315), [`Layout.magnitude_nonneg`](../../Core/Float/Format.lean#L317-L318), [`Layout.fieldVal_inj`](../../Core/Float/Format.lean#L320-L335), [`Layout.binary_low`](../../Core/Float/Format.lean#L337-L340), [`Layout.binary_sign`](../../Core/Float/Format.lean#L342-L348), [`Layout.binary_pattern`](../../Core/Float/Format.lean#L350-L361), [`Layout.decode_binary_cases`](../../Core/Float/Format.lean#L363-L389), [`Layout.fieldVal_ne_nan`](../../Core/Float/Format.lean#L392-L394), [`Layout.fieldVal_ne_inf`](../../Core/Float/Format.lean#L396-L398), [`Layout.decode_binary_inj`](../../Core/Float/Format.lean#L400-L420), [`Layout.decode_fixed_inj`](../../Core/Float/Format.lean#L422-L466), [`Layout.decode_inj`](../../Core/Float/Format.lean#L468-L478), [`Layout.encode_decode`](../../Core/Float/Format.lean#L480-L489), [`Layout.decode_of_encode`](../../Core/Float/Format.lean#L491-L497), [`FVal.num_fieldVal`](../../Core/Float/Format.lean#L500-L504), [`FloatFmt.layout_eq`](../../Core/Float/Format.lean#L506-L510), [`FloatFmt.magnitude_eq`](../../Core/Float/Format.lean#L512-L522), [`FloatFmt.decode_eq`](../../Core/Float/Format.lean#L524-L547), [`Layout.binary_pattern_parts`](../../Core/Float/Format.lean#L550-L572), [`Layout.decode_field_ieee`](../../Core/Float/Format.lean#L574-L587), [`Layout.decode_field_e4m3`](../../Core/Float/Format.lean#L589-L609), [`Layout.decode_infPattern_ieee`](../../Core/Float/Format.lean#L611-L623), [`FloatFmt.decode_field`](../../Core/Float/Format.lean#L625-L638), [`FloatFmt.decode_signPattern`](../../Core/Float/Format.lean#L640-L647), [`FloatFmt.decode_infPattern`](../../Core/Float/Format.lean#L649-L655)

<details>
<summary>Details for reviewers</summary>

- §5.2.3: "the .f16 type indicates 5 bits reserved for exponent and 10 bits reserved for mantissa"
- §5.2.3: "bf16 data format: This data format is a 16-bit floating point format with 8 bits for
    exponent and 7 bits for mantissa."
- §5.2.3: "e5m2 data format: This data format is an 8-bit floating point format with 5 bits for
    exponent and 2 bits for mantissa"
- §5.2.3: "The e4m3 encoding does not support infinity and NaN values are limited to 0x7f and 0xff"
- §4.5.2: "To specify IEEE 754 double-precision floating point values, the constant begins with 0d
    or 0D followed by 16 hex digits."
- §5.2.3: "The ue8m0 encoding does not support infinity. NaN value is limited to 0xff ."
- §5.2.4: "This data format is 8-bit signed 2’s complement integer with 2 sign-integer bits and 6
    fractional bits with form xx.xxxxxx ."
- §5.2.4: "The s2f6 encoding does not support infinity and NaN ."
- §5.2.4: "s2f6 value = s8 value * 2^(-6)"
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."
- EXT-UE8M0
- EXT-NARROW-FLOAT

**Applies:** The patterns of every floating and fixed-point format

**Effect:** Representation. `.f64`, `.f32`, `.f16`, `.bf16` and `.e5m2` are IEEE 754 binary layouts with infinities and NaN at the all-ones exponent field; `.e4m3` has no infinity and its NaN is the pattern with exponent and mantissa all ones; `.ue8m0` and `.ue5m3` have no sign bit, no infinity, and NaN at the all-ones pattern, and the `.ue8m0` pattern `0` has no value (EXT-UE8M0); `.e2m1`, `.e2m3` and `.e3m2` have neither infinity nor NaN (EXT-NARROW-FLOAT). `.tf32` has no layout, since its internal layout is implementation defined. A NaN read from a pattern keeps the pattern. `Layout.encode` is the inverse of `Layout.decode`. The format `.f64` is the IEEE 754 double-precision format, with 11 exponent bits and 52 mantissa bits (§4.5.2). `FloatFmt.decode` and `f32Value` give the number of a finite pattern of a payload format, with either zero read as `0`. `Layout.maxNorm` is the largest finite magnitude (MAX_NORM), and `Layout.flush` maps a subnormal number to the zero of its sign, as `.ftz` does.

</details>

<a id="mem-byte"></a>
#### memory bytes (`MEM-BYTE`)

*Rule* · [Lean comment: `Core/Data/Value.lean` L134-L149](../../Core/Data/Value.lean#L134-L149)

Memory is a set of bytes, and the content of a byte is byte `k` of the value that a write stored there, or the content that the initial write `W0` gave it. A packed pair stores its low half first.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Byte`](../../Core/Data/Value.lean#L169-L170) ([concept](#c-byte)), [`Value.byteAt`](../../Core/Data/Value.lean#L172-L182) ([concept](#c-value-byteat)), [`Value.toBytes`](../../Core/Data/Value.lean#L184-L185) ([concept](#c-value-tobytes))

<details>
<summary>Details for reviewers</summary>

- §8.2 (memory is bytes); choice: abstract contents, little-endian packing

**Effect:** Memory is a set of bytes, with no global memory state: a byte's content is what a write event wrote to it, or what the initial write `W0` wrote. Contents are abstract: byte `k` of a stored scalar `Value`. A packed pair stores its low half first (little-endian, external fact EXT-ENDIAN).

</details>

<a id="ext-endian"></a>
##### byte order (`EXT-ENDIAN`)

*Interpretation (EXT)* · [Lean comment: `Core/Data/Value.lean` L151-L166](../../Core/Data/Value.lean#L151-L166)

The model stores multi-byte values and packed pairs little-endian, low half first. The PTX ISA does not state a byte order for them.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Evidence:** CUDA's little-endian memory. PTX ISA §5.2.5 defines the packed data types but gives no byte order in memory, so this is not ISA text; the address of each element of a vector access is EXT-VECTOR-ELEM.

**Effect:** If it does not hold, a value read at a different width or offset than it was written (a byte of a word, a half of a packed pair) is not the one the model gives, and every result computed from it, including addresses and control flow, may differ from the hardware's. Disclosed by every kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.

</details>

<a id="obj-clc-response"></a>
#### opaque cancellation response (`OBJ-CLC-RESPONSE`)

*Rule* · [Lean comment: `Core/Data/Value.lean` L23-L37](../../Core/Data/Value.lean#L23-L37)

A cancellation response is an opaque 16-byte value. It remembers which request it answers and, when the request succeeded, the three coordinates of the first CTA of the cancelled cluster. Copying the response keeps its identity.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`ClcResponse`](../../Core/Data/Value.lean#L39-L44) ([concept](#c-clcresponse))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.18–19

**Effect:** The 16-byte opaque response retains the dynamic request identity and, on success, the first CTA's three coordinates; no bit encoding is asserted. Copying the response preserves its identity; multicast replicas are not independent cancellations.

</details>

<a id="err-fault-reason"></a>
#### undefined behaviour of one instruction (`ERR-FAULT-REASON`)

*Rule* · [Lean comment: `Core/Data/Value.lean` L187-L209](../../Core/Data/Value.lean#L187-L209)

A fault names the reason that one instruction has undefined behaviour, and every fault makes the whole execution undefined. An instruction form or an arithmetic result for which neither the model nor a kernel assumption has a rule is a fault, so no result is left open.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Fault`](../../Core/Data/Value.lean#L212-L220) ([concept](#c-fault)), [`Exec`](../../Core/Data/Value.lean#L222-L223) ([concept](#c-exec))

<details>
<summary>Details for reviewers</summary>

- §9.7: "behavior is undefined"

**Effect:** A fault is the reason an instruction is undefined. Every fault is undefined behaviour of the execution (ERR-UNSAFE); the reason is only for reading. `noRule` covers every instruction form the model has no rule for, and every arithmetic operation whose result the model does not give: a floating operation no assumption supplies a rule for (`mmaRule`, `reduceRule`, scalar floating profiles) and operands that are not values of the operation's type. For all arithmetic, scalar instructions (`.error .noRule`), MMA (ERR-TC-MMA) and tensor reductions (DEP-REDUCTION-VALUES, `ReduceNoRule`) report a missing rule as undefined behaviour, so no result is left open.

</details>

### Locations and the launch

Memory locations, the launch configuration and the memory at launch.

<a id="mem-location"></a>
#### locations and footprints (`MEM-LOCATION`)

*Rule* · [Lean comment: `Core/Data/Value.lean` L225-L250](../../Core/Data/Value.lean#L225-L250)

A location is a state space, its owner (the CTA for shared memory, the thread for local memory, 0 for global and constant memory) and a byte address. A memory access covers a number of bytes from a location, and two accesses overlap when some byte lies in both. Distinct addresses are distinct bytes, so launches with aliased addresses are not supported.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`Loc`](../../Core/Data/Value.lean#L253-L260) ([concept](#c-loc)), [`Loc.at`](../../Core/Data/Value.lean#L262-L262), [`Loc.InRange`](../../Core/Data/Value.lean#L264-L265), [`Acc`](../../Core/Data/Value.lean#L270-L284) ([concept](#c-acc)), [`Acc.Strong`](../../Core/Data/Value.lean#L286-L288), [`Acc.Covers`](../../Core/Data/Value.lean#L292-L292), [`Acc.Overlap`](../../Core/Data/Value.lean#L294-L295) ([concept](#c-acc-overlap)), [`Acc.SameFootprint`](../../Core/Data/Value.lean#L290-L290)

<details>
<summary>Details for reviewers</summary>

- §8.2 (memory operations)
- §8.2.1 (overlap)
- §8.3 (state spaces)
- §8.4: "strong operation A memory fence operation, or a memory operation with a .relaxed , .acquire
    , .release , .acq_rel , .volatile , or .mmio qualifier."
- EXT-LAUNCH (no aliases)

**Effect:** A location is a state space, its owner (shared memory is per CTA, local memory per thread; global and constant memory use `0`) and a byte address. A footprint is `size` bytes from a location; two footprints overlap when some byte is in both. The memory semantics (`.relaxed`, `.acquire`, `.release`, both for `.acq_rel`, none for a weak access) and the scope are kept apart from footprint equality (`Acc.SameFootprint`); an access with one of these qualifiers is strong (`Acc.Strong`, §8.4). Distinct addresses are distinct bytes: §8.2.2 defines aliases (distinct virtual addresses that map to one memory location) and does not exclude them, so the model supports only launches without aliases, an obligation of EXT-LAUNCH.

</details>

<a id="prog-launch"></a>
#### the launch (`PROG-LAUNCH`)

*Rule* · [Lean comment: `Core/Data/Value.lean` L297-L359](../../Core/Data/Value.lean#L297-L359)

A launch is a grid of CTAs with the same number of threads each, grouped into clusters. Each of the grid, the CTA and the cluster has a shape of up to three dimensions, given by its extents in `x`, `y` and `z`. A cluster has the regular or the preferred cluster shape, and the launch places each cluster in the grid. The launch also fixes whether the cluster launch is explicit, the kernel parameters, the host-created tensor maps, the by-value parameter objects and the special register values that the driver or the machine sets before a thread starts.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Dim3`](../../Core/Data/Value.lean#L362-L367), [`Dim3.get`](../../Core/Data/Value.lean#L369-L373), [`Dim3.prod`](../../Core/Data/Value.lean#L375-L376), [`Dim3.coord`](../../Core/Data/Value.lean#L378-L380), [`ClusterPlace`](../../Core/Data/Value.lean#L382-L389), [`ClusterPlace.uniform`](../../Core/Data/Value.lean#L391-L397), [`Launch`](../../Core/Data/Value.lean#L399-L448) ([concept](#c-launch)), [`Launch.threads`](../../Core/Data/Value.lean#L450-L451) ([concept](#c-launch-threads)), [`Launch.OneDim`](../../Core/Data/Value.lean#L453-L460), [`Launch.tidOf`](../../Core/Data/Value.lean#L462-L464), [`Launch.oneDim_tidOf`](../../Core/Data/Value.lean#L466-L474)

<details>
<summary>Details for reviewers</summary>

- §5.1.6.1 (kernel parameters)
- §2.2.1: "Each CTA has a 1D, 2D, or 3D shape specified by a three-element vector ntid (with
    elements ntid.x , ntid.y , and ntid.z )."
- §2.2.2: "Each cluster of CTAs has 1D, 2D or 3D shape specified by the parameter cluster_nctaid ."
- §2.2.2: "The total number of CTAs across all the dimensions in the cluster is specified by
    cluster_nctarank ."
- §2.2.2: "If the user specifies the cluster dimensions at launch time then it will be treated as
    explicit cluster launch, otherwise it will be treated as implicit cluster launch with default
    dimension 1x1x1."
- §2.2.3: "Each grid of CTAs has 1D, 2D, or 3D shape specified by the parameter nctaid ."
- §10.2: "The total number of threads in a CTA is (%ntid.x * %ntid.y * %ntid.z) ."
- §10.7: "The %nctaid special register contains a 3D grid shape vector, with each element having a
    value of at least 1 ."
- §9.7.17.1: "warp-rank of a warp is defined as: (%tid.x + %tid.y * %ntid.x + %tid.z * %ntid.x *
    %ntid.y) / 32"

**Applies:** Every launch

**Premises:** None; `Launch.clusterGridValid` (PROG-CLUSTER, part of CORRECT-LAUNCH) relates the counts to the shapes.

**Effect:** Representation of the launch; THREAD-SREG reads its geometry. The launch counts its CTAs (`grid`), the threads of a CTA (`block`) and the CTAs of a regular cluster (`clusterSize`), and gives the shapes `nctaid`, `ntid` and `clusterNctaid`, whose extents multiply to these counts in every launch the theorems speak about (`Launch.clusterGridValid`, CORRECT-LAUNCH). `preferredNctaid` is the preferred cluster shape, and `nclusters` and `clusterPlaces` place each cluster (PROG-CLUSTER, EXT-PREFERRED-CLUSTER); unless given, the clusters are the regular clusters tiling the grid (`ClusterPlace.uniform`). Thread `g` is thread `g % block` of CTA `g / block`. The number `g % block` is the linear thread index of §9.7.17.1, `%tid.x + %tid.y * %ntid.x + %tid.z * %ntid.x * %ntid.y`, so the thread's `%tid` is `Launch.tidOf`, with `x` varying fastest. The CTA number `g / block` is the model's own numbering of the CTAs: the CTAs of one cluster are consecutive (PROG-CLUSTER), and PROG-CLUSTER gives the `%ctaid` of each number. The shapes default to the one-dimensional shapes of the counts with regular clusters (`Launch.OneDim`), in which `Launch.tidOf` is `(g % block, 0, 0)` (`Launch.oneDim_tidOf`). Parameters are raw bits. `explicitCluster` says whether the cluster dimensions were given at launch (`%is_explicit_cluster`); a launch without them has the cluster shape 1x1x1 (§2.2.2, CORRECT-LAUNCH). `tensorMaps` supplies the immutable, host-created descriptor properties including allocation class available at launch (EXT-LAUNCH); device-side map mutation and dynamic tensormap-proxy publication are not modeled. `tensorLargeAllocMinBytes` records the actual device attribute when known, never a kernel-selected lower bound. `paramObjects` supplies the actual launch ABI bindings for by-value objects; addresses, declarations and descriptor contents must agree with the passed host objects (EXT-LAUNCH). `paramBytes` supplies the bytes of those objects, which `ld.param` reads (THREAD-MOVE); a byte that is not supplied cannot be read. `sregInit` gives each thread the values of the special registers that THREAD-SREG leaves unconstrained. A kernel theorem quantifies over the launch, so when its premises do not name `sregInit` it holds for every choice of these values.

</details>

<a id="prog-launch-memory"></a>
#### memory at launch (`PROG-LAUNCH-MEMORY`)

*Rule* · [Lean comment: `Core/Data/Value.lean` L476-L492](../../Core/Data/Value.lean#L476-L492)

At kernel start each byte is either not allocated, allocated with an unknown content, or allocated with a known content. An access to an unallocated byte is undefined behaviour, and each execution fixes one value for every unknown byte.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Mem0`](../../Core/Data/Value.lean#L495-L498) ([concept](#c-mem0))

<details>
<summary>Details for reviewers</summary>

- §8.2.6 (initialization: the initial write W0)
- EXT-LAUNCH

**Effect:** `W0` records what it wrote per byte: `none` = not allocated, `some none` = allocated with an unknown value, `some (some b)` = byte `b`. `Execution.initial` fixes each unknown byte within an execution; it is not the absence of a readable byte. That this describes the device memory at kernel start is external fact EXT-LAUNCH.

</details>
