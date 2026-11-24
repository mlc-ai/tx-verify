# Correctness

What it means for a kernel to be correct, how the other chapters fit into that definition, and how far the conclusion carries to real hardware. The first group of rules holds the three interpretations that apply to every kernel: the toolchain implements the ISA, the launch data describes the real launch and meets six obligations, and the Lean source is the compiled program. They state how far the conclusion `Correct` carries to real hardware. The top-level definition is [Correct](#correct) (concept [`Correct`](#c-correct)), in the second group of rules. It has four parts for every launch the kernel admits: no possible execution is unsafe (safety), every execution that cannot grow is complete (progress), the possible executions have a common bound on their size (termination), and the memory after every complete execution satisfies the postcondition (result). The groups after it define each part: which executions are possible, what counts as an error, what progress, fairness and termination mean, and what the memory after the kernel is. The rules of the other chapters supply the fields of `Consistent` and the disjuncts of `Unsafe`. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` and `Assumption/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [Kernels, launches and executions](#kernels-launches-and-executions)
    - [`Kernel`](#c-kernel)
    - [`Launch`](#c-launch)
    - [`Mem0`](#c-mem0)
    - [`Execution`](#c-execution)
    - [`Execution.le`](#c-execution-le)
    - [`Execution.size`](#c-execution-size)
  - [Possible and unsafe executions](#possible-and-unsafe-executions)
    - [`Produces`](#c-produces)
    - [`Consistent`](#c-consistent)
    - [`Unsafe`](#c-unsafe)
    - [`HasUb`](#c-hasub)
  - [Progress and termination](#progress-and-termination)
    - [`Maximal`](#c-maximal)
    - [`AsyncDrained`](#c-asyncdrained)
    - [`Complete`](#c-complete)
    - [`FairRun`](#c-fairrun)
  - [Memory after the kernel](#memory-after-the-kernel)
    - [`FinalMem`](#c-finalmem)
    - [`CoStep`](#c-costep)
    - [`CoBefore`](#c-cobefore)
    - [`CoOrder`](#c-coorder)
    - [`CoMaximal`](#c-comaximal)
    - [`IsFinal`](#c-isfinal)
  - [Correctness](#correctness)
    - [`Launch.Valid`](#c-launch-valid)
    - [`Correct`](#c-correct)
- [Rules](#rules)
  - [How far the conclusion carries to hardware](#how-far-the-conclusion-carries-to-hardware)
      - [the toolchain implements the ISA](#ext-isa) (`EXT-ISA`)
      - [memory and parameters at launch](#ext-launch) (`EXT-LAUNCH`)
      - [clusters of a preferred and a regular shape](#ext-preferred-cluster) (`EXT-PREFERRED-CLUSTER`)
      - [the source is the program](#ext-import) (`EXT-IMPORT`)
  - [The definition of a correct kernel](#the-definition-of-a-correct-kernel)
    - [total correctness](#correct) (`CORRECT`)
    - [launches the kernel's declarations admit](#correct-launch) (`CORRECT-LAUNCH`)
  - [Which executions are possible](#which-executions-are-possible)
    - [possible executions](#correct-consistent) (`CORRECT-CONSISTENT`)
    - [the stages of an asynchronous operation](#dep-async-stage-order) (`DEP-ASYNC-STAGE-ORDER`)
      - [the stages of one operation follow each other](#ext-stage-order) (`EXT-STAGE-ORDER`)
    - [a thread resumes only after what its instruction waits for](#dep-order) (`DEP-ORDER`)
    - [the canonical spin on an mbarrier poll](#dep-canonical-spin) (`DEP-CANONICAL-SPIN`)
  - [What counts as an error](#what-counts-as-an-error)
    - [a poll result used outside a canonical spin](#err-poll-shape) (`ERR-POLL-SHAPE`)
    - [undefined behaviour](#err-unsafe) (`ERR-UNSAFE`)
    - [instruction faults](#err-undefined-instruction) (`ERR-UNDEFINED-INSTRUCTION`)
  - [Progress, fairness and termination](#progress-fairness-and-termination)
    - [the size and growth of an execution](#correct-grow) (`CORRECT-GROW`)
    - [executions that cannot grow](#correct-maximal) (`CORRECT-MAXIMAL`)
    - [launched threads exited, canceled clusters accounted for and work drained](#correct-complete) (`CORRECT-COMPLETE`)
    - [fair runs](#correct-fair) (`CORRECT-FAIR`)
      - [fair scheduling, including asynchronous completion and observation](#ext-fair) (`EXT-FAIR`)
  - [The memory after the kernel](#the-memory-after-the-kernel)
    - [memory after the kernel](#correct-final) (`CORRECT-FINAL`)

## Concepts

The definitions a reader needs to follow the rules, from the parts of an execution up to `Correct`. Each text is the Lean doc comment, and each entry links to its Lean source.

### Kernels, launches and executions

The program, its launch and one candidate execution. The kernel's own assumptions are described in [Assumptions a kernel may declare](assumptions.md).

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

<a id="c-mem0"></a>
#### `Mem0`

*abbrev*

Memory at launch, as written by `W0` (§8.2.6): `none` = not allocated (any access is
undefined); `some none` = allocated with an unknown constant value; `some (some b)` =
byte `b`.

[Lean source: `Core/Data/Value.lean` L495-L498](../../Core/Data/Value.lean#L495-L498)

<a id="c-execution"></a>
#### `Execution`

*structure*

One candidate execution of a kernel (MEM-EXECUTION): the thread traces, reads-from, the
asynchronous effects, and the histories of the synchronization objects.

- `tr`: The finite event trace of each thread, indexed by the thread's id in the grid.
- `rf`: For read `e` and byte `k` of its footprint: the write it read from, or `none` for the initial write `W0`.
- `async`: Independent asynchronous accesses and completion notifications.
- `objects`: One atomic operation history per mbarrier address, including failed polls.
- `initial`: A concrete choice for each unspecified allocated launch byte. Known `Mem0` bytes take precedence. This is initial content, not a mutable memory state.

[Lean source: `Core/Data/Types.lean` L326-L365](../../Core/Data/Types.lean#L326-L365)

<a id="c-execution-le"></a>
#### `Execution.le`

*def*

Preserve all observations, including async reads, completion records and object history.

[Lean source: `Core/Data/Events.lean` L678-L692](../../Core/Data/Events.lean#L678-L692)

<a id="c-execution-size"></a>
#### `Execution.size`

*def*

The counted size of an execution: its thread events and asynchronous stages, plus its
Tensor Memory allocator records and pairings. Failed `try_wait` events do not count.

[Lean source: `Core/Data/Events.lean` L674-L676](../../Core/Data/Events.lean#L674-L676)

### Possible and unsafe executions

The executions the model allows and the executions it rejects as undefined.

<a id="c-produces"></a>
#### `Produces`

*def*

Thread `g` can produce the trace `l` from its initial state.

[Lean source: `Core/Thread/Run.lean` L398-L399](../../Core/Thread/Run.lean#L398-L399)

<a id="c-consistent"></a>
#### `Consistent`

*structure*

The possible executions of kernel `K` under assumptions `A`, launch `L` and launch
memory `mem0`.

- `thr`: CORRECT-CONSISTENT: traces (THREAD-RUN)
- `outside`: CORRECT-CONSISTENT: traces (THREAD-RUN)
- `rf`: MEM-READS-FROM
- `ctaBar`: OBJ-CTA-BARRIER-SYNC: the CTA barrier histories
- `cluster`: OBJ-CLUSTER-BARRIER-SYNC: the cluster barrier histories
- `dependency`: DEP-ORDER: every returned event is ready, and the dependency order with the order of any one object has no cycle
- `shfl`: DEP-WARP-SHUFFLE
- `vote`: DEP-WARP-VOTE
- `warpValue`: DEP-WARP-VOTE (modes), DEP-WARP-REDUX, DEP-WARP-MATCH, DEP-WARP-ACTIVEMASK
- `matrix`: DEP-WARP-MATRIX, DEP-WARP-MMA
- `elect`: DEP-WARP-ELECT
- `warpBar`: DEP-WARP-BARRIER
- `observation`: MEM-OBJECT-ORDER-CAUSALITY: a synchronizing observation never precedes its source in causality
- `object`: MEM-OBJECT-ORDER-CAUSALITY (EXT-OBJECT-ORDER): the synchronizing part of each object's order agrees with causality, one object at a time
- `asyncObject`: MEM-OBJECT-ORDER-CAUSALITY (EXT-ASYNC-OBJECT): an asynchronous update follows its issue in its object's order
- `initFence`: OBJ-MBAR-INIT-PUBLICATION (EXT-INIT-FENCE-ARRIVE): an initialization published by `fence.mbarrier_init` and a cluster barrier precedes, in its object's order, the operations issued after the wait
- `noFuture`: MEM-READ-AXIOMS
- `hidden`: MEM-READ-AXIOMS
- `tma`: DEP-ASYNC-ORIGIN
- `clc`: OBJ-CLC-ORIGIN
- `tensor`: DEP-TENSOR-LOAD-ORIGIN
- `store`: DEP-BULK-WAIT
- `reduce`: DEP-REDUCTION-VALUES
- `atomic`: MEM-ATOMICITY
- `fenceSc`: MEM-FENCE-SC
- `tmemPair`: OBJ-TMEM-ORIGIN
- `tmemPairCompletion`: OBJ-TMEM-COMPLETION-PREFIX
- `tmemPairResult`: OBJ-TMEM-ALLOC-RESULT
- `tcCommit`: OBJ-MBAR-ORIGIN: per-target commit delivery
- `mmaCompletion`: DEP-TC-COMPLETION-CLOSURE: same-source identical-footprint D writes.
- `tcRead`: DEP-TC-LOAD-VALUE
- `asm`: ASM-INTERFACE: what each kernel assumption adds

[Lean source: `Core/Assembly/Execution.lean` L66-L140](../../Core/Assembly/Execution.lean#L66-L140)

<a id="c-unsafe"></a>
#### `Unsafe`

*def*

The execution `X` has undefined behaviour (ERR-UNSAFE): the disjunction of every safety check of
the model and of the kernel assumptions' `ub` conditions.

[Lean source: `Core/Assembly/Execution.lean` L206-L217](../../Core/Assembly/Execution.lean#L206-L217)

<a id="c-hasub"></a>
#### `HasUb`

*def*

Some event of `X` is an undefined-behaviour event (kind `ub`).

[Lean source: `Core/Assembly/Safety.lean` L502-L503](../../Core/Assembly/Safety.lean#L502-L503)

### Progress and termination

Executions that cannot grow, complete executions and fair runs.

<a id="c-maximal"></a>
#### `Maximal`

*def*

`X` is possible and no possible execution extends `X` by more counted events
(`Execution.size`, which does not count failed polls).

[Lean source: `Core/Assembly/Correctness.lean` L33-L37](../../Core/Assembly/Correctness.lean#L33-L37)

<a id="c-asyncdrained"></a>
#### `AsyncDrained`

*def*

Every issued asynchronous operation has finished: every stage that completes it
(`AsyncCopy.FinalStage`, the table of DEP-ASYNC-STAGE-ORDER) is present.

[Lean source: `Core/Assembly/Correctness.lean` L63-L66](../../Core/Assembly/Correctness.lean#L63-L66)

<a id="c-complete"></a>
#### `Complete`

*def*

`X` is complete: every launched thread has exited or belongs to a canceled cluster, the
asynchronous work is drained (`AsyncDrained`), and every paired Tensor Memory allocator request
belongs to a completed collective operation (`Tmem.Pair.Drained`).

[Lean source: `Core/Assembly/Correctness.lean` L114-L119](../../Core/Assembly/Correctness.lean#L114-L119)

<a id="c-fairrun"></a>
#### `FairRun`

*def*

The run `Xs` is fair (CORRECT-FAIR): every member is possible, each extends the previous one,
and whenever a member can be extended by a counted event, a later member has more counted
events.

[Lean source: `Core/Assembly/Progress.lean` L78-L84](../../Core/Assembly/Progress.lean#L78-L84)

### Memory after the kernel

The coherence order of the writes and the final value of each byte.

<a id="c-finalmem"></a>
#### `FinalMem`

*abbrev*

Memory after the kernel, per byte (`none` = not allocated).

[Lean source: `Core/Assembly/Correctness.lean` L190-L191](../../Core/Assembly/Correctness.lean#L190-L191)

<a id="c-costep"></a>
#### `CoStep`

*def*

One coherence-order edge between two writes that cover a byte `l`: `ByteCausality` (causality,
§8.10.1); an atomic read-modify-write reading from another one morally strong with it at the same
footprint (MEM-ATOMICITY); or a write `ByteCausality`-before a read of `l` from another write
morally strong with it (§8.9.6, §8.10.6).

[Lean source: `Core/Assembly/Correctness.lean` L193-L202](../../Core/Assembly/Correctness.lean#L193-L202)

<a id="c-cobefore"></a>
#### `CoBefore`

*def*

The coherence order of the writes that the execution determines (§8.9.6).

[Lean source: `Core/Assembly/Correctness.lean` L219-L221](../../Core/Assembly/Correctness.lean#L219-L221)

<a id="c-coorder"></a>
#### `CoOrder`

*structure*

A coherence order of the execution's writes (§8.9.6): a strict order that relates every two
distinct overlapping morally strong writes and contains each `CoBefore` edge whose reverse is not
in `CoBefore`.

- `irrefl`
- `trans`
- `strong`
- `before`

[Lean source: `Core/Assembly/Correctness.lean` L223-L231](../../Core/Assembly/Correctness.lean#L223-L231)

<a id="c-comaximal"></a>
#### `CoMaximal`

*def*

`w` writes byte `l` and no write of `l` follows it in `co`.

[Lean source: `Core/Assembly/Correctness.lean` L233-L237](../../Core/Assembly/Correctness.lean#L233-L237)

<a id="c-isfinal"></a>
#### `IsFinal`

*def*

`m` is the memory after `X`: for a coherence order `co` of `X`, each byte holds the write
that every other write to it precedes in `co`, the value all its co-maximal writes agree on, or
its launch content.

[Lean source: `Core/Assembly/Correctness.lean` L239-L249](../../Core/Assembly/Correctness.lean#L239-L249)

### Correctness

The launches a kernel admits and the definition of a correct kernel.

<a id="c-launch-valid"></a>
#### `Launch.Valid`

*def*

The launch is one the kernel's declarations admit.

[Lean source: `Core/Assembly/Correctness.lean` L294-L299](../../Core/Assembly/Correctness.lean#L294-L299)

<a id="c-correct"></a>
#### `Correct`

*structure*

Total correctness of kernel `K` under assumptions `A`, for launch `L`, launch memory `mem0`
and postcondition `post` (CORRECT). Each field holds for a launch the kernel admits
(`Launch.Valid`).

- `safe`: The kernel uses one `tcgen05` CTA-group qualifier (PROG-TC-CTA-GROUP), and no possible execution is unsafe (ERR-UNSAFE).
- `progress`: Every maximal possible execution is complete (CORRECT-MAXIMAL, CORRECT-COMPLETE).
- `terminates`: One bound covers the number of counted events of every possible execution.
- `result`: The memory after every complete possible execution satisfies `post` (CORRECT-FINAL).

[Lean source: `Core/Assembly/Correctness.lean` L523-L537](../../Core/Assembly/Correctness.lean#L523-L537)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### How far the conclusion carries to hardware

Three interpretations that every kernel's theorem relies on. A theorem says nothing about a run on hardware that breaks one of them.

<a id="ext-isa"></a>
##### the toolchain implements the ISA (`EXT-ISA`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/Correctness.lean` L311-L354](../../Core/Assembly/Correctness.lean#L311-L354)

The model takes `ptxas` and the hardware to implement the PTX ISA, its memory consistency model included (§8), for the instructions a kernel uses. `ptxas` may reorder or combine instructions only as far as the memory model allows. The model's axioms are stated over PTX program order, so a theorem carries to hardware only as far as this holds. For the execution layer (DEP-ORDER), the model also trusts that `ptxas` and the hardware keep the program order of the synchronizing and blocking instructions and of the canonical spins, as listed under Review.

Source:

- - §9.7.15.10: "vote.sync will cause executing thread to wait until all non-exited threads corresponding to membermask have executed vote.sync with the same qualifiers and same membermask value before resuming execution." - §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited threads from its warp and marks warps’ arrival at barrier."

Direction: `trust` (if `ptxas` or the hardware deviates from the ISA, no theorem transfers). (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH)). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Evidence:** §1.1 ("PTX defines a virtual machine and ISA for general purpose parallel thread execution. PTX programs are translated at install time to the target hardware instruction set.") and §1.2 ("Provide a stable ISA that spans multiple GPU generations."): the ISA is the specification the translator and the hardware are documented to meet. That they meet it is trusted. The model does not check it. It covers only what the ISA text states; every reading the model takes beyond that text is a separate EXT note (indexed in `Core/README.md`), and each kernel's `Theorem.lean` lists the ones that apply to it (see Disclosure in `Core/README.md`).

**Effect:** Disclosed by every kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.

</details>

<a id="ext-launch"></a>
##### memory and parameters at launch (`EXT-LAUNCH`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/Correctness.lean` L356-L442](../../Core/Assembly/Correctness.lean#L356-L442)

The model takes `mem0` to be the device memory when the kernel starts and the launch data (the shapes `Launch.nctaid`, `Launch.ntid`, `Launch.clusterNctaid` with their counts, `Launch.explicitCluster`, `Launch.params`, `Launch.paramObjects`, `Launch.tensorMaps`) to describe what the host passed. A theorem carries to a real launch only when that launch also meets the six obligations listed in this note, which the model does not check.

Direction: `trust` (the six obligations are facts about the launch environment that the model does not check; for a launch that does not meet one of them, no theorem transfers). (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH)). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Effect:** The memory and the parameters the kernel starts with. `mem0` is the device memory when the kernel starts, and `Launch.params` are the parameter values passed. The grid, CTA and cluster shapes are the dimensions the host launched with, and `Launch.explicitCluster` says whether it gave cluster dimensions. At a `.local` location `⟨.local, g, x⟩` it is byte `x` of thread `g`'s local memory (allocated or not), and at a `.const` location `⟨.const, 0, x⟩` byte `x` of the constant memory as the host initialized it. `Launch.paramObjects` supplies the actual by-value parameter declarations and their generic addresses; bindings must agree with `Kernel.paramObjects` and the launch ABI, including object identity, size, alignment and disjoint storage. `Launch.paramBytes name k`, when supplied, is byte `k` of the by-value parameter object `name` as the host passed it; how the host's argument is laid out in those bytes is the launch's. A `tensorMaps` entry at such an address must describe the actual descriptor passed by value in that parameter object. `Launch.tensorLargeAllocMinBytes`, when supplied, must equal the device-reported `CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE`. The descriptor allocation class must match the actual opaque tensor map. `Launch.tensorMaps` records the properties of actual host-created, immutable tensor maps at their addresses, published before launch. The host proof or review must establish these properties from descriptor construction; they are not conclusions about the kernel's output. Device-side updates are outside this launch-only interface. Writes before the launch are ordered before every event of the kernel, and every event of the kernel before the memory is read afterwards (§8.9.4: start and end of a kernel synchronize).

**Evidence:** CUDA C++ Programming Guide (kernel launch, stream ordering).

</details>

<a id="ext-preferred-cluster"></a>
##### clusters of a preferred and a regular shape (`EXT-PREFERRED-CLUSTER`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/Correctness.lean` L444-L485](../../Core/Assembly/Correctness.lean#L444-L485)

The model takes a launch to place its clusters as the CUDA launch attributes allow: each cluster has the regular cluster shape or the preferred cluster shape, the clusters tile the grid, and each cluster's origin lies on the lattice of the regular shape. A launch may mix the two shapes in any such tiling, and the model's theorems cover every tiling. `Launch.clusterNctaid` is the cluster dimension (`clusterDim`) and `Launch.preferredNctaid` the preferred cluster dimension (`preferredClusterDim`) of the launch; without a preferred dimension the two are equal. `Launch.clusterPlaces` gives each cluster's origin `%ctaid`, its shape, and the `%clusterid` and `%nclusterid` its threads read. `Launch.clusterGridValid` admits a placement when each grid extent is a whole number of regular and of preferred extents, each preferred extent is a whole number of regular extents in `x` and `y` and equal to the regular extent in `z`, each cluster has one of the two shapes and lies in the grid with its origin a multiple of the regular extent in each dimension, the clusters have exactly the grid's CTAs with no `%ctaid` twice, and the clusters have distinct `%clusterid`, each below its `%nclusterid`. A grid of regular clusters is the special case `ClusterPlace.uniform`.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Evidence:** CUDA Driver API, `CUlaunchAttributeValue` (CUDA 12.8 and later): for `clusterDim`, “x - The X dimension of the cluster, in blocks. Must be a divisor of the grid X dimension.” (and likewise for y and z); for `preferredClusterDim`, “x - The X dimension of the preferred cluster, in blocks. Must be a divisor of the grid X dimension, and must be a multiple of the x field of CUlaunchAttributeValue::clusterDim.” (and likewise for y), and for z “Must be equal to the z field of CUlaunchAttributeValue::clusterDim.” The CUDA Runtime API documentation of the preferred cluster dimension says that blocks are grouped into preferred clusters on a best-effort basis and that the device may launch the regular clusters instead.

**Why it is not spec text:** The PTX ISA does not mention preferred clusters. The CUDA documentation does not say whether one launch mixes the two shapes, how a mixed grid is tiled, which part of the grid gets which shape, or which `%clusterid` and `%nclusterid` the threads of a preferred cluster read. The model admits every tiling by the two shapes whose origins lie on the lattice of the regular shape, and leaves the identifiers to the launch apart from their being distinct and below their counts. The alignment to the regular lattice is the reading's choice; it follows from tiling when every cluster has the regular shape.

**Effect:** A theorem holds for every placement `Launch.clusterGridValid` admits. If hardware places clusters outside this set (for example a preferred cluster whose origin is not on the regular lattice), the launch is outside the theorem. Each cluster's registers, peers, CTA pairs, multicast masks, cluster barrier and cluster launch control response are those of its own cluster (PROG-CLUSTER). Disclosed by every kernel whose statement names `Launch.preferredNctaid` or `Launch.clusterPlaces`: none.

</details>

<a id="ext-import"></a>
##### the source is the program (`EXT-IMPORT`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/Correctness.lean` L487-L497](../../Core/Assembly/Correctness.lean#L487-L497)

The model takes the Lean program of each kernel to be the parse of the `.ptx` file that the compiler produced for that kernel: `Kernels/<K>/Ptx.lean` is the parse of `Kernels/<K>/<k>.ptx`. The Python parser and exporter that produce it are outside Lean.

<details>
<summary>Details for reviewers</summary>

**Evidence:** `tests/test_semantics.py` regenerates `Ptx.lean` from the `.ptx` file, and the `.ptx` file from the `.cu` source with nvcc.

**Effect:** Disclosed by every kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.

</details>

### The definition of a correct kernel

The top-level definition. Every kernel theorem states `Correct` for its kernel, its own assumptions (ASM-INTERFACE), launch, launch memory and postcondition; the launch premise restricts it to the launches the kernel's declarations admit.

<a id="correct"></a>
#### total correctness (`CORRECT`)

*Rule* · [Lean comment: `Core/Assembly/Correctness.lean` L500-L520](../../Core/Assembly/Correctness.lean#L500-L520)

A kernel is correct for a launch, its launch memory and a postcondition when, if the launch is valid, the kernel uses one `tcgen05` CTA-group qualifier, no possible execution is unsafe, every maximal possible execution is complete, the possible executions have a common bound on their number of counted events, and the memory after every complete execution satisfies the postcondition.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`Correct`](../../Core/Assembly/Correctness.lean#L523-L537) ([concept](#c-correct))

<details>
<summary>Details for reviewers</summary>

- none (the statement of every theorem)

**Effect:** For a launch the kernel admits (CORRECT-LAUNCH), the source obeys PROG-TC-CTA-GROUP. No possible execution is unsafe. An execution that cannot grow is complete, that is, every thread has exited or belongs to a canceled cluster, every asynchronous operation has finished, and every paired Tensor Memory allocator request belongs to a completed collective operation (CORRECT-COMPLETE). One bound covers the number of counted events. After a complete execution the memory satisfies `post`. Together, `progress` and `terminates` give that every fair run reaches a complete execution (CORRECT-FAIR, `Correct.exits`).

</details>

<a id="correct-launch"></a>
#### launches the kernel's declarations admit (`CORRECT-LAUNCH`)

*Rule* · [Lean comment: `Core/Assembly/Correctness.lean` L251-L291](../../Core/Assembly/Correctness.lean#L251-L291)

A launch is valid for a kernel when its counts are the products of its shapes and the grid is a whole number of clusters in each dimension, the CTA size is at most the product of the `.maxntid` extents and equals the `.reqntid` extents in each dimension, and every `.ptr` parameter is a multiple of its alignment. Correctness concludes nothing about any other launch.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Launch.Valid`](../../Core/Assembly/Correctness.lean#L294-L299) ([concept](#c-launch-valid)), [`Launch.oneDim_reqntid`](../../Core/Assembly/Correctness.lean#L301-L305)

<details>
<summary>Details for reviewers</summary>

- §11.5.2 (.maxntid): "The maximum number of threads in the thread block, computed as the product of
    the maximum extent specified for each dimension, is guaranteed not to be exceeded in any
    invocation of the kernel in which this directive appears. Exceeding the maximum number of
    threads results in a runtime error or kernel launch failure."
- §11.5.3 (.reqntid): "The size of each CTA dimension specified in any invocation of the kernel is
    required to be equal to that specified in this directive. Specifying a different CTA dimension
    at launch will result in a runtime error or kernel launch failure."
- §5.1.6.3 (.ptr): "If no alignment is specified, the memory pointed to is assumed to be aligned to
    a 4 byte boundary."
- PROG-CLUSTER (`Launch.clusterGridValid`)

**Applies:** The launch `L` of kernel `K` in every CORRECT conclusion

**Premises:** None; this is the premise of the conclusions.

**Effect:** CORRECT concludes nothing about a launch outside `Launch.Valid`: hardware fails such a launch, no hardware launch has its counts and shapes, or the compiled code relies on what it violates.

</details>

### Which executions are possible

The conjunction of the thread rules and the execution constraints of every chapter.

<a id="correct-consistent"></a>
#### possible executions (`CORRECT-CONSISTENT`)

*Rule* · [Lean comment: `Core/Assembly/Execution.lean` L42-L63](../../Core/Assembly/Execution.lean#L42-L63)

An execution is possible when the trace of every launched thread is one that the thread rules produce from the initial state, threads outside the launch have no events, and the execution satisfies every execution constraint of the model. These constraints cover reads-from and the memory axioms, blocking and collective operations, the order of each synchronization object, the origin of asynchronous effects, and what each kernel assumption adds.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Consistent`](../../Core/Assembly/Execution.lean#L66-L140) ([concept](#c-consistent)), [`Consistent.reduceUnique`](../../Core/Assembly/Execution.lean#L142-L146), [`Consistent.reduceAcyclic`](../../Core/Assembly/Execution.lean#L148-L152)

<details>
<summary>Details for reviewers</summary>

- §8 (an execution is possible when it satisfies the axioms); several fields rest on named readings
    (EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT, EXT-ENABLES-OBJECT, EXT-TMEM-ALLOC-ORDER, EXT-STAGE-ORDER,
    EXT-TCACQUIRE, EXT-TC-EXEC-ORDER, EXT-PAIR-ASYNC, EXT-INIT-FENCE-ARRIVE), so the conjunction is
    a reading

**Effect:** The conjunction of the rules above. Each field names its rule. Each thread's trace is one that its thread rules allow from the initial state, and threads outside the launch have none (THREAD-RUN). Blocking and waiting are one field, `Consistent.dependency` (DEP-ORDER); the value rules of the collectives keep only what they say about values. `Consistent.reduceUnique` and `Consistent.reduceAcyclic` derive the two conclusions of EXT-TMA-REDUCE-ATOMIC from MEM-ATOMICITY.

</details>

<a id="dep-async-stage-order"></a>
#### the stages of an asynchronous operation (`DEP-ASYNC-STAGE-ORDER`)

*Rule* · [Lean comment: `Core/Assembly/Waiting.lean` L26-L76](../../Core/Assembly/Waiting.lean#L26-L76)

The stages of one asynchronous operation follow its issue and each other as listed under Effect, and one table lists the stages that complete each operation.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`StageEdge`](../../Core/Assembly/Waiting.lean#L79-L109), [`StageOrder`](../../Core/Assembly/Waiting.lean#L111-L118), [`IssueStage`](../../Core/Assembly/Waiting.lean#L120-L129), [`AsyncCopy.FinalStage`](../../Core/Assembly/Waiting.lean#L131-L141)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28 (copy stages)
- §9.7.15.16.18 (cp.async.mbarrier.arrive triggers its arrive-on upon completion of the prior
    cp.async operations)
- §9.7.18.12.1 (tcgen05.commit arrives on completion)
- §9.7.15.18
- §9.7.10.28.1: "Asynchronous operations may be tracked by either of the completion mechanisms or
    both mechanisms. The tracking mechanism is instruction/instruction-variant specific."
- EXT-STAGE-ORDER

**Applies:** The stages of asynchronous copies, stores, MMAs, commits and CLC requests

**Premises:** Every edge relates stages that are present.

**Effect:** `StageOrder` is shared by both layers: it is part of `stageCausality` (MEM-OBJECT-ORDER-CAUSALITY) and of the dependency order (`DepStep`, DEP-ORDER). `IssueStage` belongs to the dependency order only. The issue precedes every stage except a notification, a bulk store's full completion, an MMA's completion and the arrive-on of a `cp.async.mbarrier.arrive`, which follow other stages of their operation (`IssueStage`). The read of a slot precedes its write, and the write of a slot precedes the notification that signals it (`Part.target`). CLC resolution precedes each response write. A store's reads precede its read completion, its writes and old-value reads precede its full completion, and its read completion precedes its full completion. MMA operand reads precede the MMA completion, and a tracked MMA completion precedes its commit notification. The write of a tracked `cp.async` precedes the arrive-on of `cp.async.mbarrier.arrive`. The source read of an element-wise linear operation precedes each element write, and each element write and old-value read precedes its `.write .copy` stage, which marks its completion. `FinalStage` is the one table of the stages that complete an operation, by its completion mechanism (§9.7.10.28.1): the notification of a linear copy completed through an mbarrier, the write of any other linear copy, the arrive-on of `cp.async.mbarrier.arrive`, the completion of `tcgen05.mma` and `tcgen05.cp`, the notification at each target of a CLC request, the notification of a tensor load, the full completion of a tensor store, and the arrive-on at each target of `tcgen05.commit`. `AsyncDrained` (CORRECT-COMPLETE) and `SharedUse` (ERR-SHARED-LIFETIME) read it.

</details>

<a id="ext-stage-order"></a>
##### the stages of one operation follow each other (`EXT-STAGE-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/WaitOrder.lean` L234-L272](../../Core/Assembly/WaitOrder.lean#L234-L272)

Within one operation, the issue precedes the completion, the operand reads of a tracked `tcgen05.mma` precede its completion, and the resolution of a CLC request precedes the write of its response. (1) The issue of an instruction or stage precedes its completion: the two points of one node (`StageOrder`). (2) The reads of the operands of a tracked `tcgen05.mma` precede its completion, and the resolution of a `clusterlaunchcontrol.try_cancel` request precedes the write of its response (`StageEdge`).

Source:

- - §9.7.10.28.5.3 (1): "Upon the completion of the asynchronous copy operation, the complete-tx operation, with completeCount argument equal to amount of data copied in bytes, will be performed on the mbarrier object specified by the operand mbar" - §9.7.18.12.1 (1): "Upon the completion of the tracked asynchronous tcgen05 operations, the signal specified by the .completion_mechanism is triggered by the system on the mbarrier object" - §9.7.18.10.10.1 (2, tcgen05.mma): "is an asynchronous instruction which initiates an MxNxK matrix multiply and accumulate operation, D = A*B+D" - §9.7.15.18 (2, try_cancel): "asynchronously writes an opaque response to shared memory indicating whether the operation succeeded or failed"

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The sentences state that completion follows initiation and that a response indicates the outcome. They state no order between the operand reads and the completion, or between the resolution and the response write. The edges read completion as following the initiation, and the result as following the decision that it reports.

**Evidence:** Each edge relates two points of one hardware operation (an operation cannot complete before it is issued or report an outcome before it is decided), and no edge of this reading leads from one operation to a different one.

**Effect:** Executions in which a completion precedes its own issue, an MMA completes before its operand reads, or a CLC response is written before its request resolves are removed from `Consistent` (`Consistent.observation`, `.object`, `.dependency`, ERR-SHARED-LIFETIME). If hardware allows them, the model excludes executions that may occur. Disclosed by every kernel whose statement names `Op.mbarInit`, `Op.mbarArrive`, `Op.mbarWait`, `Op.barSync`, `Op.barSyncN`, `Op.barArrive`, `Op.cluster`, `Op.cpBulk`, `Op.cpTensor`, `Op.cpTensorStore`, `Op.tcMma`, `Op.tcCommit` or `Op.clcTryCancel`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm, TmaCopy.

</details>

<a id="dep-order"></a>
#### a thread resumes only after what its instruction waits for (`DEP-ORDER`)

*Rule* · [Lean comment: `Core/Assembly/Dependency.lean` L24-L157](../../Core/Assembly/Dependency.lean#L24-L157)

A blocking instruction returns only when every need of its wait condition is filled, and every later event of its thread comes after the return; where the manual says "non-exited", a participant's exit fills its need. A poll returns at once, and when it reports a completed phase and is a canonical spin, the events after the spin's exit come after the return. Each return comes after the events that fill its needs, and the dependency order these edges form, together with the order of any one synchronization object, has no cycle.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Resume`](../../Core/Assembly/Dependency.lean#L189-L200), [`TcKind.resume`](../../Core/Assembly/Dependency.lean#L202-L205), [`Kind.resume`](../../Core/Assembly/Dependency.lean#L207-L223), [`Need`](../../Core/Assembly/Dependency.lean#L225-L232), [`needsIf`](../../Core/Assembly/Dependency.lean#L235-L236), [`warpLane`](../../Core/Assembly/Dependency.lean#L238-L239), [`warpLanes`](../../Core/Assembly/Dependency.lean#L241-L242), [`maskNeeds`](../../Core/Assembly/Dependency.lean#L244-L251), [`tcNeeds`](../../Core/Assembly/Dependency.lean#L253-L256), [`ctaBarWarpNeeds`](../../Core/Assembly/Dependency.lean#L258-L265), [`CtaBarCounted`](../../Core/Assembly/Dependency.lean#L267-L277), [`ctaBarNeeds`](../../Core/Assembly/Dependency.lean#L279-L285), [`clusterWarpNeeds`](../../Core/Assembly/Dependency.lean#L287-L295), [`ClusterCounted`](../../Core/Assembly/Dependency.lean#L297-L308), [`clusterNeeds`](../../Core/Assembly/Dependency.lean#L310-L316), [`ReuseRelease`](../../Core/Assembly/Dependency.lean#L318-L327), [`Tmem.Pair.AllocResultFill`](../../Core/Assembly/Dependency.lean#L331-L334), [`Tmem.Pair.allocResultNeeds`](../../Core/Assembly/Dependency.lean#L336-L340), [`Tmem.Pair.AllocResultFill.written`](../../Core/Assembly/Dependency.lean#L365-L374), [`Tmem.Pair.allocResultNeeds_node`](../../Core/Assembly/Dependency.lean#L342-L351), [`Tmem.Pair.allocResultNeeds_transport`](../../Core/Assembly/Dependency.lean#L353-L363), [`resourceNeeds`](../../Core/Assembly/Dependency.lean#L378-L393), [`groupNeeds`](../../Core/Assembly/Dependency.lean#L395-L399), [`pollNeeds`](../../Core/Assembly/Dependency.lean#L401-L403), [`KindNeeds`](../../Core/Assembly/Dependency.lean#L405-L437), [`kindNeeds_free`](../../Core/Assembly/Dependency.lean#L439-L444), [`Needs`](../../Core/Assembly/Dependency.lean#L446-L450), [`Ready`](../../Core/Assembly/Dependency.lean#L452-L456), [`Witness`](../../Core/Assembly/Dependency.lean#L458-L460), [`Returned`](../../Core/Assembly/Dependency.lean#L462-L471), [`SpinExit`](../../Core/Assembly/Dependency.lean#L473-L477), [`Resumes`](../../Core/Assembly/Dependency.lean#L479-L485), [`DepStep`](../../Core/Assembly/Dependency.lean#L487-L495), [`DependencyOk`](../../Core/Assembly/Dependency.lean#L497-L502), [`Witness.of_need`](../../Core/Assembly/Dependency.lean#L504-L508), [`Resumes.of_blocking`](../../Core/Assembly/Dependency.lean#L510-L515), [`DepStep.of_witness`](../../Core/Assembly/Dependency.lean#L517-L520), [`DepStep.of_resumes`](../../Core/Assembly/Dependency.lean#L522-L525), [`maskNeeds_mem`](../../Core/Assembly/Dependency.lean#L527-L536), [`ctaBarCounted_witnessed`](../../Core/Assembly/Dependency.lean#L538-L547), [`covered_witnessed`](../../Core/Assembly/Dependency.lean#L558-L574), [`allocResult_witnessed`](../../Core/Assembly/Dependency.lean#L549-L556)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.10: "vote.sync will cause executing thread to wait until all non-exited threads
    corresponding to membermask have executed vote.sync with the same qualifiers and same
    membermask value before resuming execution."
- §9.7.10.6 (shfl.sync): "wait until all non-exited threads corresponding to membermask have
    executed shfl.sync with the same qualifiers and same membermask value before resuming execution"
- §9.7.15.11: "match.sync will cause executing thread to wait until all non-exited threads from
    membermask have executed match.sync with the same qualifiers and same membermask value before
    resuming execution."
- §9.7.15.13: "redux.sync will cause the executing thread to wait until all non-exited threads
    corresponding to membermask have executed redux.sync with the same qualifiers and same
    membermask value before resuming execution."
- §9.7.15.15: "The mandatory .sync qualifier indicates that elect causes the executing thread to
    wait until all threads in the membermask execute the elect instruction before resuming
    execution."
- §9.7.15.2 (bar.warp.sync)
- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited threads
    from its warp and marks warps’ arrival at barrier."
- §9.7.15.1 (bar.sync waits for the non-exited threads of all other warps participating)
- §9.7.14.7: "Barriers exclusively waiting on arrivals from exited threads are always released."
- §9.7.15.3 (barrier.cluster: the warp rendezvous and the wait for all non-exited threads)
- §9.7.16.5.15: "The mandatory .sync qualifier indicates that ldmatrix causes the executing thread
    to wait until all threads in the warp execute the same ldmatrix instruction before resuming
    execution."
- §9.7.16.5.17: "The mandatory .sync qualifier indicates that movmatrix causes the executing thread
    to wait until all threads in the warp execute the same movmatrix instruction before resuming
    execution."
- §9.7.16.5.14 (mma), §9.7.16.5.16 (stmatrix), §9.7.16.6.3 (mma.sp)
- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
    executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
    before resuming execution."
- §9.7.18.8.5 (.sync): "causes the executing thread to wait until all threads in the warp execute
    the same tcgen05.wait_operation instruction before resuming execution"
- §9.7.18.7.1: "The tcgen05.alloc blocks if the requested amount of Tensor Memory is not available
    and unblocks as soon as the requested amount of Tensor Memory becomes available for
    allocation."
- §9.7.18.7.1: "When .cta_group::2 is specified, one warp from each of the peer CTAs must
    collectively perform the allocation and de-allocation."
- §9.7.18.7.1: "tcgen05.dealloc may block to collectively performs the deallocation with the other
    peer CTA ’s warp"
- §9.7.10.28.6.2 (cp.async.bulk.wait_group)
- §9.7.10.28.3.3 (cp.async.wait_group)
- §9.7.15.16.19: "If the phase is not complete, the executing thread may be suspended."
- §9.7.15.16.19: "Suspended thread resumes execution when the specified phase completes OR before
    the phase completes following a system-dependent time limit."
- §9.7.15.16.19: "mbarrier.test_wait is a non-blocking instruction which tests for the completion
    of the phase."
- EXT-TMEM-ALLOC-RESULT-ORDER
- EXT-ENABLES-OBJECT
- EXT-STAGE-ORDER
- EXT-WARP-INSTANCE
- EXT-SETMAXNREG-EFFECTIVE (the wait for the CTA's register pool is not a need)

**Applies:** every event kind (`Kind.resume` and `KindNeeds` are total)

**Effect:** `Consistent.dependency`. Used by Maximal and FairRun through Consistent, by ERR-NONUNIFORM-GUARD (the dependency order of EXT-DEPENDENCY-ORDER) and by ERR-SHARED-LIFETIME. Not used by `baseCausality`, `stageCausality`, `ObservationCausal`, `ObjectCoherent` or any memory axiom. `Kind.resume` classifies every kind: free (the thread goes on at once; loads, stores, atomics, issues of asynchronous operations, fences, queries), blocking with the completed instance recorded (vote, ballot, redux, match, shfl, elect, `bar.warp.sync`, the warp-level matrix instructions: the event exists only when its needs are filled), blocking at the arrival (`bar.sync`, `bar.arrive`, `barrier.cluster`, the group waits, setmaxnreg, the `.sync` tcgen05 instructions: the event exists at the arrival and returns when the next event of its thread exists), and observing (the mbarrier polls). `KindNeeds` lists the needs of each kind: - `shfl.sync`, `vote.sync` (both forms), `redux.sync`, `match.sync`: for each lane of the member mask, its event of the same instance with the same qualifiers, or its exit before it (`MaskWait`, DEP-WARP-INSTANCE). - `elect.sync`, `bar.warp.sync`: for each lane of the mask, its event of the instance (its label). - warp-level matrix instructions: for each of the 32 lanes, its event of the same ordinal, or its exit short of it (the instance then exists and ERR-ALIGNED-MISMATCH reports the undefined behaviour). - setmaxnreg: for each of the 32 lanes, the same request (`SetMaxNReg.SameRequest`). - `tcgen05.ld`, `tcgen05.st` and their waits: for each lane of the warp, its warp-collective tcgen05 event of the same ordinal (`Execution.TcK`). - Tensor Memory allocation management: the lanes as above; the allocator has performed the request (`Tmem.Pair.Performed`); when the instruction waits for its operation (`Tmem.Pair.MustWait`), the operation is complete (`Tmem.Pair.Covered`), for a `cta_group::2` instruction the peer warp's lanes are needs, and for an allocation the lanes of every release that last freed a column of the returned range are needs (`ReuseRelease`). For nonleader lanes of an allocation, the actual result store of the local leader is also a need (`Tmem.Pair.AllocResultFill`, EXT-TMEM-ALLOC-RESULT-ORDER). - `bar.sync`, `bar.arrive`: for each lane of the warp, its arrival in the event's record, or its exit recorded before that record; for `bar.sync`, also the release of its generation, and every arrival of the generation and every exit recorded up to the release (`CtaBarCounted`). - `barrier.cluster.arrive`, `barrier.cluster.wait`: for each lane of the warp, its event in the same record, or its exit recorded before it; for a wait, also every arrival of the phase it waits for and every exit of the cluster recorded before its record (`ClusterCounted`). - `cp.async.bulk.wait_group{.read}`, `cp.async.wait_group`: the stages `GroupWaitStages` of every covered operation (DEP-ASYNC-STAGE-ORDER). - a successful poll: each counter update of the phase it observed (`MbarObserved`); a failed poll has no need. `Returned` says which events must be ready, `Witness` which nodes fill a need, and `Resumes` which events follow a return: every later event of the thread of a blocking event, and, for a successful poll of a canonical spin, every later event of its thread (`SpinExit`); a poll whose result is not read, and a failed poll, are followed by nothing. `DependencyOk.acyclic` excludes a cycle of `DepStep` with the order of one object of `OrderObject.Enabling`.

</details>

<a id="dep-canonical-spin"></a>
#### the canonical spin on an mbarrier poll (`DEP-CANONICAL-SPIN`)

*Rule* · [Lean comment: `Core/Assembly/PollShape.lean` L17-L60](../../Core/Assembly/PollShape.lean#L17-L60)

A canonical spin is a loop that consists of one mbarrier poll followed by one or two branches: a branch on the poll's predicate leaves the loop or returns to the poll, and the other branch, if there is one, returns to the poll unconditionally. The loop repeats the poll with unchanged operands until it returns True and then leaves, and every instruction that reads the predicate is the branch of such a loop. The dependency order uses the exit of a canonical spin (`SpinExit`, DEP-ORDER), and ERR-POLL-SHAPE rejects every other use of a poll result.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Opnd.regs`](../../Core/Assembly/PollShape.lean#L63-L66), [`Addr.regs`](../../Core/Assembly/PollShape.lean#L68-L72), [`Op.readRegs`](../../Core/Assembly/PollShape.lean#L74-L140), [`Instr.readsReg`](../../Core/Assembly/PollShape.lean#L142-L144), [`Kernel.targeted`](../../Core/Assembly/PollShape.lean#L150-L155), [`Kernel.pollReg`](../../Core/Assembly/PollShape.lean#L157-L161), [`Kernel.pollDst`](../../Core/Assembly/PollShape.lean#L163-L167), [`Kernel.spinExit?`](../../Core/Assembly/PollShape.lean#L169-L180), [`Kernel.SpinShape`](../../Core/Assembly/PollShape.lean#L182-L183), [`Kernel.spinPred`](../../Core/Assembly/PollShape.lean#L185-L189), [`Kernel.SpinPred`](../../Core/Assembly/PollShape.lean#L191-L192), [`Kernel.CanonicalSpin`](../../Core/Assembly/PollShape.lean#L194-L196)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16.19: "mbarrier.try_wait is a potentially blocking instruction which tests for the
    completion of the phase."
- §9.7.15.16.19 (an example of shape B): "waitLoop:
    mbarrier.try_wait.phase_type::primary.relaxed.cluster.shared.b64 complete, [shMem], %r1;
    @!complete bra waitLoop;"
- §9.7.15.16.19 (Examples 1a, 2 and 5, with a `nanosleep.u32` between the poll and the branch):
    "@!complete nanosleep.u32 20; @!complete bra waitLoop;"
- modelling choice (representation): the two shapes and the absence of branches into the loop
    body after the poll; the manual shows shape B only (quoted above). The model also requires the
    branch right after the poll, so the manual's examples with a `nanosleep.u32` between the poll
    and the branch (Examples 1a, 2 and 5, quoted above) are no canonical spins, and ERR-POLL-SHAPE
    rejects them

**Applies:** every `mbarrier.try_wait` and `mbarrier.test_wait` position of a kernel

**Effect:** Definitions of the loop shapes, used by DEP-ORDER (`SpinExit`) and ERR-POLL-SHAPE. A canonical spin (`Kernel.CanonicalSpin`) at position `pc` is an unguarded poll writing predicate `p` that does not read `p`, followed either (shape A) by `@p bra exit` and an unguarded `bra pc`, where `exit` lies outside the positions `pc` to `pc + 2` so that a successful poll leaves the loop, or (shape B) by `@!p bra pc` with the exit at `pc + 2`; `bra` and `bra.uni` are both accepted; no branch targets the loop body after the poll (`pc + 1` and `pc + 2` in shape A, `pc + 1` in shape B), so the loop consists of these instructions only and its address, parity and hint operands do not change; and every instruction of the kernel that reads `p` is the branch right after a poll of such a shape that writes `p` (`Kernel.SpinPred`). Register reads are over-approximated (`Op.readRegs` lists every register operand an instruction may read, and an instruction without a family representation may read any register), which only makes fewer loops canonical spins.

</details>

### What counts as an error

The disjunction of the safety checks of every chapter, and the faults that instructions raise themselves.

<a id="err-poll-shape"></a>
#### a poll result used outside a canonical spin (`ERR-POLL-SHAPE`)

*Rule* · [Lean comment: `Core/Assembly/PollShape.lean` L198-L245](../../Core/Assembly/PollShape.lean#L198-L245)

An execution is unsafe when it performs a poll at a position that is neither a canonical spin (DEP-CANONICAL-SPIN) nor a poll whose result is never read.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Kernel.PollUnused`](../../Core/Assembly/PollShape.lean#L247-L250), [`PollShapeUnsafe`](../../Core/Assembly/PollShape.lean#L254-L258)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16.19: "mbarrier.test_wait is a non-blocking instruction which tests for the completion
    of the phase."
- §9.7.15.16.19: "Suspended thread resumes execution when the specified phase completes OR before
    the phase completes following a system-dependent time limit."
- DEP-CANONICAL-SPIN

**Applies:** every `mbarrier.try_wait` and `mbarrier.test_wait` event

**Effect:** Safety rejection (part of Unsafe). It rejects executions and never admits one: an execution that performs such a poll is unsafe, so a kernel can prove `Correct.safe` only if no consistent execution performs it. A poll whose result is never read (`Kernel.PollUnused`) writes a predicate that only the branches of canonical spin shapes read, each after its own poll has overwritten it. Rejected uses include a result saved to a register or combined with another predicate, a result that guards another instruction, a loop that polls several objects or contains another instruction, a parity or address changed inside the loop, a nested retry loop, and a single poll whose result a branch reads. The over-approximated register reads of DEP-CANONICAL-SPIN only reject more executions.

</details>

<a id="err-unsafe"></a>
#### undefined behaviour (`ERR-UNSAFE`)

*Rule* · [Lean comment: `Core/Assembly/Execution.lean` L154-L203](../../Core/Assembly/Execution.lean#L154-L203)

An execution is unsafe when it contains an undefined-behaviour event, touches unallocated memory, has a data race or a mixed-size conflict, breaks a rule of the barriers, mbarriers, bulk copies, CLC, Tensor Memory, shared-memory lifetime or warp-level matrix instructions, breaks the `.aligned` qualifier, uses an mbarrier that no published initialization precedes, diverges within a warp at an instruction that needs a uniform guard, uses an mbarrier poll result other than in a canonical spin, or is declared undefined by a kernel assumption.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Unsafe`](../../Core/Assembly/Execution.lean#L206-L217) ([concept](#c-unsafe))

<details>
<summary>Details for reviewers</summary>

- §9.7 (the undefined-behaviour sentences of the individual instruction descriptions)
- §8.7 (data races)
- §8.2.6 (allocation, ERR-UNALLOCATED-ACCESS)
- the ERR- entries named in the Effect; the `stricter` ones among them are the checks that are
    stricter than the text (their Direction says so in `Core/README.md`)

**Effect:** The disjunction of the checks of the model, each owned by an ERR- entry, and of the `ub` conditions of the kernel assumptions, which have no ERR- entry. In the order of `Unsafe`, an execution is unsafe if it has a `ub` event (`HasUb`, ERR-UNDEFINED-INSTRUCTION), touches an unallocated byte (`Unalloc`, ERR-UNALLOCATED-ACCESS), has a data race (`Race`, ERR-DATA-RACE) or a mixed-size conflict (`Mixed`, ERR-MIXED-SIZE), a CTA barrier mismatch (`BarMismatch`, ERR-BARRIER-MISMATCH), an mbarrier fault or an object used outside its lifetime (`TmaUnsafe`, ERR-OBJECT-LIFETIME), or a Tensor Memory read without a read source (`TcMma.SourceUnsafe`, ERR-TMEM-READ-SOURCE), if a kernel assumption declares it undefined (`a.ub`), or if it has an aligned instruction executed differently by the lanes of a warp or skipped by an exited participant (`AlignedMismatch`, ERR-ALIGNED-MISMATCH), a use of shared memory outside its lifetime (`SharedLifetimeUnsafe`, ERR-SHARED-LIFETIME), a CLC request after an observed failure (`ClcUnsafe`, ERR-CLC-REQUEST-AFTER-FAILURE), a tensor load that writes a byte without a scalar value (`TensorUnsafe`, ERR-TENSOR-FILL-VALUE), a performed reduction element without an arithmetic rule (`TensorStoreUnsafe`, ERR-REDUCTION-NO-RULE), an out-of-bounds element of a tensor map of the large allocation class without an accessible backing range (`TensorAllocationUnsafe`, ERR-TENSOR-LARGE-OOB), a Tensor Memory allocator fault (`Tmem.Pair.ResourceUnsafe`, ERR-TMEM-RESOURCE), a Tensor Memory allocation still live at kernel completion (`Tmem.Pair.ReleaseUnsafe`, ERR-TMEM-NOT-RELEASED), a poll whose result is used other than in a canonical spin (`PollShapeUnsafe`, ERR-POLL-SHAPE), a Tensor Memory access outside a completed allocation or not completed before its release (`Tmem.Pair.AccessUnsafe`, ERR-TMEM-ACCESS-LIFETIME), a `tcgen05.commit` whose CTA group does not exist in the cluster (`TcCommitUnsafe`, ERR-TC-COMMIT-GROUP), two unordered Tensor Memory writes of a cell (`TcMma.WritesUnsafe`, ERR-TMEM-RACE), an invalid MMA or `tcgen05.cp` instance or a completed MMA result without a derived value (`TcMma.InstructionUnsafe`, ERR-TC-MMA), an MMA read unordered with a write of its cell (`TcMma.ReadsUnsafe`, ERR-TMEM-RACE), an illegal `setmaxnreg` request (`SetMaxNReg.UnsafeAt`, ERR-SETMAXNREG), a CTA barrier fault (`CtaBarFault`, ERR-CTA-BARRIER), a cluster barrier fault (`ClusterFault`, ERR-CLUSTER-BARRIER), warp-divergent control flow at an instruction that requires a uniform guard (`WarpDivergent`, ERR-NONUNIFORM-GUARD), an undefined instance of a warp-level matrix instruction (`MatrixUnsafe`, ERR-WARP-MATRIX), or an mbarrier operand whose initialization is not published to the instruction (`MbarUninit`, ERR-MBAR-UNINITIALIZED).

</details>

<a id="err-undefined-instruction"></a>
#### instruction faults (`ERR-UNDEFINED-INSTRUCTION`)

*Rule* · [Lean comment: `Core/Assembly/Safety.lean` L480-L499](../../Core/Assembly/Safety.lean#L480-L499)

An execution that contains an undefined-behaviour event is unsafe. Such events come from the "behavior is undefined" sentences of the instruction descriptions, from instruction forms that the model has no rule for, and from the model's checks that are stricter than the text.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`HasUb`](../../Core/Assembly/Safety.lean#L502-L503) ([concept](#c-hasub))

<details>
<summary>Details for reviewers</summary>

- no ISA section (the model's own accounting rule: an event of kind `ub` makes an execution unsafe)
- §9.7: "behavior is undefined"
- ERR-FAULT-REASON (an instruction form without a rule, `noRule`, and the checks that are stricter
    than the text are also faults)

**Applies:** Instruction fault events

**Premises:** An event has kind ub.

**Effect:** Safety rejection.

</details>

### Progress, fairness and termination

Executions that cannot grow must be complete; the fairness assumption carries this to real runs.

<a id="correct-grow"></a>
#### the size and growth of an execution (`CORRECT-GROW`)

*Rule* · [Lean comment: `Core/Data/Events.lean` L600-L622](../../Core/Data/Events.lean#L600-L622)

The size of an execution counts the thread events (failed `try_wait`s excluded), the stages of asynchronous operations that have happened, and the allocator records and pairings. One execution extends another when it keeps all observations of the first: thread prefixes, read sources, asynchronous effects and object histories.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Event.counts`](../../Core/Data/Events.lean#L629-L633), [`Execution.elemSize`](../../Core/Data/Events.lean#L635-L642), [`Execution.elemSize_eq_zero`](../../Core/Data/Events.lean#L644-L649), [`Execution.asyncSize`](../../Core/Data/Events.lean#L651-L663), [`Execution.threadSize`](../../Core/Data/Events.lean#L665-L668), [`Execution.pairSize`](../../Core/Data/Events.lean#L670-L672), [`Execution.size`](../../Core/Data/Events.lean#L674-L676) ([concept](#c-execution-size)), [`Execution.le`](../../Core/Data/Events.lean#L678-L692) ([concept](#c-execution-le))

<details>
<summary>Details for reviewers</summary>

- none (definitions of the statement)

**Effect:** The size is the number of thread events and independent async stages (including each tensor byte read/write, notification and output completion), plus allocator records and pairings of Tensor Memory operations. It does not count failed `try_wait`s. Extension preserves thread prefixes, actual read sources, async effects and object-history prefixes (`List.IsPrefix`: recorded operations, replies and phase identities are preserved), so no progress is obtained by rewriting an earlier observation. Together with `RfWf` at both endpoints, this also preserves any initial-byte choice already observed by a W0 read (`initial_choice_preserved`); unobserved choices are immaterial to the prefix and may be resolved by a later extension.

</details>

<a id="correct-maximal"></a>
#### executions that cannot grow (`CORRECT-MAXIMAL`)

*Rule* · [Lean comment: `Core/Assembly/Correctness.lean` L21-L30](../../Core/Assembly/Correctness.lean#L21-L30)

An execution is maximal when it is possible and no possible execution that extends it has more counted events.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`Maximal`](../../Core/Assembly/Correctness.lean#L33-L37) ([concept](#c-maximal))

<details>
<summary>Details for reviewers</summary>

- none

</details>

<a id="correct-complete"></a>
#### launched threads exited, canceled clusters accounted for and work drained (`CORRECT-COMPLETE`)

*Rule* · [Lean comment: `Core/Assembly/Correctness.lean` L39-L60](../../Core/Assembly/Correctness.lean#L39-L60)

An execution is complete when every launched thread has exited or belongs to a cluster that was canceled before it launched, every issued asynchronous operation has delivered its completion, and every paired Tensor Memory allocator request belongs to a completed collective operation.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`AsyncDrained`](../../Core/Assembly/Correctness.lean#L63-L66) ([concept](#c-asyncdrained)), [`asyncDrained_iff`](../../Core/Assembly/Correctness.lean#L68-L112), [`Complete`](../../Core/Assembly/Correctness.lean#L114-L119) ([concept](#c-complete))

<details>
<summary>Details for reviewers</summary>

- §9.7.14.6–7 (thread exit)
- §9.7.10.28.1 (asynchronous completion)
- §9.7.18.6.2.1.1 (the completion of `tcgen05.mma`, `tcgen05.cp` and `tcgen05.shift` is observed
    through the mbarrier based waiting mechanism)

**Effect:** Every thread either exited or belongs to a canceled, unlaunched cluster. Every issued linear/tensor input or output copy (a linear copy without an mbarrier by its write), `cp.async.mbarrier.arrive` arrive-on, MMA, `tcgen05.cp` (`TcAsync`) and commit finished, and each CLC target received its completion notification. Every issued paired allocator request belongs to its recorded collective resource operation. A thread is accounted for only by a recorded exit (or its cluster's cancellation), and pending work only by its completion.

</details>

<a id="correct-fair"></a>
#### fair runs (`CORRECT-FAIR`)

*Rule* · [Lean comment: `Core/Assembly/Progress.lean` L20-L44](../../Core/Assembly/Progress.lean#L20-L44)

A run is a sequence of possible executions, each extending the previous one. A run is fair when, whenever its current execution can be extended by a counted event (any event except a failed poll), a later execution of the run has more counted events.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`FairRun`](../../Core/Assembly/Progress.lean#L78-L84) ([concept](#c-fairrun))

<details>
<summary>Details for reviewers</summary>

- CUDA C++ Programming Guide (forward progress)
- EXT-FAIR

**Applies:** Sequences of consistent executions

**Premises:** Prefixes and existing read sources are preserved; whenever a counted extension exists, a later member has more counted events.

**Effect:** Assumption on runs; failed polls are uncounted. A run is a sequence of possible executions, each extending the previous one. It is fair if, whenever its current execution can be extended by a counted event (any event except a failed `try_wait`), the run later has more counted events than it has now. A thread that can make progress eventually does, and a thread does not poll forever while a completed phase could be observed. This is the Lean form of EXT-FAIR; `Correct.exits` proves that every fair run of a correct kernel reaches an execution where launched threads have exited, canceled clusters are accounted for, and async work is drained.

</details>

<a id="ext-fair"></a>
##### fair scheduling, including asynchronous completion and observation (`EXT-FAIR`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/Progress.lean` L46-L74](../../Core/Assembly/Progress.lean#L46-L74)

The model assumes that every real run is fair in the sense of CORRECT-FAIR: when the current execution can be extended by a counted event, the run later gains counted events. The counted events include the completion of an asynchronous operation and a successful observation (`FairRun` does not distinguish a thread's event from an asynchronous stage), so when only the completion of an asynchronous copy or a successful observation remains available, it eventually happens. Failed polls may repeat any number of times, and the run still gains counted events.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Evidence:** CUDA C++ Programming Guide, CUDA C++ Execution Model (forward progress). PTX ISA §9.7.10.28.4.1 and §9.7.15.16 describe completion and waiting; the eventual-progress condition for asynchronous operations is an accepted external contract.

**Effect:** The accepted scheduling contract is CORRECT-FAIR: a run with an available counted extension eventually gains counted events. It is a progress condition on the whole sequence of consistent executions, and it promises nothing to any single thread. For the supported bulk-copy protocol, the hardware contract must justify eventual counted progress when only copy completion or successful observation remains available. `FairRun` excludes staying at the same counted size forever when an extension exists. The model's `Consistent` executions are unaffected; if a real run is not a `FairRun`, because a thread that can progress never does or because a copy completion or a successful observation stays unavailable forever, the completion and termination results (`Correct.exits`) do not transfer to it, while the safety results still hold. Disclosed by every kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.

</details>

### The memory after the kernel

The final value of each byte, given by a coherence order of the execution's writes.

<a id="correct-final"></a>
#### memory after the kernel (`CORRECT-FINAL`)

*Rule* · [Lean comment: `Core/Assembly/Correctness.lean` L121-L187](../../Core/Assembly/Correctness.lean#L121-L187)

The memory after a complete execution comes from a coherence order of its writes that orders every two overlapping morally strong writes and contains each coherence edge the execution determines in one direction only. A byte holds the value of its last write in that order, the common value of its last writes when they all agree, or its launch content when no write covers it.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`FinalMem`](../../Core/Assembly/Correctness.lean#L190-L191) ([concept](#c-finalmem)), [`CoStep`](../../Core/Assembly/Correctness.lean#L193-L202) ([concept](#c-costep)), [`coStep_of_reduceReads`](../../Core/Assembly/Correctness.lean#L204-L217), [`CoBefore`](../../Core/Assembly/Correctness.lean#L219-L221) ([concept](#c-cobefore)), [`CoOrder`](../../Core/Assembly/Correctness.lean#L223-L231) ([concept](#c-coorder)), [`CoMaximal`](../../Core/Assembly/Correctness.lean#L233-L237) ([concept](#c-comaximal)), [`IsFinal`](../../Core/Assembly/Correctness.lean#L239-L249) ([concept](#c-isfinal))

<details>
<summary>Details for reviewers</summary>

- §8.9.4: "End of all threads in a kernel synchronize with end of the kernel."
- §8.9.6: "There exists a partial transitive order that relates overlapping write operations,
    determined at runtime, called the coherence order 1 . Two overlapping write operations are
    related in coherence order if they are morally strong or if they are related in causality order
    ."
- §8.9.6: "Two overlapping writes are unrelated in coherence order if they are in a data-race ,
    which gives rise to the partial nature of coherence order ."
- §8.9.6: "It may be observed indirectly by its use in constraining the set of candidate writes that
    a read operation may read from."
- §8.10.1: "If a write W precedes an overlapping write W’ in causality order , then W must precede
    W’ in coherence order ."
- §8.10.3: "When an atomic operation A and a write W overlap and are morally strong , then the
    following two communications cannot both exist in the same execution, for the set of bytes
    accessed by both A and W: A reads any byte from a write W’ that precedes W in coherence order .
    A follows W in coherence order ."
- §8.10.3 (Litmus Test 1: two morally strong `atom.inc` of `x = 0`): "FINAL STATE : x == 2"
- §8.10.5 (a cycle of program order and morally strong communication order is forbidden)
- §8.10.6: "If a write W precedes an overlapping read R in causality order , then for any byte
    accessed by both R and W, R cannot read from any write W’ that precedes W in coherence order ."
- EXT-LAUNCH
- MEM-ATOMICITY

**Applies:** Each byte of memory after a complete execution

**Premises:** The writes of the execution, `ByteCausality` between them, reads-from among the morally strong atomic read-modify-writes of one footprint, and the sources of reads that follow a write in `ByteCausality`.

**Effect:** Constrains `m` in CORRECT `result`. The end of the kernel follows every event of the kernel, including asynchronous writes completed after the last thread exit (EXT-LAUNCH; §8.9.4 states it for the end of the threads), so a read of memory after the kernel reads a write that no other write follows in coherence order (§8.10.6). One order `co` serves every byte, so the bytes of one write that follows another in coherence order all hold its value. Three kinds of edges give the coherence order the execution determines (`CoStep`, closed transitively in `CoBefore`), each at a byte both writes cover: - `ByteCausality` from one write to another is causality (§8.10.1). - An atomic read-modify-write that reads a byte from another one, morally strong with it at the same footprint, follows it (MEM-ATOMICITY, `AtomicReads`). Over these operations this is the single reads-from chain of MEM-ATOMICITY, so concurrent `atom`s, `red`s or tensor reductions of one element (split-K) end with the result of the last one, which has applied every earlier one. - A write `W` that is `ByteCausality`-before a read reading from a different write `W’` morally strong with `W` precedes `W’`: the two are related in coherence order (§8.9.6), and `W’` before `W` is what §8.10.6 forbids.

</details>
