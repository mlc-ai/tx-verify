# Memory model

How the model orders memory accesses and decides which values a read may return: byte locations and footprints, scopes, program order, base causality order, the byte-specific model causality order that also covers asynchronous accesses, the reads-from and coherence axioms, and the memory errors (data races, including the exemption for writes of identical values, mixed-size conflicts, unallocated bytes and the shared-memory lifetime). The coherence order of writes and the memory after the kernel are part of the correctness chapter (CORRECT-FINAL). Concepts come first, then the rules.

Generated from the Lean comments of `Core/` and `Assumption/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [Locations, footprints and scopes](#locations-footprints-and-scopes)
    - [`Loc`](#c-loc)
    - [`Acc`](#c-acc)
    - [`Acc.Overlap`](#c-acc-overlap)
    - [`Mem0`](#c-mem0)
    - [`MbarScope`](#c-mbarscope)
    - [`MbarScopeIncludes`](#c-mbarscopeincludes)
  - [Memory operations](#memory-operations)
    - [`AsyncCopy.Ref`](#c-asynccopy-ref)
    - [`Execution.Intent`](#c-execution-intent)
    - [`Execution.MemReads`](#c-execution-memreads)
    - [`Execution.MemWrites`](#c-execution-memwrites)
  - [Order](#order)
    - [`po`](#c-po)
    - [`synchronizesWith`](#c-synchronizeswith)
    - [`FenceSync`](#c-fencesync)
    - [`baseCausality`](#c-basecausality)
    - [`ProxyBefore`](#c-proxybefore)
    - [`AsyncFinished`](#c-asyncfinished)
    - [`CompletionBefore`](#c-completionbefore)
    - [`AsyncChain`](#c-asyncchain)
    - [`PairAsync`](#c-pairasync)
    - [`modelCausality`](#c-modelcausality)
    - [`ByteCausality`](#c-bytecausality)
  - [Reads](#reads)
    - [`RfWf`](#c-rfwf)
    - [`NoFuture`](#c-nofuture)
    - [`Hidden`](#c-hidden)
  - [Races](#races)
    - [`Conflict`](#c-conflict)
    - [`StrongScoped`](#c-strongscoped)
    - [`MorallyStrong`](#c-morallystrong)
    - [`SameValueWrites`](#c-samevaluewrites)
    - [`Race`](#c-race)
    - [`Mixed`](#c-mixed)
    - [`Unalloc`](#c-unalloc)
  - [Shared-memory lifetime](#shared-memory-lifetime)
    - [`SharedUse`](#c-shareduse)
    - [`LifetimeOrder`](#c-lifetimeorder)
    - [`CompletedBefore`](#c-completedbefore)
    - [`SharedLifetimeUnsafe`](#c-sharedlifetimeunsafe)
- [Rules](#rules)
  - [How accesses are ordered](#how-accesses-are-ordered)
    - [program order](#mem-program-order) (`MEM-PROGRAM-ORDER`)
    - [the threads a scope includes](#mem-scope) (`MEM-SCOPE`)
    - [release and acquire patterns](#mem-release-acquire) (`MEM-RELEASE-ACQUIRE`)
    - [the Fence-SC order](#mem-fence-sc) (`MEM-FENCE-SC`)
    - [base causality order](#mem-base-causality) (`MEM-BASE-CAUSALITY`)
    - [base proxy and completion order at one byte](#mem-model-causality) (`MEM-MODEL-CAUSALITY`)
    - [byte order used by memory checks](#mem-byte-causality) (`MEM-BYTE-CAUSALITY`)
      - [a cta_group::2 pair is one thread block for asynchronous accesses](#ext-pair-async) (`EXT-PAIR-ASYNC`)
      - [a `.read` bulk-group wait orders the source reads before generic accesses](#ext-read-wait-order) (`EXT-READ-WAIT-ORDER`)
      - [an observed commit orders prior writes to its operand bytes](#ext-tc-commit-operand-order) (`EXT-TC-COMMIT-OPERAND-ORDER`)
      - [overwriting a shared source after observed Tensor Core completion](#ext-tc-source-reuse) (`EXT-TC-SOURCE-REUSE`)
  - [Which values a read may return](#which-values-a-read-may-return)
    - [reads-from](#mem-reads-from) (`MEM-READS-FROM`)
    - [the memory model axioms](#mem-read-axioms) (`MEM-READ-AXIOMS`)
  - [What counts as a memory error](#what-counts-as-a-memory-error)
    - [unordered conflicting accesses](#err-data-race) (`ERR-DATA-RACE`)
    - [atomicity of read-modify-write operations](#mem-atomicity) (`MEM-ATOMICITY`)
    - [overlapping accesses of different widths](#err-mixed-size) (`ERR-MIXED-SIZE`)
    - [allocation checks](#err-unallocated-access) (`ERR-UNALLOCATED-ACCESS`)
    - [shared memory exists for every use and outlives its completion](#err-shared-lifetime) (`ERR-SHARED-LIFETIME`)
- [The memory layer against PTX §8.9](#the-memory-layer-against-ptx-89)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### Locations, footprints and scopes

A byte of memory, the bytes one memory operation accesses, the memory at launch, and the scope of a strong operation.

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

<a id="c-mem0"></a>
#### `Mem0`

*abbrev*

Memory at launch, as written by `W0` (§8.2.6): `none` = not allocated (any access is
undefined); `some none` = allocated with an unknown constant value; `some (some b)` =
byte `b`.

[Lean source: `Core/Data/Value.lean` L495-L498](../../Core/Data/Value.lean#L495-L498)

<a id="c-mbarscope"></a>
#### `MbarScope`

*inductive*

The scope of a strong operation (§8.5, Table 21): `.cta`, `.cluster`, `.gpu` or `.sys`. It is
distinct from an object's shared address qualifier.

- `cta`
- `cluster`
- `gpu`
- `sys`

[Lean source: `Core/Isa/Types.lean` L81-L85](../../Core/Isa/Types.lean#L81-L85)

<a id="c-mbarscopeincludes"></a>
#### `MbarScopeIncludes`

*def*

Scope `scope` of thread `g` includes thread `h` (§8.5): the two threads of the launch are in
the same CTA for `.cta` and in the same cluster for `.cluster`; `.gpu` and `.sys` include every
thread of the launch.

[Lean source: `Core/Sync/Barrier.lean` L131-L138](../../Core/Sync/Barrier.lean#L131-L138)

### Memory operations

The accesses of thread instructions and of the stages of asynchronous operations.

<a id="c-asynccopy-ref"></a>
#### `AsyncCopy.Ref`

*inductive*

A reference to an operation that can be a source or a target of ordering: a thread's
instruction instance, or one stage (`Part`) of an asynchronous operation issued by one.

- `thread`
- `async`

[Lean source: `Core/Data/AsyncTypes.lean` L145-L150](../../Core/Data/AsyncTypes.lean#L145-L150)

<a id="c-execution-intent"></a>
#### `Execution.Intent`

*def*

Memory operations with their footprint and direction, pending or performed; an
asynchronous stage writes exactly when it is a write.

[Lean source: `Core/Data/Events.lean` L470-L474](../../Core/Data/Events.lean#L470-L474)

<a id="c-execution-memreads"></a>
#### `Execution.MemReads`

*def*

Actual read effects: a thread's read or the read of its atomic read-modify-write, one byte per
non-contiguous MMA operand location, and the reads of copies, tensor stores and loads.

[Lean source: `Core/Data/Events.lean` L352-L376](../../Core/Data/Events.lean#L352-L376)

<a id="c-execution-memwrites"></a>
#### `Execution.MemWrites`

*def*

The bytes that a write puts at an access: a thread's store or the write of its atomic
read-modify-write, or a write stage of an
asynchronous operation that has happened (a tile byte of a tensor store or tensor load, the CLC
response at a target CTA, or the destination range of a linear copy).

[Lean source: `Core/Data/Events.lean` L378-L400](../../Core/Data/Events.lean#L378-L400)

### Order

Program order, base causality order between thread instructions, and the byte-specific model causality order that relates thread and asynchronous accesses.

<a id="c-po"></a>
#### `po`

*def*

Program order (§8.9.1): `e` comes before `f` in the trace of one thread, and the two events
are not elements of one vector access.

[Lean source: `Core/Memory/Order.lean` L76-L79](../../Core/Memory/Order.lean#L76-L79)

<a id="c-synchronizeswith"></a>
#### `synchronizesWith`

*def*

Release/acquire synchronization from `e` to `f` (§8.9.4): `e` writes with release semantics
(a release store or the write of a releasing atomic read-modify-write) and `f` reads with acquire
semantics (an acquire load or the read of an acquiring `atom`), with the same nonempty footprint,
`f` reads every byte from `e`, and the scope of each includes the thread of the other.

[Lean source: `Core/Memory/Acquire.lean` L149-L158](../../Core/Memory/Acquire.lean#L149-L158)

<a id="c-fencesync"></a>
#### `FenceSync`

*def*

The synchronization of a release pattern starting at `e` with an acquire pattern ending at `f`
where at least one of them is a fence (§8.8, §8.9.4), or of two `fence.sc` ordered by the Fence-SC
order (MEM-FENCE-SC).

[Lean source: `Core/Memory/Acquire.lean` L193-L204](../../Core/Memory/Acquire.lean#L193-L204)

<a id="c-basecausality"></a>
#### `baseCausality`

*def*

The base causality order between thread instruction events (§8.9.5): the transitive closure
of program order and the synchronizes-with edges of CTA barriers (`CtaBarSync`), mbarriers
(`MSync`), cluster barriers (`ClusterSync`), warp barriers (`WarpBarSync`), release/acquire
accesses (`synchronizesWith`), and release and acquire patterns with fences and the Fence-SC order
(`FenceSync`).

[Lean source: `Core/Memory/Order.lean` L128-L135](../../Core/Memory/Order.lean#L128-L135)

<a id="c-proxybefore"></a>
#### `ProxyBefore`

*def*

A `fence.proxy.async` whose state space covers byte `l` is ordered after `e` and before the
issue of an asynchronous operation by `baseCausality`, and the issuer is a thread the fence reaches
(`ProxyFenceReach`). ISA §9.7.15.4 permits the proxy fence effect to compose with other forms of
synchronization; the fence and the async issue may occur in different threads. For a fence without
a scope the issuer may be another CTA of the fence's cluster (a multicast or peer write into this
CTA): the fence then reaches it only through `baseCausality`, i.e. through synchronization whose
scope includes both CTAs.

[Lean source: `Core/Memory/Order.lean` L446-L456](../../Core/Memory/Order.lean#L446-L456)

<a id="c-asyncfinished"></a>
#### `AsyncFinished`

*def*

The wait `w` observes the completion of part `p` of the asynchronous operation issued by `i`:
a group wait covering `i` whose kind makes `p` visible (`GroupWaitVisible`, the table of
DEP-BULK-WAIT), once every stage the wait waits for is present (`GroupWaitStages`), or an
acquire wait that observes the operation's own completion notification (for an MMA, the arrive-on
of a commit tracking it; for a `cp.async`, the arrive-on of a `cp.async.mbarrier.arrive` that
tracks it), the wait's scope and the notification's `.cluster` scope each including the other's
thread.

[Lean source: `Core/Memory/Order.lean` L242-L252](../../Core/Memory/Order.lean#L242-L252)

<a id="c-completionbefore"></a>
#### `CompletionBefore`

*def*

From the observation `w` of part `p`'s completion to the generic access `f`: causality,
and for the shared-memory reads of `tcgen05.mma` and `tcgen05.cp` (asynchronous proxy,
§9.7.18.6.5) a `fence.proxy.async` between them (`ProxyBefore`).

[Lean source: `Core/Memory/Order.lean` L512-L517](../../Core/Memory/Order.lean#L512-L517)

<a id="c-asyncchain"></a>
#### `AsyncChain`

*inductive*

Only actual asynchronous memory effects can be interior vertices. The
fixed byte and typed vertices exclude chaining through unrelated addresses,
ordinary issuing instructions, or completion notifications. Endpoints retain
their issue footprints so pending conflicting accesses are still checked.

- `direct`
- `tail`

[Lean source: `Core/Memory/Order.lean` L490-L498](../../Core/Memory/Order.lean#L490-L498)

<a id="c-pairasync"></a>
#### `PairAsync`

*def*

Two threads issue asynchronous accesses to shared byte `l` of one `cta_group::2` pair:
both issuing CTAs and the byte's CTA belong to the pair (EXT-PAIR-ASYNC).

[Lean source: `Core/Memory/Order.lean` L500-L504](../../Core/Memory/Order.lean#L500-L504)

<a id="c-modelcausality"></a>
#### `modelCausality`

*def*

The proxy and completion order at byte `l` (MEM-MODEL-CAUSALITY) between thread accesses and the
parts of asynchronous operations: `baseCausality` or a same-byte allocation-result handoff
between two thread accesses; from a thread access
to an asynchronous access, an async proxy fence (`ProxyBefore`), or `baseCausality` to the issue of
an operation performed in the generic proxy (`GenericCopy`); an observed completion
(`AsyncFinished`, `ObservedCompletionBefore`) from an asynchronous access to a thread access;
and a chain of observed completions (`AsyncChain`) between asynchronous accesses in one CTA or one
`cta_group::2` pair (`PairAsync`) when one of the two operations is a `cta_group::2` `tcgen05`
operation (`PairTc`).

[Lean source: `Core/Memory/Order.lean` L588-L605](../../Core/Memory/Order.lean#L588-L605)

<a id="c-bytecausality"></a>
#### `ByteCausality`

*inductive*

Byte causality consists of the base proxy and completion paths and the observed shared
operand handoff. The handoff may use a preceding handoff to reach the operand read.

- `direct`
- `commitOperand`

[Lean source: `Core/Memory/CommitOperandOrder.lean` L90-L104](../../Core/Memory/CommitOperandOrder.lean#L90-L104)

### Reads

Which write a read byte comes from and which sources the axioms exclude.

<a id="c-rfwf"></a>
#### `RfWf`

*def*

Reads-from is well formed (§8.9.7): every read, ordinary or asynchronous, returns one byte
per byte of its footprint, and each byte is the value of its source, the covering write it reads
from or the initial write `W0`.

[Lean source: `Core/Memory/Read.lean` L42-L50](../../Core/Memory/Read.lean#L42-L50)

<a id="c-nofuture"></a>
#### `NoFuture`

*def*

Causality axiom, first clause (§8.10.6): no read reads a byte from a write that the read
precedes in `ByteCausality` at that byte.

[Lean source: `Core/Memory/Read.lean` L82-L86](../../Core/Memory/Read.lean#L82-L86)

<a id="c-hidden"></a>
#### `Hidden`

*def*

Causality axiom, second clause, and coherence (§8.10.1, §8.10.6): when a write precedes a read
in `ByteCausality` at a byte, the read does not read that byte from the initial write `W0`
or from a write that precedes the first write in `ByteCausality` at that byte.

[Lean source: `Core/Memory/Read.lean` L88-L96](../../Core/Memory/Read.lean#L88-L96)

### Races

Conflicting accesses, moral strength and the race checks.

<a id="c-conflict"></a>
#### `Conflict`

*def*

Two distinct accesses `e` and `f`, pending or performed, whose footprints `a` and `b` overlap,
and at least one of which writes (§8.7).

[Lean source: `Core/Assembly/Safety.lean` L116-L120](../../Core/Assembly/Safety.lean#L116-L120)

<a id="c-strongscoped"></a>
#### `StrongScoped`

*def*

`e` with footprint `a` is a strong operation whose scope includes thread `g` (§8.4, §8.5): a
thread access with the `.relaxed`, `.acquire`, `.release` or `.acq_rel` qualifier (`Acc.Strong`)
at its scope, or a tensor reduction element at `.gpu` scope.

[Lean source: `Core/Assembly/Safety.lean` L122-L134](../../Core/Assembly/Safety.lean#L122-L134)

<a id="c-morallystrong"></a>
#### `MorallyStrong`

*def*

§8.7: program-order related, or each strong with a scope including the other's thread;
the same proxy; complete overlap of the two operations.

[Lean source: `Core/Assembly/Safety.lean` L199-L205](../../Core/Assembly/Safety.lean#L199-L205)

<a id="c-samevaluewrites"></a>
#### `SameValueWrites`

*def*

Two writes of the same bytes (one footprint) with the same value, compared as the model
represents values (byte lists), for every write kind (`MemWrites`). A write not yet performed has
no value; such a pair is compared in the executions that perform both.

[Lean source: `Core/Assembly/Safety.lean` L207-L212](../../Core/Assembly/Safety.lean#L207-L212)

<a id="c-race"></a>
#### `Race`

*def*

A data race (§8.7.1): two conflicting accesses with the same footprint that are not morally
strong, are not two writes of the same value, and are unordered in both directions in
`ByteCausality` at a byte they access.

[Lean source: `Core/Assembly/Safety.lean` L214-L220](../../Core/Assembly/Safety.lean#L214-L220)

<a id="c-mixed"></a>
#### `Mixed`

*def*

A mixed-size conflict (§8.7.2): two conflicting accesses with different footprints that are
unordered in both directions in `ByteCausality` at a byte both cover.

[Lean source: `Core/Assembly/Safety.lean` L241-L245](../../Core/Assembly/Safety.lean#L241-L245)

<a id="c-unalloc"></a>
#### `Unalloc`

*def*

Some access of `X`, pending or performed, touches a byte that is unallocated in `mem0`, or an
mbarrier operand of some event covers such a byte.

[Lean source: `Core/Assembly/Safety.lean` L532-L536](../../Core/Assembly/Safety.lean#L532-L536)

### Shared-memory lifetime

The uses of a CTA's shared memory and the order that places them inside the CTA's lifetime.

<a id="c-shareduse"></a>
#### `SharedUse`

*def*

`e` uses the shared memory of CTA `c` (the table of ERR-SHARED-LIFETIME): a thread
instruction or performed stage accessing it or operating on an mbarrier object in it, or,
performed or not, the stage completing an issued operation's use of it.

[Lean source: `Core/Assembly/SharedLifetime.lean` L251-L263](../../Core/Assembly/SharedLifetime.lean#L251-L263)

<a id="c-lifetimeorder"></a>
#### `LifetimeOrder`

*def*

Lifetime order of two nodes: a path of base causality, or a path of the dependency order
together with the order of one object of `OrderObject.Enabling` (`LifetimeStep`).

[Lean source: `Core/Assembly/SharedLifetime.lean` L208-L213](../../Core/Assembly/SharedLifetime.lean#L208-L213)

<a id="c-completedbefore"></a>
#### `CompletedBefore`

*def*

The completion of `e` precedes the node `n`: a lifetime-order path from the completion
node of `e`, or, for an asynchronous stage, a dependency path (with one object's order) from
the return of a wait that the stage is a witness of (a group wait covering it, or a successful
poll that observed its notification).

[Lean source: `Core/Assembly/SharedLifetime.lean` L215-L223](../../Core/Assembly/SharedLifetime.lean#L215-L223)

<a id="c-sharedlifetimeunsafe"></a>
#### `SharedLifetimeUnsafe`

*def*

The shared-memory lifetime check fails: a use of CTA `owner`'s shared memory issued from
another CTA is not preceded by an instruction of the owner (`PeerSharedStarted`), or the owner
has exited and the use did not complete before an exit of one of its threads
(`SharedFinished`).

[Lean source: `Core/Assembly/SharedLifetime.lean` L283-L291](../../Core/Assembly/SharedLifetime.lean#L283-L291)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### How accesses are ordered

Program order, the synchronization that enters base causality order, and the byte-specific order that composes thread and asynchronous accesses.

<a id="mem-program-order"></a>
#### program order (`MEM-PROGRAM-ORDER`)

*Rule* · [Lean comment: `Core/Memory/Order.lean` L27-L51](../../Core/Memory/Order.lean#L27-L51)

The events of one thread are ordered as they appear in its trace, except that the scalar element operations of one vector access are unordered among themselves.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TraceBefore`](../../Core/Memory/Order.lean#L54-L56), [`Event.acc`](../../Core/Memory/Order.lean#L58-L61), [`Acc.shift`](../../Core/Memory/Order.lean#L63-L65), [`SameAccess`](../../Core/Memory/Order.lean#L67-L71), [`po`](../../Core/Memory/Order.lean#L76-L79) ([concept](#c-po))

<details>
<summary>Details for reviewers</summary>

- §8.9.1 (program order)
- §8.2.4: "Memory operations with a vector data type are modeled as a set of equivalent memory
    operations with a scalar data type, executed in an unspecified order on the elements in the
    vector."
- EXT-VECTOR-ELEM

**Applies:** Events in a single thread trace

**Premises:** The source index is smaller than the target index, the target exists, and the two events are not elements of one vector access.

**Effect:** Order construction. MEM-BASE-CAUSALITY states which program-order edges enter `baseCausality`. The trace lists the elements of an access in element order, each at the next element number and the next address (EXT-VECTOR-ELEM): the events from `e` to `f` are elements of one access when each is `e`'s footprint shifted by its distance from `e`. The access as a whole is ordered with every other event.

</details>

<a id="mem-scope"></a>
#### the threads a scope includes (`MEM-SCOPE`)

*Rule* · [Lean comment: `Core/Sync/Barrier.lean` L95-L128](../../Core/Sync/Barrier.lean#L95-L128)

The scope `.cta` of a strong operation by thread `g` includes the threads of the launch in the CTA of `g`, and `.cluster` includes those in the cluster of `g`. The scopes `.gpu` and `.sys` include every thread of the launch.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`MbarScopeIncludes`](../../Core/Sync/Barrier.lean#L131-L138) ([concept](#c-mbarscopeincludes))

<details>
<summary>Details for reviewers</summary>

- §8.5: "Each strong operation must specify a scope , which is the set of threads that may interact
    directly with that operation and establish any of the relations described in the memory
    consistency model."
- §8.5: ".cta The set of all threads executing in the same CTA as the current thread."
- §8.5: ".cluster The set of all threads executing in the same cluster as the current thread."
- §8.5: ".gpu The set of all threads in the current program executing on the same compute device as
    the current thread. This also includes other kernel grids invoked by the host program on the
    same compute device."
- §8.5: ".sys The set of all threads in the current program, including all kernel grids invoked by
    the host program on all compute devices, and all threads constituting the host program itself."

**Applies:** The scope of every strong operation the model represents

**Premises:** Both threads are threads of the launch.

**Effect:** Determines which pairs of strong operations are morally strong (ERR-DATA-RACE) and which release/acquire pairs synchronize (MEM-RELEASE-ACQUIRE, MEM-MBAR-SYNCHRONIZES).

</details>

<a id="mem-release-acquire"></a>
#### release and acquire patterns (`MEM-RELEASE-ACQUIRE`)

*Rule* · [Lean comment: `Core/Memory/Acquire.lean` L11-L80](../../Core/Memory/Acquire.lean#L11-L80)

A release pattern synchronizes with an acquire pattern when the acquire pattern's strong read reads every one of its bytes from the release pattern's strong write, the two have the same nonempty footprint and mutually including scopes, and the scopes of the pattern's first and last instructions include each other's thread. A release pattern is a release write, or a release or acquire-release fence followed in program order by a strong write; an acquire pattern is an acquire read, or a strong read followed in program order by an acquire or acquire-release fence.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`synchronizesWith`](../../Core/Memory/Acquire.lean#L149-L158) ([concept](#c-synchronizeswith)), [`synchronizesWith_iff_of_not_rmw`](../../Core/Memory/Acquire.lean#L160-L171), [`ReleaseHead`](../../Core/Memory/Acquire.lean#L174-L179), [`AcquireTail`](../../Core/Memory/Acquire.lean#L181-L186), [`StrongRead`](../../Core/Memory/Acquire.lean#L188-L191), [`FenceSync`](../../Core/Memory/Acquire.lean#L193-L204) ([concept](#c-fencesync)), [`not_fenceSync_of_noFence`](../../Core/Memory/Acquire.lean#L206-L212)

<details>
<summary>Details for reviewers</summary>

- §8.9.4: "A release pattern X synchronizes with an acquire pattern Y, if a write operation in X
    precedes a read operation in Y in observation order , and the first operation in X and the last
    operation in Y are morally strong ."
- §8.9.2: "A write W precedes a read R in observation order if: R and W are morally strong and R
    reads the value written by W, or For some atomic operation Z, W precedes Z and Z precedes R in
    observation order ."
- §8.8: "A release pattern on a location M consists of one of the following: A release operation on
    M E.g.: st.release [M]; or atom.release [M]; or mbarrier.arrive.release [M];"
- §8.8: "Or a release or acquire-release memory fence followed by a strong write on M in program
    order E.g.: fence.release; st.relaxed [M]; or fence.release; atom.relaxed [M];"
- §8.8: "An acquire pattern on a location M consists of one of the following: An acquire operation
    on M E.g.: ld.acquire [M]; or atom.acquire [M]; or mbarrier.test_wait.acquire [M];"
- §8.8: "Or a strong read on M followed by an acquire memory fence in program order E.g.: ld.relaxed
    [M]; fence.acquire; or atom.relaxed [M]; fence.acquire;"
- §8.8: "Note that while atomic reductions conceptually perform a strong read as part of its
    read-modify-write sequence, this strong read does not form an acquire pattern."
- §8.7 (morally strong)
- §8.2 (Table 20): "read operation All variants of ld instruction and atom instruction (but not red
    instruction)."
- §9.7.15.4 (fence)
- §9.7.10.8 (ld)
- §9.7.10.11 (st)
- §9.7.15.5 (atom)
- §9.7.15.6 (red)

**Applies:** Generic-proxy release and acquire patterns of thread loads, stores, atomic read-modify-writes and thread fences, with mutually covering scopes

**Premises:** Equal nonempty footprints; every byte of the read reads from the pattern's write; the write and the read are strong with scopes that include each other's thread; the first instruction of the release pattern and the last of the acquire pattern have scopes that include each other's thread; a fence precedes its write, or follows its read, in program order.

**Effect:** Adds a synchronization edge to baseCausality from the first instruction of each release pattern to the last instruction of each acquire pattern under the premises (`synchronizesWith` when both are memory operations, `FenceSync` when one is a fence); every read keeps the ordinary read, allocation and race checks. `synchronizesWith` is the pattern of a release write read directly by an acquire read. `FenceSync` is the pattern with a release or acquire-release fence at its start, an acquire or acquire-release fence at its end, or both, and it also carries the `fence.sc` synchronization of MEM-FENCE-SC. The edge starts at the first instruction of the release pattern and ends at the last instruction of the acquire pattern, so it orders the operations before the first instruction (§8.8: "Any memory synchronization established by a release pattern only affects operations occurring in program order before the first instruction in that pattern.") and those after the last one.

</details>

<a id="mem-fence-sc"></a>
#### the Fence-SC order (`MEM-FENCE-SC`)

*Rule* · [Lean comment: `Core/Memory/Acquire.lean` L82-L118](../../Core/Memory/Acquire.lean#L82-L118)

The `fence.sc` events of an execution are ordered by an acyclic order that relates every two morally strong `fence.sc` and agrees with causality, and a `fence.sc` synchronizes with every morally strong `fence.sc` that follows it in this order.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`ScStrong`](../../Core/Memory/Acquire.lean#L121-L125), [`FenceScSync`](../../Core/Memory/Acquire.lean#L127-L130), [`FenceScOk`](../../Core/Memory/Acquire.lean#L132-L137), [`fenceScOk_of_noSc`](../../Core/Memory/Acquire.lean#L139-L147)

<details>
<summary>Details for reviewers</summary>

- §8.9.3: "The Fence-SC order is an acyclic partial order, determined at runtime, that relates every
    pair of morally strong fence.sc operations."
- §8.9.4: "A fence.sc operation X synchronizes with a fence.sc operation Y if X precedes Y in the
    Fence-SC order."
- §8.10.2: "Fence-SC order cannot contradict causality order . For a pair of morally strong fence.sc
    operations F1 and F2, if F1 precedes F2 in causality order , then F1 must precede F2 in Fence-SC
    order."
- §8.7 (morally strong)
- §9.7.15.4: "On sm_70 and higher membar is a synonym for fence.sc"

**Applies:** Thread fences with `.sc` semantics (`fence.sc`, `membar`)

**Premises:** Two `fence.sc` are morally strong: one thread executes both, or the scope of each includes the other's thread.

**Effect:** `Execution.fenceSC` is the order; `FenceScOk` constrains it (CORRECT-CONSISTENT), and its edges between morally strong `fence.sc` enter baseCausality through `FenceSync`.

</details>

<a id="mem-base-causality"></a>
#### base causality order (`MEM-BASE-CAUSALITY`)

*Rule* · [Lean comment: `Core/Memory/Order.lean` L81-L125](../../Core/Memory/Order.lean#L81-L125)

`baseCausality` is the base causality order of §8.9.5 for the thread instructions of one launch: the transitive closure of program order and synchronizes-with between thread instructions. Its synchronizes-with edges come from CTA barriers, mbarriers, cluster barriers, warp barriers, release and acquire patterns and the Fence-SC order.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`baseCausality`](../../Core/Memory/Order.lean#L128-L135) ([concept](#c-basecausality))

<details>
<summary>Details for reviewers</summary>

- §8.9.5: "An operation X precedes an operation Y in base causality order if: X precedes Y in
    program order , or X synchronizes with Y, or For some operation Z, X precedes Z in program order
    and Z precedes Y in base causality order , or X precedes Z in base causality order and Z
    precedes Y in program order , or X precedes Z in base causality order and Z precedes Y in base
    causality order ."
- §8.9.4 (memory synchronization: bar.sync and bar.arrive to bar.sync, release/acquire)
- §8.8 (release and acquire patterns)
- §8.9.3 (Fence-SC order)
- §9.7.15.2 (bar.warp.sync memory ordering)
- §9.7.15.16.19 (mbarrier acquire)
- §9.7.15.3 (cluster barrier)

**Applies:** Thread instruction events; independent asynchronous effects are not ordered

**Premises:** Each edge is program order, CTA/cluster/warp barrier synchronization, phase-matched mbarrier synchronization, release/acquire read-from synchronization with or without fences (MEM-RELEASE-ACQUIRE), or Fence-SC synchronization (MEM-FENCE-SC).

**Effect:** Generic-proxy ordering between thread events. The effects of asynchronous operations are ordered through the observation of their completion (MEM-OBSERVED-COMPLETION, MEM-MODEL-CAUSALITY).

</details>

<a id="mem-model-causality"></a>
#### base proxy and completion order at one byte (`MEM-MODEL-CAUSALITY`)

*Rule* · [Lean comment: `Core/Memory/Order.lean` L273-L367](../../Core/Memory/Order.lean#L273-L367)

`modelCausality` is applied at a byte that both accesses touch; between two thread accesses it is `baseCausality` (§8.9.5) or allocation-result order at that byte (EXT-TMEM-ALLOC-RESULT-ORDER). From a thread access to the access of a `cp.async`, `st.async` or `red.async`, which are performed in the generic proxy, it is also `baseCausality` to the issue. Its proxy-fence case (`ProxyBefore`), which orders a thread access before the async-proxy access of an asynchronous operation through a `fence.proxy.async`, is the text of §9.7.15.4. Its observed-completion and async-chain cases, which order the accesses of asynchronous operations, are model readings of the manual text quoted for each. `ByteCausality` adds the observed MMA operand handoff to these paths (EXT-TC-COMMIT-OPERAND-ORDER).

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`AsyncCovers`](../../Core/Memory/Order.lean#L424-L427), [`AsyncFenceCovers`](../../Core/Memory/Order.lean#L429-L437), [`ProxyFenceReach`](../../Core/Memory/Order.lean#L439-L444), [`ProxyBefore`](../../Core/Memory/Order.lean#L446-L456) ([concept](#c-proxybefore)), [`proxyBefore_iff_of_cta`](../../Core/Memory/Order.lean#L458-L472), [`AsyncOnlyFinished`](../../Core/Memory/Order.lean#L474-L480), [`AsyncBefore`](../../Core/Memory/Order.lean#L482-L488), [`AsyncChain`](../../Core/Memory/Order.lean#L490-L498) ([concept](#c-asyncchain)), [`PairAsync`](../../Core/Memory/Order.lean#L500-L504) ([concept](#c-pairasync)), [`PairTc`](../../Core/Memory/Order.lean#L506-L510), [`CompletionBefore`](../../Core/Memory/Order.lean#L512-L517) ([concept](#c-completionbefore)), [`GenericCopy`](../../Core/Memory/Order.lean#L410-L413), [`not_genericCopy_of_mbarrier`](../../Core/Memory/Order.lean#L415-L422), [`modelCausality`](../../Core/Memory/Order.lean#L588-L605) ([concept](#c-modelcausality)), [`modelCausality.of_base`](../../Core/Memory/Order.lean#L607-L608), [`modelCausality.of_allocResultBefore`](../../Core/Memory/Order.lean#L610-L612), [`modelCausality_thread_async_of_not_generic`](../../Core/Memory/Order.lean#L614-L620), [`TcReadReuseBefore`](../../Core/Memory/Order.lean#L557-L566), [`TcReadReuseBefore.base`](../../Core/Memory/Order.lean#L573-L578), [`TcReadReuseBefore.congr`](../../Core/Memory/Order.lean#L580-L586), [`ObservedCompletionBefore`](../../Core/Memory/Order.lean#L568-L571)

<details>
<summary>Details for reviewers</summary>

- §8.9.5 (thread-thread case): "An operation X precedes an operation Y in base causality order if:
    X precedes Y in program order , or X synchronizes with Y"
- EXT-TMEM-ALLOC-RESULT-ORDER (allocation-result readback)
- §8.9.5 (proxy-fence and async-chain cases): "A memory operation X precedes a memory operation Y
    in proxy-preserved base causality order if X precedes Y in base causality order , and: X and Y
    are performed to the same address, using the generic proxy , or X and Y are performed to the
    same address, using the same proxy , and by the same thread block, or X and Y are aliases and
    there is an alias proxy fence along the base causality path from X to Y."
- §9.7.15.4 (proxy-fence case): "membar.proxy and fence.proxy instructions establish an ordering
    between memory accesses that may happen through different proxies ."
- §9.7.15.4 (proxy-fence case): "A uni-directional proxy ordering from the from-proxykind to the
    to-proxykind establishes ordering between a prior memory access performed via the
    from-proxykind and a subsequent memory access performed via the to-proxykind ."
- §9.7.15.4 (proxy-fence case): "Value .async of the .proxykind qualifier specifies that the memory
    ordering is established between the async proxy and the generic proxy."
- §9.7.15.4 (proxy-fence case): "The memory ordering is limited only to operations performed on
    objects in the state space specified."
- §9.7.15.4 (proxy-fence case): "If no state space is specified, then the memory ordering applies
    on all state spaces."
- §9.7.15.4 (proxy-fence case, reach of a fence with a scope): "The scope qualifier specifies the
    set of threads that may observe the ordering effect of this operation."
- §9.7.15.4 (proxy-fence case, reach of a fence without a scope): "Their cross-proxy synchronizing
    effect composes with other forms of synchronization according to the rules of the Memory
    Consistency Model ."
- §9.7.10.28.2 (proxy-fence case, async-proxy operations): "The cp{.reduce}.async.bulk operations
    are performed in the asynchronous proxy (or async proxy )."
- §9.7.10.28.3.1 (thread-to-async case, generic-proxy operations, ordered without a fence):
    "cp.async is treated as a weak memory operation performed in the generic proxy in the Memory
    Consistency Model ."
- §9.7.10.12 (thread-to-async case, generic-proxy operations, ordered without a fence): "st.async
    is performed in the generic proxy."
- §9.7.15.7 (thread-to-async case, generic-proxy operations, ordered without a fence): "red.async
    is performed in the generic proxy."
- §8.9.1.1 (thread-to-async case, async-proxy operations: ordered after prior instructions of the
    same thread; the model still requires a proxy fence): "These asynchronous operations are
    ordered after prior instructions in the same thread"
- §9.7.10.28.1.1 (observed-completion case: a wait observes completion): "When an async-group
    completes, all the asynchronous operations belonging to that group are complete and the
    executing thread that initiated the asynchronous operations can read the result of the
    asynchronous operations."
- §9.7.10.28.1.2 (observed-completion case: a wait observes completion): "When the current phase
    of the mbarrier object is complete, it implies that all asynchronous operations tracked by this
    phase are complete, and all threads participating in that mbarrier object can access the result
    of the asynchronous operations."
- §9.7.10.28.6.2 (observed-completion case: bulk-group wait modes)
- §9.7.18.6.5 (observed-completion case: proxy fence for the tcgen05 shared-memory reads)
- EXT-TCACQUIRE
- EXT-TC-SOURCE-REUSE (reusing a completed Tensor Core source)
- EXT-PAIR-ASYNC

**Applies:** Ordinary accesses and the independent accesses of copies/MMAs

**Premises:** Async-to-async order holds between two operations issued by threads of the same CTA ("by the same thread block"), or, under EXT-PAIR-ASYNC, by the two CTAs of one `cta_group::2` pair at a shared byte of that pair when one of the two operations is a `cta_group::2` `tcgen05.mma` or `tcgen05.cp` (`PairTc`), joined by a chain of observed-completion edges; generic-to-async order has an explicit async proxy fence whose state space covers the byte (`AsyncFenceCovers`; for `.shared::cta` the byte is in the fence's CTA), ordered by baseCausality before the issue, whose thread the fence reaches (`ProxyFenceReach`): a thread of the fence's cluster, possibly in a peer CTA, and for a fence with a scope a thread that the scope includes, or, for a `cp.async`, `st.async` or `red.async` (generic proxy, `GenericCopy`), baseCausality to its issue; async-to-later order has an observation of that operation's completion, followed for the shared-memory reads of `tcgen05.mma` and `tcgen05.cp` by an async proxy fence covering the byte (`CompletionBefore`, §9.7.18.6.5) or a completed source overwrite (EXT-TC-SOURCE-REUSE). Scope and accessed byte match.

**Effect:** Read-source/coherence and conflicting-access checks. The fence composes with ordinary synchronization before/after it; it need not be executed by the eventual async issuer. Chains are built only from the typed edges above (`AsyncChain`). Direct asynchronous edges compose through an actual asynchronous memory effect at the same byte. The composed order relates the two endpoint operations only when their issuing threads are in one CTA, or in one `cta_group::2` pair at a byte of that pair when one of the two is a `cta_group::2` `tcgen05` operation (EXT-PAIR-ASYNC), and the interior operations of the chain may belong to any CTA. Each edge relates the accesses of one operation, or of the next operation in the chain, at the one byte.

</details>

<a id="mem-byte-causality"></a>
#### byte order used by memory checks (`MEM-BYTE-CAUSALITY`)

*Rule* · [Lean comment: `Core/Memory/CommitOperandOrder.lean` L12-L31](../../Core/Memory/CommitOperandOrder.lean#L12-L31)

Byte causality consists of the base proxy and completion paths and the observed handoff of a shared operand byte of an MMA or a Tensor Memory copy.

Source:

- - §8.9.5 (base proxy order) - EXT-TC-COMMIT-OPERAND-ORDER (observed operand handoff) - EXT-TC-SOURCE-REUSE (observed copy-source overwrite)

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`ByteCausality`](../../Core/Memory/CommitOperandOrder.lean#L90-L104) ([concept](#c-bytecausality)), [`ByteCausality.direct_iff_of_global`](../../Core/Memory/CommitOperandOrder.lean#L106-L114), [`ByteCausality.direct_iff_of_no_operand`](../../Core/Memory/CommitOperandOrder.lean#L116-L128), [`ByteCausality.direct_iff_of_not_write`](../../Core/Memory/CommitOperandOrder.lean#L130-L140), [`CommitOperandIssue`](../../Core/Memory/CommitOperandOrder.lean#L69-L77), [`CommitOperandIssue.congr`](../../Core/Memory/CommitOperandOrder.lean#L79-L88)

<details>
<summary>Details for reviewers</summary>

**Applies:** The memory checks for two accesses to one byte.

**Premises:** A direct `modelCausality` edge or all premises of the observed operand handoff.

**Effect:** Supplies the byte order used in read consistency, coherence and safety.

</details>

<a id="ext-pair-async"></a>
##### a cta_group::2 pair is one thread block for asynchronous accesses (`EXT-PAIR-ASYNC`)

*Interpretation (EXT)* · [Lean comment: `Core/Memory/Order.lean` L369-L407](../../Core/Memory/Order.lean#L369-L407)

Asynchronous-proxy accesses to the shared memory of either CTA of a `cta_group::2` pair, issued by either CTA of the pair, count as performed by the same thread block when one of the two operations is a `cta_group::2` `tcgen05.mma` or `tcgen05.cp`; a chain of observed completions then orders them as it orders the asynchronous accesses of one CTA.

Source:

- - §8.9.5: "A memory operation X precedes a memory operation Y in proxy-preserved base causality order if X precedes Y in base causality order , and: X and Y are performed to the same address, using the generic proxy , or X and Y are performed to the same address, using the same proxy , and by the same thread block, or X and Y are aliases and there is an alias proxy fence along the base causality path from X to Y." - §9.7.18.10.10.1: "The qualifier .cta_group::2 specifies that the matrix multiply and accumulate operation is performed on the Tensor Memory of the executing thread’s CTA and its peer CTA ." - §9.7.10.28.5.3: "When .cta_group::2 is specified, the mbarrier object mbar can be in shared memory of either the same CTA as the shared memory destination dstMem or in its peer-CTA ."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The ISA text does not extend "by the same thread block" to the two CTAs of a pair. The model reads it so: for a CTA pair formed by `cta_group::2` (`SameCtaGroup L .two`), asynchronous-proxy accesses to the shared memory of either CTA of the pair, issued by either CTA of the pair, count as performed by the same thread block in §8.9.5 (`PairAsync`) when one of the two operations is a `cta_group::2` `tcgen05.mma` or `tcgen05.cp` (`PairTc`). A `cta_group::2` operation is meaningful only under this reading: the peer CTA's load, observed through an mbarrier of the leader's CTA, is read by the leader's MMA, and the MMA's completion, committed to the peer's barrier, frees the peer's load. CUTLASS and DeepGEMM 2-CTA kernels rely on it. Each of these orders relates a `cta_group::2` MMA to a copy. For two operations neither of which is a `cta_group::2` `tcgen05` operation the text and this evidence say nothing: two copies of two CTAs of a pair (a `cp.async.bulk` into the peer CTA's shared memory and a later bulk read of it by the peer) stay unordered, as for any two CTAs, even when a `cta_group::2` MMA lies between them on the chain.

**Effect:** The rule is wider than the text for the cross-CTA endpoints of a pair. If it does not hold, an asynchronous access by one CTA of a pair and a conflicting asynchronous access by the other (a peer CTA's tensor load and the leader's MMA operand read, an MMA's read and the next load into the same buffer) are unordered on hardware: such programs race, which the model does not report. Disclosed by every kernel whose statement names `CtaGroup.two`: FlashAttn4Fwd, Fp16Gemm8192.

</details>

<a id="ext-read-wait-order"></a>
##### a `.read` bulk-group wait orders the source reads before generic accesses (`EXT-READ-WAIT-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Memory/Order.lean` L207-L239](../../Core/Memory/Order.lean#L207-L239)

Once a `cp.async.bulk.wait_group.read` that covers the bulk group of a tensor store returns, the store's asynchronous-proxy source reads are ordered before the generic accesses that the waiting thread's return precedes in causality (`AsyncFinished`, the `.read (.store ..)` case), with no `fence.proxy.async` between them.

Source:

- - §9.7.10.28.2: "Accessing the same memory location across multiple proxies needs a cross-proxy fence. For the async proxy , fence.proxy.async should be used to synchronize memory between generic proxy and the async proxy ." - §9.7.10.28.2: "The completion of a cp{.reduce}.async.bulk operation is followed by an implicit generic-async proxy fence." - §9.7.10.28.6.2: "The optional .read modifier indicates that the waiting has to be done until all the bulk async operations in the specified bulk async-group have completed: reading from the tensormap the reading from their source locations."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The implicit generic-async proxy fence follows the completion of the operation, and a `.read` wait waits only until the source reads are done; it does not wait until the operation is complete. Without a proxy fence the async-proxy reads and a later generic store to the same bytes are not ordered by §8.9.5 (proxy-preserved base causality).

**Effect:** A generic store that reuses the source buffer is not a race with those reads, and the reads do not see it. The rule is wider than the text: it relies on hardware completing the source reads in a way that a later generic access of the waiting thread's causal successors cannot overtake. CUTLASS epilogues rely on it: they wait with `cp.async.bulk.wait_group.read` (`tma_store_wait`) and then reuse the shared-memory buffer without a proxy fence. If it does not hold, such a reuse is a data race and the store may write the reused buffer's new contents to global memory, which the model does not report. Disclosed by every kernel whose statement names `Op.bulkWait (mode := BulkGroup.WaitMode.read)`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192.

</details>

<a id="ext-tc-commit-operand-order"></a>
##### an observed commit orders prior writes to its operand bytes (`EXT-TC-COMMIT-OPERAND-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Memory/CommitOperandOrder.lean` L35-L66](../../Core/Memory/CommitOperandOrder.lean#L35-L66)

Observing the completion of an MMA through a tracked commit carries the order of writes that precede a shared operand read to the waiting thread's subsequent accesses to the same byte.

Source:

- - PTX ISA 9.5 §9.7.18.6.4.2, Example 2: "tcgen05.mma [d], ... tcgen05.commit.mbarrier::arrive::one mbarrier.try_wait.relaxed.cluster (loop until successful)" - PTX ISA 9.5 §9.7.18.6.4.2: "For the completion of the asynchronous tcgen05.mma , tcgen05.commit is used." - PTX ISA 9.5 §9.7.18.12.1: "Upon the completion of the tracked asynchronous tcgen05 operations, the signal specified by the .completion_mechanism is triggered by the system on the mbarrier object."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The example establishes how a thread observes completion. It does not give an order across proxies from a writer of an operand through the MMA to a later access of that shared byte. The reading lets that access reuse the byte once the read is complete. Disclosed by every kernel whose statement names `Op.tcMma` and `Op.tcCommit`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

**Applies:** Writes to a shared byte read by an actual MMA, and later ordinary or asynchronous accesses to that byte issued by the thread observing the corresponding commit notification.

**Premises:** The write precedes the actual operand read at this byte. A successful wait in scope observes the notification of a commit that tracks the MMA. The wait precedes the later access's issue in program order. The two conflicting accesses both cover the byte.

**Effect:** The write precedes the later access in byte causality for the race, mixed access, read source and coherence checks. The rule gives no order to accesses of other bytes and does not turn the commit notification into a release.

</details>

<a id="ext-tc-source-reuse"></a>
##### overwriting a shared source after observed Tensor Core completion (`EXT-TC-SOURCE-REUSE`)

*Interpretation (EXT)* · [Lean comment: `Core/Memory/Order.lean` L520-L554](../../Core/Memory/Order.lean#L520-L554)

Observed completion of a shared-byte read by a Tensor Memory copy or an MMA ends its use of that byte before a covering generic store. For an MMA, the store must follow the acquire in the same thread. The copy's operand handoff also carries an earlier write that precedes the copy read to the covering store.

Source:

- - PTX ISA 9.5 §9.7.18.6.2.1.1 (mbarrier-based completion of `tcgen05.cp` and `tcgen05.mma`) - PTX ISA 9.5 §9.7.18.12.1: "Upon the completion of the tracked asynchronous tcgen05 operations, the signal specified by the .completion_mechanism is triggered by the system on the mbarrier object." - PTX ISA 9.5 §9.7.18.6.5: "Accessing the same memory location across multiple proxies needs a cross-proxy fence."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The commit mechanism fixes when the tracked source read finishes. The shared-memory rule requires a fence across proxies and does not make an exception for recycling a source whose read has already finished. The reading treats the observed end of the read as enough to avoid overlap with a later plain overwrite of that byte. Generic writes supplying the read still require their original proxy order into the operation.

**Applies:** A `tcgen05.cp` or `tcgen05.mma` shared operand byte and an ordinary store covering that byte.

**Premises:** A real source footprint covers the byte and an in-scope acquire observes that operation's completion (`AsyncFinished`). The acquire precedes the store in base causality. For MMA it also precedes the store in the same thread's trace. Carrying an earlier write into the copy-source overwrite requires a recorded copy byte read, byte order into that read, and a store after the acquire in the same thread (`CommitOperandIssue`).

**Effect:** Orders the source read before the overwrite at that byte. No fence is inferred for another address or for accesses that consume an asynchronously written value. Disclosed by every kernel whose statement names `Op.tcCp` and `Op.tcCommit` or `Op.tcMma` and `Op.tcCommit`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

</details>

### Which values a read may return

The reads-from relation and the causality and coherence axioms that constrain it.

<a id="mem-reads-from"></a>
#### reads-from (`MEM-READS-FROM`)

*Rule* · [Lean comment: `Core/Memory/Read.lean` L20-L39](../../Core/Memory/Read.lean#L20-L39)

Each byte that a read returns comes from a write that covers the byte, or from the initial write W0. W0 supplies the launch content of the byte, or, for an allocated byte whose content is unspecified, one value that is fixed for the whole execution.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`RfWf`](../../Core/Memory/Read.lean#L42-L50) ([concept](#c-rfwf))

<details>
<summary>Details for reviewers</summary>

- §8.2.6 (W0)
- §8.9.7 (communication order: reads-from)

**Applies:** Each byte of an ordinary or asynchronous read

**Premises:** The execution contains that read and its chosen source.

**Effect:** Execution constraint in Consistent.rf. `W0` supplies known launch bytes from `Mem0` and unspecified allocated bytes from `X.initial`, so two W0 reads of one address cannot choose different initial values. This choice supplies bytes to copies as well as ordinary reads.

</details>

<a id="mem-read-axioms"></a>
#### the memory model axioms (`MEM-READ-AXIOMS`)

*Rule* · [Lean comment: `Core/Memory/Read.lean` L52-L79](../../Core/Memory/Read.lean#L52-L79)

A read never reads a byte from a write that the read precedes at that byte. When a write precedes a read at a byte, the read reads that byte neither from the initial write nor from a write that precedes that write at the byte; "precedes" is the model causality order `ByteCausality` (MEM-MODEL-CAUSALITY and EXT-TC-COMMIT-OPERAND-ORDER).

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`NoFuture`](../../Core/Memory/Read.lean#L82-L86) ([concept](#c-nofuture)), [`Hidden`](../../Core/Memory/Read.lean#L88-L96) ([concept](#c-hidden))

<details>
<summary>Details for reviewers</summary>

- §8.10.6 (causality)
- §8.10.1 (coherence)
- §8.9.6 (coherence order)

**Applies:** Ordinary/async reads and covering writes

**Premises:** A read chooses a source; another write may be visible at the same byte.

**Effect:** Execution constraints in Consistent.noFuture and Consistent.hidden.

</details>

### What counts as a memory error

Executions that are rejected as unsafe because of how they access memory.

<a id="err-data-race"></a>
#### unordered conflicting accesses (`ERR-DATA-RACE`)

*Rule* · [Lean comment: `Core/Assembly/Safety.lean` L25-L113](../../Core/Assembly/Safety.lean#L25-L113)

An execution is unsafe when two distinct accesses with the same footprint, at least one of them a write, are not morally strong and neither precedes the other in model causality order (`ByteCausality`) at a byte they access. Two writes of the same bytes with the same value are exempt.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Conflict`](../../Core/Assembly/Safety.lean#L116-L120) ([concept](#c-conflict)), [`StrongScoped`](../../Core/Assembly/Safety.lean#L122-L134) ([concept](#c-strongscoped)), [`not_strongScoped_write_copy`](../../Core/Assembly/Safety.lean#L136-L144), [`strongScoped_thread_of_old`](../../Core/Assembly/Safety.lean#L146-L152), [`strongScoped_thread_old`](../../Core/Assembly/Safety.lean#L154-L176), [`AsyncCopy.Ref.Generic`](../../Core/Assembly/Safety.lean#L178-L182), [`generic_async_iff`](../../Core/Assembly/Safety.lean#L184-L187), [`OpFootprint`](../../Core/Assembly/Safety.lean#L189-L197), [`MorallyStrong`](../../Core/Assembly/Safety.lean#L199-L205) ([concept](#c-morallystrong)), [`SameValueWrites`](../../Core/Assembly/Safety.lean#L207-L212) ([concept](#c-samevaluewrites)), [`Race`](../../Core/Assembly/Safety.lean#L214-L220) ([concept](#c-race))

<details>
<summary>Details for reviewers</summary>

- §8.7: "Two operations are said to be morally strong relative to each other if they satisfy all of
    the following conditions: The operations are related in program order (i.e, they are both
    executed by the same thread), or each operation is strong and specifies a scope that includes
    the thread executing the other operation. Both operations are performed via the same proxy . If
    both are memory operations, then they overlap completely."
- §8.7.1: "Two conflicting memory operations are said to be in a data-race if they are not related
    in causality order and they are not morally strong ."
- §8.4 (strong operations)
- §8.6 (proxies)
- §9.7.10.28.5.4: "Each reduction operation performed by cp.reduce.async.bulk.tensor has
    individually .relaxed.gpu memory ordering semantics and are element-wise atomic."
- §9.7.10.28.4.2: "These are element-wise atomic at the specified scope."
- §9.7.10.28.4.2: "When .sem.scope is not specified, it defaults to .relaxed.sys ."
- §9.7.10.28.4.2: "The memory operations are performed in the async proxy."
- §9.7.15.7 (red.async): "The reduce operation is a relaxed memory operation."
- §9.7.15.7 (red.async): "The reduce operation is a strong memory operation with .release semantics
    at the scope specified by .scope ."
- §9.7.10.12 (st.async): "The store operation is a strong memory operation with .release semantics
    at the scope specified by .scope ."
- §9.7.10.28.1 (async access hazards)
- §9.7.18.10 (MMA source stability)
- §8.7.2: "The axioms in the memory consistency model do not apply if a PTX program contains one or
    more mixed-size data-races . But these axioms are sufficient to describe the behavior of a PTX
    program with only uniform-size data-races ."
- §8.9.6: "Two overlapping writes are unrelated in coherence order if they are in a data-race ,
    which gives rise to the partial nature of coherence order ."
- §8.10.1: "If a write W precedes an overlapping write W’ in causality order , then W must precede
    W’ in coherence order ."
- §8.10.6: "If a read R precedes an overlapping write W in causality order , then R cannot read from
    W. If a write W precedes an overlapping read R in causality order , then for any byte accessed
    by both R and W, R cannot read from any write W’ that precedes W in coherence order ."

**Applies:** Ordinary and asynchronous access intents, including still-pending effects and the never-completing reads of tensor prefetches (THREAD-TENSOR-PREFETCH, EXT-PREFETCH-PENDING)

**Premises:** Distinct accesses overlap at a byte, at least one writes, they are not morally strong, they are not two writes of the same bytes with the same value (`SameValueWrites`), and neither direction is ordered by the causality order at the byte (`ByteCausality`).

**Effect:** Safety rejection. Source/destination reuse before or after an operation is permitted when the corresponding order is proved. A morally strong pair is not a race; a read in such a pair is constrained by MEM-READS-FROM and MEM-READ-AXIOMS only. The strong operations represented are the thread accesses with a `.relaxed`, `.acquire`, `.release` or `.acq_rel` qualifier (`Acc.Strong`: the strong loads and stores of THREAD-ACCESS, `.volatile` ones as `.relaxed` at `.sys`, `.mmio` ones with their own `.sem` at `.sys`, and every `atom` and `red`, whose `.sem` is `.relaxed` when absent), with the access's `scope` (`.gpu` when absent for `atom` and `red`), the element reductions of `cp.reduce.async.bulk.tensor` (`.relaxed.gpu`), the element reductions of `cp.reduce.async.bulk` and `red.async` at the scope of their `.sem.scope` (`.relaxed.sys` when absent for `cp.reduce.async.bulk`), and the write of `st.async.release` at its scope. Scope inclusion is MEM-SCOPE (`MbarScopeIncludes`). An atomic read-modify-write is one access that both reads and writes, so two `atom` or `red` operations of the same footprint whose scopes include each other's thread are morally strong and are not a race, while an `atom` and a conflicting weak access are. Thread accesses and the stages of `cp.async`, `st.async` and `red.async` use the generic proxy, the other asynchronous effects the async proxy (§8.6). The issuing thread executes an asynchronous operation. A reduction's read and write of a byte are part of its element's operation (DEP-REDUCTION-VALUES), so two reductions overlap completely when they reduce the same element.

</details>

<a id="mem-atomicity"></a>
#### atomicity of read-modify-write operations (`MEM-ATOMICITY`)

*Rule* · [Lean comment: `Core/Memory/Atomic.lean` L22-L86](../../Core/Memory/Atomic.lean#L22-L86)

Two atomic read-modify-write operations of the same footprint that are morally strong never read a byte from the same write, and never both read a byte from the initial write W0. Reads-from among morally strong atomic read-modify-writes of one footprint has no cycle. The atomic read-modify-writes are the elements of `atom` and `red` and of tensor and linear reductions.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`RmwId`](../../Core/Memory/Atomic.lean#L89-L97), [`RmwId.newRef`](../../Core/Memory/Atomic.lean#L99-L103), [`Execution.oldRf`](../../Core/Memory/Atomic.lean#L105-L109), [`Execution.RmwAt`](../../Core/Memory/Atomic.lean#L111-L116), [`RmwStrong`](../../Core/Memory/Atomic.lean#L118-L122), [`AtomicReads`](../../Core/Memory/Atomic.lean#L124-L128), [`AtomicUnique`](../../Core/Memory/Atomic.lean#L130-L134), [`AtomicAcyclic`](../../Core/Memory/Atomic.lean#L136-L138), [`AtomicOk`](../../Core/Memory/Atomic.lean#L140-L143), [`rmwStrong_tensor`](../../Core/Memory/Atomic.lean#L145-L174), [`atomicReads_of_reduceReads`](../../Core/Memory/Atomic.lean#L176-L184), [`reduceUnique_of_atomic`](../../Core/Memory/Atomic.lean#L186-L198), [`reduceAcyclic_of_atomic`](../../Core/Memory/Atomic.lean#L200-L212)

<details>
<summary>Details for reviewers</summary>

- §8.10.3: "Atomicity of read-modify-write (RMW) operations When an atomic operation A and a write W
    overlap and are morally strong , then the following two communications cannot both exist in the
    same execution, for the set of bytes accessed by both A and W: A reads any byte from a write W’
    that precedes W in coherence order . A follows W in coherence order ."
- §8.10.3: "Atomicity is guaranteed when the operations are morally strong ."
- §8.10.3: "Atomicity is not guaranteed if the operations are not morally strong ."
- §8.9.6: "Two overlapping write operations are related in coherence order if they are morally
    strong or if they are related in causality order ."
- §9.7.15.5 (atom): "Two atomic operations ( atom or red ) are performed atomically with respect to
    each other only if each operation specifies a scope that includes the other. When this condition
    is not met, each operation observes the other operation being performed as if it were split into
    a read followed by a dependent write."
- §9.7.15.6 (red)
- ERR-DATA-RACE (`MorallyStrong`)
- §9.7.10.28.4.2: "These are element-wise atomic at the specified scope."
- THREAD-ATOMIC
- EXT-TMA-REDUCE-ATOMIC

**Applies:** Every pair of performed atomic read-modify-writes (`RmwId`) of one footprint that are morally strong

**Premises:** Both operations are performed at the same footprint (`RmwAt`) and are morally strong (`RmwStrong`: ERR-DATA-RACE's `MorallyStrong` of their writes, which requires the same proxy, scopes that include each other's thread or the same thread, and complete overlap).

**Effect:** Execution constraint in Consistent.atomic; the reads-from edges among such operations are coherence edges of CORRECT-FINAL (`CoStep`). An atomic read-modify-write is one operation that reads and writes its footprint: a thread's `.rmw` event (one per element of an `atom` or `red`, THREAD-ATOMIC), one element of a tensor reduction (EXT-TMA-REDUCE-ATOMIC), whose read of byte `k` is its `.old` stage and whose write of byte `k` is its `.write` stage, or one element of a linear reduction (`cp.reduce.async.bulk`, `red.async`), whose old-value read and write are its stages `.old (.elem j)` and `.write (.elem j)` (§9.7.10.28.4.2: "These are element-wise atomic at the specified scope."). The model imposes two consequences of §8.10.3 and records no coherence order. Let `A1` and `A2` be distinct morally strong atomic operations of one footprint. They are related in coherence order (§8.9.6), say `A1` before `A2`. The model reads an atomic operation as following, in coherence order, the write it reads a byte from, and W0 precedes every write. If both read byte `k` from the same write `W’`, or both from W0, then `W’` precedes `A1`, so `A2` reads a byte from a write that precedes `A1` while following `A1`, which §8.10.3 forbids with `A = A2` and `W = A1` (`AtomicUnique`). Every reads-from edge between them goes forward in coherence order, a strict order, so these edges have no cycle (`AtomicAcyclic`), which also excludes an operation reading its own write. Together they make the morally strong atomic operations of one footprint a single reads-from chain per byte.

</details>

<a id="err-mixed-size"></a>
#### overlapping accesses of different widths (`ERR-MIXED-SIZE`)

*Rule* · [Lean comment: `Core/Assembly/Safety.lean` L222-L238](../../Core/Assembly/Safety.lean#L222-L238)

An execution is unsafe when two conflicting accesses with different footprints overlap at a byte and neither precedes the other in `ByteCausality` at that byte.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Mixed`](../../Core/Assembly/Safety.lean#L241-L245) ([concept](#c-mixed))

<details>
<summary>Details for reviewers</summary>

- §8.7.2 (mixed-size races)
- §9.7.10.28.1 (async hazards)

**Applies:** Ordinary and asynchronous conflicting access intents with different footprints

**Premises:** An overlapping byte has no order (`ByteCausality`) in either direction.

**Effect:** Safety rejection, with read consistency checked byte by byte.

</details>

<a id="err-unallocated-access"></a>
#### allocation checks (`ERR-UNALLOCATED-ACCESS`)

*Rule* · [Lean comment: `Core/Assembly/Safety.lean` L506-L529](../../Core/Assembly/Safety.lean#L506-L529)

An execution is unsafe when an access touches a byte that is not allocated at launch. This covers thread loads, including non-coherent loads, thread stores and the footprints of asynchronous accesses, pending ones and tensor prefetch reads included. It also covers the eight bytes of every mbarrier object that an instruction names as an operand.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Unalloc`](../../Core/Assembly/Safety.lean#L532-L536) ([concept](#c-unalloc))

<details>
<summary>Details for reviewers</summary>

- §8.2.6 (the initial write W0 covers the allocated memory); no ISA sentence makes an access to an
    unallocated byte undefined
- §9.7.15.16: "An mbarrier object is an opaque object in memory"

**Applies:** Bytes touched by load/store events, including nc, the footprints of asynchronous accesses, pending ones and tensor prefetch reads (EXT-PREFETCH-PENDING) included, and the eight bytes of each mbarrier operand (`UsesMbar`: arrivals, polls, initializations, invalidations, the completion mbarriers of linear copies and tensor loads, `cp.async.mbarrier.arrive`, the targets of `tcgen05.commit` and the response mbarriers of the target CTAs of a CLC request)

**Premises:** A touched location is unallocated in mem0.

**Effect:** Safety rejection.

</details>

<a id="err-shared-lifetime"></a>
#### shared memory exists for every use and outlives its completion (`ERR-SHARED-LIFETIME`)

*Rule* · [Lean comment: `Core/Assembly/SharedLifetime.lean` L10-L138](../../Core/Assembly/SharedLifetime.lean#L10-L138)

A use of a CTA's shared memory by an instruction of another CTA must be preceded, in lifetime order, by an instruction of the owning CTA, which shows that the owner has started. If every thread of the owning CTA has exited, the use must have occurred and its completion must precede the exit of one of the owner's threads.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`CommitNext`](../../Core/Assembly/SharedLifetime.lean#L141-L150), [`not_commitNext`](../../Core/Assembly/SharedLifetime.lean#L152-L162), [`TensorStore.Selected`](../../Core/Assembly/SharedLifetime.lean#L164-L166), [`TensorStore.ReadsDrainedBeforeExit`](../../Core/Assembly/SharedLifetime.lean#L168-L171), [`StoreReadsBeforeExit`](../../Core/Assembly/SharedLifetime.lean#L173-L180), [`LifetimeStep`](../../Core/Assembly/SharedLifetime.lean#L182-L188), [`lifetimeStep_noAssumedOrder`](../../Core/Assembly/SharedLifetime.lean#L190-L206), [`LifetimeOrder`](../../Core/Assembly/SharedLifetime.lean#L208-L213) ([concept](#c-lifetimeorder)), [`CompletedBefore`](../../Core/Assembly/SharedLifetime.lean#L215-L223) ([concept](#c-completedbefore)), [`CompletedBefore.of_storeReadsBeforeExit`](../../Core/Assembly/SharedLifetime.lean#L225-L231), [`StageUses`](../../Core/Assembly/SharedLifetime.lean#L233-L249), [`SharedUse`](../../Core/Assembly/SharedLifetime.lean#L251-L263) ([concept](#c-shareduse)), [`PeerSharedStarted`](../../Core/Assembly/SharedLifetime.lean#L265-L270), [`CtaExited`](../../Core/Assembly/SharedLifetime.lean#L272-L274), [`SharedFinished`](../../Core/Assembly/SharedLifetime.lean#L276-L281), [`SharedLifetimeUnsafe`](../../Core/Assembly/SharedLifetime.lean#L283-L291) ([concept](#c-sharedlifetimeunsafe))

<details>
<summary>Details for reviewers</summary>

- §2.2.2: "The executing CTA has to make sure that the shared memory of the peer CTA exists before
    communicating with it via shared memory and the peer CTA hasn’t exited before completing the
    shared memory operation."
- §5.1.7: "The shared ( .shared ) state space is a memory that is owned by an executing CTA"
- §9.7.15.18 (the response written to each target CTA): "The behavior of instruction with
    .multicast::cluster::all qualifier is undefined if any CTA in the cluster is exited."
- §9.7.10.28.1.2: "When the current phase of the mbarrier object is complete, it implies that all
    asynchronous operations tracked by this phase are complete"
- §9.7.10.28.6.2: "wait until only N or fewer of the most recent bulk async-groups are pending and
    all the prior bulk async-groups committed by the executing threads are complete"
- MEM-OBJECT-ORDER-CAUSALITY (`stageCausality`, `ObjectOrder`, ObjectCoherent)
- DEP-ORDER (`DepStep`, `Witness`, `DependencyOk`)
- EXT-ENABLES-OBJECT

**Applies:** Every use of a CTA's shared memory (`SharedUse`), whether that CTA is the issuer's or another one: thread instructions and performed asynchronous stages that access it or operate on an mbarrier object in it, and, performed or not, the stage that completes an issued asynchronous operation's use of it

**Premises:** For a CTA other than the issuer's, an instruction of that CTA precedes the issuing instruction in `LifetimeOrder`. If the owning CTA has exited, the use has occurred and its completion precedes at least one of the owner's exit instructions (`SharedFinished`).

**Effect:** Unsafe rejects missing lifetime evidence. The rule is a safety check that is valid with any order: it only reads the orders it uses (`LifetimeOrder`, `CompletedBefore`) and adds no edge to any order, so it lives with the other Unsafe items in the assembly layer. The direction is `reading` because the second order of `LifetimeOrder` rests on EXT-ENABLES-OBJECT; the first order and the completion requirement are stricter than the text. §2.2.2 and §5.1.7 state one rule for every shared memory operation, whichever instruction performs it and whichever CTA owns the memory. The table of uses (`SharedUse`, with `StageUses` for the stages that complete an operation, which are the `AsyncCopy.FinalStage` table of DEP-ASYNC-STAGE-ORDER) is the only kind-specific part: Columns: Operation; Stage that completes its use of CTA `c`; `c`. Rows: - thread instruction — Stage that completes its use of CTA `c`: the instruction; `c`: the CTA of a shared location it accesses or of an mbarrier it operates on - `tcgen05.commit` — Stage that completes its use of CTA `c`: the issuing instruction; `c`: each CTA of the issuer's CTA group (§9.7.18.5) - any performed asynchronous stage — Stage that completes its use of CTA `c`: the stage; `c`: the CTA of a shared location it accesses or of an mbarrier it updates - tensor load — Stage that completes its use of CTA `c`: each data write (`.write (.load ..)`); `c`: the destination CTA - tensor load — Stage that completes its use of CTA `c`: its notification (`.notify .load`); `c`: the mbarrier's CTA - tensor store — Stage that completes its use of CTA `c`: its source reads' completion (`.readsDone`); `c`: the source CTA - linear copy completed through an mbarrier — Stage that completes its use of CTA `c`: its notification (`.notify .copy`); `c`: the CTA of its shared source or destination and the mbarrier's CTA - linear copy completed through an async-group (`.bulk_group`, `cp.async`) — Stage that completes its use of CTA `c`: its write (`.write .copy`); `c`: the CTA of its shared source or destination - `cp.async.mbarrier.arrive` — Stage that completes its use of CTA `c`: its arrive-on (`.arriveOn`, a performed stage that updates the mbarrier, as in the row above) - CLC request — Stage that completes its use of CTA `c`: its notification at `c` (`.notify (.cta c)`); `c`: each target CTA - `tcgen05.mma`, `tcgen05.cp` — Stage that completes its use of CTA `c`: its completion (`.mmaDone`); `c`: the CTAs holding its operands (`lowCta`, `highCta`; the copy's CTA) - `tcgen05.commit` — Stage that completes its use of CTA `c`: its arrival at rank `r` (`.tcNotify r`); `c`: the target mbarrier's CTA The completing stage of an asynchronous operation comes after its other stages in `StageOrder`, so when it is finished every performed stage of the operation is; a stage that never occurs (an out-of-bounds read of a tensor store) is no access. "Before" in §2.2.2 is read as one of two orders of issue/completion nodes, each acyclic in every consistent execution, and never joined with each other (`LifetimeOrder`): - base causality, a `stageCausality` path: program order and synchronizes-with between thread instructions (`baseCausality`, §8.9.5), the release complete-tx of a copy observed by an acquire wait, and the stages of one asynchronous operation. It has no cycle by ObjectCoherent. - dependency, a path of `DepStep` together with the order of one object of `OrderObject.Enabling`: a later instruction reached only because a spinning wait succeeded or a blocking instruction returned, a stage that exists only because its operation was issued or its previous stage completed, a return that needed the updates or participants it observed, and the atomic order of that one object. It has no cycle by `DependencyOk.acyclic` (EXT-ENABLES-OBJECT).

</details>

## The memory layer against PTX §8.9

This section maps the memory layer of Core onto §8.9 (Ordering of memory operations) of PTX ISA
9.5, clause by clause. The first table takes the definitions of base causality order and causality
order in §8.9.5 and the relations of §8.9.1 to §8.9.7 that they use. For each clause it gives the
Core definitions that implement it, the rule that states it, and the direction of the
correspondence with one sentence that explains it. A row whose Core column says none is a clause
that Core leaves out, and its direction says why. The last row of the first table is the No Thin
Air axiom of §8.10.4. The second table lists the orders of Core that no clause of §8.9 states,
each with the rule or EXT note that states its reading. Quotes are verbatim from PTX ISA 9.5,
including the spaces that the manual's text places before punctuation.

The direction labels are those of the rules of Core. In this section `equal` means that Core
follows the clause. `stricter` means that Core gives fewer orders than the clause or leaves an
axiom out, so that its race check reports at least the races of the text and its consistent
executions include at least the executions that the text allows. `reading` means that Core relies
on an interpretation of the text, which its rule or EXT note states.

### Clauses of §8.9 and §8.10.4

| Clause of PTX ISA 9.5 | Core definitions | Rule | Direction |
| --- | --- | --- | --- |
| §8.9.1 (program order): "It is a transitive relation that forms a total order over the operations performed by the thread, but does not relate operations from different threads." | `Core/Memory/Order.lean`: [`po`](../../Core/Memory/Order.lean#L76-L79), [`TraceBefore`](../../Core/Memory/Order.lean#L54-L56), [`SameAccess`](../../Core/Memory/Order.lean#L67-L71) | [MEM-PROGRAM-ORDER](#mem-program-order) | `reading`: `po` is the order of one thread's trace, except that the element operations of one vector access are unordered among themselves, as §8.2.4 models a vector access ([EXT-VECTOR-ELEM](threads.md#ext-vector-elem)). |
| §8.9.1.1 (asynchronous operations): "These asynchronous operations are ordered after prior instructions in the same thread (except in the case of wgmma.mma_async ), but they are not part of the program order for that thread." | `Core/Memory/Order.lean`: [`modelCausality`](../../Core/Memory/Order.lean#L588-L605), [`GenericCopy`](../../Core/Memory/Order.lean#L410-L413), [`ProxyBefore`](../../Core/Memory/Order.lean#L446-L456) | [MEM-MODEL-CAUSALITY](#mem-model-causality) | `stricter`: the accesses of an asynchronous operation are not events of the thread's trace, so they are outside `po` and `baseCausality`; `modelCausality` orders them after an earlier access of the issuing thread through `baseCausality` to the issue only for the operations performed in the generic proxy (`cp.async`, `st.async`, `red.async`), and through a `fence.proxy.async` for the operations performed in the async proxy. `wgmma.mma_async` is not modeled. |
| §8.9.1.1: "the loads and stores performed as part of a cp.async are ordered with respect to each other" | `Core/Assembly/Waiting.lean`: [`StageEdge`](../../Core/Assembly/Waiting.lean#L79-L109), [`StageOrder`](../../Core/Assembly/Waiting.lean#L111-L118) | [DEP-ASYNC-STAGE-ORDER](correctness.md#dep-async-stage-order) | `stricter`: the read stage of a `cp.async` precedes its write stage in `stageCausality`, which the object-order axioms use, but `modelCausality`, which the race check and the read axioms use, does not contain this order. |
| §8.9.1.1: "but not to those of any other cp.async instructions initiated by the same thread, nor any other instruction subsequently issued by the thread with the exception of cp.async.commit_group or cp.async.mbarrier.arrive" | `Core/Memory/Order.lean`: [`modelCausality`](../../Core/Memory/Order.lean#L588-L605), [`AsyncFinished`](../../Core/Memory/Order.lean#L242-L252), [`AsyncChain`](../../Core/Memory/Order.lean#L490-L498) | [MEM-OBSERVED-COMPLETION](mbarrier.md#mem-observed-completion) | `stricter`: a later instruction of the thread, or a later `cp.async`, is ordered after a `cp.async` only through a wait that observes it, a `cp.async.wait_group` or `cp.async.wait_all` that covers its group or an acquire wait that observes the arrive-on of a `cp.async.mbarrier.arrive` that tracks it; `cp.async.commit_group` alone orders nothing. |
| §8.9.1.1: "The asynchronous mbarrier arrive-on operation performed by a cp.async.mbarrier.arrive instruction is ordered with respect to the memory operations performed by all prior cp.async operations initiated by the same thread, but not to those of any other instruction issued by the thread." | `Core/Assembly/Waiting.lean`: [`StageEdge`](../../Core/Assembly/Waiting.lean#L79-L109); `Core/MBarrier/AsyncMBarrier.lean`: [`AsyncCopy.TracksCpAsync`](../../Core/MBarrier/AsyncMBarrier.lean#L133-L137), [`AsyncCopy.AsyncObserved`](../../Core/MBarrier/AsyncMBarrier.lean#L245-L248); `Core/Memory/Order.lean`: [`AsyncFinished`](../../Core/Memory/Order.lean#L242-L252) | [DEP-ASYNC-STAGE-ORDER](correctness.md#dep-async-stage-order), [MEM-OBSERVED-COMPLETION](mbarrier.md#mem-observed-completion) | `stricter`: the write of each tracked `cp.async` precedes the arrive-on, and the order reaches an access of another instruction only through an acquire wait that observes the arrive-on with a scope that meets the arrive-on's, which the text does not require. |
| §8.9.1.1: "The implicit mbarrier complete-tx operation that is part of all variants of cp.async.bulk and cp.reduce.async.bulk instructions is ordered only with respect to the memory operations performed by the same asynchronous instruction, and in particular it does not transitively establish ordering with respect to prior instructions from the issuing thread." | `Core/Assembly/WaitOrder.lean`: [`stageCausality`](../../Core/Assembly/WaitOrder.lean#L314-L323), [`CopyReleaseSync`](../../Core/Assembly/WaitOrder.lean#L307-L312); `Core/Memory/Order.lean`: [`AsyncFinished`](../../Core/Memory/Order.lean#L242-L252) | [MEM-OBJECT-ORDER-CAUSALITY](mbarrier.md#mem-object-order-causality), [MEM-OBSERVED-COMPLETION](mbarrier.md#mem-observed-completion) | `equal`: `stageCausality` has no edge from the issuing instruction to the stages of its operation (`IssueStage` is not one of its edges), and a wait that observes the complete-tx orders only the accesses of the same copy. |
| §8.9.2 (observation order): "A write W precedes a read R in observation order if: R and W are morally strong and R reads the value written by W" | `Core/Memory/Acquire.lean`: [`synchronizesWith`](../../Core/Memory/Acquire.lean#L149-L158), [`FenceSync`](../../Core/Memory/Acquire.lean#L193-L204); `Core/Data/Types.lean`: [`Execution.rf`](../../Core/Data/Types.lean#L326-L365) | [MEM-RELEASE-ACQUIRE](#mem-release-acquire) | `stricter`: Core has no separate observation order; the clause is used only inside the synchronization of a release pattern with an acquire pattern, where the read must read every byte of the same nonempty footprint from the pattern's write and the scopes of the two must include each other's thread. |
| §8.9.2: "For some atomic operation Z, W precedes Z and Z precedes R in observation order" | none | [MEM-RELEASE-ACQUIRE](#mem-release-acquire) | `stricter`: a chain of atomic read-modify-write operations between the release pattern's write and the acquire pattern's read gives no synchronization. |
| §8.9.3 (Fence-SC order): "The Fence-SC order is an acyclic partial order, determined at runtime, that relates every pair of morally strong fence.sc operations." | `Core/Data/Types.lean`: [`Execution.fenceSC`](../../Core/Data/Types.lean#L326-L365); `Core/Memory/Acquire.lean`: [`ScStrong`](../../Core/Memory/Acquire.lean#L121-L125), [`FenceScOk`](../../Core/Memory/Acquire.lean#L132-L137) | [MEM-FENCE-SC](#mem-fence-sc) | `reading`: the order is part of the execution, and `FenceScOk` makes it acyclic and total on morally strong `fence.sc` and requires it to contain `baseCausality` between them, where §8.10.2 requires it to contain causality order, so Core admits more Fence-SC orders than the text. |
| §8.9.4 (memory synchronization): "A fence.sc operation X synchronizes with a fence.sc operation Y if X precedes Y in the Fence-SC order." | `Core/Memory/Acquire.lean`: [`FenceScSync`](../../Core/Memory/Acquire.lean#L127-L130), [`FenceSync`](../../Core/Memory/Acquire.lean#L193-L204) | [MEM-FENCE-SC](#mem-fence-sc) | `equal`: `FenceScSync` is this edge between two morally strong `fence.sc`, and `FenceSync` adds it to `baseCausality`. |
| §8.9.4: "A bar{.cta}.sync or bar{.cta}.red or bar{.cta}.arrive operation synchronizes with a bar{.cta}.sync or bar{.cta}.red operation executed on the same barrier." | `Core/Sync/CtaBarrierExecution.lean`: [`CtaBarSync`](../../Core/Sync/CtaBarrierExecution.lean#L104-L109), [`CtaBarArrivalK`](../../Core/Sync/CtaBarrierExecution.lean#L84-L90), [`CtaBarK`](../../Core/Sync/CtaBarrierExecution.lean#L92-L98) | [OBJ-CTA-BARRIER-SYNC](barriers.md#obj-cta-barrier-sync) | `stricter`: `CtaBarSync` is this edge from a `bar.sync` or `bar.arrive` to a `bar.sync` of the same generation of the same barrier, but `bar.red` is decoded without a Core rule and gives no edge. |
| §8.9.4: "A barrier.cluster.arrive operation synchronizes with a barrier.cluster.wait operation." | `Core/Sync/ClusterBarrierExecution.lean`: [`ClusterSync`](../../Core/Sync/ClusterBarrierExecution.lean#L79-L85); `Core/Sync/ClusterBarrierHistory.lean`: [`ClusterBarrier.Synchronizes`](../../Core/Sync/ClusterBarrierHistory.lean#L106-L110) | [OBJ-CLUSTER-BARRIER-SYNC](barriers.md#obj-cluster-barrier-sync) | `stricter`: only a release arrival gives the edge, because §9.7.15.3 says "The optional .relaxed qualifier on barrier.cluster.arrive specifies that there are no memory ordering and visibility guarantees provided for the memory accesses performed prior to barrier.cluster.arrive". |
| §8.9.4: "A release pattern X synchronizes with an acquire pattern Y, if a write operation in X precedes a read operation in Y in observation order , and the first operation in X and the last operation in Y are morally strong ." | `Core/Memory/Acquire.lean`: [`synchronizesWith`](../../Core/Memory/Acquire.lean#L149-L158), [`FenceSync`](../../Core/Memory/Acquire.lean#L193-L204), [`ReleaseHead`](../../Core/Memory/Acquire.lean#L174-L179), [`AcquireTail`](../../Core/Memory/Acquire.lean#L181-L186), [`StrongRead`](../../Core/Memory/Acquire.lean#L188-L191) | [MEM-RELEASE-ACQUIRE](#mem-release-acquire) | `stricter`: the edge goes from the first instruction of the release pattern to the last instruction of the acquire pattern only when the acquire pattern's strong read reads every byte of the same footprint from the release pattern's strong write; a relaxed `atom` followed by an acquire fence and the patterns of asynchronous operations give no edge. |
| §8.9.4 release and acquire patterns, applied by §8.8 to "mbarrier.arrive.release [M];" and "mbarrier.test_wait.acquire [M];" | `Core/Sync/Barrier.lean`: [`MSync`](../../Core/Sync/Barrier.lean#L179-L188), [`MbarRelease`](../../Core/Sync/Barrier.lean#L170-L172), [`ScopesMeet`](../../Core/Sync/Barrier.lean#L174-L177); `Core/Assembly/WaitOrder.lean`: [`CopyReleaseSync`](../../Core/Assembly/WaitOrder.lean#L307-L312) | [MEM-MBAR-SYNCHRONIZES](mbarrier.md#mem-mbar-synchronizes), [MEM-OBJECT-ORDER-CAUSALITY](mbarrier.md#mem-object-order-causality) | `reading`: §8.4 lists no mbarrier instruction as a read or a write, so the observation order that §8.9.4 requires does not apply as written; Core takes an acquire wait that observes the phase completed by a release arrival, or by a copy's complete-tx, as the observation, with scopes that include each other's thread ([EXT-OBJECT-ORDER](mbarrier.md#ext-object-order)). |
| §8.9.4: "A synchronizes relation can also be established by certain CUDA APIs." | none | [MEM-BASE-CAUSALITY](#mem-base-causality) | `stricter`: Core models the threads of one launch and no CUDA API operation; the API edges other than the start and the end of the kernel (the next two rows) are left out. |
| §8.9.4: "Start of a CUDA kernel synchronizes with start of all threads in the kernel." | `Core/Data/Value.lean`: [`Mem0`](../../Core/Data/Value.lean#L495-L498); `Core/Memory/Read.lean`: [`RfWf`](../../Core/Memory/Read.lean#L42-L50) | [MEM-READS-FROM](#mem-reads-from), [EXT-LAUNCH](correctness.md#ext-launch) | `reading`: the writes before the launch are the launch content `Mem0`, which a read takes from the initial write W0, and [EXT-LAUNCH](correctness.md#ext-launch) states that the launch provides this content. |
| §8.9.4: "End of all threads in a kernel synchronize with end of the kernel." | `Core/Assembly/Correctness.lean`: [`FinalMem`](../../Core/Assembly/Correctness.lean#L190-L191), [`IsFinal`](../../Core/Assembly/Correctness.lean#L239-L249) | [CORRECT-FINAL](correctness.md#correct-final), [EXT-LAUNCH](correctness.md#ext-launch) | `reading`: the memory after the kernel follows every event of the kernel, including asynchronous writes that complete after the last thread exits, which the text does not name. |
| §8.9.4: "In addition to establishing a synchronizes relation, the CUDA API synchronization mechanisms above also participate in proxy-preserved base causality order except for the tensormap-proxy which is not acquired from generic-proxy at CUDA Kernel start and must therefore be acquired explicitly using fence.proxy.tensormap::generic.acquire when needed." | `Core/Data/Value.lean`: [`Launch.tensorMaps`](../../Core/Data/Value.lean#L399-L448) | [THREAD-FENCE](threads.md#thread-fence), [EXT-LAUNCH](correctness.md#ext-launch) | `reading`: a tensor-map read reads a host-created map of `Launch.tensorMaps`, which [EXT-LAUNCH](correctness.md#ext-launch) requires to stay unchanged while the kernel runs, and the tensormap proxy fences order nothing in Core. |
| §8.9.5 (base causality order): "An operation X precedes an operation Y in base causality order if: X precedes Y in program order" | `Core/Memory/Order.lean`: [`baseCausality`](../../Core/Memory/Order.lean#L128-L135), [`po`](../../Core/Memory/Order.lean#L76-L79) | [MEM-BASE-CAUSALITY](#mem-base-causality) | `equal`: `po` is a base edge of `baseCausality`. |
| §8.9.5: "X synchronizes with Y" | `Core/Memory/Order.lean`: [`baseCausality`](../../Core/Memory/Order.lean#L128-L135); `Core/Sync/CtaBarrierExecution.lean`: [`CtaBarSync`](../../Core/Sync/CtaBarrierExecution.lean#L104-L109); `Core/Sync/Barrier.lean`: [`MSync`](../../Core/Sync/Barrier.lean#L179-L188); `Core/Sync/ClusterBarrierExecution.lean`: [`ClusterSync`](../../Core/Sync/ClusterBarrierExecution.lean#L79-L85); `Core/Sync/WarpBarrier.lean`: [`WarpBarSync`](../../Core/Sync/WarpBarrier.lean#L75-L79); `Core/Memory/Acquire.lean`: [`synchronizesWith`](../../Core/Memory/Acquire.lean#L149-L158), [`FenceSync`](../../Core/Memory/Acquire.lean#L193-L204) | [MEM-BASE-CAUSALITY](#mem-base-causality) | `reading`: the synchronizes-with edges are those of the §8.9.4 rows above, with their restrictions, and `WarpBarSync`, which no clause of §8.9.4 states (second table). |
| §8.9.5: "For some operation Z, X precedes Z in program order and Z precedes Y in base causality order" | `Core/Memory/Order.lean`: [`baseCausality`](../../Core/Memory/Order.lean#L128-L135) | [MEM-BASE-CAUSALITY](#mem-base-causality) | `equal`: `baseCausality` is the transitive closure of its base edges, which contains this composition. |
| §8.9.5: "X precedes Z in base causality order and Z precedes Y in program order" | `Core/Memory/Order.lean`: [`baseCausality`](../../Core/Memory/Order.lean#L128-L135) | [MEM-BASE-CAUSALITY](#mem-base-causality) | `equal`: the transitive closure contains this composition. |
| §8.9.5: "X precedes Z in base causality order and Z precedes Y in base causality order" | `Core/Memory/Order.lean`: [`baseCausality`](../../Core/Memory/Order.lean#L128-L135) | [MEM-BASE-CAUSALITY](#mem-base-causality) | `equal`: the transitive closure is transitive. |
| §8.9.5 (proxy-preserved base causality order): "X and Y are performed to the same address, using the generic proxy" | `Core/Memory/Order.lean`: [`modelCausality`](../../Core/Memory/Order.lean#L588-L605) | [MEM-MODEL-CAUSALITY](#mem-model-causality) | `equal`: between two thread accesses, which use the generic proxy, `modelCausality` is `baseCausality`, and Core applies it only at a byte that both accesses touch. |
| §8.9.5: "X and Y are performed to the same address, using the same proxy , and by the same thread block" | `Core/Memory/Order.lean`: [`modelCausality`](../../Core/Memory/Order.lean#L588-L605), [`AsyncChain`](../../Core/Memory/Order.lean#L490-L498), [`AsyncBefore`](../../Core/Memory/Order.lean#L482-L488), [`AsyncCovers`](../../Core/Memory/Order.lean#L424-L427) | [MEM-MODEL-CAUSALITY](#mem-model-causality) | `reading`: the accesses of asynchronous operations are not in `baseCausality`; for two of them issued by threads of one CTA, Core reads base causality order as a chain of observed completions at the byte, each followed by the issue of the next operation (`AsyncBefore`). |
| §8.9.5: "X and Y are aliases and there is an alias proxy fence along the base causality path from X to Y." | none | [THREAD-FENCE](threads.md#thread-fence), [EXT-LAUNCH](correctness.md#ext-launch) | `stricter`: [EXT-LAUNCH](correctness.md#ext-launch) requires a launch without aliases, so every byte has one address, and the alias proxy fence creates no order. |
| §8.9.5 (causality order): "An operation X precedes an operation Y in causality order if: X precedes Y in proxy-preserved base causality order" | `Core/Memory/Order.lean`: [`modelCausality`](../../Core/Memory/Order.lean#L588-L605); `Core/Memory/Read.lean`: [`NoFuture`](../../Core/Memory/Read.lean#L82-L86), [`Hidden`](../../Core/Memory/Read.lean#L88-L96); `Core/Assembly/Safety.lean`: [`Race`](../../Core/Assembly/Safety.lean#L214-L220) | [MEM-MODEL-CAUSALITY](#mem-model-causality), [MEM-READ-AXIOMS](#mem-read-axioms), [ERR-DATA-RACE](#err-data-race) | `reading`: `modelCausality` is the causality order of Core at one byte; its case between two thread accesses follows the text, and its cases with an asynchronous access are the readings of the rows above and of the second table. |
| §8.9.5: "For some operation Z, X precedes Z in observation order, and Z precedes Y in proxy-preserved base causality order ." | none | [MEM-MODEL-CAUSALITY](#mem-model-causality) | `stricter`: `modelCausality` has no observation-order prefix, so a write that a morally strong read reads is ordered before the reader's later accesses only when the two synchronize; with fewer orders the race check reports more and the read axioms exclude fewer executions. |
| §8.9.6 (coherence order): "There exists a partial transitive order that relates overlapping write operations, determined at runtime, called the coherence order" and "Two overlapping write operations are related in coherence order if they are morally strong or if they are related in causality order ." | `Core/Assembly/Correctness.lean`: [`CoStep`](../../Core/Assembly/Correctness.lean#L193-L202), [`CoBefore`](../../Core/Assembly/Correctness.lean#L219-L221), [`CoOrder`](../../Core/Assembly/Correctness.lean#L223-L231) | [CORRECT-FINAL](correctness.md#correct-final), [MEM-READ-AXIOMS](#mem-read-axioms) | `stricter`: Core builds a coherence order only for the memory after the kernel, and its read axiom `Hidden` uses `modelCausality` where §8.10.6 uses coherence order, which excludes fewer read sources. |
| §8.9.6: "Two overlapping writes are unrelated in coherence order if they are in a data-race , which gives rise to the partial nature of coherence order ." | `Core/Assembly/Safety.lean`: [`Race`](../../Core/Assembly/Safety.lean#L214-L220), [`SameValueWrites`](../../Core/Assembly/Safety.lean#L207-L212); `Core/Assembly/Correctness.lean`: [`CoOrder`](../../Core/Assembly/Correctness.lean#L223-L231) | [ERR-DATA-RACE](#err-data-race), [CORRECT-FINAL](correctness.md#correct-final) | `stricter`: Core rejects every execution with a data race, except for two writes of the same bytes with the same value, which `CoOrder` leaves unordered. |
| §8.9.7 (communication order): "A write W precedes an overlapping read R in communication order if R returns the value of any byte that was written by W." | `Core/Data/Types.lean`: [`Execution.rf`](../../Core/Data/Types.lean#L326-L365); `Core/Memory/Read.lean`: [`RfWf`](../../Core/Memory/Read.lean#L42-L50) | [MEM-READS-FROM](#mem-reads-from) | `equal`: `Execution.rf` gives the write that each read byte comes from, and `RfWf` requires the byte to have that write's value. |
| §8.9.7: "A write W precedes a write W’ in communication order if W precedes W’ in coherence order ." | `Core/Assembly/Correctness.lean`: [`CoBefore`](../../Core/Assembly/Correctness.lean#L219-L221), [`CoOrder`](../../Core/Assembly/Correctness.lean#L223-L231) | [CORRECT-FINAL](correctness.md#correct-final) | `stricter`: as for coherence order, Core uses this order only for the memory after the kernel. |
| §8.9.7: "A read R precedes an overlapping write W in communication order if, for any byte accessed by both R and W, R returns the value written by a write W’ that precedes W in coherence order ." | none | [CORRECT-FINAL](correctness.md#correct-final) | `stricter`: Core has no relation from a read to a later write; the axiom of §8.10.5 that uses this relation is not stated, and `NoFuture` and `Hidden` exclude its cycles only where they follow from causality, so Core admits more executions than the text. |
| §8.10.4 (No Thin Air): "Values may not appear “out of thin air”: an execution cannot speculatively produce a value in such a way that the speculation becomes self-satisfying through chains of instruction dependencies and inter-thread communication." | none | none | `stricter`: Core has no No Thin Air axiom, so its consistent executions include executions whose values justify themselves in this way, and the safety, progress and result obligations are proved over this larger set. No test of this repository examines the gap. |

### Orders of Core that no clause of §8.9 states

| Order | Core definitions | Rule or reading | Direction |
| --- | --- | --- | --- |
| The allocating warp's weak result store before its same-byte readback | `Core/Tmem/AllocResult.lean`: [`Tmem.Pair.AllocResultBefore`](../../Core/Tmem/AllocResult.lean#L77-L82); `Core/Memory/Order.lean`: [`modelCausality`](../../Core/Memory/Order.lean#L588-L605) | [EXT-TMEM-ALLOC-RESULT-ORDER](tmem.md#ext-tmem-alloc-result-order) | `reading`: a participating lane reads the shared result of its own collective instance. The edge is confined to that byte. |
| Synchronization through `bar.warp.sync`, read from §9.7.15.2: "bar.warp.sync also guarantee memory ordering among threads participating in barrier." | `Core/Sync/WarpBarrier.lean`: [`WarpBarSync`](../../Core/Sync/WarpBarrier.lean#L75-L79), [`WarpBarEdge`](../../Core/Sync/WarpBarrier.lean#L62-L64) | [DEP-WARP-BARRIER](barriers.md#dep-warp-barrier), [MEM-BASE-CAUSALITY](#mem-base-causality) | `reading`: `WarpBarSync` is a synchronizes-with edge of `baseCausality` from the accesses of a participant before the barrier to the accesses of the participants after it. No EXT note states this reading; the direction of [DEP-WARP-BARRIER](barriers.md#dep-warp-barrier) and the review notes of [MEM-BASE-CAUSALITY](#mem-base-causality) do. |
| A generic access before an async-proxy access through `fence.proxy.async`, from §9.7.15.4: "membar.proxy and fence.proxy instructions establish an ordering between memory accesses that may happen through different proxies ." "A uni-directional proxy ordering from the from-proxykind to the to-proxykind establishes ordering between a prior memory access performed via the from-proxykind and a subsequent memory access performed via the to-proxykind ." "Value .async of the .proxykind qualifier specifies that the memory ordering is established between the async proxy and the generic proxy. The memory ordering is limited only to operations performed on objects in the state space specified." "Their cross-proxy synchronizing effect composes with other forms of synchronization according to the rules of the Memory Consistency Model ." | `Core/Memory/Order.lean`: [`ProxyBefore`](../../Core/Memory/Order.lean#L446-L456), [`ProxyFenceReach`](../../Core/Memory/Order.lean#L439-L444), [`AsyncFenceCovers`](../../Core/Memory/Order.lean#L429-L437) | [MEM-MODEL-CAUSALITY](#mem-model-causality) | `equal`: a prior thread access precedes the subsequent access of an asynchronous operation in the async proxy when a `fence.proxy.async` whose state space covers the byte lies between the access and the issue in `baseCausality` and reaches the issuing thread; the order is limited to the fence's state space and composes with other synchronization through `baseCausality`. §8.9.5 has no clause for two accesses through different proxies, so the order is stated by §9.7.15.4. |
| An asynchronous access before the accesses that follow an observation of its completion, read from §9.7.10.28.1.2: "When the current phase of the mbarrier object is complete, it implies that all asynchronous operations tracked by this phase are complete, and all threads participating in that mbarrier object can access the result of the asynchronous operations." | `Core/Memory/Order.lean`: [`AsyncFinished`](../../Core/Memory/Order.lean#L242-L252), [`CompletionBefore`](../../Core/Memory/Order.lean#L512-L517); `Core/MBarrier/AsyncMBarrier.lean`: [`AsyncCopy.AsyncObserved`](../../Core/MBarrier/AsyncMBarrier.lean#L245-L248) | [MEM-OBSERVED-COMPLETION](mbarrier.md#mem-observed-completion), [EXT-READ-WAIT-ORDER](#ext-read-wait-order) | `reading`: an acquire wait that observes the operation's completion notification with meeting scopes, or a group wait that covers the operation, orders its accesses before the accesses that the wait precedes in `baseCausality`; the shared-memory reads of `tcgen05.mma` and `tcgen05.cp` also need a `fence.proxy.async` after the wait, and a `.read` bulk-group wait orders the source reads of a tensor store without one ([EXT-READ-WAIT-ORDER](#ext-read-wait-order)). |
| An asynchronous access before a later asynchronous operation of the waiting thread, from §9.7.10.28.6.2: "The qualifier sync_restrict::proxy::async only orders async-proxy global and shared memory accesses before subsequent async-proxy accesses; not before subsequent generic-proxy accesses." | `Core/Memory/Order.lean`: [`AsyncOnlyFinished`](../../Core/Memory/Order.lean#L474-L480), [`AsyncBefore`](../../Core/Memory/Order.lean#L482-L488) | [MEM-MODEL-CAUSALITY](#mem-model-causality) | `stricter`: Core orders the covered operation's accesses only before the asynchronous operations that the waiting thread issues after the wait in program order. |
| Asynchronous accesses of the two CTAs of a `cta_group::2` pair | `Core/Memory/Order.lean`: [`PairAsync`](../../Core/Memory/Order.lean#L500-L504), [`PairTc`](../../Core/Memory/Order.lean#L506-L510) | [EXT-PAIR-ASYNC](#ext-pair-async) | `reading`: two async-proxy accesses to the shared memory of either CTA of a pair, issued by either CTA, count as performed by the same thread block when one of the two operations is a `cta_group::2` `tcgen05.mma` or `tcgen05.cp`. |
| The order of tcgen05 operations | `Core/Tc/TcFence.lean`: [`ExecOrder`](../../Core/Tc/TcFence.lean#L153-L157), [`MbarExec`](../../Core/Tc/TcFence.lean#L131-L136), [`TcMma.FenceOrder`](../../Core/Tc/TcFence.lean#L161-L163), [`TcMma.TcBefore`](../../Core/Tc/TcFence.lean#L165-L168); `Core/Tc/TcMmaLifetime.lean`: [`TcMma.DoneBefore`](../../Core/Tc/TcMmaLifetime.lean#L101-L106) | [DEP-TC-FENCE](mbarrier.md#dep-tc-fence), [EXT-TC-EXEC-ORDER](tcgen05.md#ext-tc-exec-order), [EXT-TCACQUIRE](tcgen05.md#ext-tcacquire) | `reading`: a tcgen05 operation precedes another in `baseCausality`, or through a `tcgen05.fence::before_thread_sync` and a `tcgen05.fence::after_thread_sync` joined by `baseCausality` or by one observed mbarrier arrival, relaxed or release; this order is separate from `modelCausality`. |
| The issue and completion points of instructions and asynchronous stages | `Core/Assembly/WaitOrder.lean`: [`stageCausality`](../../Core/Assembly/WaitOrder.lean#L314-L323), [`CopyReleaseSync`](../../Core/Assembly/WaitOrder.lean#L307-L312); `Core/Assembly/Waiting.lean`: [`StageOrder`](../../Core/Assembly/Waiting.lean#L111-L118) | [MEM-OBJECT-ORDER-CAUSALITY](mbarrier.md#mem-object-order-causality), [EXT-STAGE-ORDER](correctness.md#ext-stage-order) | `reading`: `stageCausality` extends `baseCausality` to the issue and completion points of thread instructions and asynchronous stages, with the stage order of one operation and a copy's release complete-tx to the successors of an acquire wait that observes it; the object-order and observation axioms use it, and the race check and the read axioms do not. |
| The order of the operations on one synchronization object | `Core/Assembly/WaitOrder.lean`: [`ObjectOrder`](../../Core/Assembly/WaitOrder.lean#L337-L353), [`SyncObjectOrder`](../../Core/Assembly/WaitOrder.lean#L368-L379), [`ObservationCausal`](../../Core/Assembly/WaitOrder.lean#L381-L384), [`ObjectCoherent`](../../Core/Assembly/WaitOrder.lean#L386-L389), [`AsyncObjectOrdered`](../../Core/Assembly/WaitOrder.lean#L391-L400) | [MEM-OBJECT-ORDER-CAUSALITY](mbarrier.md#mem-object-order-causality), [EXT-OBJECT-ORDER](mbarrier.md#ext-object-order), [EXT-ASYNC-OBJECT](mbarrier.md#ext-async-object) | `reading`: the operations on one mbarrier, CTA barrier, cluster barrier or Tensor Memory allocator take effect in one order whose synchronizing part never contradicts `stageCausality`, while §8.10.1 orders only overlapping writes. |
| The publication of an mbarrier initialization | `Core/MBarrier/InitPublication.lean`: [`InitFenceSync`](../../Core/MBarrier/InitPublication.lean#L106-L118), [`InitFenceOrdered`](../../Core/MBarrier/InitPublication.lean#L130-L135) | [OBJ-MBAR-INIT-PUBLICATION](mbarrier.md#obj-mbar-init-publication), [EXT-INIT-FENCE-ARRIVE](mbarrier.md#ext-init-fence-arrive) | `reading`: an `mbarrier.init` followed in its thread by `fence.mbarrier_init.release.cluster` and a cluster arrival, relaxed or release, is ordered before the cluster wait that observes the arrival; this order enters neither `baseCausality` nor `stageCausality`. |
