# mbarrier

How the model treats `mbarrier` objects: what each instruction does to an object, which executions are allowed, and what counts as an error. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [The object and its operations](#the-object-and-its-operations)
    - [`MBarrier.State`](#c-mbarrier-state)
    - [`MBarrier.Action`](#c-mbarrier-action)
    - [`MBarrier.Reply`](#c-mbarrier-reply)
    - [`MBarrier.Error`](#c-mbarrier-error)
    - [`MBarrier.limit`](#c-mbarrier-limit)
    - [`MBarrier.perform`](#c-mbarrier-perform)
  - [Events and executions](#events-and-executions)
    - [`Kind`](#c-kind)
    - [`Event`](#c-event)
    - [`Execution`](#c-execution)
    - [`MbarScope`](#c-mbarscope)
  - [Object histories](#object-histories)
    - [`MBarrier.Record`](#c-mbarrier-record)
    - [`MBarrier.CheckedLog`](#c-mbarrier-checkedlog)
    - [`MBarrier.SameLifetime`](#c-mbarrier-samelifetime)
    - [`MBarrier.UpdateBeforeWait`](#c-mbarrier-updatebeforewait)
    - [`MBarrier.InitBefore`](#c-mbarrier-initbefore)
    - [`MBarrier.Before`](#c-mbarrier-before)
  - [Observation](#observation)
    - [`AsyncCopy.WaitObserves`](#c-asynccopy-waitobserves)
    - [`AsyncCopy.AsyncObserved`](#c-asynccopy-asyncobserved)
    - [`MbarObserved`](#c-mbarobserved)
  - [Synchronization and ordering](#synchronization-and-ordering)
    - [`ScopesMeet`](#c-scopesmeet)
    - [`MSync`](#c-msync)
    - [`CopyReleaseSync`](#c-copyreleasesync)
    - [`MbarExec`](#c-mbarexec)
    - [`AsyncFinished`](#c-asyncfinished)
    - [`ObjectOrder`](#c-objectorder)
    - [`ObjectCoherent`](#c-objectcoherent)
    - [`AsyncObjectOrdered`](#c-asyncobjectordered)
  - [Initialization and safety](#initialization-and-safety)
    - [`InitPublished`](#c-initpublished)
    - [`ObjectPublished`](#c-objectpublished)
    - [`TmaUnsafe`](#c-tmaunsafe)
- [Rules](#rules)
  - [What an mbarrier instruction does](#what-an-mbarrier-instruction-does)
    - [mbarrier and bulk-copy instructions](#thread-tma) (`THREAD-TMA`)
    - [layout::v0 mbarrier object operations](#obj-mbar-state) (`OBJ-MBAR-STATE`)
  - [Which executions are allowed](#which-executions-are-allowed)
    - [object histories and phase identities](#obj-mbar-phases) (`OBJ-MBAR-PHASES`)
    - [checked operations of one object](#obj-mbar-history) (`OBJ-MBAR-HISTORY`)
    - [copy effects name actual issuing instructions](#obj-mbar-origin) (`OBJ-MBAR-ORIGIN`)
    - [a successful wait observes an update in its phase](#obj-mbar-observe) (`OBJ-MBAR-OBSERVE`)
    - [mbarrier release/acquire synchronization](#mem-mbar-synchronizes) (`MEM-MBAR-SYNCHRONIZES`)
    - [restricted publication of mbarrier initialization](#obj-mbar-init-publication) (`OBJ-MBAR-INIT-PUBLICATION`)
      - [a relaxed cluster arrival carries the init fence's release](#ext-init-fence-arrive) (`EXT-INIT-FENCE-ARRIVE`)
    - [memory-layer axioms over causality, observation and object order](#mem-object-order-causality) (`MEM-OBJECT-ORDER-CAUSALITY`)
      - [the operations on one synchronization object are totally ordered](#ext-object-order) (`EXT-OBJECT-ORDER`)
      - [an asynchronous update follows its issue in its object's order](#ext-async-object) (`EXT-ASYNC-OBJECT`)
      - [an event that exists because of a return is not placed before its witness](#ext-enables-object) (`EXT-ENABLES-OBJECT`)
    - [observation of a particular operation's completion](#mem-observed-completion) (`MEM-OBSERVED-COMPLETION`)
    - [tcgen05 fences composed with execution ordering](#dep-tc-fence) (`DEP-TC-FENCE`)
  - [What counts as an error](#what-counts-as-an-error)
    - [every mbarrier operation uses an initialized object](#err-mbar-uninitialized) (`ERR-MBAR-UNINITIALIZED`)
    - [object faults, object lifetimes and async lifetimes](#err-object-lifetime) (`ERR-OBJECT-LIFETIME`)
    - [the issuing CTA group exists](#err-tc-commit-group) (`ERR-TC-COMMIT-GROUP`)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### The object and its operations

The contents of one mbarrier object and the effect of each operation on it.

<a id="c-mbarrier-state"></a>
#### `MBarrier.State`

*structure*

The contents of a valid layout::v0 mbarrier object (§9.7.15.16.3): the current phase, the
expected arrival count, the pending arrival count, the tx-count, and whether the preceding
completed phase has been observed.

- `phase`: The number of the current phase. Initialization sets it to zero and each phase completion increments it; `try_wait.parity` tests its parity.
- `expected`: The expected arrival count that `mbarrier.init` sets. Each phase completion reloads the pending arrival count with it.
- `pending`: The pending arrival count: the number of arrivals the current phase still needs.
- `tx`: The tx-count of the current phase: the transaction bytes added by expect-tx operations minus the bytes signalled by complete-tx operations. It is negative when complete-tx operations have signalled more bytes than were expected so far.
- `observed`: Has the preceding completed phase been successfully observed? Initially true.

[Lean source: `Core/MBarrier/MBarrierObject.lean` L56-L74](../../Core/MBarrier/MBarrierObject.lean#L56-L74)

<a id="c-mbarrier-action"></a>
#### `MBarrier.Action`

*inductive*

An operation on an mbarrier object, as its history records it: an initialization, a
complete-tx, an arrival with optional expect-tx, a pending-count increment, a parity poll, or an
invalidation.

- `init`: `mbarrier.init` with expected arrival count `count`.
- `completeTx`: An asynchronous operation's complete-tx of `count` bytes.
- `arrive`: `count` arrivals after expecting `tx` transaction bytes (`arrive.expect_tx`).
- `increment`: The increment of the pending count by 1 that `cp.async.mbarrier.arrive` without `.noinc` performs before its asynchronous arrive-on.
- `pollParity`: A try_wait.parity observation: `false` may be returned without observing completion.
- `inval`: `mbarrier.inval`: the location no longer contains a valid object.

[Lean source: `Core/MBarrier/MBarrierObject.lean` L76-L93](../../Core/MBarrier/MBarrierObject.lean#L76-L93)

<a id="c-mbarrier-reply"></a>
#### `MBarrier.Reply`

*structure*

The reply of the object to one operation.

- `state`: The object state after the operation; `none` when the location then holds no valid object.
- `waited`: The result of a parity poll; absent for the other operations.
- `completed`: The completed phase actually observed; absent on an initial opposite-parity poll.

[Lean source: `Core/MBarrier/MBarrierObject.lean` L106-L115](../../Core/MBarrier/MBarrierObject.lean#L106-L115)

<a id="c-mbarrier-error"></a>
#### `MBarrier.Error`

*inductive*

An object fault, each of which the ISA makes undefined behaviour: an operation other than
`mbarrier.init` on a location without a valid object (`invalidObject`), `mbarrier.init` on a valid
object (`alreadyInitialized`), an arrival count or transaction operand out of range
(`countRange`), a tx-count that leaves its range (`transactionRange`), more arrivals than are
pending (`arrivalUnderflow`), and an arrival in a phase whose preceding completion no successful
poll observed (`precedingPhaseNotObserved`, §9.7.15.16.5.1).

- `invalidObject`
- `alreadyInitialized`
- `countRange`
- `transactionRange`
- `arrivalUnderflow`
- `precedingPhaseNotObserved`

[Lean source: `Core/MBarrier/MBarrierObject.lean` L95-L104](../../Core/MBarrier/MBarrierObject.lean#L95-L104)

<a id="c-mbarrier-limit"></a>
#### `MBarrier.limit`

*def*

The largest expected arrival count and the largest magnitude of the tx-count of a
layout::v0 object, 2^20 - 1 (§9.7.15.16.3).

[Lean source: `Core/MBarrier/MBarrierObject.lean` L117-L119](../../Core/MBarrier/MBarrierObject.lean#L117-L119)

<a id="c-mbarrier-perform"></a>
#### `MBarrier.perform`

*def*

The effect of one operation on the object at one location: from the state before it
(`none` when the location holds no valid object) to the reply, or to an object fault. An
arrival or complete-tx that leaves both the pending arrival count and the tx-count at zero
completes the phase (`advance`). A successful poll tests the parity of the phase before the
current one, which has completed; a poll may also fail when that phase has completed. An increment
raises the pending count by one and completes no phase.

[Lean source: `Core/MBarrier/MBarrierObject.lean` L133-L168](../../Core/MBarrier/MBarrierObject.lean#L133-L168)

### Events and executions

The events that mbarrier instructions produce and the parts of an execution that record them.

<a id="c-kind"></a>
#### `Kind`

*inductive*

The kind of an event: the effect of the instruction that performed it, together with the
values it returned. The mbarrier kinds are `mbInit`, `mbInval`, `arrive`, `wait` and
`fenceMbarInit`.

- `mbInit`: `mbarrier.init` of the mbarrier object at `m`, with its expected arrival count.
- `mbInval`: `mbarrier.inval` of the mbarrier object at `m`.
- `fenceMbarInit`: `fence.mbarrier_init.release.cluster`, which publishes the thread's prior `mbarrier.init` operations on `.shared::cta` objects (§9.7.15.4).
- `arrive`: `mbarrier.arrive{.expect_tx}`: `count` arrivals on `m` after expecting `tx` transaction bytes, with release (`release`) or relaxed semantics at `scope`. The defaults are the PTX defaults: one arrival, `.release`, `.cta`.
- `wait`: `mbarrier.try_wait.parity`: whether phase `parity` of `m` was found complete, with acquire (`acquire`) or relaxed semantics at `scope`; PTX default `.acquire.cta`.

[Lean source: `Core/Data/Types.lean` L200-L295](../../Core/Data/Types.lean#L200-L295)

<a id="c-event"></a>
#### `Event`

*structure*

One event of a thread trace: the source position of its instruction and its kind.

- `pc`: Source position of the instruction that performed it.
- `kind`

[Lean source: `Core/Data/Types.lean` L297-L301](../../Core/Data/Types.lean#L297-L301)

<a id="c-execution"></a>
#### `Execution`

*structure*

One candidate execution of a kernel (MEM-EXECUTION): the thread traces, reads-from, the
asynchronous effects, and the histories of the synchronization objects.

- `tr`: The finite event trace of each thread, indexed by the thread's id in the grid.
- `async`: Independent asynchronous accesses and completion notifications.
- `objects`: One atomic operation history per mbarrier address, including failed polls.

[Lean source: `Core/Data/Types.lean` L326-L365](../../Core/Data/Types.lean#L326-L365)

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

### Object histories

The recorded operations of one mbarrier address, their phases and lifetimes.

<a id="c-mbarrier-record"></a>
#### `MBarrier.Record`

*structure*

One entry of an object's history: the identity of the operation (a thread event or an
asynchronous notification), the operation, the object's reply, and the object fault it caused,
if any.

- `id`
- `action`
- `reply`
- `fault`: Object UB is recorded, not removed from the set of executions.

[Lean source: `Core/MBarrier/MBarrierHistory.lean` L39-L48](../../Core/MBarrier/MBarrierHistory.lean#L39-L48)

<a id="c-mbarrier-checkedlog"></a>
#### `MBarrier.CheckedLog`

*def*

A valid history of one address: the operation identities are distinct, and the records form a
sequence of valid steps that starts at a location without a valid object.

[Lean source: `Core/MBarrier/MBarrierHistory.lean` L110-L113](../../Core/MBarrier/MBarrierHistory.lean#L110-L113)

<a id="c-mbarrier-samelifetime"></a>
#### `MBarrier.SameLifetime`

*def*

No invalidation lies strictly between positions `i` and `j`.

[Lean source: `Core/MBarrier/MBarrierHistory.lean` L63-L65](../../Core/MBarrier/MBarrierHistory.lean#L63-L65)

<a id="c-mbarrier-updatebeforewait"></a>
#### `MBarrier.UpdateBeforeWait`

*def*

A specific counter update belongs to the phase actually observed by this wait.

[Lean source: `Core/MBarrier/MBarrierHistory.lean` L115-L120](../../Core/MBarrier/MBarrierHistory.lean#L115-L120)

<a id="c-mbarrier-initbefore"></a>
#### `MBarrier.InitBefore`

*def*

`init` is the successful initialization of the object lifetime that `operation` belongs
to: it precedes the operation and no invalidation lies between them.

[Lean source: `Core/MBarrier/MBarrierHistory.lean` L122-L127](../../Core/MBarrier/MBarrierHistory.lean#L122-L127)

<a id="c-mbarrier-before"></a>
#### `MBarrier.Before`

*def*

Atomic object order, separate from memory visibility.

[Lean source: `Core/MBarrier/MBarrierHistory.lean` L129-L131](../../Core/MBarrier/MBarrierHistory.lean#L129-L131)

### Observation

Which updates a successful wait observes.

<a id="c-asynccopy-waitobserves"></a>
#### `AsyncCopy.WaitObserves`

*def*

The successful wait `w` on `m`, with acquire flag `acq` and scope `ws`, observed the update
`x`: the record of `x` belongs to the phase whose completion `w` observed.

[Lean source: `Core/MBarrier/AsyncMBarrier.lean` L212-L217](../../Core/MBarrier/AsyncMBarrier.lean#L212-L217)

<a id="c-asynccopy-asyncobserved"></a>
#### `AsyncCopy.AsyncObserved`

*def*

The successful wait `w` observed the notification of part `p` of the operation `i`.

[Lean source: `Core/MBarrier/AsyncMBarrier.lean` L245-L248](../../Core/MBarrier/AsyncMBarrier.lean#L245-L248)

<a id="c-mbarobserved"></a>
#### `MbarObserved`

*def*

The present counter update `x` belongs to the phase whose completion the successful
wait `w` observed (`AsyncCopy.WaitObserves`, any qualifiers). Relaxed and release updates
alike; the memory layer uses it only through `SyncObserved`.

[Lean source: `Core/Assembly/WaitOrder.lean` L284-L289](../../Core/Assembly/WaitOrder.lean#L284-L289)

### Synchronization and ordering

The synchronization that mbarrier operations create and the order constraints on each object.

<a id="c-scopesmeet"></a>
#### `ScopesMeet`

*def*

An update by thread `g` with scope `us` and a wait by thread `h` with scope `ws` are morally
strong relative to each other: each scope includes the other thread (§8.7).

[Lean source: `Core/Sync/Barrier.lean` L174-L177](../../Core/Sync/Barrier.lean#L174-L177)

<a id="c-msync"></a>
#### `MSync`

*def*

Mbarrier synchronization from `e` to `f` (§8.9.4): a release arrival `x` at or after `e` in
`e`'s thread is observed by a successful acquire wait `w`, the scope of each of `x` and `w`
includes the other's thread, and `f` follows `w` in `w`'s thread.

[Lean source: `Core/Sync/Barrier.lean` L179-L188](../../Core/Sync/Barrier.lean#L179-L188)

<a id="c-copyreleasesync"></a>
#### `CopyReleaseSync`

*def*

The release complete-tx (`.cluster` scope) of a tensor or bulk copy synchronizes with an
acquire wait observing it whose scope includes the issuing thread, ordering it before the
wait's program-order successor `f`.

[Lean source: `Core/Assembly/WaitOrder.lean` L307-L312](../../Core/Assembly/WaitOrder.lean#L307-L312)

<a id="c-mbarexec"></a>
#### `MbarExec`

*def*

A morally strong mbarrier arrival `x`, relaxed or release, counted in the phase that the
successful wait `w`, relaxed or acquire, observed.

[Lean source: `Core/Tc/TcFence.lean` L131-L136](../../Core/Tc/TcFence.lean#L131-L136)

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

<a id="c-objectorder"></a>
#### `ObjectOrder`

*def*

The recorded operation order of one object.

[Lean source: `Core/Assembly/WaitOrder.lean` L337-L353](../../Core/Assembly/WaitOrder.lean#L337-L353)

<a id="c-objectcoherent"></a>
#### `ObjectCoherent`

*def*

Causality together with the synchronizing part of the order of any single object has no
cycle.

[Lean source: `Core/Assembly/WaitOrder.lean` L386-L389](../../Core/Assembly/WaitOrder.lean#L386-L389)

<a id="c-asyncobjectordered"></a>
#### `AsyncObjectOrdered`

*def*

EXT-ASYNC-OBJECT: an asynchronous update `.async i p` on object `m` is not before, in `m`'s
history, an earlier operation of the issuing thread, and not before the object's initialization
or invalidation or an acquire wait observing the update when that operation causally precedes
the issue of `i`.

[Lean source: `Core/Assembly/WaitOrder.lean` L391-L400](../../Core/Assembly/WaitOrder.lean#L391-L400)

### Initialization and safety

When an initialization is published to a use, and which executions are unsafe.

<a id="c-initpublished"></a>
#### `InitPublished`

*def*

The initialization `init` of `m` is published to `user`: it happens before `user`, or it is
published through the init fence and a cluster barrier (`InitFencePublished`).

[Lean source: `Core/MBarrier/InitPublication.lean` L125-L128](../../Core/MBarrier/InitPublication.lean#L125-L128)

<a id="c-objectpublished"></a>
#### `ObjectPublished`

*def*

The operation lies inside its object lifetime. An initialization happens after every
earlier invalidation; another operation is ordered after the initialization of its lifetime
and before that lifetime's invalidation, if any.
Bulk-copy completion accesses the mbarrier through the generic proxy.

[Lean source: `Core/Assembly/Safety.lean` L308-L320](../../Core/Assembly/Safety.lean#L308-L320)

<a id="c-tmaunsafe"></a>
#### `TmaUnsafe`

*def*

The mbarrier and bulk-copy safety check. It fails when an object record faults, a record lies
outside its object lifetime (`ObjectPublished`), a memory access to an object's bytes is ordered
neither before its initialization nor after the invalidation that ends that lifetime, two
`cp.async` operations of one group copy to an overlapping location (`CpAsyncOverlap`), or the
destination range of a `.cp_mask` copy covers an unallocated byte (`MaskedRangeUnalloc`).

[Lean source: `Core/Assembly/Safety.lean` L322-L334](../../Core/Assembly/Safety.lean#L322-L334)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### What an mbarrier instruction does

The event a thread produces for each mbarrier instruction, and how an object changes under each operation.

<a id="thread-tma"></a>
#### mbarrier and bulk-copy instructions (`THREAD-TMA`)

*Rule* · [Lean comment: `Core/Async/Tma.lean` L21-L145](../../Core/Async/Tma.lean#L21-L145)

Each mbarrier instruction of a thread produces one event: `mbarrier.init`, `mbarrier.inval`, `mbarrier.arrive` with or without `expect_tx`, and `mbarrier.try_wait.parity` each produce one event, and a `cp.async.bulk` copy or `cp.reduce.async.bulk` reduction produces only its issue event, one for each destination CTA of a multicast copy. A `.cp_mask` copy writes only the bytes its mask selects, and a reduction writes each element with an atomic read-modify-write at the scope of its `.sem.scope`. A misaligned address, an arrival count outside [1, 2^20), an invalid bulk-copy size, a source or destination range that overflows its memory space, or a destination or mbarrier in a CTA the direction does not allow produces an undefined-behaviour event instead.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`ofExec`](../../Core/Async/Tma.lean#L148-L151), [`mbarLoc`](../../Core/Async/Tma.lean#L153-L156), [`mbarClusterLoc`](../../Core/Async/Tma.lean#L158-L161), [`genericSharedLoc`](../../Core/Async/Tma.lean#L163-L171), [`mbarStateDest`](../../Core/Async/Tma.lean#L173-L177), [`bulkSizeOk`](../../Core/Async/Tma.lean#L179-L182), [`bulkSpaceEnd`](../../Core/Async/Tma.lean#L187-L191), [`bulkRangeOk`](../../Core/Async/Tma.lean#L193-L196), [`bulkPolicy`](../../Core/Async/Tma.lean#L201-L208), [`bulkIgnoreOob`](../../Core/Async/Tma.lean#L210-L217), [`bulkSpec`](../../Core/Async/Tma.lean#L219-L223), [`bulkMulticast`](../../Core/Async/Tma.lean#L225-L239), [`bulkReduceOk`](../../Core/Async/Tma.lean#L241-L253), [`bulkWrites`](../../Core/Async/Tma.lean#L255-L272), [`bulkCopyTmpl`](../../Core/Async/Tma.lean#L274-L323), [`tmaTmpl`](../../Core/Async/Tma.lean#L325-L344), [`tmaTmpl_cpBulk_cta`](../../Core/Async/Tma.lean#L346-L363)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16.12 (mbarrier.init)
- §9.7.15.16.13 (mbarrier.inval): "mbarrier.inval invalidates the mbarrier object at the location
    specified by the address operand addr"
- §9.7.15.16.14–16 (mbarrier.arrive.expect_tx): "mbarrier.arrive operation on an mbarrier object
    located in .shared::cta returns an opaque 64-bit register capturing the phase of the mbarrier
    object prior to the arrive-on operation in the destination operand state. Contents of the state
    operand are implementation specific."
- §5.1.7: "If no sub-qualifier is specified with the .shared state space, then it defaults to ::cta
    ."
- §9.7.15.16.19 (mbarrier.try_wait)
- §9.7.10.28.4.1 (cp.async.bulk): "size must be a multiple of 16. If the value is not a multiple of
    16, then the behavior is undefined."
- §9.7.10.28.4.1 (cp.async.bulk): "The memory range [dstMem, dstMem + size - 1] must not overflow
    the destination memory space and the memory range [srcMem, srcMem + size - 1] must not overflow
    the source memory space. Otherwise, the behavior is undefined."
- §9.7.10.28.4.1 (cp.async.bulk): "The addresses dstMem and srcMem must be aligned to 16 bytes."
- §9.7.10.28.4.1 (cp.async.bulk): "When the destination of the copy is .shared::cta the destination
    address has to be in the shared memory of the executing CTA within the cluster, otherwise the
    behavior is undefined."
- §9.7.10.28.4.1 (cp.async.bulk): "When the source of the copy is .shared::cta and the destination
    is .shared::cluster , the destination has to be in the shared memory of a different CTA within
    the cluster."
- §9.7.10.28.4.1 (cp.async.bulk): "The source data is multicast to the same CTA-relative offset as
    dstMem in the shared memory of each destination CTA. The mbarrier signal is also multicast to
    the same CTA-relative offset as mbar in the shared memory of the destination CTA."
- §9.7.10.28.4.1 (cp.async.bulk): "The only valid values for ignoreBytesLeft and ignoreBytesRight
    are [0..15] , and any other value may result in undefined behavior."
- §9.7.10.28.4.1 (cp.async.bulk): "When .sem is .relaxed , the data copy accesses memory with
    naturally-aligned strong memory operations with element-wise atomic size specified by .type and
    thread scope specified by .scope ."
- §9.7.10.28.4.1 (cp.async.bulk): "It is treated as a performance hint only, and does not change the
    memory consistency behavior of the program."
- §9.7.10.28.4.1 (cp.async.bulk): "When the optional qualifier .cp_mask is specified, the argument
    byteMask is required."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "The size of the source and the destination array must be
    the same and is specified by the operand size ."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "size must be a multiple of 16. If the value is not a
    multiple of 16, then the behavior is undefined."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "The memory range [dstMem, dstMem + size - 1] must not
    overflow the destination memory space and the memory range [srcMem, srcMem + size - 1] must not
    overflow the source memory space. Otherwise, the behavior is undefined."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "The addresses dstMem and srcMem must be aligned to 16
    bytes."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "When .sem.scope is not specified, it defaults to
    .relaxed.sys ."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "Source location accesses are .weak , that is, not atomic."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "The cp.reduce.async.bulk.add.f16 and
    cp.reduce.async.bulk.add.bf16 operations require .noftz qualifier."
- §9.7.15.4 (mbarrier-init fence)

**Applies:** Mbarrier instructions and `cp.async.bulk` in every direction of the instruction table (`.shared::cta.global` with an optional `.ignore_oob`, `.shared::cluster.global` with an optional `.multicast::cluster{::16b, ::32b}`, `.shared::cluster.shared::cta`, `.global.shared::cta.bulk_group` with an optional `.cp_mask`), `.weak` or `.relaxed`, with an optional `.L2::cache_hint`; `cp.reduce.async.bulk` in both directions with every operation and type of the table

**Premises:** Addresses, alignment, sizes, counts and CTAs pass the checks below.

**Effect:** Event production and local faults. An mbarrier object is an 8-byte aligned shared location; its arrival count must lie in `[1, 2^20)` and an unsigned 32-bit transaction operand (the object checks the resulting signed counter). `mbarrier.init`, `mbarrier.inval` and `mbarrier.arrive.expect_tx` are one event each; `fence.mbarrier_init` is an event. A bulk copy needs a positive size that is a multiple of 16 and 16-byte aligned addresses (`bulkSizeOk`), and its source and destination ranges must not overflow their memory spaces (`bulkRangeOk`), whatever its `.cp_mask` selects: a global range ends at most at `2^64` and a shared range at most at `2^32`, the address ranges of the model's locations (EXT-ADDR-WRAP). A range that stays below these bounds but reaches past the bytes of its space allocated at launch is rejected by the allocation checks: the footprint of the source and of an unmasked destination by ERR-UNALLOCATED-ACCESS, and the whole destination range of a `.cp_mask` copy by ERR-BULK-MASK-RANGE. Only its issue is in the thread trace (`Kind.copy`). Its read, write and notification are separate asynchronous effects (DEP-LINEAR-COPY-EFFECTS). The source and destination of a copy have the copy's size; the completion is the complete-tx on the instruction's mbarrier, or the issuing thread's bulk async-group for `.bulk_group`. The CTAs a copy may name: a `.shared::cta` destination and its mbarrier are in the executing CTA. A `.shared::cluster` destination of a copy from global memory and its mbarrier are in one CTA of the cluster, which may be the executing one; the text does not say where the mbarrier of a non-multicast copy may lie, and requiring the destination's CTA is stricter. A copy from `.shared::cta` to `.shared::cluster` reads the executing CTA's shared memory and writes another CTA's ("has to be in the shared memory of a different CTA"), with the mbarrier in that CTA (stricter, as above). A multicast copy issues one copy per destination CTA of its mask, in rank order through sub-steps, each to the CTA-relative offsets of `dstMem` and `mbar` in that CTA; each copy reads the source itself, which over-approximates the single read of the hardware, as for tensor multicast (THREAD-TENSOR-ISSUE). A mask with a rank outside the cluster, or with no rank, is undefined (stricter for the empty mask). `.ignore_oob` with both `ignoreBytesLeft` and `ignoreBytesRight` zero is the plain copy. Any other value leaves destination bytes indeterminate, which the linear copy effect does not represent, so it is an undefined-behaviour event (stricter). `.relaxed` copies are treated as weak: their accesses are weak async-proxy accesses (stricter: a race with them is reported although strong accesses of including scopes would not race). The `.L2::cache_hint` operand must be a defined 64-bit value and has no other effect. `try_wait.parity` is one event whose result is open; the thread sets its predicate from it. `mbarrier.arrive` on a `.shared` (that is `.shared::cta`) object with a destination register instead of the sink `_` is the same arrival event; the register's prior value is discarded and it holds no value afterwards (`mbarStateDest`), so a later read of it is an `uninitialized` fault. The text gives the state no meaning a thread can use ("Contents of the state operand are implementation specific."), so any use of it is rejected (stricter). A `.cp_mask` copy (only from `.shared::cta` to global memory, as the syntax states) writes byte `k` of its destination when bit `k % 16` of the 16-bit `byteMask` is set, with its source byte, and leaves the other bytes unwritten (`WriteMode.masked`, DEP-LINEAR-COPY-EFFECTS). A `cp.reduce.async.bulk` reads its `.shared::cta` source with weak accesses and reduces each element of its type into the destination with one atomic read-modify-write (`WriteMode.reduce`), strong at the scope of its `.sem.scope`, `.sys` when absent, in the async proxy (ERR-DATA-RACE, MEM-ATOMICITY, DEP-REDUCTION-VALUES); the operation and type must be a combination of the table for its destination (`bulkReduceOk`). The bit operations `.and`, `.or` and `.xor` also accept `.u` and `.s` types of the listed widths, as the instruction's own example `xor.s32` does. The `.noftz` qualifier is not recorded: the floating values come from an assumption. Its directions and checks are those of the copy with the same state spaces. Anything else in these instructions is undefined.

</details>

<a id="obj-mbar-state"></a>
#### layout::v0 mbarrier object operations (`OBJ-MBAR-STATE`)

*Rule* · [Lean comment: `Core/MBarrier/MBarrierObject.lean` L10-L53](../../Core/MBarrier/MBarrierObject.lean#L10-L53)

An mbarrier object counts the pending arrivals and the transaction bytes of its current phase; when both counts reach zero, the phase completes, the phase number advances and the pending count is reset to the expected count; a poll may fail at any time, and a successful poll reports the completed phase it observed. An object fault occurs when an operation other than initialization uses a location that holds no valid object, when a valid object is initialized, when a count leaves its range, when more arrivals occur than are pending, or when an arrival in a new phase comes before a successful wait observed the previous completion.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`MBarrier.State`](../../Core/MBarrier/MBarrierObject.lean#L56-L74) ([concept](#c-mbarrier-state)), [`MBarrier.Action`](../../Core/MBarrier/MBarrierObject.lean#L76-L93) ([concept](#c-mbarrier-action)), [`MBarrier.Error`](../../Core/MBarrier/MBarrierObject.lean#L95-L104) ([concept](#c-mbarrier-error)), [`MBarrier.Reply`](../../Core/MBarrier/MBarrierObject.lean#L106-L115) ([concept](#c-mbarrier-reply)), [`MBarrier.limit`](../../Core/MBarrier/MBarrierObject.lean#L117-L119) ([concept](#c-mbarrier-limit)), [`MBarrier.validCount`](../../Core/MBarrier/MBarrierObject.lean#L120-L121), [`MBarrier.validTx`](../../Core/MBarrier/MBarrierObject.lean#L122-L123), [`MBarrier.validTxOperand`](../../Core/MBarrier/MBarrierObject.lean#L124-L125), [`MBarrier.advance`](../../Core/MBarrier/MBarrierObject.lean#L127-L131), [`MBarrier.perform`](../../Core/MBarrier/MBarrierObject.lean#L133-L168) ([concept](#c-mbarrier-perform))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16.3, .5, .6, .8, .9, .12, .14–.16, .19
- §9.7.15.16.18: "When .noinc modifier is not specified, the pending count of the mbarrier object is
    incremented by 1 prior to the asynchronous arrive-on operation ."
- §9.7.15.16.18: "The pending count of the mbarrier object after the increment should not exceed the
    limit as mentioned in Contents of the mbarrier object . Otherwise, the behavior is undefined."
- §9.7.15.16: "An mbarrier object is an opaque object in memory which can be initialized and
    invalidated using : mbarrier.init mbarrier.inval"
- §9.7.15.16: "Performing any mbarrier operation except mbarrier.init on an uninitialized mbarrier
    object results in undefined behavior."
- §9.7.15.16.4: "An mbarrier object must be invalidated to repurpose its memory for any purpose,
    including repurposing it for another mbarrier object."
- §9.7.15.16.12: "The behavior of performing an mbarrier.init operation on a memory location
    containing a valid mbarrier object is undefined"
- §9.7.15.16.13: "mbarrier.inval invalidates the mbarrier object at the location specified by the
    address operand addr"
- §9.7.15.16.13: "Performing any mbarrier operation except mbarrier.init on a memory location that
    does not contain a valid mbarrier object , results in undefined behavior."

**Applies:** One layout::v0 object and the operations the decoder produces on it: initialization, invalidation, arrivals (with optional expected transaction bytes), the pending-count increment of `cp.async.mbarrier.arrive`, transaction completion and parity polls

**Premises:** Operations belong to this object's history; counts are in the ISA ranges.

**Effect:** Object-local transitions used by the object history; memory ordering and completion provenance are separate rules. Initialization of a location without a valid object creates one, and invalidation of a valid object removes it, so a later initialization creates a new object. Transaction updates are signed. A successful poll agrees with the current parity. The rule that a successful poll observes a phase before an arrival in the next phase is §9.7.15.16.5.1.

</details>

### Which executions are allowed

The recorded history of an object and the ordering and synchronization constraints that an execution must satisfy.

<a id="obj-mbar-phases"></a>
#### object histories and phase identities (`OBJ-MBAR-PHASES`)

*Rule* · [Lean comment: `Core/MBarrier/MBarrierHistory.lean` L10-L36](../../Core/MBarrier/MBarrierHistory.lean#L10-L36)

Each mbarrier address has a history that lists the operations on it in the object's atomic order. A counter update belongs to the phase it changes and a successful wait to the completed phase it observed, and phase numbers are compared only within one lifetime of the object, which runs from an initialization to the next invalidation.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`MBarrier.Record`](../../Core/MBarrier/MBarrierHistory.lean#L39-L48) ([concept](#c-mbarrier-record)), [`MBarrier.stateBefore`](../../Core/MBarrier/MBarrierHistory.lean#L50-L53), [`MBarrier.phaseAt`](../../Core/MBarrier/MBarrierHistory.lean#L55-L57), [`MBarrier.observedAt`](../../Core/MBarrier/MBarrierHistory.lean#L59-L61), [`MBarrier.SameLifetime`](../../Core/MBarrier/MBarrierHistory.lean#L63-L65) ([concept](#c-mbarrier-samelifetime))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16.3 (phases)
- §9.7.15.16.12 (init): "The primary and conditional phases are initialized to zero."
- §9.7.15.16.13 (inval)
- §9.7.15.16.19 (successful waits)

**Applies:** The operation history of one mbarrier address

**Premises:** Each record names the unique instruction or asynchronous notification that performs the operation.

**Effect:** Object-local provenance stored in Execution.objects. Parity alone never identifies a completion. The list is the atomic operation order of this one object. It gives no global order of thread instructions or memory accesses. An initial opposite-parity poll has no observed phase. Initialization restarts phases at zero, so phase numbers identify a phase only together with the lifetime: positions with no invalidation between them (`SameLifetime`).

</details>

<a id="obj-mbar-history"></a>
#### checked operations of one object (`OBJ-MBAR-HISTORY`)

*Rule* · [Lean comment: `Core/MBarrier/MBarrierHistory.lean` L67-L94](../../Core/MBarrier/MBarrierHistory.lean#L67-L94)

Every record of an object's history carries the reply that the object operations determine from the state before it, or an explicit object fault. A successful wait is matched only with the counter updates that precede it in the history and belong to the phase it observed, in the same lifetime.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`MBarrier.RecordOk`](../../Core/MBarrier/MBarrierHistory.lean#L97-L101), [`MBarrier.RecordedHistory`](../../Core/MBarrier/MBarrierHistory.lean#L103-L108), [`MBarrier.CheckedLog`](../../Core/MBarrier/MBarrierHistory.lean#L110-L113) ([concept](#c-mbarrier-checkedlog)), [`MBarrier.UpdateBeforeWait`](../../Core/MBarrier/MBarrierHistory.lean#L115-L120) ([concept](#c-mbarrier-updatebeforewait)), [`MBarrier.InitBefore`](../../Core/MBarrier/MBarrierHistory.lean#L122-L127) ([concept](#c-mbarrier-initbefore)), [`MBarrier.Before`](../../Core/MBarrier/MBarrierHistory.lean#L129-L131) ([concept](#c-mbarrier-before))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16.5–9 (phase completion, expect/complete transaction operations)
- §9.7.15.16.19 (wait observation)
- §9.7.15.16.4: "An mbarrier object must be invalidated to repurpose its memory for any purpose,
    including repurposing it for another mbarrier object."

**Applies:** A per-object history over arbitrarily many phases

**Premises:** Records use distinct operation identities and each transition is the one OBJ-MBAR-STATE determines, or its explicit fault.

**Effect:** Validity and provenance predicates used by Consistent; object faults are kept in the history and rejected by safety. `InitBefore` names the initialization of an operation's own object lifetime: the successful initialization before it with no invalidation in between. A manual complete_tx changes the counter but is not a data transfer: copy visibility also requires that the observed update is the completed copy's own notification (`AsyncCopy.Notifies`, OBJ-MBAR-OBSERVE).

</details>

<a id="obj-mbar-origin"></a>
#### copy effects name actual issuing instructions (`OBJ-MBAR-ORIGIN`)

*Rule* · [Lean comment: `Core/MBarrier/AsyncMBarrier.lean` L13-L50](../../Core/MBarrier/AsyncMBarrier.lean#L13-L50)

Every operation in an mbarrier's history comes from an actual instruction or from the actual completion notification of an asynchronous operation, and every such operation, including a failed wait, appears in the history. A copy or a tracked MMA counts as observed only through its own completion notification on its target object, so a manual `complete_tx` never stands for the completion of a copy. A `cp.async.mbarrier.arrive` tracks every earlier `cp.async` of its thread, and its arrive-on occurs only after all of them have written their destinations.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`AsyncCopy.issuedBy`](../../Core/MBarrier/AsyncMBarrier.lean#L53-L57), [`AsyncCopy.objectAction`](../../Core/MBarrier/AsyncMBarrier.lean#L59-L92), [`AsyncCopy.MatchesObject`](../../Core/MBarrier/AsyncMBarrier.lean#L94-L100), [`AsyncCopy.CoversObject`](../../Core/MBarrier/AsyncMBarrier.lean#L102-L105), [`AsyncCopy.TracksMma`](../../Core/MBarrier/AsyncMBarrier.lean#L107-L111), [`AsyncCopy.CommitOk`](../../Core/MBarrier/AsyncMBarrier.lean#L113-L117), [`AsyncCopy.TcEffectsOk`](../../Core/MBarrier/AsyncMBarrier.lean#L119-L131), [`AsyncCopy.TracksCpAsync`](../../Core/MBarrier/AsyncMBarrier.lean#L133-L137), [`AsyncCopy.ArriveOk`](../../Core/MBarrier/AsyncMBarrier.lean#L139-L144), [`AsyncCopy.ObjectsOk`](../../Core/MBarrier/AsyncMBarrier.lean#L146-L150)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.4.1 (the copy's own complete_tx notification)
- §9.7.15.16.15 (manual complete_tx does not perform a memory operation)
- §9.7.15.16.19 (wait observation)
- §9.7.15.16.18: "Causes an arrive-on operation to be triggered by the system on the mbarrier object
    upon the completion of all prior cp.async operations initiated by the executing thread."
- §9.7.15.16.18: "When .noinc modifier is not specified, the pending count of the mbarrier object is
    incremented by 1 prior to the asynchronous arrive-on operation ."
- §9.7.15.16.18: "When the .noinc modifier is specified, the increment to the pending count of the
    mbarrier object is not performed."

**Applies:** Linear and tensor copy, CLC, tcgen05 commit and cp.async.mbarrier.arrive events, independent effects and per-object histories

**Premises:** The history's operations resolve to actual instructions or actual copy notifications; successful-wait results agree.

**Effect:** Provenance and validity predicates used by Consistent and memory visibility. A manual complete_tx may change a counter but is not an async notification. A `cp.async.mbarrier.arrive` without `.noinc` records its pending-count increment as its own thread operation; with `.noinc` the instruction records no operation. Its arrive-on is an asynchronous operation (`.arriveOn`) of one arrival. Failed polls do not advance the object but are included, so use of an invalid object is still checked. Matching the histories to thread/proxy ordering, and checking that every required operation occurs, are separate obligations.

</details>

<a id="obj-mbar-observe"></a>
#### a successful wait observes an update in its phase (`OBJ-MBAR-OBSERVE`)

*Rule* · [Lean comment: `Core/MBarrier/AsyncMBarrier.lean` L152-L209](../../Core/MBarrier/AsyncMBarrier.lean#L152-L209)

A successful wait on an mbarrier observes every update recorded in the phase it saw complete, including the completion notifications of the asynchronous operations that phase tracks. The observation requires no acquire semantics and no scope, and each rule that uses it states the qualifiers it needs, such as the scopes that include each other in memory synchronization (MEM-MBAR-SYNCHRONIZES).

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`AsyncCopy.WaitObserves`](../../Core/MBarrier/AsyncMBarrier.lean#L212-L217) ([concept](#c-asynccopy-waitobserves)), [`AsyncCopy.NotifyOn`](../../Core/MBarrier/AsyncMBarrier.lean#L219-L227), [`AsyncCopy.Notifies`](../../Core/MBarrier/AsyncMBarrier.lean#L229-L243), [`AsyncCopy.AsyncObserved`](../../Core/MBarrier/AsyncMBarrier.lean#L245-L248) ([concept](#c-asynccopy-asyncobserved)), [`AsyncCopy.notifies_copy_of_mbarrier`](../../Core/MBarrier/AsyncMBarrier.lean#L250-L267)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16.19: "Checks whether the mbarrier object has completed the phase"
- §9.7.15.16.19: "The test_wait and try_wait operations are valid only for : the current incomplete
    phase, for which waitComplete returns False . the immediately preceding phase, for which
    waitComplete returns True ."
- §9.7.15.16.8 (phase completion)
- §9.7.10.28.1.2: "When the current phase of the mbarrier object is complete, it implies that all
    asynchronous operations tracked by this phase are complete, and all threads participating in
    that mbarrier object can access the result of the asynchronous operations."
- §9.7.10.28.3.3: "Writes performed by cp.async operations are made visible to the executing thread
    only after: The completion of cp.async.wait_all or The completion of cp.async.wait_group on the
    cp.async-group in which the cp.async belongs to or mbarrier.test_wait and mbarrier.try_wait
    returns True on an mbarrier object which is tracking the completion of the cp.async operation."
- §9.7.18.6.2.1.1: "Completion of the following instruction’s asynchronous operations is observed
    through the mbarrier based waiting mechanism: tcgen05.mma tcgen05.cp tcgen05.shift"
- §9.7.10.28.4.1
- §9.7.10.28.5.3
- §9.7.15.18
- §9.7.18.12.1 (the notification each asynchronous operation performs on its mbarrier)

**Applies:** Every successful mbarrier wait and every update recorded in the object history: thread arrivals, the complete-tx of linear and tensor copies and of CLC responses, and the arrive-on of commits and of `cp.async.mbarrier.arrive`

**Premises:** The wait's record has no fault and returned True; the update's record has no fault, precedes the wait in the object's history and belongs to the phase the wait observed.

**Effect:** The observation used by MSync, MbarExec, TcMma.CommitObserved, TcMma.DoneBefore, AsyncFinished, CopyReleaseSync and MbarObserved. `WaitObserves x w m acq ws` says that the successful wait `w` on `m`, with acquire flag `acq` and scope `ws`, observed the update `x`. `NotifyOn i t m` says that the notification `t` of `i` occurred on `m`; it is the copy's own complete-tx, the tensor load's, or the CLC response's to one target CTA. `Notifies i p n m` says that `n` is the notification on `m` that signals the completion of part `p` of the asynchronous operation issued by `i`: its notification `p.target` (`NotifyOn`), or the arrive-on of a commit tracking the MMA. `AsyncObserved i p w acq ws` says that the wait observed that notification. A `cp.async` has no notification of its own; the arrive-on of a `cp.async.mbarrier.arrive` that tracks it signals its completion (§9.7.10.28.3.3: "mbarrier.test_wait and mbarrier.try_wait returns True on an mbarrier object which is tracking the completion of the cp.async operation"). Every observation of an update, by any rule, is `WaitObserves`. Memory synchronization requires the scopes of both operations to include each other (`ScopesMeet`, MEM-MBAR-SYNCHRONIZES), and the visibility of a completed operation's accesses requires an acquire wait whose scope and the notification's scope include each other's thread (MEM-OBSERVED-COMPLETION). The needs of a successful poll (`MbarObserved`, DEP-ORDER) require no acquire and no scope. The source part names the operation through its actual notification, so a manual complete_tx (`objectAction` of a thread instruction) cannot stand in for a copy, and a multicast delivery to one CTA does not imply delivery to another.

</details>

<a id="mem-mbar-synchronizes"></a>
#### mbarrier release/acquire synchronization (`MEM-MBAR-SYNCHRONIZES`)

*Rule* · [Lean comment: `Core/Sync/Barrier.lean` L140-L167](../../Core/Sync/Barrier.lean#L140-L167)

A release arrival on an mbarrier synchronizes with a successful acquire wait that observes the arrival's phase, provided the scope of each operation includes the other thread. The accesses of the arriving thread before the arrival then happen before the accesses of the waiting thread after the wait.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`ScopesMeet`](../../Core/Sync/Barrier.lean#L174-L177) ([concept](#c-scopesmeet)), [`MbarRelease`](../../Core/Sync/Barrier.lean#L170-L172), [`MSync`](../../Core/Sync/Barrier.lean#L179-L188) ([concept](#c-msync))

<details>
<summary>Details for reviewers</summary>

- §8.7: "each operation is strong and specifies a scope that includes the thread executing the other
    operation"
- §8.9.4 (synchronization)
- §9.7.15.16.16 (release arrival)
- §9.7.15.16.19 (acquire wait observes the completed phase)
- MEM-SCOPE (scopes, §8.5)
- OBJ-MBAR-OBSERVE

**Applies:** Release arrivals and successful acquire waits on one mbarrier object, at CTA or cluster scope

**Premises:** Each scope includes the other participant; the arrival's actual object-history record belongs to the generation and phase observed by the wait; the source is at or before the arrival and the target follows the wait.

**Effect:** Adds baseCausality edges between thread events. The edges come from release arrivals and acquire waits at the instruction's scope.

</details>

<a id="obj-mbar-init-publication"></a>
#### restricted publication of mbarrier initialization (`OBJ-MBAR-INIT-PUBLICATION`)

*Rule* · [Lean comment: `Core/MBarrier/InitPublication.lean` L11-L62](../../Core/MBarrier/InitPublication.lean#L11-L62)

An mbarrier initialization is published to a later operation when it happens before that operation, or when its thread follows it with `fence.mbarrier_init.release.cluster` and a `barrier.cluster.arrive`, and a `barrier.cluster.wait` that observed this arrival happens before that operation. The second route publishes the initialization and no other operation of its thread, and it places the initialization before every operation of the object whose issue the wait causally precedes.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`InitFenceSync`](../../Core/MBarrier/InitPublication.lean#L106-L118), [`InitFencePublished`](../../Core/MBarrier/InitPublication.lean#L120-L123), [`InitPublished`](../../Core/MBarrier/InitPublication.lean#L125-L128) ([concept](#c-initpublished)), [`InitFenceOrdered`](../../Core/MBarrier/InitPublication.lean#L130-L135)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.4: "When .op_restrict is .mbarrier_init , the synchronizing effect of the fence only
    applies to the prior mbarrier.init operations executed by the same thread on mbarrier objects in
    .shared::cta state space."
- §9.7.15.4 (example): "Release local barrier state via generic proxy. mbarrier.init [bar];
    fence.mbarrier_init.release.cluster; barrier.cluster.arrive.relaxed;"
- §8.9.4: "A barrier.cluster.arrive operation synchronizes with a barrier.cluster.wait operation."
- §9.7.15.3: "The optional .relaxed qualifier on barrier.cluster.arrive specifies that there are no
    memory ordering and visibility guarantees provided for the memory accesses performed prior to
    barrier.cluster.arrive ."
- §9.7.15.3: "If the optional .acquire qualifier is absent for barrier.cluster.wait , .acquire is
    assumed by default."
- §8.8: "Any memory synchronization established by a release pattern only affects operations
    occurring in program order before the first instruction in that pattern."
- §8.9.5 (base causality order)
- EXT-OBJECT-ORDER
- EXT-ASYNC-OBJECT
- EXT-INIT-FENCE-ARRIVE

**Applies:** A shared::cta mbarrier initialization, followed in its thread by fence.mbarrier_init.release.cluster and then by a cluster arrival of either qualifier

**Premises:** The initialization of `m` (in the thread's own CTA), the fence and the arrival are in one thread, in that program order; a cluster wait observed the arrival (the cluster barrier's history records the wait for the phase the arrival belongs to, `ClusterBarrier.ArrivalOf` and `ClusterBarrier.WaitOf`); causality orders the wait before the use, or before the issue of the operation of `m`'s history.

**Effect:** Initialization publication checks in safety (`InitPublished`) and an execution constraint (Consistent.initFence), separate from baseCausality and modelCausality: the init is not composed with the program order before it, nor with any memory access; the async proxy fence is its own instruction (MEM-MODEL-CAUSALITY). `InitFenceSync` is the restricted synchronization: from the initialization to the wait. It enters neither `baseCausality` nor `stageCausality`, since both are closed under program order on the left (§8.9.5: "For some operation Z, X precedes Z in program order and Z precedes Y in base causality order"). The fence orders the initializations before it (§9.7.15.4) and no other operation of the thread. `InitFenceOrdered` is the order of one object agreeing with this synchronization, as `ObjectCoherent` and `AsyncObjectOrdered` are for causality (EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT): the operation, or the asynchronous update issued after the wait, comes after the initialization. The object history separately selects the initialization of the actual lifetime.

</details>

<a id="ext-init-fence-arrive"></a>
##### a relaxed cluster arrival carries the init fence's release (`EXT-INIT-FENCE-ARRIVE`)

*Interpretation (EXT)* · [Lean comment: `Core/MBarrier/InitPublication.lean` L64-L103](../../Core/MBarrier/InitPublication.lean#L64-L103)

The sequence `mbarrier.init`, `fence.mbarrier_init.release.cluster`, `barrier.cluster.arrive` publishes the initialization to the threads that wait for the arrival, also when the arrival is `.relaxed`. The fence and the relaxed arrival together order the thread's prior initializations before the waiters' later operations, and they order no other prior access of the thread. This is the synchronization `InitFenceSync`.

Source:

- - §8.9.4: "A barrier.cluster.arrive operation synchronizes with a barrier.cluster.wait operation." - §9.7.15.3: "The optional .relaxed qualifier on barrier.cluster.arrive specifies that there are no memory ordering and visibility guarantees provided for the memory accesses performed prior to barrier.cluster.arrive ." - §9.7.15.4: "When .op_restrict is .mbarrier_init , the synchronizing effect of the fence only applies to the prior mbarrier.init operations executed by the same thread on mbarrier objects in .shared::cta state space." - §9.7.15.4 (example): "Release local barrier state via generic proxy. mbarrier.init [bar]; fence.mbarrier_init.release.cluster; barrier.cluster.arrive.relaxed;"

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** Three passages bear on this sequence, and the text does not say how they combine. §8.9.4 states without condition that "A barrier.cluster.arrive operation synchronizes with a barrier.cluster.wait operation."; with base causality (§8.9.5) that alone would order every operation the arriving thread performed before the arrival before the wait's causal successors. The `.relaxed` sentence of §9.7.15.3 states the opposite for a relaxed arrival: "there are no memory ordering and visibility guarantees provided for the memory accesses performed prior to barrier.cluster.arrive", so it alone would order none of them. `fence.mbarrier_init` states that "the synchronizing effect of the fence only applies to the prior mbarrier.init operations executed by the same thread", and its example publishes the initialization by exactly this sequence. The reading picks the initializations only: the relaxed arrival orders no prior access by itself, the fence makes it order the thread's prior initializations, and nothing else.

**Effect:** Wider than the text by the reading only: if the example does not order the initialization before the users after a peer's wait, a user's arrival or a copy's complete-tx may reach the object before its initialization (undefined behaviour, §9.7.15.16), which the model does not report. The init fence's release is not applied to any other operation of the thread. Disclosed by every kernel whose statement names `Op.fenceMbarInit`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192.

</details>

<a id="mem-object-order-causality"></a>
#### memory-layer axioms over causality, observation and object order (`MEM-OBJECT-ORDER-CAUSALITY`)

*Rule* · [Lean comment: `Core/Assembly/WaitOrder.lean` L22-L136](../../Core/Assembly/WaitOrder.lean#L22-L136)

An execution is allowed only if no cycle combines causality with the synchronizing part of the operation order of a single synchronization object, no synchronizing observation follows in causality the issue of what it observed, and no asynchronous update is placed in its object's order before an operation that is tied to its issue by program order, the object's lifetime or an acquire observation. Causality here is `stageCausality`, the model's extension of base causality (`baseCausality`, §8.9.5) to the issue and completion nodes of instructions and asynchronous stages: the stage order, base causality from a completion to a later issue, and a copy's release complete-tx to the successors of a wait that observes it.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`CounterUpdate`](../../Core/Assembly/WaitOrder.lean#L275-L282), [`MbarObserved`](../../Core/Assembly/WaitOrder.lean#L284-L289) ([concept](#c-mbarobserved)), [`ReleaseUpdate`](../../Core/Assembly/WaitOrder.lean#L291-L295), [`SyncObserved`](../../Core/Assembly/WaitOrder.lean#L297-L305), [`CopyReleaseSync`](../../Core/Assembly/WaitOrder.lean#L307-L312) ([concept](#c-copyreleasesync)), [`stageCausality`](../../Core/Assembly/WaitOrder.lean#L314-L323), [`CtaBarOn`](../../Core/Assembly/WaitOrder.lean#L325-L328), [`OrderObject`](../../Core/Assembly/WaitOrder.lean#L330-L335), [`ObjectOrder`](../../Core/Assembly/WaitOrder.lean#L337-L353) ([concept](#c-objectorder)), [`MbarSyncRecord`](../../Core/Assembly/WaitOrder.lean#L355-L362), [`MbarLifetimeRecord`](../../Core/Assembly/WaitOrder.lean#L364-L366), [`SyncObjectOrder`](../../Core/Assembly/WaitOrder.lean#L368-L379), [`ObservationCausal`](../../Core/Assembly/WaitOrder.lean#L381-L384), [`ObjectCoherent`](../../Core/Assembly/WaitOrder.lean#L386-L389) ([concept](#c-objectcoherent)), [`AsyncObjectOrdered`](../../Core/Assembly/WaitOrder.lean#L391-L400) ([concept](#c-asyncobjectordered)), [`OrderObject.Enabling`](../../Core/Assembly/WaitOrder.lean#L402-L406)

<details>
<summary>Details for reviewers</summary>

- §8.9.1
- §8.9.1.1 (program order; asynchronous operations)
- §8.9.4 (synchronizes-with)
- §8.9.5 (base causality order)
- §8.10.1
- §8.10.6 (Coherence, Causality axioms)
- §8.8: "A release pattern on a location M consists of one of the following: A release operation
    on M E.g.: st.release [M]; or atom.release [M]; or mbarrier.arrive.release [M];"
- §8.8: "An acquire pattern on a location M consists of one of the following: An acquire operation
    on M E.g.: ld.acquire [M]; or atom.acquire [M]; or mbarrier.test_wait.acquire [M];"
- §8.7 (morally strong)
- §9.7.10.28.4.1
- §9.7.10.28.5.3 (copy stages; complete-tx upon completion of the copy; complete-tx has .release
    semantics at .cluster scope; mbarrier operand accessed using generic-proxy)
- §9.7.10.28.6.2 (bulk-group wait: writes being made visible to the executing thread)
- §9.7.10.28.3.3 (cp.async.wait_group)
- §9.7.15.16.5.1 (primary phases)
- §9.7.15.16.8 (atomic phase transition)
- §9.7.15.16.16
- §9.7.15.16.19: "The .relaxed qualifier does not provide any memory ordering semantics and
    visibility guarantees."
- §9.7.15.16.19: "When mbarrier.test_wait and mbarrier.try_wait operations with .acquire qualifier
    returns True , they form the acquire pattern as described in the Memory Consistency Model ."
- §9.7.15.18 (CLC complete-tx upon completion)
- §9.7.18.12.1 (commit signals upon completion of tracked operations)
- EXT-OBJECT-ORDER
- EXT-ASYNC-OBJECT
- EXT-STAGE-ORDER

**Applies:** The issue/completion nodes of thread instructions and asynchronous stages

**Effect:** Consistent.observation, Consistent.object and Consistent.asyncObject. These are the memory-layer axioms. No edge of the dependency order (DEP-ORDER: needs, witnesses, the returns of blocking instructions and the canonical spins) enters them, so the collectives without memory text (vote, redux, shfl, match, elect, the `.sync` tcgen05 instructions, setmaxnreg, the warp-level matrix instructions) and the relaxed mbarrier observations order no memory operation. The barriers' memory effects are their own base-causality edges in MEM-BASE-CAUSALITY (`CtaBarSync`, `ClusterSync`, `WarpBarSync`, `MSync`), each with its memory quote.

</details>

<a id="ext-object-order"></a>
##### the operations on one synchronization object are totally ordered (`EXT-OBJECT-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/WaitOrder.lean` L178-L232](../../Core/Assembly/WaitOrder.lean#L178-L232)

(Execution layer.) The operations on one mbarrier, on one CTA barrier and on one cluster barrier each take effect in a single total order, the history the execution records for the object, and the dependency order together with that order of any single object has no cycle (`DependencyOk.acyclic`, DEP-ORDER). (Memory layer.) For an mbarrier, the pairs of that order of two synchronizing records whose scopes meet, the pairs with the object's initialization or invalidation, and the pairs of one thread never contradict causality; for a CTA barrier or a cluster barrier the whole order never does (`ObjectCoherent` over `SyncObjectOrder`).

Source:

- - §9.7.15.16.8 (mbarrier; when the phase completes): "the following actions are performed atomically" - §8.10.1 (mbarrier; coherence orders only overlapping writes) - §8.10.5 (mbarrier) - §9.7.15.1 (CTA barrier): "Each CTA instance has sixteen barriers" - §9.7.15.1 (CTA barrier): "the barrier is reinitialized so that it can be immediately reused" - §9.7.15.3 (cluster barrier): "the barrier completes and is automatically reinitialized" - §8.4: "read operation All variants of ld instruction and atom instruction (but not red instruction)." - §8.4: "write operation All variants of st instruction, and atomic operations if they result in a write." - §8.8 (release and acquire patterns, as quoted in MEM-OBJECT-ORDER-CAUSALITY) - §9.7.15.16.19: "The .relaxed qualifier does not provide any memory ordering semantics and visibility guarantees." - §9.7.15.16.5.1: "In each primary phase {0, 1, 2, …}, threads perform in program order : arrive-on operations to complete the current primary phase and test_wait / try_wait operations to check for the completion of the current primary phase."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** §8.10.1 orders writes to overlapping memory locations. The CTA barrier and the cluster barrier have no memory location, and for the mbarrier the text states the atomicity of one phase transition. It does not state that all its operations form one order that agrees with causality. One order per object is the reading that each such object is a single atomic state machine whose operations take effect one after another. The memory part is restricted for the mbarrier because the manual is inconsistent about it: §8.4 lists only `ld` and `atom` as read operations and `st` and atomic writes as write operations, while §8.8 names `mbarrier.arrive.release [M]` and `mbarrier.test_wait.acquire [M]` as release and acquire operations, and §8.9.4 requires a write in the release pattern and a read in the acquire pattern. So it is unclear whether a release or acquire mbarrier operation is a write or read operation of the memory model, and whether a relaxed one is a strong operation. The model keeps every execution that either reading allows: synchronization is taken only from the release and acquire mbarrier operations that §8.8 names, with scopes that include each other's thread (§8.7), and a relaxed mbarrier operation contributes no memory-layer order. No proof may derive an order from a relaxed poll combined with a release/acquire chain.

**Effect:** Executions in which the operations on one object cannot be ordered consistently with the dependency order, or its synchronizing part with causality, are removed. The relaxed-poll example (K9 in `Tests/Progress/DependencyLitmus.lean`: one thread's relaxed poll succeeds and then it stores with release; another thread loads that value with acquire and then arrives relaxed) stays consistent. The fourth object kind, one CTA's Tensor Memory allocator, is EXT-TMEM-ALLOC-ORDER. Disclosed by every kernel whose statement names `Op.mbarInit`, `Op.mbarArrive`, `Op.mbarWait`, `Op.barSync`, `Op.barSyncN`, `Op.barArrive` or `Op.cluster`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm, TmaCopy.

</details>

<a id="ext-async-object"></a>
##### an asynchronous update follows its issue in its object's order (`EXT-ASYNC-OBJECT`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/WaitOrder.lean` L138-L176](../../Core/Assembly/WaitOrder.lean#L138-L176)

An update that an asynchronous operation makes to an mbarrier, a complete-tx or an arrive-on, comes in that mbarrier's order after every operation of the issuing thread that precedes the issuing instruction in program order. It also comes after the object's `mbarrier.init` or `mbarrier.inval`, and after an acquire wait that observes it, whenever that operation causally precedes the issuing instruction.

Source:

- - §8.9.1.1: "These asynchronous operations are ordered after prior instructions in the same thread" - §9.7.10.28.5.3 (the complete-tx is performed upon completion of the copy) - §9.7.18.12.1 (the commit's arrive-on is signalled upon completion of the tracked operations) - §9.7.15.18 - §8.8 (acquire pattern)

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The quoted text states the ordering of the operation's memory accesses and not the object order of its notification. The model reads it as: the update of an object by an asynchronous operation comes, in that object's atomic order, after the operations of the same object that the manual ties to the issue: the issuing thread's earlier operations (program order), the object's lifetime records, and an acquire wait that observes the update. Other operations of other threads, relaxed operations among them, do not take part, whatever the notification's release semantics, because a relaxed operation forms no synchronization (§8.8, §9.7.15.16.19).

**Evidence:** An operation completes after it is issued, and the canonical pipelines initialize an mbarrier, publish the initialization (`fence.mbarrier_init`, then a CTA or cluster barrier) and only then issue copies or commits that signal it (CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23), include/cutlass/pipeline/sm90_pipeline.hpp, sm100_pipeline.hpp); a notification that reached the object before its initialization would make these programs fault.

**Effect:** Executions in which an asynchronous update is ordered in its object's history before such an operation are removed from `Consistent`; if hardware allows them, the model excludes executions that may occur. The relaxed-poll example with a copy's complete-tx (K9b in `Tests/Progress/DependencyLitmus.lean`) stays consistent. Disclosed by every kernel whose statement names `Op.cpBulk`, `Op.cpTensor`, `Op.tcCommit` or `Op.clcTryCancel`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm, TmaCopy.

</details>

<a id="ext-enables-object"></a>
##### an event that exists because of a return is not placed before its witness (`EXT-ENABLES-OBJECT`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/Dependency.lean` L159-L186](../../Core/Assembly/Dependency.lean#L159-L186)

An event that exists only because a thread resumed from a blocking instruction, or follows the exit of a canonical spin whose successful poll observed a record, is never placed before a witness of that return in the order of a synchronization object. Program order alone, as after a single poll whose result no instruction reads, creates no dependency; every other use of a poll result is unsafe (ERR-POLL-SHAPE).

Source:

- - §9.7.15.16.8 (atomic phase transition) - §9.7.15.16.19 (a poll returns at once with whether the phase completed) - the waiting sentences quoted in DEP-ORDER

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The instruction descriptions state what a thread waits for. They do not state that the order of a synchronization object agrees with these waits. The reading is the physical dependency: an operation cannot be performed before the observation or the return that it needed.

**Effect:** Executions in which an event that exists only because of a return is placed before a witness of that return in one object's order are removed from `Consistent` (`DependencyOk.acyclic`); if hardware allows them, the model excludes executions that may occur. The load buffering through two mbarriers with single relaxed polls (K1 in `Tests/Progress/DependencyLitmus.lean`) stays allowed, while the same shape with canonical spins is excluded. Disclosed by every kernel whose statement names `Op.mbarInit`, `Op.mbarArrive`, `Op.mbarWait`, `Op.barSync`, `Op.barSyncN`, `Op.barArrive` or `Op.cluster`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm, TmaCopy.

</details>

<a id="mem-observed-completion"></a>
#### observation of a particular operation's completion (`MEM-OBSERVED-COMPLETION`)

*Rule* · [Lean comment: `Core/Memory/Order.lean` L137-L205](../../Core/Memory/Order.lean#L137-L205)

An acquire wait that observes the completion notification of a copy, a tensor load, a CLC response or an MMA, with scopes that include each other's thread, orders the memory accesses of that operation before the accesses that follow the wait, except that the shared-memory reads of `tcgen05.mma` and `tcgen05.cp` use a `fence.proxy.async` between the wait and a later generic access (MEM-MODEL-CAUSALITY), with a completed source overwrite also ordered under EXT-TC-SOURCE-REUSE. A bulk-group wait does the same for the tensor stores and linear copies of the groups it covers, and a `.read` bulk-group wait orders their source reads before later generic accesses without a proxy fence (EXT-READ-WAIT-ORDER). A `cp.async` wait does the same for the `cp.async` operations of the groups it covers, and an acquire wait that observes the arrive-on of a `cp.async.mbarrier.arrive` for the `cp.async` operations it tracks.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`AsyncFinished`](../../Core/Memory/Order.lean#L242-L252) ([concept](#c-asyncfinished)), [`asyncFinished_copy_of_mbarrier`](../../Core/Memory/Order.lean#L254-L271)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.1.2: "When the current phase of the mbarrier object is complete, it implies that all
    asynchronous operations tracked by this phase are complete, and all threads participating in
    that mbarrier object can access the result of the asynchronous operations."
- §9.7.10.28.1.2: "Once the mbarrier.test_wait or mbarrier.try_wait operation returns True , access
    the results of the asynchronous operations tracked by the mbarrier object ."
- §9.7.10.28.2: "The completion of a cp{.reduce}.async.bulk operation is followed by an implicit
    generic-async proxy fence. So the result of the asynchronous operation is made visible to the
    generic proxy as soon as its completion is observed."
- §9.7.18.6.2.1.1 (tcgen05.mma completion is observed through the mbarrier based waiting mechanism)
- §9.7.18.6.5: "The shared memory accesses by tcgen05.mma and tcgen05.cp operations are performed
    asynchronously and via the asynchronous proxy (async proxy). These shared memory accesses are
    not subject to the pipelining rules above. Accessing the same memory location across multiple
    proxies needs a cross-proxy fence. For the async proxy, fence.proxy.async should be used to
    synchronize memory between generic proxy and the async proxy."
- §9.7.10.28.6.2 (bulk-group wait)
- §9.7.10.28.3.3: "Writes performed by cp.async operations are made visible to the executing thread
    only after: The completion of cp.async.wait_all or The completion of cp.async.wait_group on the
    cp.async-group in which the cp.async belongs to or mbarrier.test_wait and mbarrier.try_wait
    returns True on an mbarrier object which is tracking the completion of the cp.async operation."
- §9.7.10.28.3.3: "cp.async.wait_group and cp.async.wait_all does not provide any ordering and
    visibility guarantees for any other memory operation apart from cp.async ."
- §9.7.18.12.1 (commit tracks prior tcgen05 operations): "The scope of the arrive-on operation is
    the cluster scope."
- §9.7.15.18 (clusterlaunchcontrol.try_cancel): "The completion of the asynchronous operation is
    tracked using the mbarrier completion mechanism at .cluster scope."
- §8.7 (morally strong)
- OBJ-MBAR-OBSERVE
- EXT-READ-WAIT-ORDER
- EXT-TC-SOURCE-REUSE

**Applies:** The actual notification of a copy, tensor load (its `.notify .load`), CLC response or MMA (the arrive-on of a commit that tracks it), and the arrive-on of a `cp.async.mbarrier.arrive`, in its object's exact generation and phase (`AsyncCopy.Notifies`); the bulk group of a tensor store or linear copy; the `cp.async`-group of a `cp.async`

**Premises:** An acquire wait observes that notification (`AsyncCopy.AsyncObserved`) and its scope and the notification's `.cluster` scope each include the other's thread (`ScopesMeet`, as for `CopyReleaseSync`); or a group wait whose mode makes the part visible (`GroupWaitVisible`) covers the operation's group (`GroupWaitsFor`) and the stages it waits for are present: a full or `.read` bulk-group wait for a tensor store or a linear copy, a `cp.async.wait_group` or `cp.async.wait_all` for a `cp.async`.

**Effect:** Completion and visibility (MEM-MODEL-CAUSALITY). The quoted text does not require an acquire wait; the rule requires one, and requires the scopes to meet (stricter). The `.read` wait is the reading EXT-READ-WAIT-ORDER. The observing thread may belong to another CTA of the issuer's cluster when its wait has cluster scope. A `cp.async` group wait makes the writes visible to the waiting thread; the order then reaches other threads only through `baseCausality` from the wait, as for a full bulk-group wait, and it orders no other memory operation of the thread.

</details>

<a id="dep-tc-fence"></a>
#### tcgen05 fences composed with execution ordering (`DEP-TC-FENCE`)

*Rule* · [Lean comment: `Core/Tc/TcFence.lean` L11-L89](../../Core/Tc/TcFence.lean#L11-L89)

A tcgen05 operation is ordered before another tcgen05 operation when it precedes it in base causality order (program order, or synchronization between threads under EXT-TCACQUIRE), or when a `tcgen05.fence::before_thread_sync` after the first reaches a `tcgen05.fence::after_thread_sync` before the second through base causality or through one observed mbarrier arrival, relaxed or release. The completion of an MMA is ordered before a later operation when a wait observes the arrive-on of a `tcgen05.commit` that tracks the MMA and reaches a `tcgen05.fence::after_thread_sync` before that operation through base causality.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`MbarExec`](../../Core/Tc/TcFence.lean#L131-L136) ([concept](#c-mbarexec)), [`ExecOrder`](../../Core/Tc/TcFence.lean#L153-L157) ([concept](tcgen05.md#c-execorder)), [`TcMma.CommitObserved`](../../Core/Tc/TcFence.lean#L140-L145) ([concept](tcgen05.md#c-tcmma-commitobserved)), [`TcMma.AfterSync`](../../Core/Tc/TcFence.lean#L147-L149), [`TcMma.FenceOrder`](../../Core/Tc/TcFence.lean#L161-L163), [`TcMma.TcBefore`](../../Core/Tc/TcFence.lean#L165-L168) ([concept](tcgen05.md#c-tcmma-tcbefore))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.3: "The standard memory consistency model synchronization mechanisms also apply to the
    tcgen05 family of instructions."
- §9.7.18.6.3: "The tcgen05.fence::before_thread_sync and tcgen05.fence::after_thread_sync composes
    with execution ordering instructions, like morally strong ld / st / atom instructions, mbarrier
    instruction, barrier instructions and so on, to establish an ordering between the tcgen05
    operations across threads. The asynchronous tcgen05 instructions that are ordered across threads
    in the same warp also form a tcgen05 pipeline. An asynchronous tcgen05 operation prior to a
    tcgen05.fence::before_thread_sync is ordered before all subsequent tcgen05 and the execution
    ordering operations. An asynchronous tcgen05 operation subsequent to a
    tcgen05.fence::after_thread_sync is ordered after all the prior tcgen05 and the execution
    ordering operations."
- §9.7.18.6.4 (canonical patterns, quoted below)
- §9.7.18.11.1: "The tcgen05.fence::* instructions compose with execution ordering instructions
    across a thread scope and provide ordering between tcgen05 instructions across the same scope."
- §9.7.18.12.1: "The scope of the arrive-on operation is the cluster scope."
- §9.7.15.16.19 (a successful wait observes the completed phase)
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

**Applies:** tcgen05 operations of any thread ordered through `tcgen05.fence::before_thread_sync`, `tcgen05.commit` and `tcgen05.fence::after_thread_sync`

**Premises:** An execution ordering (`ExecOrder`) from a `fence::before_thread_sync` program-ordered after the earlier operation (`FenceOrder`) reaches a `fence::after_thread_sync` program-ordered before the later operation (`AfterSync`) by base causality (`baseCausality`: program order, `bar.sync`, `bar.warp.sync`, release `barrier.cluster.arrive`, release/acquire mbarrier and memory synchronization), or by one mbarrier arrival, relaxed or release, program-ordered after the first fence and counted in the phase that a successful wait, relaxed or acquire, observes (`MbarExec`, each scope including the other thread), followed by base causality. An MMA's completion is ordered by a successful wait observing the arrive-on of a `tcgen05.commit` tracking it (`CommitObserved`; the commit's implicit before-fence and arrival) followed by base causality to the `fence::after_thread_sync` (`AfterSync`). Each ordering contains at most one observation, at its head (§8.9.5 causality order).

**Effect:** Order relations used by the completion, pipeline, source, conflict and access rules of `Tc/` and `Tmem/`. A relaxed mbarrier synchronization enters an ordering through `MbarExec` or `CommitObserved`; the fenced route needs no acquire wait. The completion of the earlier operation is ordered before a later operation only through the completion mechanisms, which are `tcgen05.wait::ld`, `tcgen05.wait::st` and a commit whose arrival a wait observes, as DEP-TC-COMPLETION and DEP-TMEM-STORE-VALUE use them.

</details>

### What counts as an error

Executions that are rejected as unsafe because of an mbarrier object.

<a id="err-mbar-uninitialized"></a>
#### every mbarrier operation uses an initialized object (`ERR-MBAR-UNINITIALIZED`)

*Rule* · [Lean comment: `Core/MBarrier/InitPublication.lean` L137-L173](../../Core/MBarrier/InitPublication.lean#L137-L173)

An execution is unsafe when an instruction other than `mbarrier.init` names an mbarrier object as an operand and no initialization of that object is published to its issue. This covers the thread's own mbarrier operations, the asynchronous operations that complete on an mbarrier, the targets of `tcgen05.commit` and the response mbarriers of a CLC request.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`MbarUninit`](../../Core/MBarrier/InitPublication.lean#L176-L180)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16: "Performing any mbarrier operation except mbarrier.init on an uninitialized mbarrier
    object results in undefined behavior."
- §9.7.15.16.13: "Performing any mbarrier operation except mbarrier.init on a memory location that
    does not contain a valid mbarrier object , results in undefined behavior."
- §9.7.10.28.4.1 (generic-proxy mbarrier operand)
- §9.7.10.28.5.3 (generic-proxy mbarrier operand)
- §9.7.18.12.1 (generic-proxy mbarrier operand)
- OBJ-MBAR-INIT-PUBLICATION

**Applies:** Every event that names an mbarrier operand (`Execution.UsesMbar`) and is not its initialization: arrivals, polls, invalidations, linear copies and tensor loads with mbarrier completion, `cp.async.mbarrier.arrive`, every target of a `tcgen05.commit`, and the response mbarrier of every target CTA of a CLC request

**Premises:** An initialization of the object is published to the issue (`InitPublished`: it happens before the issue, or it is published through `fence.mbarrier_init` and a cluster barrier).

**Effect:** Safety rejection. The exact lifetime of each operation that reaches the object history is ERR-OBJECT-LIFETIME (`ObjectPublished`). The storage of the object is ERR-UNALLOCATED-ACCESS.

</details>

<a id="err-object-lifetime"></a>
#### object faults, object lifetimes and async lifetimes (`ERR-OBJECT-LIFETIME`)

*Rule* · [Lean comment: `Core/Assembly/Safety.lean` L247-L298](../../Core/Assembly/Safety.lean#L247-L298)

An execution is unsafe when an mbarrier operation faults, or when an operation on an object is not ordered after the initialization of its lifetime or not ordered before the invalidation that ends that lifetime. It is also unsafe when an ordinary memory access to an object's bytes is ordered neither before its initialization nor after its invalidation, when two `cp.async` operations of one group overlap (ERR-CP-ASYNC-OVERLAP), or when the destination range of a `.cp_mask` copy covers an unallocated byte (ERR-BULK-MASK-RANGE).

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`RecordBefore`](../../Core/Assembly/Safety.lean#L301-L306), [`ObjectPublished`](../../Core/Assembly/Safety.lean#L308-L320) ([concept](#c-objectpublished)), [`TmaUnsafe`](../../Core/Assembly/Safety.lean#L322-L334) ([concept](#c-tmaunsafe))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16 (mbarrier lifetime and initialization): "Performing any mbarrier operation except
    mbarrier.init on an uninitialized mbarrier object results in undefined behavior. Performing any
    non-mbarrier or mbarrier.init operations on an initialized mbarrier object results in undefined
    behavior"
- §9.7.15.16.4: "An mbarrier object must be invalidated to repurpose its memory for any purpose,
    including repurposing it for another mbarrier object."
- §9.7.15.16.13: "An mbarrier object must be invalidated before using its memory location for any
    other purpose. Performing any mbarrier operation except mbarrier.init on a memory location that
    does not contain a valid mbarrier object , results in undefined behavior."
- §9.7.15.16.13 (example): "bar.cta.sync 0; @t0 mbarrier.inval.shared.b64 [shmem]; // shmem can be
    reused here for unrelated use : bar.cta.sync 0; st.shared.b64 [shmem], ...; // shmem can be
    re-initialized as mbarrier object : bar.cta.sync 0; @t0 mbarrier.init.shared.b64 [shmem], 24;"
- §9.7.10.28.4.1 (generic-proxy mbarrier operand)

**Applies:** Actual object records and the memory accesses of an object's bytes (the initialization published to the issue of every mbarrier operation: ERR-MBAR-UNINITIALIZED; the storage of an mbarrier: ERR-UNALLOCATED-ACCESS; shared-memory lifetimes: ERR-SHARED-LIFETIME)

**Premises:** A recorded object transition faults; an operation is not ordered after the initialization of its lifetime (`InitPublished`) or, when that lifetime is invalidated, before the invalidation (`RecordBefore`); a re-initialization does not happen after an earlier invalidation; a memory access touches a byte of an mbarrier and is neither ordered before an initialization nor after the invalidation that ends that initialization's lifetime, at that byte (MEM-MODEL-CAUSALITY `modelCausality`: a thread access happens before it; an asynchronous access has its completion observed by a wait that happens before it; an asynchronous access after a thread event has a proxy fence between them).

**Effect:** Safety rejection.

</details>

<a id="err-tc-commit-group"></a>
#### the issuing CTA group exists (`ERR-TC-COMMIT-GROUP`)

*Rule* · [Lean comment: `Core/Tc/TcCommitSafety.lean` L12-L32](../../Core/Tc/TcCommitSafety.lean#L12-L32)

An execution is unsafe when a CTA of the CTA group that issues a `tcgen05.commit` does not exist in the cluster.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`TcCommitIssueSafe`](../../Core/Tc/TcCommitSafety.lean#L34-L38), [`TcCommitUnsafe`](../../Core/Tc/TcCommitSafety.lean#L40-L42)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5 (issue granularity)

**Applies:** Every `tcgen05.commit`, either cta_group, whatever its target mask

**Premises:** Every CTA of the issuer's CTA group exists.

**Effect:** Safety rejection. The issuing CTA group must exist whatever the target mask. The lifetimes of the target CTAs (each arrival is a use of its mbarrier's CTA) and of the CTA group (the issue is a use of each of its CTAs) are ERR-SHARED-LIFETIME. Every target is an mbarrier operand of the commit (`UsesMbar`): its initialization is ERR-MBAR-UNINITIALIZED and its storage ERR-UNALLOCATED-ACCESS. Once delivered, ObjectPublished and the checked object history select the exact initialized lifetime and phase.

</details>
