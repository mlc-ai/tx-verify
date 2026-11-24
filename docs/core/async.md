# Asynchronous copies and tensor maps

How the model treats the asynchronous engine: bulk copies and tensor copies (TMA), tensor maps and their geometry, multicast, bulk groups and their waits, tensor stores and reductions, and the safety checks that apply to them. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [Linear bulk copies](#linear-bulk-copies)
    - [`AsyncCopy.Notification`](#c-asynccopy-notification)
    - [`AsyncCopy.CopyOk`](#c-asynccopy-copyok)
    - [`TmaOk`](#c-tmaok)
  - [Bulk groups](#bulk-groups)
    - [`BulkGroup.WaitMode`](#c-bulkgroup-waitmode)
    - [`BulkGroup.State`](#c-bulkgroup-state)
    - [`BulkGroup.Action`](#c-bulkgroup-action)
    - [`BulkGroup.Done`](#c-bulkgroup-done)
    - [`BulkGroup.WaitReady`](#c-bulkgroup-waitready)
    - [`BulkWaitsFor`](#c-bulkwaitsfor)
    - [`GroupWaitStages`](#c-groupwaitstages)
  - [Tensor maps](#tensor-maps)
    - [`TensorDescriptor.Format`](#c-tensordescriptor-format)
    - [`TensorDescriptor.Fill`](#c-tensordescriptor-fill)
    - [`TensorDescriptor.Descriptor`](#c-tensordescriptor-descriptor)
    - [`TensorDescriptor.Valid`](#c-tensordescriptor-valid)
    - [`TensorDescriptor.BoxAligned`](#c-tensordescriptor-boxaligned)
  - [Tensor geometry](#tensor-geometry)
    - [`TensorAddress.Geometry`](#c-tensoraddress-geometry)
    - [`TensorAddress.InBounds`](#c-tensoraddress-inbounds)
    - [`TensorTile.Box`](#c-tensortile-box)
  - [Shared layout](#shared-layout)
    - [`TensorSwizzle.Mode`](#c-tensorswizzle-mode)
    - [`TensorTile.sharedByte`](#c-tensortile-sharedbyte)
  - [The bytes of a transfer](#the-bytes-of-a-transfer)
    - [`TensorTransfer.Slot`](#c-tensortransfer-slot)
    - [`TensorTransfer.Source`](#c-tensortransfer-source)
    - [`TensorTransfer.bytes`](#c-tensortransfer-bytes)
    - [`TensorHasOob`](#c-tensorhasoob)
    - [`TensorBox`](#c-tensorbox)
    - [`requireBoxAligned`](#c-requireboxaligned)
  - [Tensor loads](#tensor-loads)
    - [`TensorCopy.Spec`](#c-tensorcopy-spec)
    - [`TensorCopy.Effects`](#c-tensorcopy-effects)
    - [`TensorCopy.CopyOk`](#c-tensorcopy-copyok)
    - [`TensorCopy.Completion`](#c-tensorcopy-completion)
    - [`TensorCopy.Observation`](#c-tensorcopy-observation)
    - [`TensorOk`](#c-tensorok)
  - [Tensor stores and reductions](#tensor-stores-and-reductions)
    - [`TensorStore.Spec`](#c-tensorstore-spec)
    - [`TensorStore.Valid`](#c-tensorstore-valid)
    - [`TensorStore.Effects`](#c-tensorstore-effects)
    - [`TensorStore.CopyOk`](#c-tensorstore-copyok)
    - [`TensorStore.Observation`](#c-tensorstore-observation)
    - [`TensorStoreOk`](#c-tensorstoreok)
    - [`TensorStore.reduceValue`](#c-tensorstore-reducevalue)
    - [`TensorStore.ReduceOk`](#c-tensorstore-reduceok)
  - [Instruction events](#instruction-events)
    - [`tensorTmpl`](#c-tensortmpl)
    - [`tensorStoreTmpl`](#c-tensorstoretmpl)
  - [Safety](#safety)
    - [`TensorBackingMissing`](#c-tensorbackingmissing)
    - [`TensorAllocationUnsafe`](#c-tensorallocationunsafe)
    - [`TensorUnsafe`](#c-tensorunsafe)
    - [`TensorStoreUnsafe`](#c-tensorstoreunsafe)
- [Rules](#rules)
  - [What the instructions do](#what-the-instructions-do)
    - [issuing a tensor load](#thread-tensor-issue) (`THREAD-TENSOR-ISSUE`)
    - [issuing a tensor-data or linear prefetch](#thread-tensor-prefetch) (`THREAD-TENSOR-PREFETCH`)
      - [a prefetch is an initiated read that stays pending](#ext-prefetch-pending) (`EXT-PREFETCH-PENDING`)
    - [output tensor issue and bulk-group instructions](#thread-tensor-store) (`THREAD-TENSOR-STORE`)
    - [cp.async, its groups and cp.async.mbarrier.arrive](#thread-cp-async) (`THREAD-CP-ASYNC`)
    - [st.async and red.async](#thread-async-store) (`THREAD-ASYNC-STORE`)
      - [the destination CTA of st.async](#ext-st-async-cta) (`EXT-ST-ASYNC-CTA`)
  - [Tensor maps and geometry](#tensor-maps-and-geometry)
    - [non-interleaved tiled descriptor properties](#thread-tensor-descriptor) (`THREAD-TENSOR-DESCRIPTOR`)
      - [a misaligned box start traps](#ext-tma-box-align) (`EXT-TMA-BOX-ALIGN`)
    - [global tensor coordinates and byte addresses](#thread-tensor-global-address) (`THREAD-TENSOR-GLOBAL-ADDRESS`)
    - [tiled bounding-box traversal](#thread-tensor-tile) (`THREAD-TENSOR-TILE`)
    - [tiled shared layout](#thread-tensor-tile-shared) (`THREAD-TENSOR-TILE-SHARED`)
      - [tiled tensor geometry and descriptor limits from the CUDA Driver API](#ext-tma-geometry) (`EXT-TMA-GEOMETRY`)
    - [16-byte-atom tensor shared-memory swizzles](#thread-tensor-swizzle) (`THREAD-TENSOR-SWIZZLE`)
    - [byte correspondence for a tensor load](#thread-tensor-transfer-map) (`THREAD-TENSOR-TRANSFER-MAP`)
      - [the four rows of `.tile::gather4`](#ext-tma-gather4) (`EXT-TMA-GATHER4`)
      - [the four rows of `.tile::scatter4`](#ext-tma-scatter4) (`EXT-TMA-SCATTER4`)
  - [Which executions are allowed](#which-executions-are-allowed)
    - [independent effects of asynchronous operations](#dep-async-stages) (`DEP-ASYNC-STAGES`)
    - [thread and asynchronous memory accesses](#mem-footprint) (`MEM-FOOTPRINT`)
    - [independent asynchronous effects and object histories](#dep-async-origin) (`DEP-ASYNC-ORIGIN`)
    - [effects and completion of a linear copy](#dep-linear-copy-effects) (`DEP-LINEAR-COPY-EFFECTS`)
    - [tensor effects belong to actual instruction instances](#dep-tensor-load-origin) (`DEP-TENSOR-LOAD-ORIGIN`)
    - [CTA-group identities and tensor completion routing](#prog-cta-group) (`PROG-CTA-GROUP`)
    - [independent tensor byte effects and completion](#dep-tensor-load-effects) (`DEP-TENSOR-LOAD-EFFECTS`)
    - [scalar byte adapters for tensor effects](#dep-tensor-load-bytes) (`DEP-TENSOR-LOAD-BYTES`)
    - [tensor shared-to-global addresses and independent effects](#dep-tensor-store-effects) (`DEP-TENSOR-STORE-EFFECTS`)
      - [out-of-bounds elements of a tensor store are not written](#ext-tma-store-oob) (`EXT-TMA-STORE-OOB`)
      - [tensor reductions use the store's layout](#ext-tma-reduce) (`EXT-TMA-REDUCE`)
    - [output tensor byte footprints and observed values](#dep-tensor-store-bytes) (`DEP-TENSOR-STORE-BYTES`)
    - [reduced values of tensor reduction elements](#dep-reduction-values) (`DEP-REDUCTION-VALUES`)
      - [the operations of a tensor reduction](#ext-tma-reduce-op) (`EXT-TMA-REDUCE-OP`)
      - [a tensor reduction element is one atomic operation](#ext-tma-reduce-atomic) (`EXT-TMA-REDUCE-ATOMIC`)
    - [per-thread bulk async-group membership and waits](#obj-bulk-group) (`OBJ-BULK-GROUP`)
    - [bulk groups of actual thread instruction instances](#obj-bulk-group-trace) (`OBJ-BULK-GROUP-TRACE`)
    - [actual output effects and what a group wait covers](#dep-bulk-wait) (`DEP-BULK-WAIT`)
  - [What counts as an error](#what-counts-as-an-error)
    - [overlapping cp.async destinations in one group](#err-cp-async-overlap) (`ERR-CP-ASYNC-OVERLAP`)
    - [the destination range of a masked bulk copy](#err-bulk-mask-range) (`ERR-BULK-MASK-RANGE`)
    - [tensor load value adapters](#err-tensor-fill-value) (`ERR-TENSOR-FILL-VALUE`)
    - [tensor and linear reduction rules](#err-reduction-no-rule) (`ERR-REDUCTION-NO-RULE`)
    - [large allocation-class OOB backing requirement](#err-tensor-large-oob) (`ERR-TENSOR-LARGE-OOB`)
  - [Representation of growth and progress](#representation-of-growth-and-progress)
    - [extension preserves asynchronous observations](#correct-async-grow) (`CORRECT-ASYNC-GROW`)
    - [count the independent effects of one tensor copy](#correct-tensor-size) (`CORRECT-TENSOR-SIZE`)
    - [count output-copy effects and completion stages](#correct-tensor-store-size) (`CORRECT-TENSOR-STORE-SIZE`)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### Linear bulk copies

The recorded effects of a linear bulk copy and how they grow.

<a id="c-asynccopy-notification"></a>
#### `AsyncCopy.Notification`

*def*

One actual completion notification; issue or destination write alone do not signal.

[Lean source: `Core/Async/AsyncCopy.lean` L122-L126](../../Core/Async/AsyncCopy.lean#L122-L126)

<a id="c-asynccopy-copyok"></a>
#### `AsyncCopy.CopyOk`

*def*

The effects `e` of the linear operation `s` are valid: the source is at most as large as the
destination, only a memory source is read and the bytes read have its size, a whole write writes
the source bytes (`sourceBytes`), the write stage of an element-wise operation is present only after
every element is written and records no bytes, a completion notification belongs to an mbarrier
completion and implies that the write stage is present, and the element effects are valid.

[Lean source: `Core/Async/AsyncCopy.lean` L88-L100](../../Core/Async/AsyncCopy.lean#L88-L100)

<a id="c-tmaok"></a>
#### `TmaOk`

*def*

Every recorded linear copy, MMA completion, `cp.async.mbarrier.arrive` arrive-on and mbarrier
history of the execution `X` is valid: effects belong to actual issues, and each object record
follows from the object operations.

[Lean source: `Core/Async/Tma.lean` L393-L398](../../Core/Async/Tma.lean#L393-L398)

### Bulk groups

Per-thread grouping of bulk operations and the waits on groups.

<a id="c-bulkgroup-waitmode"></a>
#### `BulkGroup.WaitMode`

*inductive*

The form of a `cp.async.bulk.wait_group`: `read` waits for the covered operations to finish
reading their sources, `full` waits for them to complete, and `asyncProxy` requires the same
completion as `full` but grants no generic-proxy visibility.

- `read`
- `full`
- `asyncProxy`

[Lean source: `Core/Async/BulkGroup.lean` L52-L57](../../Core/Async/BulkGroup.lean#L52-L57)

<a id="c-bulkgroup-state"></a>
#### `BulkGroup.State`

*structure*

The grouping state of one thread: its issued operations that are not yet committed, and its
committed groups in commit order.

- `pending`
- `groups`

[Lean source: `Core/Async/BulkGroup.lean` L59-L64](../../Core/Async/BulkGroup.lean#L59-L64)

<a id="c-bulkgroup-action"></a>
#### `BulkGroup.Action`

*inductive*

A bulk-group action of a thread: issuing an operation, `cp.async.bulk.commit_group`, or
`cp.async.bulk.wait_group` with its mode and the number of most recent groups it leaves out.

- `issue`
- `commit`
- `wait`

[Lean source: `Core/Async/BulkGroup.lean` L66-L72](../../Core/Async/BulkGroup.lean#L66-L72)

<a id="c-bulkgroup-done"></a>
#### `BulkGroup.Done`

*def*

The operation `id` is finished for a wait mode: a read wait needs its reads finished, and a
full or async-proxy wait needs its reads finished and the operation complete.

[Lean source: `Core/Async/BulkGroup.lean` L100-L104](../../Core/Async/BulkGroup.lean#L100-L104)

<a id="c-bulkgroup-waitready"></a>
#### `BulkGroup.WaitReady`

*def*

A wait can complete: every operation it covers is done for its mode.

[Lean source: `Core/Async/BulkGroup.lean` L106-L108](../../Core/Async/BulkGroup.lean#L106-L108)

<a id="c-bulkwaitsfor"></a>
#### `BulkWaitsFor`

*def*

The bulk operation `operation` is covered by the wait event `waiter` of mode `mode`: it belongs
to a group that the wait observes in the state before it.

[Lean source: `Core/Async/BulkExecution.lean` L59-L63](../../Core/Async/BulkExecution.lean#L59-L63)

<a id="c-groupwaitstages"></a>
#### `GroupWaitStages`

*def*

The stages of the operation issued by `i` that a group wait of kind `k` covering it waits for:
the read completion of a tensor store or the read of a linear copy for a `.read` wait, and both
completions otherwise.

[Lean source: `Core/Async/BulkExecution.lean` L281-L289](../../Core/Async/BulkExecution.lean#L281-L289)

### Tensor maps

The descriptor of a tiled tensor.

<a id="c-tensordescriptor-format"></a>
#### `TensorDescriptor.Format`

*inductive*

The element type of a tensor map.

- `u8`
- `u16`
- `u32`
- `s32`
- `u64`
- `s64`
- `f16`
- `bf16`
- `f32`
- `f64`

[Lean source: `Core/Async/Tensor/TensorDescriptor.lean` L68-L71](../../Core/Async/Tensor/TensorDescriptor.lean#L68-L71)

<a id="c-tensordescriptor-fill"></a>
#### `TensorDescriptor.Fill`

*inductive*

The value written for an out-of-bounds element of a tensor load: zero, or NaN (floating-point
element types only).

- `zero`
- `oobNan`

[Lean source: `Core/Async/Tensor/TensorDescriptor.lean` L83-L87](../../Core/Async/Tensor/TensorDescriptor.lean#L83-L87)

<a id="c-tensordescriptor-descriptor"></a>
#### `TensorDescriptor.Descriptor`

*structure*

A tiled tensor map of `outer + 1` axes: the element format, the global base address, the extent
of each axis, the byte strides of the outer axes, the bounding box, the swizzle mode, the
out-of-bounds fill and the allocation class.

- `format`
- `base`
- `extent`
- `outerStride`
- `box`
- `swizzle`
- `fill`
- `allocationClass`

[Lean source: `Core/Async/Tensor/TensorDescriptor.lean` L94-L105](../../Core/Async/Tensor/TensorDescriptor.lean#L94-L105)

<a id="c-tensordescriptor-valid"></a>
#### `TensorDescriptor.Valid`

*def*

The descriptor obeys the limits of the host API that creates tensor maps: rank, alignment,
extents, strides, box sizes, traversal strides, swizzle fit and fill mode.

[Lean source: `Core/Async/Tensor/TensorDescriptor.lean` L112-L123](../../Core/Async/Tensor/TensorDescriptor.lean#L112-L123)

<a id="c-tensordescriptor-boxaligned"></a>
#### `TensorDescriptor.BoxAligned`

*def*

The bounding box's global start is 16-byte aligned (§5.5.3.1). Base and outer strides are
multiples of 16 (`Valid`), so this is the innermost coordinate's byte offset (EXT-TMA-BOX-ALIGN).

[Lean source: `Core/Async/Tensor/TensorDescriptor.lean` L135-L138](../../Core/Async/Tensor/TensorDescriptor.lean#L135-L138)

### Tensor geometry

Global addresses and the elements a bounding box selects.

<a id="c-tensoraddress-geometry"></a>
#### `TensorAddress.Geometry`

*structure*

The geometry of a global tensor of `rank` axes, fastest first: its base address, the byte size
of an element, and for each axis the extent in elements and the stride in bytes.

- `base`
- `elementBytes`
- `extent`
- `stride`

[Lean source: `Core/Async/Tensor/TensorAddress.lean` L38-L44](../../Core/Async/Tensor/TensorAddress.lean#L38-L44)

<a id="c-tensoraddress-inbounds"></a>
#### `TensorAddress.InBounds`

*def*

The coordinate lies inside the tensor: on every axis it is nonnegative and below the extent.

[Lean source: `Core/Async/Tensor/TensorAddress.lean` L46-L48](../../Core/Async/Tensor/TensorAddress.lean#L46-L48)

<a id="c-tensortile-box"></a>
#### `TensorTile.Box`

*structure*

A bounding box of `rank` axes: for each axis, the number of elements it spans and the traversal
stride with which elements are selected.

- `size`
- `traversal`

[Lean source: `Core/Async/Tensor/TensorTile.lean` L36-L40](../../Core/Async/Tensor/TensorTile.lean#L36-L40)

### Shared layout

Where a selected element lies in shared memory.

<a id="c-tensorswizzle-mode"></a>
#### `TensorSwizzle.Mode`

*inductive*

The swizzle mode of a shared tile: no swizzle, or the 32, 64 or 128 byte swizzle.

- `none`
- `b32`
- `b64`
- `b128`

[Lean source: `Core/Async/Tensor/TensorSwizzle.lean` L41-L44](../../Core/Async/Tensor/TensorSwizzle.lean#L41-L44)

<a id="c-tensortile-sharedbyte"></a>
#### `TensorTile.sharedByte`

*def*

The shared address of byte `byte` of the element at `column` of row `row` of a tile based at
`base`: the base plus the swizzled offset of the byte.

[Lean source: `Core/Async/Tensor/TensorTile.lean` L180-L184](../../Core/Async/Tensor/TensorTile.lean#L180-L184)

### The bytes of a transfer

The bytes that one tensor transfer moves.

<a id="c-tensortransfer-slot"></a>
#### `TensorTransfer.Slot`

*abbrev*

One byte of one element that a tensor box selects: the element's column, its row (the
combination of its outer-axis indices) and the byte within the element.

[Lean source: `Core/Async/Tensor/TensorTransfer.lean` L92-L95](../../Core/Async/Tensor/TensorTransfer.lean#L92-L95)

<a id="c-tensortransfer-source"></a>
#### `TensorTransfer.Source`

*inductive*

Where a byte of a tensor load comes from: a global address, or the out-of-bounds fill of the
descriptor for a byte of the given format.

- `global`
- `fill`

[Lean source: `Core/Async/Tensor/TensorTransfer.lean` L107-L112](../../Core/Async/Tensor/TensorTransfer.lean#L107-L112)

<a id="c-tensortransfer-bytes"></a>
#### `TensorTransfer.bytes`

*def*

The number of bytes a tensor transfer moves: the selected elements times the element size,
including out-of-bounds elements and excluding shared padding.

[Lean source: `Core/Async/Tensor/TensorTransfer.lean` L131-L134](../../Core/Async/Tensor/TensorTransfer.lean#L131-L134)

<a id="c-tensorhasoob"></a>
#### `TensorHasOob`

*def*

Some element the transfer selects is outside the tensor (§5.5.3.3).

[Lean source: `Core/Async/Tensor/TensorTransfer.lean` L140-L145](../../Core/Async/Tensor/TensorTransfer.lean#L140-L145)

<a id="c-tensorbox"></a>
#### `TensorBox`

*structure*

The tensor box of one tensor load or store: the descriptor of its transfer (four-row modes:
the map's with four rows, `Descriptor.fourRows`), the signed origin, the shared base and, in
four-row mode, the tensor row of each box row (EXT-TMA-GATHER4, EXT-TMA-SCATTER4).

- `outer`: Rank minus one (`.1d` .. `.5d`).
- `descriptor`
- `origin`
- `sharedBase`
- `rows`

[Lean source: `Core/Async/Tensor/TensorCopy.lean` L32-L41](../../Core/Async/Tensor/TensorCopy.lean#L32-L41)

<a id="c-requireboxaligned"></a>
#### `requireBoxAligned`

*def*

The bounding box's global start is 16-byte aligned (§5.5.3.1, EXT-TMA-BOX-ALIGN), checked once
when the thread issues a tensor load, store, reduction or prefetch: a box whose start is not aligned
is undefined behaviour (`misaligned`), so no issue event records such a box. The check takes the
descriptor and origin that a `TensorBox` or the elements of a prefetch record.

[Lean source: `Core/Async/Tensor/TensorCopy.lean` L56-L62](../../Core/Async/Tensor/TensorCopy.lean#L56-L62)

### Tensor loads

The specification and recorded effects of a tensor load.

<a id="c-tensorcopy-spec"></a>
#### `TensorCopy.Spec`

*structure*

A tensor load: its box, the mbarrier it signals, whether its addresses are cluster addresses,
and its CTA group.

- `mbar`
- `clusterAddress`
- `group`

[Lean source: `Core/Async/Tensor/TensorCopy.lean` L120-L125](../../Core/Async/Tensor/TensorCopy.lean#L120-L125)

<a id="c-tensorcopy-effects"></a>
#### `TensorCopy.Effects`

*structure*

The recorded effects of one tensor load: the source read and the destination write of each slot,
and whether the completion notification has occurred.

- `read`
- `write`
- `notified`

[Lean source: `Core/Async/Tensor/TensorCopy.lean` L138-L143](../../Core/Async/Tensor/TensorCopy.lean#L138-L143)

<a id="c-tensorcopy-copyok"></a>
#### `TensorCopy.CopyOk`

*structure*

The effects obey the rules of a tensor load: only in-bounds slots are read, each write copies
its read or carries the fill, and a notification implies that every slot is written.

- `reads`
- `writes`
- `complete`

[Lean source: `Core/Async/Tensor/TensorCopy.lean` L152-L160](../../Core/Async/Tensor/TensorCopy.lean#L152-L160)

<a id="c-tensorcopy-completion"></a>
#### `TensorCopy.Completion`

*def*

The notification of the copy has occurred, it targets the mbarrier of the copy, and it signals
the number of bytes of the transfer.

[Lean source: `Core/Async/Tensor/TensorCopy.lean` L162-L165](../../Core/Async/Tensor/TensorCopy.lean#L162-L165)

<a id="c-tensorcopy-observation"></a>
#### `TensorCopy.Observation`

*structure*

The spec is frozen with the effects of one actual instruction instance.

- `spec`
- `effects`

[Lean source: `Core/Async/Tensor/TensorCopy.lean` L174-L177](../../Core/Async/Tensor/TensorCopy.lean#L174-L177)

<a id="c-tensorok"></a>
#### `TensorOk`

*def*

Every recorded tensor load of `X` belongs to an actual issue and has a valid descriptor, valid
effects and valid routing.

[Lean source: `Core/Async/Tensor/TensorExecution.lean` L37-L44](../../Core/Async/Tensor/TensorExecution.lean#L37-L44)

### Tensor stores and reductions

The specification and recorded effects of a tensor store or reduction.

<a id="c-tensorstore-spec"></a>
#### `TensorStore.Spec`

*structure*

A tensor store or reduction: its box, with the shared source, and the reduction operation, if
the instruction is `cp.reduce.async.bulk.tensor`.

- `reduce`: `cp.reduce.async.bulk.tensor`: the reduction; `none`: a store.

[Lean source: `Core/Async/Tensor/TensorStore.lean` L98-L102](../../Core/Async/Tensor/TensorStore.lean#L98-L102)

<a id="c-tensorstore-valid"></a>
#### `TensorStore.Valid`

*def*

The store is a valid issue by the CTA `issuerCta`: a valid descriptor, nonnegative coordinates,
and a 128-byte aligned shared source in the issuer's own CTA.

[Lean source: `Core/Async/Tensor/TensorStore.lean` L113-L118](../../Core/Async/Tensor/TensorStore.lean#L113-L118)

<a id="c-tensorstore-effects"></a>
#### `TensorStore.Effects`

*structure*

The recorded effects of one tensor store or reduction: the shared read, the global write and
(for a reduction) the old global byte read of each slot, and whether read completion and full
completion have occurred.

- `read`
- `write`
- `readsDone`
- `fullDone`
- `old`: A reduction's read of the old destination byte it reduces.

[Lean source: `Core/Async/Tensor/TensorStore.lean` L125-L134](../../Core/Async/Tensor/TensorStore.lean#L125-L134)

<a id="c-tensorstore-copyok"></a>
#### `TensorStore.CopyOk`

*structure*

The effects obey the rules of a tensor store: written slots lie in bounds and were read, a store
writes the byte it read, read completion implies every in-bounds slot was read, full completion
implies all writes, and a reduction writes all bytes of an element together with their old bytes.

- `writes`
- `readsComplete`
- `complete`
- `element`: A reduction writes all bytes of an element together, each with its old byte.
- `old`: Only a reduction reads old destination bytes, and only with the element's write.

[Lean source: `Core/Async/Tensor/TensorStore.lean` L136-L152](../../Core/Async/Tensor/TensorStore.lean#L136-L152)

<a id="c-tensorstore-observation"></a>
#### `TensorStore.Observation`

*structure*

The frozen specification of one actual tensor store with its effects so far.

- `spec`
- `effects`

[Lean source: `Core/Async/Tensor/TensorStore.lean` L163-L166](../../Core/Async/Tensor/TensorStore.lean#L163-L166)

<a id="c-tensorstoreok"></a>
#### `TensorStoreOk`

*def*

Every recorded tensor store observation of `X` is the effect of an actual store issue, has a
valid specification and obeys the effect rules of a tensor store.

[Lean source: `Core/Async/BulkExecution.lean` L261-L267](../../Core/Async/BulkExecution.lean#L261-L267)

<a id="c-tensorstore-reducevalue"></a>
#### `TensorStore.reduceValue`

*def*

The reduced element from the old destination bytes and the source bytes: the value of
THREAD-ATOMIC-OP for the element's operation and type.

[Lean source: `Core/Async/Tensor/TensorReduce.lean` L151-L157](../../Core/Async/Tensor/TensorReduce.lean#L151-L157)

<a id="c-tensorstore-reduceok"></a>
#### `TensorStore.ReduceOk`

*structure*

The reductions of the execution `X`, tensor and linear, write the reduced values. Their
atomicity is MEM-ATOMICITY.

- `values`
- `copies`

[Lean source: `Core/Async/Tensor/TensorReduce.lean` L243-L247](../../Core/Async/Tensor/TensorReduce.lean#L243-L247)

### Instruction events

The events that tensor and bulk-group instructions produce.

<a id="c-tensortmpl"></a>
#### `tensorTmpl`

*def*

The event of a tensor load: one issue, or for a multicast load one issue per destination CTA.

[Lean source: `Core/Async/Tensor/TensorThread.lean` L118-L132](../../Core/Async/Tensor/TensorThread.lean#L118-L132)

<a id="c-tensorstoretmpl"></a>
#### `tensorStoreTmpl`

*def*

The event of a tensor store, a tensor reduction, `cp.async.bulk.commit_group` or
`cp.async.bulk.wait_group`.

[Lean source: `Core/Async/Tensor/TensorThread.lean` L322-L330](../../Core/Async/Tensor/TensorThread.lean#L322-L330)

### Safety

The conditions that make a tensor operation unsafe.

<a id="c-tensorbackingmissing"></a>
#### `TensorBackingMissing`

*def*

An access that selects the elements of `origin` and `rows` through the map `d` has a large-class
map, selects an out-of-bounds element and has no accessible range behind the tensor base. A tensor
load and a store (`TensorBox`) and a prefetch record these three fields.

[Lean source: `Core/Async/Tensor/TensorAllocation.lean` L50-L56](../../Core/Async/Tensor/TensorAllocation.lean#L50-L56)

<a id="c-tensorallocationunsafe"></a>
#### `TensorAllocationUnsafe`

*def*

Some tensor load, store or prefetch with a large-class map selects an out-of-bounds element and
the range behind the tensor base is not accessible.

[Lean source: `Core/Async/Tensor/TensorAllocation.lean` L58-L66](../../Core/Async/Tensor/TensorAllocation.lean#L58-L66)

<a id="c-tensorunsafe"></a>
#### `TensorUnsafe`

*def*

Some tensor load writes a byte without a scalar value.

[Lean source: `Core/Async/Tensor/TensorSafety.lean` L36-L39](../../Core/Async/Tensor/TensorSafety.lean#L36-L39)

<a id="c-tensorstoreunsafe"></a>
#### `TensorStoreUnsafe`

*def*

A performed element of a tensor or linear reduction has no arithmetic rule.

[Lean source: `Core/Async/Tensor/TensorSafety.lean` L64-L66](../../Core/Async/Tensor/TensorSafety.lean#L64-L66)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### What the instructions do

The events of tensor loads, prefetches, stores, reductions and bulk-group instructions.

<a id="thread-tensor-issue"></a>
#### issuing a tensor load (`THREAD-TENSOR-ISSUE`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorThread.lean` L11-L55](../../Core/Async/Tensor/TensorThread.lean#L11-L55)

A tensor load produces one issue event that records the descriptor, the signed 32-bit origin, the shared destination and the mbarrier, and it produces no data write and no completion. A multicast load issues one copy to each destination CTA of its mask in rank order, each with its own destination and mbarrier at the same offsets. The optional cache policy must be a defined value and does not change any event. An operand that fails the alignment, map, mask or routing checks, or whose box start is not 16-byte aligned (`requireBoxAligned`, DEP-TENSOR-LOAD-EFFECTS), produces an undefined-behaviour event.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`tensorMulticast`](../../Core/Async/Tensor/TensorThread.lean#L57-L75), [`tensorLoadCopy`](../../Core/Async/Tensor/TensorThread.lean#L77-L92), [`tensorLoadCopy_boxAligned`](../../Core/Async/Tensor/TensorThread.lean#L94-L111), [`cachePolicyRead`](../../Core/Async/Tensor/TensorThread.lean#L113-L116), [`tensorTmpl`](../../Core/Async/Tensor/TensorThread.lean#L118-L132) ([concept](#c-tensortmpl))

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.3 (cache hint): "When the optional argument cache_policy is specified, the qualifier
    .level::cache_hint is required. The 64-bit operand cache_policy specifies the cache eviction
    policy that may be used during the memory access. cache_policy is a hint to the cache subsystem
    and may not always be respected. It is treated as a performance hint only, and does not change
    the memory consistency behavior of the program."
- §5.5.3.4
- CUDA Driver API cuTensorMapEncodeTiled
- EXT-TMA-GEOMETRY (64-byte map and 128-byte shared alignment)

**Applies:** 1D–5D tiled and 2D `.tile::gather4` global-to-shared loads, including `.multicast::cluster` and `.L2::cache_hint`, using immutable host-published tensor maps

**Premises:** The cache policy, when present, is a defined 64-bit value (`cachePolicyRead`, as for stores and prefetches). The box start is 16-byte aligned (`requireBoxAligned`). Map address is 64-byte aligned and resolves in Launch.tensorMaps to a descriptor of the instruction's rank (gather4: a 2D map whose box dimension 1 is one, EXT-TMA-GATHER4). Descriptor properties, shared alignment and CTA-group routing pass their checks; a multicast load's own `dstMem` and `mbar` operands pass the same routing check as a non-multicast load's, so `mbar` is in the CTA group of `dstMem` (§9.7.10.28.5.3: "When .cta_group::1 is specified, the mbarrier object mbar that is specified must be in the shared memory of the same CTA as the shared memory destination dstMem"; with `.cta_group::2`, "either the same CTA as the shared memory destination dstMem or in its peer-CTA") before the copies are fanned out.

**Effect:** Thread event construction. Dynamic descriptor mutation/publication is not modeled by the launch map. A gather4 load records the map's descriptor with four rows (`Descriptor.fourRows`), the origin `(x, y0)` and the four row coordinates. A multicast load names at most the cluster's ranks in `ctaMask` and issues its copies through sub-steps, and with `.cta_group::2` it signals the pair CTA with the parity of the CTA of `mbar` (§9.7.10.28.5.3). Each copy reads the source itself, which over-approximates the single read of the hardware by allowing a separate read per destination. Launch.tensorMaps is launch data justified by host descriptor creation and publication (EXT-LAUNCH); it is not an arbitrary predicate guaranteeing the copy's result.

</details>

<a id="thread-tensor-prefetch"></a>
#### issuing a tensor-data or linear prefetch (`THREAD-TENSOR-PREFETCH`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorThread.lean` L134-L195](../../Core/Async/Tensor/TensorThread.lean#L134-L195)

A tensor prefetch produces one event that records the map and the elements it selects, and a linear prefetch one event that records its global range; the thread continues with its registers unchanged. The event is a pending weak read, through the async proxy, of each in-bounds selected global byte or of the range (EXT-PREFETCH-PENDING). A box start that is not 16-byte aligned, and a linear range whose address is not 16-byte aligned or whose size is not a multiple of 16, produce an undefined-behaviour event.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`tensorPrefetchTmpl`](../../Core/Async/Tensor/TensorThread.lean#L230-L248)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is a non-blocking instruction which may initiate an
    asynchronous prefetch of tensor data from the location in .src statespace to the L2 cache."
- §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.10.28.5.5 (`.tile` or `.tile::gather4`)
- §8.6: "Operations using methods of access distinct from the generic method include: … async-proxy
    and tensormap-proxy accesses by .async.bulk operations"
- §9.7.10.28.1: "This section describes two asynchronous copy operation completion mechanisms
    supported in PTX: Async-group mechanism and mbarrier-based mechanism."
- EXT-PREFETCH-PENDING (always initiated, never complete)
- §5.5.3.1: "The address of the bounding Box must also be aligned to 16 bytes."
- §9.7.10.28.4.3: "cp.async.bulk.prefetch is a non-blocking instruction which may initiate an
    asynchronous prefetch of data from the location specified by source address operand srcMem , in
    .src statespace, to the L2 cache."
- §9.7.10.28.4.3: "size must be a multiple of 16. If the value is not a multiple of 16, then the
    behavior is undefined. The address srcMem must be aligned to 16 bytes."
- §9.7.10.28.4.3: "cp.async.bulk.prefetch is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.10.28.4.3: "Qualifier .level::eviction_priority specifies the eviction priority to be applied
    for the prefetched cache line."
- §5.5.3.3: "If a TMA operation performs an out-of-boundary access and the tensor-map object’s
    allocation class (see tensormap.replace ) is large, but the memory range [global_addr,
    global_addr + CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE) is not accessible, the
    behavior is undefined."

**Applies:** cp.async.bulk.prefetch.tensor.{1..5}d.L2.global{.tile, .tile::gather4}{.L2::cache_hint, .L2::evict_last} with an immutable host-published map; cp.async.bulk.prefetch.L2.global {.L2::cache_hint, .L2::evict_last}

**Premises:** The map passes the checks of a tensor load of the same mode (64-byte alignment, a published valid descriptor of the instruction's rank, gather4's 2D map with box dimension 1 one), the coordinates and cache policy are defined 32- and 64-bit values, and the box start is 16-byte aligned (`BoxAligned`). A linear prefetch's address is 16-byte aligned and its size a multiple of 16.

**Effect:** Thread event construction. The read is the pending read of EXT-PREFETCH-PENDING: it is never present and never completes, returns no value (so no read-from or value constraint applies), and is checked against overlapping writes (ERR-DATA-RACE, ERR-MIXED-SIZE; a write is exempt only if `modelCausality` orders it before the read, MEM-MODEL-CAUSALITY, and a generic-proxy write of a global byte never is, since that rule has no global proxy fence) and for allocation (ERR-UNALLOCATED-ACCESS). The event has no mbarrier or bulk-group action and no completion to wait for. The eviction priority `.L2::evict_last` is a cache hint without effect. im2col modes, overrides and device-updated descriptors are outside this rule. The tensor-map read through the tensormap proxy is not represented: maps are immutable launch data. The event records the elements as a tensor load of the same mode records them: the transfer descriptor (for gather4 the map's descriptor with four rows), the signed 32-bit origin and the row coordinates. The read has the footprint of a tensor load's source read of the same selection (`.read (.prefetch ..)`, MEM-FOOTPRINT). Whether a large-class map with an out-of-bounds element has its backing range is decided on the execution (ERR-TENSOR-LARGE-OOB), where launch memory is visible.

</details>

<a id="ext-prefetch-pending"></a>
##### a prefetch is an initiated read that stays pending (`EXT-PREFETCH-PENDING`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorThread.lean` L197-L228](../../Core/Async/Tensor/TensorThread.lean#L197-L228)

The model treats every tensor or linear prefetch as an initiated read, through the async proxy, of the selected in-bounds global bytes or of the range. The read returns no value and never completes.

Source:

- - §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is a non-blocking instruction which may initiate an asynchronous prefetch of tensor data from the location in .src statespace to the L2 cache." - §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is treated as a weak memory operation in the Memory Consistency Model ." - §9.7.10.28.4.3: "cp.async.bulk.prefetch is a non-blocking instruction which may initiate an asynchronous prefetch of data from the location specified by source address operand srcMem , in .src statespace, to the L2 cache." - §9.7.10.28.4.3: "cp.async.bulk.prefetch is treated as a weak memory operation in the Memory Consistency Model ." - §8.6: "Operations using methods of access distinct from the generic method include: … async-proxy and tensormap-proxy accesses by .async.bulk operations"

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text says the instruction "may initiate" a prefetch; it does not say whether the access happens or when it ends, and it gives the access no completion mechanism. The model's choice is that the access is always initiated and never complete.

**Effect:** This is a conservative abstraction for safety checking. It does not claim that the hardware access never ends. It makes every write that may overlap the access unordered be reported (ERR-DATA-RACE, ERR-MIXED-SIZE) and requires the in-bounds bytes to be allocated (ERR-UNALLOCATED-ACCESS). It may reject a program whose prefetch the hardware drops or has already completed. It adds no Lean axiom and no Assumption, and `Complete` does not require the read to complete. Disclosed by every kernel whose statement names `Op.prefetchTensor` or `Op.prefetchBulk`: none.

</details>

<a id="thread-tensor-store"></a>
#### output tensor issue and bulk-group instructions (`THREAD-TENSOR-STORE`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorThread.lean` L250-L280](../../Core/Async/Tensor/TensorThread.lean#L250-L280)

A tensor store, a tensor reduction, `cp.async.bulk.commit_group` and `cp.async.bulk.wait_group` each produce one event. A store or reduction records the descriptor, the nonnegative signed origin and the shared source in the issuing CTA, and a reduction also records its operation, which must support the map's element type. An operand that fails the alignment, sign or operation checks, or whose box start is not 16-byte aligned (`requireBoxAligned`, DEP-TENSOR-LOAD-EFFECTS), produces an undefined-behaviour event.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`tensorStoreSpec`](../../Core/Async/Tensor/TensorThread.lean#L282-L301), [`tensorStoreSpec_boxAligned`](../../Core/Async/Tensor/TensorThread.lean#L303-L320), [`tensorStoreTmpl`](../../Core/Async/Tensor/TensorThread.lean#L322-L330) ([concept](#c-tensorstoretmpl))

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.3
- §9.7.10.28.6.1–2
- CUDA Programming Guide §4.13.4 (output coordinates)
- EXT-TMA-GEOMETRY (64-byte map and 128-byte shared alignment)

**Applies:** Non-interleaved 1D–5D tiled and 2D `.tile::scatter4` shared::cta-to-global stores, 1D–5D tiled `cp.reduce.async.bulk.tensor` reductions, commit_group and wait_group

**Premises:** Host-published map (scatter4: 2D with box dimension 1 one, EXT-TMA-SCATTER4), descriptor validity, local shared source, 128-byte alignment and nonnegative signed coordinates (scatter4: all five). Optional cache-policy operand is a defined 64-bit value. The box start is 16-byte aligned (`requireBoxAligned`).

**Effect:** Thread event construction only; operation effects, grouping, blocking and visibility are checked separately. A scatter4 store records the map's descriptor with four rows, the origin `(x, y0)` and the row coordinates. A reduction is a tile-mode operation, and its event records its operation. The read, full and async-only modes of `cp.async.bulk.wait_group` are recorded as distinct modes.

</details>

<a id="thread-cp-async"></a>
#### cp.async, its groups and cp.async.mbarrier.arrive (`THREAD-CP-ASYNC`)

*Rule* · [Lean comment: `Core/Async/CpAsync.lean` L20-L78](../../Core/Async/CpAsync.lean#L20-L78)

A `cp.async` produces one issue event: a copy of `cp-size` bytes from global memory to the executing CTA's shared memory, of which the first `src-size` bytes, or none when `ignore-src` is true, are read and the rest are zeros. `cp.async.commit_group`, `cp.async.wait_group` and `cp.async.mbarrier.arrive` each produce one event, and `cp.async.wait_all` produces a commit event followed by a wait event for no remaining group. A misaligned address or a `src-size` larger than `cp-size` produces an undefined-behaviour event.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`cpAsyncSourceSize`](../../Core/Async/CpAsync.lean#L81-L92), [`cpAsyncTmpl`](../../Core/Async/CpAsync.lean#L94-L116)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.3.1: "Operand src specifies a location in the global state space and dst specifies a
    location in the shared state space."
- §9.7.10.28.3.1: "cp-size can only be 4, 8 and 16."
- §9.7.10.28.3.1: "Operand src-size represents the size of the data in bytes to be copied from src
    to dst and must be less than or equal to cp-size . In such case, remaining bytes in destination
    dst are filled with zeros. Specifying src-size larger than cp-size results in undefined
    behavior."
- §9.7.10.28.3.1: "If the source data is ignored then zeros will be copied to destination dst ."
- §9.7.10.28.3.1: "cp.async is treated as a weak memory operation performed in the generic proxy in
    the Memory Consistency Model ."
- §9.7.10.28.3.1: "Cache operator are treated as performance hints only."
- §9.7.10.28.3.1: "The .level::prefetch_size qualifier is treated as a performance hint only."
- §6.4.1: "The address must be naturally aligned to a multiple of the access size. If an address is
    not properly aligned, the resulting behavior is undefined."
- §9.7.10.28.3.2 (cp.async.commit_group)
- §9.7.10.28.3.3: "cp.async.wait_all is equivalent to : cp.async.commit_group; cp.async.wait_group
    0;"
- §9.7.15.16.18: "Causes an arrive-on operation to be triggered by the system on the mbarrier object
    upon the completion of all prior cp.async operations initiated by the executing thread."
- §9.7.15.16.18: "If no state space is specified then Generic Addressing is used."
- §9.7.15.16.18: "If the address specified by addr does not fall within the address window of
    .shared::cta state space then the behavior is undefined."

**Applies:** `cp.async.{ca,cg}.shared{::cta}.global` with every `cp-size`, with or without `src-size` or `ignore-src`, `.L2::cache_hint` and `.L2::{64B,128B,256B}`; `cp.async.commit_group`, `cp.async.wait_group`, `cp.async.wait_all`; `cp.async.mbarrier.arrive{.noinc}` with `.shared{::cta}` written or with a generic address

**Premises:** The addresses are aligned to `cp-size`, `src-size` is at most `cp-size`, the `ignore-src` operand is a predicate and the cache policy, when present, a defined 64-bit value.

**Effect:** Thread event construction. Grouping, waits, visibility and completion are execution rules. The event of a `cp.async` is a linear copy (`Kind.copy`) whose source is the first `src-size` bytes (all `cp-size` bytes without `src-size`, none when `ignore-src` is true) and whose destination is the `cp-size` bytes at `dst`; its completion mechanism is the non-bulk async-group (`Completion.asyncGroup`), which a later `cp.async.mbarrier.arrive` of the thread may also track, and it is performed in the generic proxy (`generic`). The bytes beyond the source are zeros (DEP-LINEAR-COPY-EFFECTS). Its accesses are weak and use the generic proxy (MEM-MODEL-CAUSALITY). The cache operator `.ca`/`.cg`, the prefetch size and the cache policy have no effect. The alignment rule of §6.4.1 is applied with the access size `cp-size` to both addresses. `cp.async.wait_all` is two events of the same instruction, a commit then a wait leaving no group, through sub-steps, as its stated equivalence says. A `cp.async.mbarrier.arrive` produces one event naming the 8-byte aligned `.shared::cta` mbarrier and whether `.noinc` is written; a generic address must be a generic shared pointer of the executing CTA (`genericSharedLoc`), and any other generic address has no rule; without `.noinc` the event increments the pending count, and its arrive-on is an asynchronous stage (OBJ-MBAR-ORIGIN).

</details>

<a id="thread-async-store"></a>
#### st.async and red.async (`THREAD-ASYNC-STORE`)

*Rule* · [Lean comment: `Core/Async/AsyncStore.lean` L20-L95](../../Core/Async/AsyncStore.lean#L20-L95)

An `st.async` or `red.async` produces one issue event: a linear operation in the generic proxy whose source is the bytes of its register operands and whose destination is the location its address names. The `.mbarrier::complete_tx::bytes` forms write remote shared memory and complete with a complete-tx on their mbarrier; the `.release` forms write global memory with a strong access at their scope and have no completion the thread can observe. A `red.async` reduces its destination element with an atomic read-modify-write. An address outside the required state space or CTA, a misaligned address or an operand of the wrong size produces an undefined-behaviour event.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`asyncStoreTypeOk`](../../Core/Async/AsyncStore.lean#L118-L131), [`asyncReduceOk`](../../Core/Async/AsyncStore.lean#L133-L143), [`asyncStoreLoc`](../../Core/Async/AsyncStore.lean#L145-L154), [`asyncStoreData`](../../Core/Async/AsyncStore.lean#L156-L164), [`asyncStoreTmpl`](../../Core/Async/AsyncStore.lean#L166-L195)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.12 (st.async): "st.async is a non-blocking instruction which initiates an asynchronous
    store operation that stores the value specified by source operand b to the destination memory
    location specified by operand a ."
- §9.7.10.12 (st.async): "st.async is performed in the generic proxy."
- §9.7.10.12 (st.async): "If .ss is not specified, Generic Addressing is used."
- §9.7.10.12 (st.async): "This is a weak store to shared memory, which signals its completion
    through an mbarrier object."
- §9.7.10.12 (st.async): "The shared memory addresses of destination operand a and the mbarrier
    object mbar belong to the same CTA within the same cluster as the executing thread."
- §9.7.10.12 (st.async): "The number of CTAs within the cluster is strictly greater than one;
    %cluster_nctarank > 1 is true."
- §9.7.10.12 (st.async): "If the generic addresses specified do not fall within the address window
    of .shared::cluster state space, the behavior is undefined."
- §9.7.10.12 (st.async): "This is a release store to global memory."
- §9.7.10.12 (st.async): "If the generic address specified does not fall within the address window
    of .global state space, the behavior is undefined."
- §9.7.10.12 (st.async): "For .vec qualifier: .v2 is supported with .b32 , .b64 , .s32 , .s64 , .u32
    , .u64 , .f32 and .f64 types. .v4 qualifier is supported with .b32 , .s32 , .u32 and .f32
    types."
- §9.7.15.7 (red.async): "red.async is a non-blocking instruction which initiates an asynchronous
    reduction operation specified by .op , with the operand b and the value at the destination
    memory location specified by operand a ."
- §9.7.15.7 (red.async): "The complete-tx operation on the mbarrier has .release semantics at
    .cluster scope."
- §9.7.15.7 (red.async): "They belong to the same CTA."
- §9.7.15.7 (red.async): "The CTA to which they belong is different from the CTA of the executing
    thread, but must be within the same cluster."
- §9.7.15.7 (red.async): "When .completion_mechanism is not specified: the completion of the store
    synchronizes with the end of the CTA."
- §6.4.1: "The address must be naturally aligned to a multiple of the access size. If an address is
    not properly aligned, the resulting behavior is undefined."
- EXT-ST-ASYNC-CTA

**Applies:** `st.async{.weak}{.shared::cluster}.mbarrier::complete_tx::bytes{.v2, .v4}.type` and `st.async.release.{gpu,sys}{.global}.type`; `red.async.relaxed.cluster{.shared::cluster} .mbarrier::complete_tx::bytes.op.type` and `red.async.release.{gpu,sys}{.global}.add.type`, each with the operations and types of its syntax; none with `.mmio`

**Premises:** The address and the mbarrier are in the state spaces and CTAs below, the address is aligned to the access size and each value operand has the type's size.

**Effect:** Thread event construction (`Kind.copy`); the write, the reduction, the notification and their order are the execution rules of linear operations. The issue event is a linear operation (`AsyncCopy.Spec`) with an empty source footprint, the concatenated bytes of the value operands as its register source (`data`), the destination of the access size (the type's size times the vector length), and the generic proxy. A `red.async` writes its one element as a reduction (`WriteMode.reduce`, DEP-REDUCTION-VALUES, MEM-ATOMICITY); an `st.async` writes its destination whole. The address is located as a store's (`accessLoc`, THREAD-ADDR) with the instruction's state space, `.shared::cluster` or `.global`, or as a generic address without one, and must fall in the shared or global window the form requires. The `.mbarrier::complete_tx::bytes` forms: the destination and the mbarrier (8-byte aligned) are in one CTA of the executing thread's cluster; for `red.async` that CTA is not the executing one, and for `st.async` the cluster has more than one CTA (EXT-ST-ASYNC-CTA). The completion is the complete-tx on the mbarrier with the destination's byte count (DEP-LINEAR-COPY-EFFECTS). An `st.async` is weak; a `red.async` is a relaxed reduction at `.cluster` scope (`scope`). The `.release` forms: the destination is global; the access is strong at the instruction's scope (`scope`), and it has no completion mechanism (`Completion.unobserved`), so no wait of the model observes it and only the end of the kernel orders it before later accesses (CORRECT-COMPLETE). Their release semantics are not represented: the operation creates no release pattern of MEM-RELEASE-ACQUIRE, which gives fewer synchronization edges than the text and is stricter. The issuer's earlier accesses are ordered before it (§8.9.1.1, MEM-MODEL-CAUSALITY).

</details>

<a id="ext-st-async-cta"></a>
##### the destination CTA of st.async (`EXT-ST-ASYNC-CTA`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/AsyncStore.lean` L97-L115](../../Core/Async/AsyncStore.lean#L97-L115)

The destination and the mbarrier of an `st.async` with mbarrier completion lie in one CTA, which may be any CTA of the executing thread's cluster, including its own.

Source:

- - §9.7.10.12: "The shared memory addresses of destination operand a and the mbarrier object mbar belong to the same CTA within the same cluster as the executing thread."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The sentence can be read as requiring the CTA of the executing thread, or as requiring one CTA of the executing thread's cluster. The model takes the second reading: the destination and the mbarrier share a CTA of the cluster. The requirement "%cluster_nctarank > 1" and the use of `st.async` for distributed shared memory support it.

**Effect:** Wider than the first reading: a store into another CTA of the cluster is accepted. If the first reading holds, such a store is undefined on hardware and the model does not report it. Disclosed by every kernel whose statement names `Op.asyncStore`: none.

</details>

### Tensor maps and geometry

The tensor map, the elements a bounding box selects and their addresses and shared layout.

<a id="thread-tensor-descriptor"></a>
#### non-interleaved tiled descriptor properties (`THREAD-TENSOR-DESCRIPTOR`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorDescriptor.lean` L10-L47](../../Core/Async/Tensor/TensorDescriptor.lean#L10-L47)

A tensor map is accepted only if it obeys the limits of the host API. It has at most five axes and a 16-byte aligned base address. Its extents are positive and at most 2^32, and its outer strides are multiples of 16 below 2^40. Its box sizes are positive and at most 256, its traversal strides are positive and at most 8 with the innermost one equal to one, and the inner box byte size is a multiple of 16 that fits within the swizzle width. The NaN fill is allowed only for floating-point element types.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`TensorDescriptor.Format`](../../Core/Async/Tensor/TensorDescriptor.lean#L68-L71) ([concept](#c-tensordescriptor-format)), [`TensorDescriptor.Format.bytes`](../../Core/Async/Tensor/TensorDescriptor.lean#L73-L77), [`TensorDescriptor.Format.floating`](../../Core/Async/Tensor/TensorDescriptor.lean#L79-L81), [`TensorDescriptor.Fill`](../../Core/Async/Tensor/TensorDescriptor.lean#L83-L87) ([concept](#c-tensordescriptor-fill)), [`TensorDescriptor.AllocationClass`](../../Core/Async/Tensor/TensorDescriptor.lean#L89-L92), [`TensorDescriptor.Descriptor`](../../Core/Async/Tensor/TensorDescriptor.lean#L94-L105) ([concept](#c-tensordescriptor-descriptor)), [`TensorDescriptor.geometry`](../../Core/Async/Tensor/TensorDescriptor.lean#L107-L110), [`TensorDescriptor.Valid`](../../Core/Async/Tensor/TensorDescriptor.lean#L112-L123) ([concept](#c-tensordescriptor-valid)), [`TensorDescriptor.validDecidable`](../../Core/Async/Tensor/TensorDescriptor.lean#L125-L127), [`TensorDescriptor.Descriptor.fourRows`](../../Core/Async/Tensor/TensorDescriptor.lean#L129-L133), [`TensorDescriptor.BoxAligned`](../../Core/Async/Tensor/TensorDescriptor.lean#L135-L138) ([concept](#c-tensordescriptor-boxaligned)), [`TensorDescriptor.boxAlignedDecidable`](../../Core/Async/Tensor/TensorDescriptor.lean#L140-L143)

<details>
<summary>Details for reviewers</summary>

- CUDA Driver API 13.2.1 `cuTensorMapEncodeTiled`
- §5.5.1
- §5.5.3 (§5.5.3.2: dimension-0 traversal stride)
- §5.5.7
- EXT-TMA-GEOMETRY (the numeric limits)

**Applies:** Non-interleaved tiled descriptors with ordinary byte-sized integer/floating types and 16-byte-atom swizzle modes

**Premises:** Host encoding or descriptor-update semantics must supply these properties for the actual opaque descriptor used by the instruction.

**Effect:** Descriptor property validation. The innermost traversal stride is one because §5.5.3.2 says "For non-interleaved layout, the traversal stride in dimension 0 must always be 1". `BoxAligned` is the 16-byte alignment of a box's global start (§5.5.3.1). It is a property of the instruction's coordinates. Unsupported descriptor formats (sub-byte packing, FTZ/TF32 conversion, interleaved, im2col and other swizzle atomicities) are not represented as ordinary copies. The first byte stride is implicit in the host API and derived from the format here. No monotonic ordering of the remaining strides is assumed: split-axis layouts can have a smaller outer stride. Descriptor-storage alignment and address arithmetic bounds are instruction/access checks, not guarantees of this property record.

</details>

<a id="ext-tma-box-align"></a>
##### a misaligned box start traps (`EXT-TMA-BOX-ALIGN`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorDescriptor.lean` L49-L66](../../Core/Async/Tensor/TensorDescriptor.lean#L49-L66)

A tensor load, store or prefetch whose bounding box starts at a global address that is not 16-byte aligned is a fault.

Source:

- - §5.5.3.1 (16-byte alignment of the bounding box's address)

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Evidence:** On a B200, 2D u8 tiled loads (`Tools/probes/tma2d.ptx`) and stores (`Tools/probes/tma2d_store.ptx`) with inner coordinate 4 or 8 fail with an illegal instruction, with or without swizzle, while 0, 16, 32, 48 and -16 complete.

**Effect:** A start that is not 16-byte aligned is a fault of the model, as it is on the probed hardware; the aligned starts are accepted as the text states. Disclosed by every kernel whose statement names `Op.cpTensor`, `Op.cpTensorStore` or `Op.prefetchTensor`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.

</details>

<a id="thread-tensor-global-address"></a>
#### global tensor coordinates and byte addresses (`THREAD-TENSOR-GLOBAL-ADDRESS`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorAddress.lean` L12-L36](../../Core/Async/Tensor/TensorAddress.lean#L12-L36)

The global address of a byte of an element is the tensor base address plus, over the axes, the coordinate times the byte stride, plus the byte's position within the element. A coordinate that is negative or reaches the extent on any axis has no global address.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorAddress.Geometry`](../../Core/Async/Tensor/TensorAddress.lean#L38-L44) ([concept](#c-tensoraddress-geometry)), [`TensorAddress.InBounds`](../../Core/Async/Tensor/TensorAddress.lean#L46-L48) ([concept](#c-tensoraddress-inbounds)), [`TensorAddress.byteAddress`](../../Core/Async/Tensor/TensorAddress.lean#L50-L54), [`TensorAddress.lookup`](../../Core/Async/Tensor/TensorAddress.lean#L56-L60)

<details>
<summary>Details for reviewers</summary>

- §5.5.1 (dimensions and tensor strides)
- §5.5.3.1 (bounding-box origin)
- §5.5.3.3 (out-of-boundary access)
- EXT-TMA-GEOMETRY (the address formula)

**Applies:** Byte-sized, non-interleaved tensor elements, with dimensions ordered fastest first

**Premises:** The descriptor supplies the tensor geometry. Instruction legality, descriptor encoding, traversal selection and address-space allocation are checked separately.

**Effect:** Global address calculation only. The geometry is rank-polymorphic; the consuming ISA operation must check rank 1..5, positive extents, element type, stride alignment/ranges and stride[0] = elementBytes. In particular, returning none is not permission to access an invalid descriptor.

</details>

<a id="thread-tensor-tile"></a>
#### tiled bounding-box traversal (`THREAD-TENSOR-TILE`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorTile.lean` L11-L34](../../Core/Async/Tensor/TensorTile.lean#L11-L34)

Along the innermost axis a bounding box selects consecutive elements, and along every other axis it selects the elements at the origin plus index times the traversal stride. Each axis contributes the box size divided by the traversal stride, rounded up. Whether a selected element lies inside the tensor is checked separately.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorTile.Box`](../../Core/Async/Tensor/TensorTile.lean#L36-L40) ([concept](#c-tensortile-box)), [`TensorTile.step`](../../Core/Async/Tensor/TensorTile.lean#L42-L44), [`TensorTile.count`](../../Core/Async/Tensor/TensorTile.lean#L46-L49), [`TensorTile.coord`](../../Core/Async/Tensor/TensorTile.lean#L51-L55), [`TensorTile.source`](../../Core/Async/Tensor/TensorTile.lean#L57-L63), [`TensorTile.rowsOf`](../../Core/Async/Tensor/TensorTile.lean#L65-L70), [`TensorTile.unflatten`](../../Core/Async/Tensor/TensorTile.lean#L72-L76), [`TensorTile.rows`](../../Core/Async/Tensor/TensorTile.lean#L78-L80), [`TensorTile.indexOf`](../../Core/Async/Tensor/TensorTile.lean#L82-L85)

<details>
<summary>Details for reviewers</summary>

- §5.5.3.1–§5.5.3.3
- CUDA Driver API cuTensorMapEncodeTiled (boxDim and elementStrides)
- EXT-TMA-GEOMETRY

**Applies:** Non-interleaved tiled tensor accesses with byte-sized elements

**Premises:** Descriptor validity checks box sizes and traversal strides. Indices enumerate selected elements. They enumerate no skipped elements and no shared padding.

**Effect:** Selected-element geometry and global source addresses. A valid descriptor's dimension-0 traversal stride is one (THREAD-TENSOR-DESCRIPTOR, §5.5.3.2), so `step` is the traversal stride on every axis of a valid box. Legality and host encoding remain separate from this geometry.

</details>

<a id="thread-tensor-tile-shared"></a>
#### tiled shared layout (`THREAD-TENSOR-TILE-SHARED`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorTile.lean` L87-L116](../../Core/Async/Tensor/TensorTile.lean#L87-L116)

The selected rows of a box, which are the combinations of its outer axes with axis 1 varying fastest, are packed in shared memory with a pitch equal to the inner box byte size, padded up to the swizzle width when the box is narrower. The swizzle permutation is applied to the physical byte offset with the phase of the actual shared base address. Padding bytes are neither written nor counted.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorTile.swizzleWidth`](../../Core/Async/Tensor/TensorTile.lean#L161-L166), [`TensorTile.rowBytes`](../../Core/Async/Tensor/TensorTile.lean#L168-L172), [`TensorTile.linearByte`](../../Core/Async/Tensor/TensorTile.lean#L174-L178), [`TensorTile.sharedByte`](../../Core/Async/Tensor/TensorTile.lean#L180-L184) ([concept](#c-tensortile-sharedbyte))

<details>
<summary>Details for reviewers</summary>

- §5.5.3 (tiled mode)
- §5.5.7 (swizzling)
- CUDA Programming Guide §4.13.2 (inner dimension padding and Table 27)
- EXT-TMA-GEOMETRY

**Applies:** Non-interleaved 1D–5D tiled copies with byte-sized elements and 16-byte-atom swizzles

**Premises:** The consuming instruction checks descriptor legality, shared base alignment, selected indices and byte bounds. For a nonzero swizzle, the inner box byte size is at most its swizzle width.

**Effect:** Shared address geometry only. Padding bytes are not selected copy elements and are not implicitly initialized.

</details>

<a id="ext-tma-geometry"></a>
##### tiled tensor geometry and descriptor limits from the CUDA Driver API (`EXT-TMA-GEOMETRY`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorTile.lean` L118-L159](../../Core/Async/Tensor/TensorTile.lean#L118-L159)

The global address of an element is the base plus, over the axes, the coordinate times the stride, with the first stride the element size. Axis 0 has unit traversal, and axis `i` of a box selects `origin + index * traversalStride_i`, each axis contributing `ceil(boxDim_i / traversalStride_i)` elements. The selected rows of a box (the combinations of the outer axes, axis 1 fastest) are packed in shared memory with a pitch equal to the inner box byte size, padded up to the swizzle width when the box is narrower, the padding being neither written nor counted. The `complete-tx` byte count is the selected elements including out-of-bounds fill and excluding padding. Descriptors outside the numeric limits of the CUDA Driver API are rejected: extents at most 2^32, strides multiples of 16 below 2^40, box sizes at most 256, traversal strides at most 8, inner box byte size a multiple of 16, a tensor map object 64-byte aligned and a shared tile 128-byte aligned.

Source:

- - CUDA Driver API 13.2.1 `cuTensorMapEncodeTiled` (`boxDim`, `elementStrides`, `globalStrides`, `globalDim`) - CUDA C++ Programming Guide §4.13.2 (inner dimension padding, Table 27) - §5.5.1 (strides specify padding) - §5.5.3.1 (bounding box), Figure 8 (address formula) - §5.5.7 (swizzling: the base offset formula uses `(dstMem / 128)`, so it does not require a 128-byte aligned tile) - §5.5.8 (the tensor map object is 128 bytes)

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The PTX text gives dimensions, strides and the bounding box in prose and figures but no coordinate-to-address formula, no traversal-stride element count, no shared pitch or padding rule, no `complete-tx` count for out-of-bounds or padded elements and none of the numeric limits; those are properties of the host API that creates the descriptor. The 64-byte alignment of the map object and the 128-byte alignment of a shared tile have no text at all (§5.5.8 gives the map's size, 128 bytes).

**Evidence:** `Tools/probes/tma2d.ptx` (2D u8 boxes on a B200: swizzles, offsets, padded rows and out-of-bounds origins matched every byte of the model's layout). The geometry for more than two axes, a traversal stride above one and the `complete-tx` count of padded or out-of-bounds elements is not probed.

**Effect:** Reading for the geometry (it decides which bytes move and where); stricter for the limits (they only reject descriptors and issues). Disclosed by every kernel whose statement names `Op.cpTensor`, `Op.cpTensorStore` or `Op.prefetchTensor`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.

</details>

<a id="thread-tensor-swizzle"></a>
#### 16-byte-atom tensor shared-memory swizzles (`THREAD-TENSOR-SWIZZLE`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorSwizzle.lean` L10-L39](../../Core/Async/Tensor/TensorSwizzle.lean#L10-L39)

A swizzle permutes the 16-byte chunks within each 128-byte row of a shared tile by XOR with a value that depends on the row number and on the 128-byte phase of the base address. Bytes within a chunk keep their order. The 128-byte swizzle with 32-byte atomicity permutes the four 32-byte chunks of a row in the same way.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorSwizzle.Mode`](../../Core/Async/Tensor/TensorSwizzle.lean#L41-L44) ([concept](#c-tensorswizzle-mode)), [`TensorSwizzle.sectors`](../../Core/Async/Tensor/TensorSwizzle.lean#L46-L51), [`TensorSwizzle.mask`](../../Core/Async/Tensor/TensorSwizzle.lean#L53-L56), [`TensorSwizzle.chunk`](../../Core/Async/Tensor/TensorSwizzle.lean#L58-L60), [`TensorSwizzle.offset`](../../Core/Async/Tensor/TensorSwizzle.lean#L62-L66), [`TensorSwizzle.offset128x32`](../../Core/Async/Tensor/TensorSwizzle.lean#L68-L71)

<details>
<summary>Details for reviewers</summary>

- §5.5.7 (128 byte swizzle mode, 32-byte atomicity sub-mode): "In this sub-mode, the 32-byte of data
    is kept intact while swizzling. The following table where each element (numbered cell) is 16
    byte shows the swizzling pattern at the destination data layout: 0 1 2 3 4 5 6 7 2 3 0 1 6 7 4 5
    4 5 6 7 0 1 2 3 6 7 4 5 2 3 0 1 … Pattern repeats …"
- CUDA Programming Guide §4.13.2, Table 27

**Applies:** No swizzle and 32/64/128-byte swizzles with 16-byte atoms (`offset`); the 128-byte swizzle with 32-byte atoms (`offset128x32`)

**Premises:** The consuming tensor operation validates shared base alignment and tile layout. The input offset is in the padded, unswizzled shared layout.

**Effect:** Address computation only. A pattern row is 128 physical bytes, which need not be a tensor row. `offset128x32` is the 32-byte-atomicity sub-mode: the four 32-byte chunks of a 128-byte row are permuted by XOR with the row number modulo 4 (the table's rows 0, 2 3 0 1 6 7 4 5, ... are the 16-byte indices `i ^ 2r`), keeping 32 bytes intact; it is not a `Mode` because the TMA descriptor does not use it here. The 8-byte-flip sub-mode and 64-byte atomicity are not represented. Tile padding is a separate layout operation.

</details>

<a id="thread-tensor-transfer-map"></a>
#### byte correspondence for a tensor load (`THREAD-TENSOR-TRANSFER-MAP`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorTransfer.lean` L11-L41](../../Core/Async/Tensor/TensorTransfer.lean#L11-L41)

Each element byte that a tensor transfer selects has a swizzled shared destination and either an in-bounds global source or the descriptor's out-of-bounds fill. Shared padding is not copied, and the byte count includes out-of-bounds elements. With four-row coordinates, box row `r` is tensor row `rows r`, starting at the column of the origin.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorTransfer.Slot`](../../Core/Async/Tensor/TensorTransfer.lean#L92-L95) ([concept](#c-tensortransfer-slot)), [`TensorTransfer.slotAt`](../../Core/Async/Tensor/TensorTransfer.lean#L97-L105), [`TensorTransfer.Source`](../../Core/Async/Tensor/TensorTransfer.lean#L107-L112) ([concept](#c-tensortransfer-source)), [`TensorTransfer.index`](../../Core/Async/Tensor/TensorTransfer.lean#L114-L117), [`TensorTransfer.coord`](../../Core/Async/Tensor/TensorTransfer.lean#L119-L128), [`TensorTransfer.bytes`](../../Core/Async/Tensor/TensorTransfer.lean#L131-L134) ([concept](#c-tensortransfer-bytes)), [`TensorHasOob`](../../Core/Async/Tensor/TensorTransfer.lean#L140-L145) ([concept](#c-tensorhasoob)), [`tensorHasOobDecidable`](../../Core/Async/Tensor/TensorTransfer.lean#L147-L151)

<details>
<summary>Details for reviewers</summary>

- §5.5.3
- §5.5.3.4 (`.tile::gather4`)
- §5.5.7
- §9.7.10.28.5.3 (cp.async.bulk.tensor)
- EXT-TMA-GEOMETRY

**Applies:** Non-interleaved 1D–5D tiled transfers and 2D `.tile::gather4`/`.tile::scatter4` transfers with the represented descriptor formats

**Premises:** Descriptor and instruction validity, storage, publication and allocation are checked by the consuming instruction rules. Each slot denotes one selected element byte.

**Effect:** An address/value-source map, without a trace order. `TensorHasOob` holds when some selected element is out of bounds. The four-row coordinates are the readings EXT-TMA-GATHER4 and EXT-TMA-SCATTER4, and the shared layout of such a box is the tile layout of the box. Slot coordinates are selected-element indices, distinct from tensor coordinates: the inner index, the row (the outer axes' indices in mixed radix, `TensorTile.indexOf`) and the element byte. The fill source is symbolic: OOB-NaN is not silently identified with a real number or zero. The byte count includes OOB-filled elements but excludes shared padding.

</details>

<a id="ext-tma-gather4"></a>
##### the four rows of `.tile::gather4` (`EXT-TMA-GATHER4`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorTransfer.lean` L43-L71](../../Core/Async/Tensor/TensorTransfer.lean#L43-L71)

The four rows that a `.tile::gather4` load requests are placed in shared memory as the tile layout of the map's box with four rows, where row `j` is tensor row `y_j` starting at column `x`.

Source:

- - §5.5.3.4: "combined to form single 2D destination tensor"

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** §5.5.3.4 says the four request coordinates form four bounding boxes (box dimension 1 must be one) that are combined to form a single 2D destination tensor, and it gives no destination layout. The model reads the destination as the tile layout of the map's box with four rows, in which row `j` is tensor row `y_j` from column `x`.

**Evidence:** On a B200 `Tools/probes/tma_gather4.ptx` (2D u8 map, 8 KiB sentinel-filled buffer) matched, in every byte, that layout: no/32B/64B/128B swizzles, destination offsets 0 to 1024 (128-byte phases), rows narrower than the swizzle width, repeated and descending rows and per-row out-of-bounds zero fill; the mbarrier completed with `4 * box width` bytes. With `.multicast::cluster` (`Tools/probes/tma_mc_gather4.ptx`, one 4-CTA cluster, masks 0xF, 0x5, 0xA, 0xE, 0x1) every masked CTA received this layout and its mbarrier completed with `4 * box width` bytes; unmasked CTAs were untouched. Box dimension 1 of 2 or 4, or an inner start that is not 16-byte aligned, fails with an illegal instruction.

**Effect:** The destination layout of a gather4 load is fixed by this row-to-tile map; if the hardware layout differs, the loaded shared bytes differ from the ones proven. Disclosed by every kernel whose statement names `Op.cpTensor (mode := TensorMode.fourRows)` or `Op.prefetchTensor (mode := TensorMode.fourRows)`: FlashMlaSparseDecodeH64.

</details>

<a id="ext-tma-scatter4"></a>
##### the four rows of `.tile::scatter4` (`EXT-TMA-SCATTER4`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorTransfer.lean` L73-L90](../../Core/Async/Tensor/TensorTransfer.lean#L73-L90)

A `.tile::scatter4` store reads the tile layout of the map's box with four rows from shared memory and writes it as four tensor rows, where box row `j` is tensor row `y_j` starting at column `x`.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Evidence:** On a B200 `Tools/probes/tma_scatter4.ptx` (2D u8 map, pattern-filled shared source, sentinel-filled tensor) matched, in every tensor byte, this store: no/32B/64B/128B swizzles, source offsets 0 to 1024, padded rows, and rows or columns past the extent unwritten. A negative column or row coordinate, box dimension 1 of 2 or an unaligned inner start fails with an illegal instruction; a 64-byte-aligned source is misaligned. With a repeated row the later row's bytes were stored (one case); the model leaves the order of the two writes to the memory rules.

**Effect:** The source layout and the written tensor rows of a scatter4 store are fixed by this map; if the hardware map differs, the stored tensor differs from the one proven. Disclosed by every kernel whose statement names `Op.cpTensorStore (mode := TensorMode.fourRows)`: none.

</details>

### Which executions are allowed

Effects of copies, tensor loads, stores and reductions, and the waits on bulk groups.

<a id="dep-async-stages"></a>
#### independent effects of asynchronous operations (`DEP-ASYNC-STAGES`)

*Rule* · [Lean comment: `Core/Data/AsyncTypes.lean` L30-L86](../../Core/Data/AsyncTypes.lean#L30-L86)

Each asynchronous operation (a bulk or tensor copy, a tensor store or reduction, a tensor prefetch, a cluster launch control request, an MMA or a commit) is split into independent stages such as a read of its source, a write of its destination, a completion notification or an operand read. A stage is named by the issuing instruction instance and the part, and an execution records the outcome of each stage separately from the thread traces.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`AsyncCopy.Slot`](../../Core/Data/AsyncTypes.lean#L89-L104), [`AsyncCopy.Target`](../../Core/Data/AsyncTypes.lean#L106-L110), [`AsyncCopy.Part`](../../Core/Data/AsyncTypes.lean#L112-L130), [`AsyncCopy.Part.target`](../../Core/Data/AsyncTypes.lean#L132-L138), [`AsyncCopy.Part.writes`](../../Core/Data/AsyncTypes.lean#L140-L143), [`AsyncCopy.Ref`](../../Core/Data/AsyncTypes.lean#L145-L150) ([concept](memory.md#c-asynccopy-ref)), [`AsyncCopy.Completion`](../../Core/Data/AsyncTypes.lean#L157-L167), [`AsyncCopy.Reduction`](../../Core/Data/AsyncTypes.lean#L169-L174), [`AsyncCopy.WriteMode`](../../Core/Data/AsyncTypes.lean#L176-L183), [`AsyncCopy.Spec`](../../Core/Data/AsyncTypes.lean#L185-L202), [`AsyncCopy.Spec.elemWidth`](../../Core/Data/AsyncTypes.lean#L204-L209), [`AsyncCopy.Spec.elemOffsets`](../../Core/Data/AsyncTypes.lean#L211-L217), [`AsyncCopy.Spec.elems`](../../Core/Data/AsyncTypes.lean#L219-L221), [`AsyncCopy.Effects`](../../Core/Data/AsyncTypes.lean#L223-L232), [`AsyncCopy.MmaOperands`](../../Core/Data/AsyncTypes.lean#L234-L237) ([concept](tcgen05.md#c-asynccopy-mmaoperands)), [`AsyncCopy.Snapshot`](../../Core/Data/AsyncTypes.lean#L239-L249), [`AsyncCopy.Snapshot.mmaStarted`](../../Core/Data/AsyncTypes.lean#L251-L252), [`AsyncCopy.present`](../../Core/Data/AsyncTypes.lean#L254-L260), [`AsyncCopy.nonempty`](../../Core/Data/AsyncTypes.lean#L262-L262), [`AsyncCopy.threadRefCoe`](../../Core/Data/AsyncTypes.lean#L152-L152), [`AsyncCopy.Ref.issuer`](../../Core/Data/AsyncTypes.lean#L154-L155)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.1 (asynchronous operations)
- §9.7.10.28 (bulk and tensor copies: read the source, write the destination, then signal
    completion)
- §9.7.10.28.3.1 (cp.async)
- §9.7.10.28.4.1 (cp.async.bulk)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)
- §9.7.15.18 (clusterlaunchcontrol.try_cancel)
- §9.7.18.10.10.1
- §9.7.18.12.1 (tcgen05.mma, tcgen05.commit)

**Applies:** The stages of linear copies (`cp.async` and `cp.async.bulk`), tensor copies, tensor stores and reductions, tensor and linear prefetch reads, CLC requests, MMAs, commits and the arrive-on of `cp.async.mbarrier.arrive`

**Premises:** The issuing instruction identifies the operation, its footprint and its mbarrier.

**Effect:** Independent asynchronous observations stored per kind in Execution. The part of a stage is a read, a write or a reduction's old-value read of one footprint slot, a notification to one target, a bulk store's read or full completion, a CLC resolution, a commit's arrive-on, the arrive-on of `cp.async.mbarrier.arrive`, an MMA operand byte read or the MMA completion. The slot depends on the kind of the issuing instruction: it is the whole linear range of a copy, one tile byte of a tensor load or store, one selected byte of a tensor prefetch, or the response at one target CTA of a CLC request. Stages occupy no positions in a thread trace. A linear operation (`Spec`: a copy, a linear reduction, `st.async` or `red.async`) names its source and destination footprints and its completion mechanism (`Completion`): the complete-tx on an mbarrier, the bulk async-group of the issuing thread, the non-bulk async-group of `cp.async`, which `cp.async.mbarrier.arrive` may also track, or none the thread can observe. The source of a `cp.async` may be shorter than its destination: the remaining destination bytes are zeros (DEP-LINEAR-COPY-EFFECTS). The source of `st.async` and `red.async` is the bytes of its register operands (`data`), with an empty `src`. The operation writes its destination as one write, or element by element (`WriteMode`): each byte whose mask bit is set for `.cp_mask`, each element of the type for a reduction, which also reads the element's old bytes. An element-wise operation has a stage `.write (.elem j)` per element and `.old (.elem j)` per reduction element, and its stage `.write .copy` has no footprint: it is present when every element has been written, which is the completion of the operation. The spec also records the proxy (`generic`) and the scope of a strong destination access (`scope`).

</details>

<a id="mem-footprint"></a>
#### thread and asynchronous memory accesses (`MEM-FOOTPRINT`)

*Rule* · [Lean comment: `Core/Data/Events.lean` L290-L333](../../Core/Data/Events.lean#L290-L333)

Every thread access and every stage of an asynchronous operation has a footprint and a direction. The footprint of a stage is fixed by its issuing instruction when the instruction executes, even while the stage is pending, and the effect records say which stages have happened. These queries assert no ordering and no read values.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Execution.MmaFootprint`](../../Core/Data/Events.lean#L336-L344), [`Execution.MmaRead`](../../Core/Data/Events.lean#L346-L350), [`Execution.MemReads`](../../Core/Data/Events.lean#L352-L376) ([concept](memory.md#c-execution-memreads)), [`Execution.MemWrites`](../../Core/Data/Events.lean#L378-L400) ([concept](memory.md#c-execution-memwrites)), [`Execution.memReads_thread_iff_of_not_rmw`](../../Core/Data/Events.lean#L415-L420), [`Execution.memWrites_thread_iff_of_not_rmw`](../../Core/Data/Events.lean#L422-L427), [`Execution.memWrites_write_copy_of_whole`](../../Core/Data/Events.lean#L402-L413), [`Execution.asyncFootprint_write_copy_of_whole`](../../Core/Data/Events.lean#L459-L468), [`Execution.AsyncFootprint`](../../Core/Data/Events.lean#L429-L457), [`Execution.Intent`](../../Core/Data/Events.lean#L470-L474) ([concept](memory.md#c-execution-intent)), [`Execution.MemTouches`](../../Core/Data/Events.lean#L476-L477), [`Execution.AsyncPresent`](../../Core/Data/Events.lean#L479-L503), [`Execution.RefPresent`](../../Core/Data/Events.lean#L505-L507)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.1 (independent async execution)
- §9.7.18.6.5 (MMA operands use the async proxy)
- §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.10.28.4.3: "cp.async.bulk.prefetch is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.15.16.18 (the arrive-on of cp.async.mbarrier.arrive is asynchronous)

**Applies:** Ordinary accesses and the stages of linear and tensor copies, tensor stores and reductions, tensor and linear prefetch reads, CLC responses, the represented MMA operands, tcgen05.cp sources and the arrive-on of cp.async.mbarrier.arrive

**Premises:** Actual instruction events determine all footprints; effect records determine which reads and writes have happened.

**Effect:** Unified memory queries; no ordering or read values are asserted here. A thread's atomic read-modify-write is one event that is both a read and a write of its footprint (`Rmw`): its read is in `MemReads` and its write, when the operation has a result, in `MemWrites`, both under the event's own reference. The footprint of an asynchronous stage is given by its issuing instruction and slot (`AsyncFootprint`), and its direction is that of its part (`Part.writes`). A reduction also reads each destination byte it writes, as its own read (`.old`) with a read intent at the write's footprint. Whether a stage is present is read from the storage of its slot's kind (`AsyncPresent`). The safety checks see the footprint of a pending stage before its completion, so an early consumer cannot evade checking by omitting the pending write. A tensor prefetch's read (`.read (.prefetch ..)`) has the footprint of a tensor load's source read of the same selection (`TensorTransfer.sourceLoc`) and is never present, so it returns no value and has no completion. A linear prefetch's read (`.read .copy` of a `cp.async.bulk.prefetch`) has the footprint of its global range and is never present either (`issuedBy` gives it no copy specification, so its effects stay empty) (EXT-PREFETCH-PENDING, THREAD-TENSOR-PREFETCH).

</details>

<a id="dep-async-origin"></a>
#### independent asynchronous effects and object histories (`DEP-ASYNC-ORIGIN`)

*Rule* · [Lean comment: `Core/Async/Tma.lean` L368-L390](../../Core/Async/Tma.lean#L368-L390)

Every recorded effect of a linear copy or an MMA belongs to an actual issuing instruction. A copy writes the bytes it read, and a completion notification or arrive-on requires the completion of the operations it tracks. The history of every mbarrier object consists of valid steps, and an object fault is still an execution, which the safety check rejects.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TmaOk`](../../Core/Async/Tma.lean#L393-L398) ([concept](#c-tmaok))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16 (object transitions)
- §9.7.10.28.4.1 (bulk effects and notification)
- §9.7.18.12.1 (commit completion)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)

**Applies:** Decoded linear copies, MMA completion, `cp.async.mbarrier.arrive` arrive-on operations and mbarrier operations across arbitrary phases

**Premises:** Each effect has an actual issuing instruction and each object record has an actual source.

**Effect:** Execution constraints in Consistent.tma. Faults remain possible executions and are rejected by safety.

</details>

<a id="dep-linear-copy-effects"></a>
#### effects and completion of a linear copy (`DEP-LINEAR-COPY-EFFECTS`)

*Rule* · [Lean comment: `Core/Async/AsyncCopy.lean` L11-L62](../../Core/Async/AsyncCopy.lean#L11-L62)

A linear copy writes the bytes it read, followed by zeros up to the size of its destination when its source is shorter (only a `cp.async` with `src-size` or `ignore-src`), and `st.async` writes the bytes of its register operands. A masked copy writes each byte whose mask bit is set with its source byte, and a reduction writes each element together with a read of its old value. Only an operation completed through an mbarrier has a completion notification; it requires the whole write, and it adds the destination byte count to that mbarrier, once.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`AsyncCopy.zeroByte`](../../Core/Async/AsyncCopy.lean#L65-L67), [`AsyncCopy.sourceBytes`](../../Core/Async/AsyncCopy.lean#L69-L74), [`AsyncCopy.ElemsOk`](../../Core/Async/AsyncCopy.lean#L76-L86), [`AsyncCopy.CopyOk`](../../Core/Async/AsyncCopy.lean#L88-L100) ([concept](#c-asynccopy-copyok)), [`AsyncCopy.WellFormed`](../../Core/Async/AsyncCopy.lean#L117-L120), [`AsyncCopy.Notification`](../../Core/Async/AsyncCopy.lean#L122-L126) ([concept](#c-asynccopy-notification)), [`AsyncCopy.copyOk_iff_of_size_eq`](../../Core/Async/AsyncCopy.lean#L102-L115)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.4.1 (copying size bytes): "The complete-tx operation, with completeCount argument equal
    to amount of data copied in bytes, will be performed on the mbarrier object specified by the
    operand mbar ."
- §9.7.10.28.4.1: "The i-th bit in the 16-bit wide byteMask operand specifies whether the i-th byte
    of each 16-byte wide chunk of source data is copied to the destination. If the bit is set, the
    byte is copied."
- §9.7.10.28.3.1: "Operand src-size represents the size of the data in bytes to be copied from src
    to dst and must be less than or equal to cp-size . In such case, remaining bytes in destination
    dst are filled with zeros."
- §9.7.10.28.3.1: "If the source data is ignored then zeros will be copied to destination dst ."
- §9.7.10.28.4.2: "Each data element in the destination array is reduced inline with the
    corresponding data element in the source array with the reduction operation specified by the
    modifier .redOp ."
- §9.7.10.12 (st.async): "initiates an asynchronous store operation that stores the value specified
    by source operand b to the destination memory location specified by operand a"
- §9.7.10.12 (st.async): "upon completion of the asynchronous operation, a complete-tx operation
    will be performed on the mbarrier object specified by the operand mbar , with completeCount
    argument equal to the amount of data stored in bytes."
- §9.7.15.7 (red.async)
- §9.7.10.28.1 (asynchronous execution)

**Applies:** Linear operations (`cp.async`, `cp.async.bulk`, `cp.reduce.async.bulk`, `st.async`, `red.async`), with source values left open

**Premises:** A copy effect is present for an issued instruction instance.

**Effect:** Per-operation validity; the stage order of the copy is `StageOrder` (DEP-ASYNC-STAGE-ORDER). A write may be present while its completion notification is still absent. Effects of distinct copies may be observed in any relative order. A completed copy contributes exactly its own byte count to exactly its own mbarrier, once. The notification has release.cluster semantics, applied by the object/visibility rules; the issuer's earlier generic accesses are not added to these edges. A copy completed through an async-group has no notification; its completion is the presence of its write (DEP-BULK-WAIT). The zero bytes of a `cp.async` are the bytes of a zero 8-bit value (`zeroByte`). An element-wise operation (`.cp_mask` copy or reduction) records each element's write, and each reduction element's old-value read, separately (`ElemsOk`); its `.write .copy` stage is present only when every element has been written, and it then records no bytes. The value a reduction element writes is DEP-REDUCTION-VALUES's (`CopyReduceValues`). A register source has no read stage.

</details>

<a id="dep-tensor-load-origin"></a>
#### tensor effects belong to actual instruction instances (`DEP-TENSOR-LOAD-ORIGIN`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorExecution.lean` L12-L35](../../Core/Async/Tensor/TensorExecution.lean#L12-L35)

Every recorded tensor load copy belongs to an actual issue with the same descriptor, coordinates, destination, mbarrier, scope and CTA group, including each per-destination copy of a multicast load. Its descriptor is valid and its effects and routing obey the rules of a tensor load.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorOk`](../../Core/Async/Tensor/TensorExecution.lean#L37-L44) ([concept](#c-tensorok))

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.3 (asynchronous copy initiated by instruction)

**Applies:** 1D–5D tiled and 2D `.tile::gather4` tensor loads, including each per-destination copy of a `.multicast::cluster` load

**Premises:** Every recorded effect identifies an existing issue with exactly the same descriptor, coordinates, destination, mbarrier, scope and CTA-group modifier.

**Effect:** Consistent.tensor and the tensor case of `AsyncCopy.Notifies` (OBJ-MBAR-OBSERVE). Tensor notifications resolve through objectAction and ObjectsOk requires their history entries. An issue may have no observation yet. Missing observation denotes no recorded effects. It also denotes no completed operation. AsyncDrained requires its notification before kernel completion.

</details>

<a id="prog-cta-group"></a>
#### CTA-group identities and tensor completion routing (`PROG-CTA-GROUP`)

*Rule* · [Lean comment: `Core/Tmem/CtaPair.lean` L10-L37](../../Core/Tmem/CtaPair.lean#L10-L37)

A tensor copy from global to shared memory faults unless its shared destination and its mbarrier lie in CTAs of the issuer's cluster, both lie in the issuing CTA when the copy uses CTA-local addresses, and the mbarrier's CTA is in the same CTA group as the destination's CTA. A CTA group is an aligned block of `group.size` cluster ranks: one rank for cta_group::1, an even rank and the next odd rank for cta_group::2. `Launch.ctaGroup` lists the CTAs of the group of a CTA, and every rule that needs the CTAs of a CTA group (tensor routing, `tcgen05.mma` operands, `tcgen05.cp`, `tcgen05.shift` and `tcgen05.commit`) takes them from it. SameCtaGroup includes equality. The checks use cluster-relative ranks, including in clusters larger than two.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`CtaInCluster`](../../Core/Tmem/CtaPair.lean#L39-L41) ([concept](tmem.md#c-ctaincluster)), [`Launch.ctaGroupRanks`](../../Core/Tmem/CtaPair.lean#L43-L48) ([concept](tmem.md#c-launch-ctagroupranks)), [`Launch.ctaGroup`](../../Core/Tmem/CtaPair.lean#L50-L53) ([concept](tmem.md#c-launch-ctagroup)), [`SameCtaGroup`](../../Core/Tmem/CtaPair.lean#L55-L58) ([concept](tmem.md#c-samectagroup)), [`sameCtaGroup_iff`](../../Core/Tmem/CtaPair.lean#L60-L73), [`Launch.ctaGroup_one`](../../Core/Tmem/CtaPair.lean#L75-L83), [`Launch.ctaGroup_two`](../../Core/Tmem/CtaPair.lean#L85-L97), [`Launch.ctaGroup_ne_none_iff`](../../Core/Tmem/CtaPair.lean#L99-L122), [`TensorRoute`](../../Core/Tmem/CtaPair.lean#L124-L133), [`tensorRouteDecidable`](../../Core/Tmem/CtaPair.lean#L135-L139)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5.1–§9.7.18.5.2 (CTA pair)
- §9.7.10.28.5.3 (shared destination and cta_group completion)

**Applies:** Non-multicast global-to-shared tensor copies in the represented 1D cluster topology

**Premises:** Both locations are shared addresses in the issuer's cluster. CTA-only addressing requires both to belong to the issuer. The mbarrier belongs to the destination's CTA group: the destination itself for group one, its pair for group two.

**Effect:** Address ownership checks only. No arrival, completion, visibility or scheduling consequence follows from cluster/pair membership.

</details>

<a id="dep-tensor-load-effects"></a>
#### independent tensor byte effects and completion (`DEP-TENSOR-LOAD-EFFECTS`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorCopy.lean` L83-L118](../../Core/Async/Tensor/TensorCopy.lean#L83-L118)

A tensor load writes each selected byte with the byte it read from global memory when the element is in bounds, and with the fill of the descriptor when it is out of bounds. Its completion notification requires every selected byte to be written, and it signals exactly the number of selected bytes to the mbarrier that the instruction names.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorTransfer.globalAddress`](../../Core/Async/Tensor/TensorCopy.lean#L13-L20), [`TensorTransfer.sourceLoc`](../../Core/Async/Tensor/TensorCopy.lean#L22-L30), [`TensorBox`](../../Core/Async/Tensor/TensorCopy.lean#L32-L41) ([concept](#c-tensorbox)), [`TensorBox.sharedLoc`](../../Core/Async/Tensor/TensorCopy.lean#L43-L48), [`TensorBox.globalAddress`](../../Core/Async/Tensor/TensorCopy.lean#L50-L54), [`requireBoxAligned`](../../Core/Async/Tensor/TensorCopy.lean#L56-L62) ([concept](#c-requireboxaligned)), [`requireBoxAligned_eq_ok`](../../Core/Async/Tensor/TensorCopy.lean#L64-L70), [`requireBoxAligned_eq_error`](../../Core/Async/Tensor/TensorCopy.lean#L72-L78), [`TensorCopy.Spec`](../../Core/Async/Tensor/TensorCopy.lean#L120-L125) ([concept](#c-tensorcopy-spec)), [`TensorCopy.Content`](../../Core/Async/Tensor/TensorCopy.lean#L132-L136), [`TensorCopy.Effects`](../../Core/Async/Tensor/TensorCopy.lean#L138-L143) ([concept](#c-tensorcopy-effects)), [`TensorCopy.source`](../../Core/Async/Tensor/TensorCopy.lean#L145-L150), [`TensorCopy.CopyOk`](../../Core/Async/Tensor/TensorCopy.lean#L152-L160) ([concept](#c-tensorcopy-copyok)), [`TensorCopy.Completion`](../../Core/Async/Tensor/TensorCopy.lean#L162-L165) ([concept](#c-tensorcopy-completion)), [`TensorCopy.Extends`](../../Core/Async/Tensor/TensorCopy.lean#L167-L172), [`TensorCopy.RoutingOk`](../../Core/Async/Tensor/TensorCopy.lean#L127-L130), [`TensorCopy.Observation`](../../Core/Async/Tensor/TensorCopy.lean#L174-L177) ([concept](#c-tensorcopy-observation)), [`TensorCopy.Observation.Extends`](../../Core/Async/Tensor/TensorCopy.lean#L179-L181), [`TensorCopy.SnapshotExtends`](../../Core/Async/Tensor/TensorCopy.lean#L183-L185)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.1 (asynchronous operations)
- §9.7.10.28.5.3 (tensor copy and mbarrier completion)
- §5.5.3.3 (OOB fill)
- §5.5.3.1: "The address of the bounding Box must also be aligned to 16 bytes."

**Applies:** One 1D–5D tiled or 2D `.tile::gather4` global-to-shared tensor load, without data multicast

**Premises:** An actual issuing instruction supplies a valid descriptor and shared/mbarrier locations. Source read values are constrained separately by memory consistency.

**Effect:** Operation-local effect validity and monotone observations. The data destination and completion location are distinct fields: a group-2 copy may signal its peer CTA without writing the peer CTA's data. CTA-group routing, allocation, proxy visibility and mbarrier phase attachment remain execution checks. Content retains symbolic typed fill bytes until the scalar-value adapter interprets them; OOB-NaN is not given a real value. Execution.tensor stores these records; TensorOk ties each record to its actual issue. Memory/effect adapters remain separate. The alignment of the bounding box (reading EXT-TMA-BOX-ALIGN of §5.5.3.1) is checked once for every tensor load, store, reduction and prefetch by `requireBoxAligned`, when the thread issues the instruction (THREAD-TENSOR-ISSUE, THREAD-TENSOR-STORE, THREAD-TENSOR-PREFETCH). A misaligned box is an undefined-behaviour event, so no issue event records one.

</details>

<a id="dep-tensor-load-bytes"></a>
#### scalar byte adapters for tensor effects (`DEP-TENSOR-LOAD-BYTES`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorMemory.lean` L11-L36](../../Core/Async/Tensor/TensorMemory.lean#L11-L36)

Each byte of a tensor load reads a one-byte global location and writes the shared location of its swizzled address. A copied byte keeps its value, and a zero fill is the zero of the descriptor's element type. A NaN fill, and a zero fill of `f64`, have no scalar value and are unsupported.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`TensorCopy.zeroValue`](../../Core/Async/Tensor/TensorMemory.lean#L38-L44), [`TensorCopy.Content.byte`](../../Core/Async/Tensor/TensorMemory.lean#L46-L51), [`TensorCopy.readLoc`](../../Core/Async/Tensor/TensorMemory.lean#L53-L55), [`TensorCopy.writeLoc`](../../Core/Async/Tensor/TensorMemory.lean#L57-L59), [`TensorCopy.readByte`](../../Core/Async/Tensor/TensorMemory.lean#L61-L63), [`TensorCopy.writeByte`](../../Core/Async/Tensor/TensorMemory.lean#L65-L68)

<details>
<summary>Details for reviewers</summary>

- §5.5.3.3 (zero fill)
- §9.7.10.28.5.3 (tensor copy)
- MEM-BYTE

**Applies:** Selected byte slots of the represented tensor copy; zero fill uses represented integer, f16, bf16 and f32 scalar values

**Premises:** The slot belongs to the copy. CopyOk constrains each write to its recorded read or typed fill source.

**Effect:** Adapters for execution memory queries. OOB-NaN and f64 zero fill have no scalar byte (`Content.byte` is none): the Value type does not represent those floating values, so such content is unsupported (ERR-TENSOR-FILL-VALUE rejects its writes). A missing effect is distinct from a zero-valued byte.

</details>

<a id="dep-tensor-store-effects"></a>
#### tensor shared-to-global addresses and independent effects (`DEP-TENSOR-STORE-EFFECTS`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorStore.lean` L12-L48](../../Core/Async/Tensor/TensorStore.lean#L12-L48)

A tensor store copies each in-bounds global byte from the corresponding swizzled byte of its shared source, and an out-of-bounds element has no global destination. A tensor reduction performs each in-bounds element as one read-modify-write that reads the shared byte and the old global byte of each element byte. Read completion and full completion are separate, and full completion requires every in-bounds write.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorStore.Spec`](../../Core/Async/Tensor/TensorStore.lean#L98-L102) ([concept](#c-tensorstore-spec)), [`TensorStore.ReduceSupported`](../../Core/Async/Tensor/TensorStore.lean#L104-L111), [`TensorStore.Valid`](../../Core/Async/Tensor/TensorStore.lean#L113-L118) ([concept](#c-tensorstore-valid)), [`TensorStore.destination`](../../Core/Async/Tensor/TensorStore.lean#L120-L123), [`TensorStore.Effects`](../../Core/Async/Tensor/TensorStore.lean#L125-L134) ([concept](#c-tensorstore-effects)), [`TensorStore.CopyOk`](../../Core/Async/Tensor/TensorStore.lean#L136-L152) ([concept](#c-tensorstore-copyok)), [`TensorStore.Extends`](../../Core/Async/Tensor/TensorStore.lean#L154-L161), [`TensorStore.Observation`](../../Core/Async/Tensor/TensorStore.lean#L163-L166) ([concept](#c-tensorstore-observation)), [`TensorStore.Observation.Extends`](../../Core/Async/Tensor/TensorStore.lean#L168-L170), [`TensorStore.SnapshotExtends`](../../Core/Async/Tensor/TensorStore.lean#L172-L174), [`TensorStore.completion`](../../Core/Async/Tensor/TensorStore.lean#L176-L179)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.3 (tensor shared-to-global)
- §9.7.10.28.5.4 (reduction)
- §9.7.10.28.6.2 (read/full completion)
- CUDA Programming Guide §4.13.4 (negative indices and out of bounds; TMA swizzling)
- EXT-TMA-STORE-OOB

**Applies:** Non-interleaved 1D–5D tiled and 2D `.tile::scatter4` shared::cta-to-global tensor stores, and 1D–5D tiled `cp.reduce.async.bulk.tensor` reductions

**Premises:** An immutable published tensor map, a local shared source, and nonnegative coordinates (scatter4: also the row coordinates). Source values are constrained by separate read-source/proxy rules.

**Effect:** Address/effect validity and a bulk-group completion adapter. With scatter4 row coordinates, box row `r` is tensor row `rows r` (EXT-TMA-SCATTER4). A reduction writes all global bytes of an element together, each after reading its shared byte and its old destination byte. The written value and the atomicity of concurrent reductions are DEP-REDUCTION-VALUES. The store reads the same shared swizzle layout that a matching load would produce. OOB slots may be read or skipped in shared memory: the footprint adapter must reserve all selected source slots, and neither choice creates a global write. Read completion closes the source observations, so later extension cannot add an OOB read after a read wait has permitted source reuse. Full completion requires every in-bounds write. The descriptor's input fill policy does not create output stores.

</details>

<a id="ext-tma-store-oob"></a>
##### out-of-bounds elements of a tensor store are not written (`EXT-TMA-STORE-OOB`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorStore.lean` L50-L73](../../Core/Async/Tensor/TensorStore.lean#L50-L73)

A tiled tensor store whose bounding box crosses the tensor boundary writes only the in-bounds elements. An out-of-bounds element has no global destination, and its shared source may be read or skipped.

Source:

- - §5.5.3.3: "PTX Tensor operation can detect and handle the case when the Bounding Box crosses the tensor boundary in any dimension" - CUDA C++ Programming Guide §4.13.4 (negative indices and out of bounds), read as: out-of-bounds elements of a store are not written - `Tools/probes/tma_scatter4.ptx` and `Tools/probes/tma_reduce.ptx` (rows, columns and elements past the extent unwritten or unchanged, on a B200)

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text states the fill of out-of-bounds elements for loads and no rule for stores. The two fill modes it lists are stated for the elements of a box "set to 0" or to OOB-NaN, which is a load. The probes cover `.tile::scatter4` and tensor reductions; no probe stores a plain tiled box across the boundary.

**Effect:** If hardware wrote a value for an out-of-bounds element, that write would be missing from the model's footprints and conflicts with it would be missed. Disclosed by every kernel whose statement names `Op.cpTensorStore`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192.

</details>

<a id="ext-tma-reduce"></a>
##### tensor reductions use the store's layout (`EXT-TMA-REDUCE`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorStore.lean` L75-L96](../../Core/Async/Tensor/TensorStore.lean#L75-L96)

A tensor reduction reads the same swizzled shared layout and reduces the same global elements as a tensor store with the same descriptor. Out-of-bounds elements are left unchanged. The reduced values are DEP-REDUCTION-VALUES.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** §9.7.10.28.5.4 describes the reduction element-wise without restating the store layout.

**Evidence:** On a B200 `Tools/probes/tma_reduce.ptx` with `run_tma_reduce.cu` (2D u32/s32 map, pattern-filled shared source) gave every tensor element `old ⊕ src` for the shared element at the store's swizzled position, and left out-of-bounds elements and the rest of the tensor unchanged, for add, min and max (signed and unsigned), and, or, xor, inc and dec, with no/32B/64B/128B swizzles, offsets 0 to 640 and partially out-of-bounds boxes. inc or dec of an s32 map, a negative coordinate and an inner start that is not 16-byte aligned fail with an illegal instruction; a 64-byte-aligned source is misaligned.

**Effect:** The destination element of each reduction and the shared source element it reads are fixed by the store's layout; if the hardware layout differs, the reduced tensor differs from the one proven. Disclosed by every kernel whose statement names `Op.cpTensorStore (reduce ≠ none)`: none.

</details>

<a id="dep-tensor-store-bytes"></a>
#### output tensor byte footprints and observed values (`DEP-TENSOR-STORE-BYTES`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorStoreMemory.lean` L11-L31](../../Core/Async/Tensor/TensorStoreMemory.lean#L11-L31)

Every selected byte of a tensor store reserves its shared source location, including out-of-bounds bytes, which may be read or skipped. Only in-bounds bytes have a global write location, and a reduction also reads the old destination byte at that location.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorStore.readLoc`](../../Core/Async/Tensor/TensorStoreMemory.lean#L33-L35), [`TensorStore.writeLoc`](../../Core/Async/Tensor/TensorStoreMemory.lean#L36-L38), [`TensorStore.readByte`](../../Core/Async/Tensor/TensorStoreMemory.lean#L39-L41), [`TensorStore.writeByte`](../../Core/Async/Tensor/TensorStoreMemory.lean#L42-L44), [`TensorStore.oldByte`](../../Core/Async/Tensor/TensorStoreMemory.lean#L45-L47)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.3 (shared-to-global tensor)
- DEP-TENSOR-STORE-EFFECTS
- EXT-TMA-STORE-OOB

**Applies:** Selected byte slots of tiled output copies

**Premises:** The instruction fixes the descriptor, origin and local shared source; effect records retain actual read and write bytes.

**Effect:** Common read-source, allocation and conflicting-access queries.

</details>

<a id="dep-reduction-values"></a>
#### reduced values of tensor reduction elements (`DEP-REDUCTION-VALUES`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorReduce.lean` L12-L84](../../Core/Async/Tensor/TensorReduce.lean#L12-L84)

A tensor or linear reduction writes `op(old, src)` for each performed element, where `old` is the destination element it read and `src` the source element, and an element for which no integer rule or floating-point assumption gives a value makes the execution unsafe. Each element is one atomic read-modify-write of MEM-ATOMICITY.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorDescriptor.Format.dtype`](../../Core/Async/Tensor/TensorReduce.lean#L137-L149), [`TensorStore.reduceValue`](../../Core/Async/Tensor/TensorReduce.lean#L151-L157) ([concept](#c-tensorstore-reducevalue)), [`TensorStore.elementBytes`](../../Core/Async/Tensor/TensorReduce.lean#L159-L162), [`TensorStore.Reduced`](../../Core/Async/Tensor/TensorReduce.lean#L164-L168), [`TensorStore.ReduceReads`](../../Core/Async/Tensor/TensorReduce.lean#L170-L175), [`TensorStore.ReduceValues`](../../Core/Async/Tensor/TensorReduce.lean#L177-L184), [`TensorStore.ReduceNoRule`](../../Core/Async/Tensor/TensorReduce.lean#L186-L191), [`TensorStore.ReduceUnique`](../../Core/Async/Tensor/TensorReduce.lean#L193-L199), [`TensorStore.ReduceAcyclic`](../../Core/Async/Tensor/TensorReduce.lean#L201-L204), [`TensorStore.copyReduceValue`](../../Core/Async/Tensor/TensorReduce.lean#L206-L217), [`TensorStore.CopyReduceValues`](../../Core/Async/Tensor/TensorReduce.lean#L219-L224), [`TensorStore.CopyReduceNoRule`](../../Core/Async/Tensor/TensorReduce.lean#L226-L230), [`TensorStore.copyReduceValues_of_none`](../../Core/Async/Tensor/TensorReduce.lean#L232-L236), [`TensorStore.not_copyReduceNoRule_of_none`](../../Core/Async/Tensor/TensorReduce.lean#L238-L241), [`TensorStore.ReduceOk`](../../Core/Async/Tensor/TensorReduce.lean#L243-L247) ([concept](#c-tensorstore-reduceok))

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.4: "Each element of the tensor data in the .dst state space is reduced inline with
    the corresponding element from the tensor data in the .src state space."
- §9.7.10.28.5.4: "The following table describes the valid combinations of .redOp and element type:
    .redOp Element type .add .u32 , .s32 , .u64 , .f32 , .f16 , .bf16 .min , .max .u32 , .s32 , .u64
    , .s64 , .f16 , .bf16 .inc , .dec .u32 .and , .or , .xor .b32 , .b64"
- §9.7.10.28.5.4: "Each reduction operation performed by cp.reduce.async.bulk.tensor has
    individually .relaxed.gpu memory ordering semantics and are element-wise atomic."
- §9.7.10.28.4.2: "Each data element in the destination array is reduced inline with the
    corresponding data element in the source array with the reduction operation specified by the
    modifier .redOp ."
- §9.7.10.28.4.2: "The .inc and .dec operations return a result in the range [0..x] where x is the
    value at the source state space."
- §9.7.15.7: "red.async is a non-blocking instruction which initiates an asynchronous reduction
    operation specified by .op , with the operand b and the value at the destination memory location
    specified by operand a ."
- THREAD-ATOMIC-OP
- EXT-TMA-REDUCE-OP
- EXT-TMA-REDUCE-ATOMIC
- MEM-ATOMICITY

**Applies:** Every performed element of a `cp.reduce.async.bulk.tensor` reduction, and of a linear reduction (`cp.reduce.async.bulk`, `red.async`)

**Premises:** The element's global bytes were written together, each with its shared source byte and its old destination byte (DEP-TENSOR-STORE-EFFECTS), or the linear element was written with its old bytes (DEP-LINEAR-COPY-EFFECTS); each old byte is a read with a reads-from source under MEM-READS-FROM and MEM-READ-AXIOMS.

**Effect:** Execution constraint in Consistent.reduce; atomicity is Consistent.atomic (MEM-ATOMICITY). The element value is the value of THREAD-ATOMIC-OP for the element's operation and type (`Format.dtype`): integer operations read the bit patterns of the old and source elements and are exact at the element width, with the operations of EXT-TMA-REDUCE-OP, and floating-point operations take their value from an assumption's `rmwRule` (ASM-INTERFACE, ASM-IDEAL). An element has no arithmetic rule when no floating-point rule gives a value or when its old or source bytes are not a value of the element type, and the reduction is then unsafe (`ReduceNoRule`, ERR-REDUCTION-NO-RULE). A reduction element is one read-modify-write. Its read of old byte `k` is the asynchronous read `.old (.store x y k)` at the footprint of the write `.write (.store x y k)` (MEM-FOOTPRINT), so the old value has a reads-from source like any read, and visibility, completion and the axioms apply to it as to the write; like the writes, the reads precede the reduction's full completion (DEP-ASYNC-STAGE-ORDER). The element footprint is that of ERR-DATA-RACE (`OpFootprint`): its first global byte and the element size. The reductions of one element are atomic with respect to each other by MEM-ATOMICITY (`RmwId.tensor`): `ReduceUnique` and `ReduceAcyclic` state its two conclusions for them, and `Consistent.reduceUnique` and `Consistent.reduceAcyclic` derive them. An element `j` of a linear reduction (`cp.reduce.async.bulk`, `red.async`) is the element of the reduction's type at destination offset `j` times its size. Its source element is the bytes at the same offset of the bytes read from `srcMem` (`cp.reduce.async.bulk`) or of the register operand (`red.async`), and its value is THREAD-ATOMIC-OP's for the reduction's operation and type on the rebuilt old and source elements (`copyReduceValue`): the `atom` operations of the same name, as EXT-TMA-REDUCE-OP reads them for tensor reductions (§9.7.10.28.4.2 names the operations without restating them; its sentence on `.inc` and `.dec` is the `atom` formula's range). A floating operation takes its value from an assumption's `rmwRule`, and an element without a value is unsafe (`CopyReduceNoRule`, ERR-REDUCTION-NO-RULE). The element is one atomic operation of MEM-ATOMICITY (`RmwId.copy`).

</details>

<a id="ext-tma-reduce-op"></a>
##### the operations of a tensor reduction (`EXT-TMA-REDUCE-OP`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorReduce.lean` L86-L109](../../Core/Async/Tensor/TensorReduce.lean#L86-L109)

The operations of a tensor reduction are those of the `atom` instruction of the same name, with the destination element as the memory operand `r` and the source element as `s`: inc and dec are `(r >= s) ? 0 : r+1` and `(r==0 || r > s) ? s : r-1`, integer add is modulo `2^w` at the element width, min and max compare as signed integers for `.s32`/`.s64` maps and as unsigned ones for the other integer maps, and `.and`/`.or`/`.xor` (`.b32`/`.b64`) are bitwise.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** §9.7.10.28.5.4 names each `.redOp` and its element types but does not restate the operations. The model reads them as the `atom` operations of the same name (§9.7.15.5, THREAD-ATOMIC-OP).

**Evidence:** The B200 probe of EXT-TMA-REDUCE observed `old ⊕ src` with these operations for every integer operation on u32 and s32 maps, including wrap-around. Floating values follow the model's convention for floating arithmetic: the Core has no default rule, and an explicit assumption supplies one (`Assumption.rmwRule`, ASM-IDEAL). Where no rule gives a value the element is a `noRule` fault (ERR-FAULT-REASON), the convention of every instruction and of MMA (ERR-TC-MMA).

**Effect:** The element values of a tensor reduction are those of these operations; if the hardware operations differ, the proven results differ. Disclosed by every kernel whose statement names `Op.cpTensorStore (reduce ≠ none)`: none.

</details>

<a id="ext-tma-reduce-atomic"></a>
##### a tensor reduction element is one atomic operation (`EXT-TMA-REDUCE-ATOMIC`)

*Interpretation (EXT)* · [Lean comment: `Core/Async/Tensor/TensorReduce.lean` L111-L134](../../Core/Async/Tensor/TensorReduce.lean#L111-L134)

Each element reduction of `cp.reduce.async.bulk.tensor` is one atomic read-modify-write of §8.10.3 at the element footprint, whose read and write are the old-value reads and the writes of the element's bytes, and its scope is `.gpu`.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** §9.7.10.28.5.4 calls the reductions "element-wise atomic" with ".relaxed.gpu memory ordering semantics" and does not name the operations that make up an element. The model reads an element as one atomic operation of MEM-ATOMICITY (`RmwId.tensor`): its read of the old value of byte `k` is `.old (.store x y k)`, its write of byte `k` is `.write (.store x y k)`, and its footprint is the element.

**Effect:** Two reductions of one element are then morally strong (ERR-DATA-RACE: strong, `.gpu` scope, async proxy, complete overlap), so MEM-ATOMICITY gives that no two of them read a byte from the same write and that reads-from among them has no cycle (`ReduceUnique`, `ReduceAcyclic`). These make the reductions of one element a single reads-from chain per byte, the same chain for every byte of the element (two different chains would contain a cycle), and CORRECT-FINAL orders their writes by it (`CoStep`), so the final element is the result of the last reduction. Executions in which two reductions of one element read a byte from the same write, or read from each other cyclically, are removed from `Consistent`. If an element were not one atomic operation on hardware (for example if its bytes were reduced separately), such executions may occur. Disclosed by every kernel whose statement names `Op.cpTensorStore (reduce ≠ none)`: none.

</details>

<a id="obj-bulk-group"></a>
#### per-thread bulk async-group membership and waits (`OBJ-BULK-GROUP`)

*Rule* · [Lean comment: `Core/Async/BulkGroup.lean` L10-L50](../../Core/Async/BulkGroup.lean#L10-L50)

A thread's `cp.async.bulk.commit_group` closes the thread's uncommitted bulk operations into one group, also when there are none. `cp.async.bulk.wait_group N` covers every committed group except the N most recent, and it completes only when the covered operations have finished reading their sources (`.read`) or have completed entirely (otherwise). Operations that are not yet committed belong to no wait. `cp.async.commit_group` and `cp.async.wait_group N` do the same for the thread's `cp.async` operations, in groups of their own, and their wait is a full wait.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`BulkGroup.WaitMode`](../../Core/Async/BulkGroup.lean#L52-L57) ([concept](#c-bulkgroup-waitmode)), [`BulkGroup.State`](../../Core/Async/BulkGroup.lean#L59-L64) ([concept](#c-bulkgroup-state)), [`BulkGroup.Action`](../../Core/Async/BulkGroup.lean#L66-L72) ([concept](#c-bulkgroup-action)), [`BulkGroup.step`](../../Core/Async/BulkGroup.lean#L74-L79), [`BulkGroup.run`](../../Core/Async/BulkGroup.lean#L81-L82), [`BulkGroup.required`](../../Core/Async/BulkGroup.lean#L84-L87), [`BulkGroup.Observes`](../../Core/Async/BulkGroup.lean#L89-L91), [`BulkGroup.Completion`](../../Core/Async/BulkGroup.lean#L93-L98), [`BulkGroup.Done`](../../Core/Async/BulkGroup.lean#L100-L104) ([concept](#c-bulkgroup-done)), [`BulkGroup.WaitReady`](../../Core/Async/BulkGroup.lean#L106-L108) ([concept](#c-bulkgroup-waitready)), [`BulkGroup.waitReady_mono`](../../Core/Async/BulkGroup.lean#L110-L120), [`BulkGroup.issue_of_foldl`](../../Core/Async/BulkGroup.lean#L122-L149), [`BulkGroup.issue_of_observes`](../../Core/Async/BulkGroup.lean#L151-L159)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.6.1 (commit_group)
- §9.7.10.28.6.2 (wait_group)
- §9.7.10.28.1.1: "The thread issuing the asynchronous operation must create separate async-groups
    for bulk and non-bulk asynchronous operations."
- §9.7.10.28.3.2: "cp.async.commit_group instruction creates a new cp.async-group per thread and
    batches all prior cp.async instructions initiated by the executing thread but not committed to
    any cp.async-group into the new cp.async-group . If there are no uncommitted cp.async
    instructions then cp.async.commit_group results in an empty cp.async-group."
- §9.7.10.28.3.3: "cp.async.wait_group instruction will cause executing thread to wait till only N
    or fewer of the most recent cp.async-group s are pending and all the prior cp.async-group s
    committed by the executing threads are complete."
- §9.7.10.28.3.3: "An empty cp.async-group is considered to be trivially complete."

**Applies:** One thread's instructions using bulk-group or `cp.async`-group completion, commits and waits

**Premises:** Operation identities denote actual bulk-group issues by this thread. Completion predicates come from the operation's actual effects. The grouping state does not supply them.

**Effect:** Group membership and wait obligations only. Group list order does not impose memory order between operations. The state records source-level grouping. It does not record the physical completion order. All committed groups are retained, so group identities are stable across waits and later commits; any pipeline depth and any operation count per group is allowed. The async-proxy-only wait keeps a distinct mode, so it cannot grant generic-proxy visibility through the full-wait adapter. The bulk groups and the `cp.async` groups of a thread are two separate states (OBJ-BULK-GROUP-TRACE).

</details>

<a id="obj-bulk-group-trace"></a>
#### bulk groups of actual thread instruction instances (`OBJ-BULK-GROUP-TRACE`)

*Rule* · [Lean comment: `Core/Async/BulkExecution.lean` L11-L38](../../Core/Async/BulkExecution.lean#L11-L38)

The groups that a wait covers are computed from the waiting thread's own trace before the wait: its operations of the wait's kind, its commits of that kind, and the wait's own mode and operand. A bulk wait covers the tensor stores and `.bulk_group` linear copies of the groups it observes, and a `cp.async` wait covers the `cp.async` operations of the groups it observes; each operation keeps the position of its issue in the trace.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`bulkAction`](../../Core/Async/BulkExecution.lean#L40-L48), [`bulkActions`](../../Core/Async/BulkExecution.lean#L50-L52), [`bulkStateBefore`](../../Core/Async/BulkExecution.lean#L54-L57), [`BulkWaitsFor`](../../Core/Async/BulkExecution.lean#L59-L63) ([concept](#c-bulkwaitsfor)), [`asyncAction`](../../Core/Async/BulkExecution.lean#L65-L72), [`asyncActions`](../../Core/Async/BulkExecution.lean#L74-L76), [`asyncStateBefore`](../../Core/Async/BulkExecution.lean#L78-L80), [`AsyncGroupWaitsFor`](../../Core/Async/BulkExecution.lean#L82-L86), [`issue_mem_actions`](../../Core/Async/BulkExecution.lean#L88-L101), [`issue_of_waitsFor`](../../Core/Async/BulkExecution.lean#L103-L116), [`not_bulkWaitsFor_of_copy`](../../Core/Async/BulkExecution.lean#L118-L129), [`not_asyncGroupWaitsFor_of_copy`](../../Core/Async/BulkExecution.lean#L131-L141)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.6.1–2 (per-thread grouping and waits)
- §9.7.10.28.3.2–3 (cp.async-groups)
- §9.7.10.28.1.1: "The thread issuing the asynchronous operation must create separate async-groups
    for bulk and non-bulk asynchronous operations."

**Applies:** Tensor stores and linear copies with bulk-group completion, bulk commit/wait events, `cp.async` copies and `cp.async` commit/wait events

**Premises:** The actual source-thread prefix contains the issues and commits. Wait mode and remaining-group operand come from its event.

**Effect:** The execution adapter for group membership. A `cp.async.wait_all` is a commit event followed by a wait event leaving no group (THREAD-CP-ASYNC), so it covers every `cp.async` of the thread before it.

</details>

<a id="dep-bulk-wait"></a>
#### actual output effects and what a group wait covers (`DEP-BULK-WAIT`)

*Rule* · [Lean comment: `Core/Async/BulkExecution.lean` L221-L259](../../Core/Async/BulkExecution.lean#L221-L259)

Every recorded tensor store belongs to an actual issue with a valid specification and obeys the store's effect rules. A group wait covers the operations of the groups it waits for, and one table gives, for each covered operation, the stages the wait waits for and the stages whose memory effects it makes visible to the waiting thread.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorStoreOk`](../../Core/Async/BulkExecution.lean#L261-L267) ([concept](#c-tensorstoreok)), [`GroupWait`](../../Core/Async/BulkExecution.lean#L269-L273), [`GroupWaitsFor`](../../Core/Async/BulkExecution.lean#L275-L279), [`GroupWaitStages`](../../Core/Async/BulkExecution.lean#L281-L289) ([concept](#c-groupwaitstages)), [`GroupWaitVisible`](../../Core/Async/BulkExecution.lean#L291-L300)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.3 (tensor output effects)
- §9.7.10.28.6.2: "The optional .read modifier indicates that the waiting has to be done until all
    the bulk async operations in the specified bulk async-group have completed: reading from the
    tensormap the reading from their source locations."
- §9.7.10.28.6.2 (wait completion; writes being made visible to the executing thread)
- §9.7.10.28.3.3 (cp.async.wait_group): "all the prior cp.async-group s committed by the executing
    threads are complete"

**Applies:** Output tensor observation records, bulk-group wait events and `cp.async` wait events

**Premises:** Each output record names its actual issue and immutable specification; each wait covers the groups from its thread prefix.

**Effect:** `Consistent.store`. The table gives the needs of the group waits (`KindNeeds`, DEP-ORDER: a wait returns only after the stages it waits for), the generic visibility of `AsyncFinished` and `AsyncOnlyFinished` (MEM-OBSERVED-COMPLETION) and the observations of `SyncObserved` (MEM-OBJECT-ORDER-CAUSALITY). By wait and covered operation: - `.read` wait, tensor store: waits for `.readsDone`; makes the source reads visible - `.read` wait, linear copy: waits for `.read .copy`; makes the source read visible - `.full` wait, tensor store: waits for `.readsDone` and `.fullDone`; makes the reads, writes and old-value reads visible - `.full` wait, linear copy: waits for `.read .copy` and `.write .copy`; makes the read, the write and the element writes and old-value reads visible - `.asyncProxy` wait: waits as a `.full` wait; makes nothing visible to generic accesses - `cp.async.wait_group`, `cp.async`: waits for `.read .copy` and `.write .copy`; makes the read and the write visible A linear copy has one read stage and one write stage (DEP-LINEAR-COPY-EFFECTS), so its reads are finished when its read is present and it is complete when its write is present.

</details>

### What counts as an error

Tensor operations that are rejected as unsafe.

<a id="err-cp-async-overlap"></a>
#### overlapping cp.async destinations in one group (`ERR-CP-ASYNC-OVERLAP`)

*Rule* · [Lean comment: `Core/Async/BulkExecution.lean` L143-L165](../../Core/Async/BulkExecution.lean#L143-L165)

An execution is unsafe when two `cp.async` operations of one thread that belong to the same cp.async-group (no commit of the thread lies between them) have overlapping destinations, whatever bytes they write.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`SameAsyncGroup`](../../Core/Async/BulkExecution.lean#L167-L172), [`CpAsyncOverlap`](../../Core/Async/BulkExecution.lean#L174-L176), [`not_cpAsyncOverlap_of_none`](../../Core/Async/BulkExecution.lean#L178-L181)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.3.2: "There is no memory ordering guarantee provided between any two cp.async
    operations within the same cp.async-group . So two or more cp.async operations within a
    cp.async-group copying data to the same location results in undefined behavior."

**Applies:** Every pair of distinct `cp.async` issues of one thread with no `cp.async.commit_group` (or the commit of a `cp.async.wait_all`) between them

**Premises:** Their destination footprints overlap at a byte.

**Effect:** Safety rejection (ERR-OBJECT-LIFETIME, `TmaUnsafe`), with no exemption for writes of the same value (unlike ERR-DATA-RACE's `SameValueWrites`). Two `cp.async` operations of one thread before and after a commit are in different groups; their destinations may overlap, and the race check (ERR-DATA-RACE) orders them only through a wait.

</details>

<a id="err-bulk-mask-range"></a>
#### the destination range of a masked bulk copy (`ERR-BULK-MASK-RANGE`)

*Rule* · [Lean comment: `Core/Async/BulkExecution.lean` L183-L210](../../Core/Async/BulkExecution.lean#L183-L210)

An execution is unsafe when the destination range of a `.cp_mask` bulk copy covers a byte that is not allocated at launch, whichever bytes its mask selects.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`MaskedRangeUnalloc`](../../Core/Async/BulkExecution.lean#L212-L214), [`not_maskedRangeUnalloc_of_none`](../../Core/Async/BulkExecution.lean#L216-L219)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.4.1: "The memory range [dstMem, dstMem + size - 1] must not overflow the destination
  memory space and the memory range [srcMem, srcMem + size - 1] must not overflow the source
  memory space. Otherwise, the behavior is undefined."
- §9.7.10.28.4.1: "The i-th bit in the 16-bit wide byteMask operand specifies whether the i-th
  byte of each 16-byte wide chunk of source data is copied to the destination."

**Applies:** Every linear copy whose writes are `WriteMode.masked` (THREAD-TMA), at issue, pending or completed.

**Premises:** A byte of the copy's whole destination range `[dstMem, dstMem + size - 1]` is unallocated in the launch memory.

**Effect:** Safety rejection (ERR-OBJECT-LIFETIME, `TmaUnsafe`). The footprint of a masked copy's write covers only the bytes its mask selects, so ERR-UNALLOCATED-ACCESS sees no other byte of the range; this check covers the rest. Its source range is a read footprint, which ERR-UNALLOCATED-ACCESS checks. THREAD-TMA bounds both ranges by the address range of their spaces (`bulkRangeOk`); this check rejects a destination range that reaches past the bytes allocated at launch. A range over an unallocated gap inside the space is rejected as well, which is stricter than the text.

</details>

<a id="err-tensor-fill-value"></a>
#### tensor load value adapters (`ERR-TENSOR-FILL-VALUE`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorSafety.lean` L14-L34](../../Core/Async/Tensor/TensorSafety.lean#L14-L34)

A tensor load is unsafe when it writes a byte that has no scalar value.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`TensorUnsafe`](../../Core/Async/Tensor/TensorSafety.lean#L36-L39) ([concept](#c-tensorunsafe))

<details>
<summary>Details for reviewers</summary>

- DEP-TENSOR-LOAD-BYTES (represented fill values)

**Applies:** Two-dimensional global-to-shared tensor loads

**Premises:** Every produced content has a scalar byte adapter.

**Effect:** Safety rejection. The box alignment is checked when the instruction is issued (`requireBoxAligned`, DEP-TENSOR-LOAD-EFFECTS). The lifetimes of the destination and mbarrier CTAs are checked by ERR-SHARED-LIFETIME. The mbarrier of the load is an mbarrier operand (`UsesMbar`): its initialization is ERR-MBAR-UNINITIALIZED, its storage ERR-UNALLOCATED-ACCESS, and its exact initialization lifetime is checked by ObjectPublished when the completion notification enters the object history. An issue is distinct from its write or notification completion.

</details>

<a id="err-reduction-no-rule"></a>
#### tensor and linear reduction rules (`ERR-REDUCTION-NO-RULE`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorSafety.lean` L41-L62](../../Core/Async/Tensor/TensorSafety.lean#L41-L62)

A tensor or linear reduction is unsafe when a performed element of it has no arithmetic rule.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`TensorStoreUnsafe`](../../Core/Async/Tensor/TensorSafety.lean#L64-L66) ([concept](#c-tensorstoreunsafe))

<details>
<summary>Details for reviewers</summary>

- ERR-FAULT-REASON (an instruction form without a rule)

**Applies:** Shared-to-global tensor issues and linear reductions

**Premises:** None beyond the issue and its performed reductions.

**Effect:** Safety rejection. The box alignment is checked when the instruction is issued (`requireBoxAligned`, DEP-TENSOR-LOAD-EFFECTS). A performed reduction element without an arithmetic rule (`ReduceNoRule`, and `CopyReduceNoRule` for a linear reduction, DEP-REDUCTION-VALUES) is a `noRule` fault, as a missing MMA rule is (ERR-TC-MMA). The lifetime of the source CTA is checked by ERR-SHARED-LIFETIME, whose completing stage is the read completion (`.readsDone`), and the read completion closes all source observations, including optional out-of-bounds reads.

</details>

<a id="err-tensor-large-oob"></a>
#### large allocation-class OOB backing requirement (`ERR-TENSOR-LARGE-OOB`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorAllocation.lean` L11-L42](../../Core/Async/Tensor/TensorAllocation.lean#L11-L42)

When a tensor load, store or prefetch with a tensor map of the large allocation class selects an out-of-bounds element, the global range of the device's minimum size that starts at the tensor base must be accessible. The execution is unsafe if the range is not accessible or if the device's minimum size is not known.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TensorLargeBacking`](../../Core/Async/Tensor/TensorAllocation.lean#L44-L48), [`TensorBackingMissing`](../../Core/Async/Tensor/TensorAllocation.lean#L50-L56) ([concept](#c-tensorbackingmissing)), [`TensorAllocationUnsafe`](../../Core/Async/Tensor/TensorAllocation.lean#L58-L66) ([concept](#c-tensorallocationunsafe)), [`tensorAllocationUnsafe_iff`](../../Core/Async/Tensor/TensorAllocation.lean#L68-L88)

<details>
<summary>Details for reviewers</summary>

- §5.5.3.3: "If a TMA operation performs an out-of-boundary access and the tensor-map object’s
    allocation class (see tensormap.replace ) is large, but the memory range [global_addr,
    global_addr + CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE) is not accessible, the
    behavior is undefined."
- CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE

**Applies:** Supported tiled tensor loads, stores and prefetches, with the actual tensor-map allocation class

**Premises:** An operation selects an out-of-bounds element (`TensorHasOob`, THREAD-TENSOR-TRANSFER-MAP) and the map class is large.

**Effect:** Safety rejects missing backing or an unknown device attribute. Ordinary accessed-byte allocation checks still apply independently. Mem0 allocation represents storage accessible for the kernel lifetime. Unknown byte contents are sufficient here, since this requirement concerns accessibility only. The minimum size is launch/device data, separate from any tile size or kernel assumption of successful accesses. EXT-LAUNCH must match it and the class to the actual hardware attribute and host-created descriptor. Device-side map updates are unsupported. A load, a store and a prefetch issue (THREAD-TENSOR-PREFETCH) are each checked with the elements they select, under the same condition.

</details>

### Representation of growth and progress

Entries that fix how effects grow and are counted.

<a id="correct-async-grow"></a>
#### extension preserves asynchronous observations (`CORRECT-ASYNC-GROW`)

*Rule* · [Lean comment: `Core/Async/AsyncCopy.lean` L128-L146](../../Core/Async/AsyncCopy.lean#L128-L146)

When an execution grows, every read, write and completion notification of an asynchronous copy, every element write and old-value read of an element-wise operation, every operand record and completion of an MMA, and every arrive-on of a `cp.async.mbarrier.arrive`, that is already present stays present with the same value.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`AsyncCopy.Extends`](../../Core/Async/AsyncCopy.lean#L149-L160)

<details>
<summary>Details for reviewers</summary>

- none (representation of execution growth)

**Applies:** Two finite-prefix observations of the same asynchronous operations

**Premises:** Read/write effects or notifications already occurred.

**Effect:** Extension relation; new effects may occur independently of thread-trace extension. `Execution.le` preserves reads-from choices separately.

</details>

<a id="correct-tensor-size"></a>
#### count the independent effects of one tensor copy (`CORRECT-TENSOR-SIZE`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorCopy.lean` L187-L206](../../Core/Async/Tensor/TensorCopy.lean#L187-L206)

The effects of a tensor load are counted as one for each recorded read, one for each recorded write and one for a completion notification. The count only measures progress and adds no permitted or forbidden behavior.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`TensorCopy.Effects.readSlots`](../../Core/Async/Tensor/TensorCopy.lean#L209-L210), [`TensorCopy.Effects.writeSlots`](../../Core/Async/Tensor/TensorCopy.lean#L212-L213), [`TensorCopy.Effects.size`](../../Core/Async/Tensor/TensorCopy.lean#L215-L216)

<details>
<summary>Details for reviewers</summary>

- none (finite progress measure)

**Applies:** A snapshot of the independent effects of one tensor load

**Premises:** Selected slots are the finite byte slots of that operation's descriptor.

**Effect:** A progress measure; no additional permitted or forbidden memory behavior. Each selected byte contributes at most one source read and one destination write; the operation contributes one completion notification. OOB fill need not read global memory. This counts recorded effects, including typed fill content that has no scalar byte.

</details>

<a id="correct-tensor-store-size"></a>
#### count output-copy effects and completion stages (`CORRECT-TENSOR-STORE-SIZE`)

*Rule* · [Lean comment: `Core/Async/Tensor/TensorStore.lean` L181-L197](../../Core/Async/Tensor/TensorStore.lean#L181-L197)

The effects of a tensor store are counted as one for each recorded read and write, one for read completion and one for full completion. The count only measures progress and adds no permitted or forbidden behavior.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`TensorStore.Effects.readSlots`](../../Core/Async/Tensor/TensorStore.lean#L199-L200), [`TensorStore.Effects.writeSlots`](../../Core/Async/Tensor/TensorStore.lean#L202-L203), [`TensorStore.Effects.size`](../../Core/Async/Tensor/TensorStore.lean#L205-L207)

<details>
<summary>Details for reviewers</summary>

- none (finite progress measure)

**Applies:** One output tensor operation's effects

**Premises:** Its descriptor determines a finite set of byte slots.

**Effect:** A progress measure only.

</details>
