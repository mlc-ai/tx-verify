# tcgen05

How the model treats the `tcgen05` instructions other than Tensor Memory allocation: the MMA kinds and descriptors, where operands and results lie in shared and Tensor Memory, the cells that loads, stores and copies access, `tcgen05.commit`, the tcgen05 fences, the order in which the Tensor Core performs its accesses and the values it produces. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [Instructions and events](#instructions-and-events)
    - [`CtaGroup`](#c-ctagroup)
    - [`MmaKind`](#c-mmakind)
    - [`TcMmaInstr`](#c-tcmmainstr)
    - [`MmaCollector`](#c-mmacollector)
    - [`TcCpShape`](#c-tccpshape)
    - [`TcLdRed`](#c-tcldred)
    - [`TcShape`](#c-tcshape)
    - [`TcKind`](#c-tckind)
    - [`Execution.MmaIssue`](#c-execution-mmaissue)
    - [`Execution.CpIssue`](#c-execution-cpissue)
    - [`Execution.TLd`](#c-execution-tld)
    - [`Execution.TSt`](#c-execution-tst)
    - [`Execution.Commit`](#c-execution-commit)
    - [`Execution.TcAsync`](#c-execution-tcasync)
    - [`AsyncCopy.MmaOperands`](#c-asynccopy-mmaoperands)
  - [Descriptors](#descriptors)
    - [`TcShared.Descriptor`](#c-tcshared-descriptor)
    - [`TcMma.F8f6f4`](#c-tcmma-f8f6f4)
    - [`TcMma.Kind`](#c-tcmma-kind)
    - [`TcMma.Descriptor`](#c-tcmma-descriptor)
    - [`TcMma.Valid`](#c-tcmma-valid)
  - [Operands and results](#operands-and-results)
    - [`TcMma.OperandSpec`](#c-tcmma-operandspec)
    - [`TcMma.Collectors`](#c-tcmma-collectors)
    - [`TcMma.Cell`](#c-tcmma-cell)
    - [`TcMma.resultCell`](#c-tcmma-resultcell)
    - [`TcMma.writeCell`](#c-tcmma-writecell)
    - [`Execution.MmaCell`](#c-execution-mmacell)
    - [`Execution.MmaReadCell`](#c-execution-mmareadcell)
  - [Load, store and copy cells](#load-store-and-copy-cells)
    - [`tcDataAddressOk`](#c-tcdataaddressok)
    - [`tcDataCell`](#c-tcdatacell)
    - [`TcCopy.Spec`](#c-tccopy-spec)
  - [Commit](#commit)
    - [`TcCommit.Spec`](#c-tccommit-spec)
    - [`TcCommit.target`](#c-tccommit-target)
  - [Ordering and completion](#ordering-and-completion)
    - [`Execution.FenceBefore`](#c-execution-fencebefore)
    - [`TcMma.CommitObserved`](#c-tcmma-commitobserved)
    - [`ExecOrder`](#c-execorder)
    - [`TcMma.TcBefore`](#c-tcmma-tcbefore)
    - [`TcMma.CompletedBefore`](#c-tcmma-completedbefore)
    - [`TcMma.Pipelined`](#c-tcmma-pipelined)
    - [`TcMma.PipeAccess`](#c-tcmma-pipeaccess)
    - [`TcMma.Before`](#c-tcmma-before)
    - [`TcMma.TmemWrite`](#c-tcmma-tmemwrite)
    - [`TcMma.WriteBefore`](#c-tcmma-writebefore)
    - [`TcMma.ReadBefore`](#c-tcmma-readbefore)
  - [Values](#values)
    - [`TcMma.eval`](#c-tcmma-eval)
    - [`TcMma.Result`](#c-tcmma-result)
    - [`TcMma.Wrote`](#c-tcmma-wrote)
    - [`TcMma.TmemRead`](#c-tcmma-tmemread)
    - [`TcMma.ReadSource`](#c-tcmma-readsource)
    - [`TcMma.ReadOk`](#c-tcmma-readok)
  - [Safety](#safety)
    - [`TcMma.SourceUnsafe`](#c-tcmma-sourceunsafe)
    - [`TcMma.InstructionUnsafe`](#c-tcmma-instructionunsafe)
    - [`TcMma.WritesUnsafe`](#c-tcmma-writesunsafe)
    - [`TcMma.ReadsUnsafe`](#c-tcmma-readsunsafe)
    - [`Kernel.TcGroupUniform`](#c-kernel-tcgroupuniform)
    - [`TcMma.CollectorSafe`](#c-tcmma-collectorsafe)
- [Rules](#rules)
  - [What a tcgen05 instruction does](#what-a-tcgen05-instruction-does)
    - [tcgen05.mma forms](#prog-isa-tc-mma) (`PROG-ISA-TC-MMA`)
    - [tcgen05.ld.red](#prog-isa-tc-ld-red) (`PROG-ISA-TC-LD-RED`)
    - [tcgen05.cp shapes and decompression](#prog-isa-tc-cp) (`PROG-ISA-TC-CP`)
    - [Tensor Core operations as events](#thread-tc-event) (`THREAD-TC-EVENT`)
    - [tcgen05 instructions](#thread-tc) (`THREAD-TC`)
    - [the reduction value of tcgen05.ld.red](#thread-tc-ld-red) (`THREAD-TC-LD-RED`)
    - [full-completion commit issue](#thread-tc-commit) (`THREAD-TC-COMMIT`)
    - [16-bit multicast target selection](#thread-tc-commit-targets) (`THREAD-TC-COMMIT-TARGETS`)
    - [shared matrix descriptor fields](#thread-tc-shared-descriptor) (`THREAD-TC-SHARED-DESCRIPTOR`)
    - [canonical operand byte addresses](#thread-tc-shared-address) (`THREAD-TC-SHARED-ADDRESS`)
    - [dense instruction descriptor and shape](#thread-tc-mma-descriptor) (`THREAD-TC-MMA-DESCRIPTOR`)
    - [shared operand locations of a CTA group](#thread-tc-mma-operands) (`THREAD-TC-MMA-OPERANDS`)
    - [D matrix cells and lane masks](#thread-tc-mma-result-layout) (`THREAD-TC-MMA-RESULT-LAYOUT`)
      - [the operand and result layouts of tcgen05.mma](#ext-tcfig) (`EXT-TCFIG`)
    - [Tensor Memory cells of tcgen05.ld and tcgen05.st](#thread-tc-data-address) (`THREAD-TC-DATA-ADDRESS`)
      - [the layout readings of tcgen05.ld and tcgen05.st](#ext-tmem-lane-field) (`EXT-TMEM-LANE-FIELD`)
    - [tcgen05.ld .pack::16b and tcgen05.st .unpack::16b](#thread-tc-pack16) (`THREAD-TC-PACK16`)
    - [shared source and Tensor Memory destination of tcgen05.cp](#thread-tc-cp-cells) (`THREAD-TC-CP-CELLS`)
      - [the row and lane maps and the decompression of tcgen05.cp](#ext-tccp) (`EXT-TCCP`)
    - [the bytes a decompressing tcgen05.cp writes](#thread-tc-cp-decompress) (`THREAD-TC-CP-DECOMPRESS`)
    - [the Tensor Memory cells of tcgen05.shift](#thread-tc-shift-cells) (`THREAD-TC-SHIFT-CELLS`)
      - [the rows and lanes of tcgen05.shift](#ext-tcshift) (`EXT-TCSHIFT`)
  - [Order and completion](#order-and-completion)
    - [warp-collective tcgen05 instances](#dep-tc-collective) (`DEP-TC-COLLECTIVE`)
      - [the execution ordering of tcgen05 fences](#ext-tc-exec-order) (`EXT-TC-EXEC-ORDER`)
    - [completion of Tensor Memory accesses](#dep-tc-completion) (`DEP-TC-COMPLETION`)
      - [acquire synchronization orders tcgen05 operations](#ext-tcacquire) (`EXT-TCACQUIRE`)
    - [the pipelined pairs of tcgen05 operations](#dep-tc-pipeline) (`DEP-TC-PIPELINE`)
    - [Tensor Memory write order and read sources](#dep-tc-read-source) (`DEP-TC-READ-SOURCE`)
    - [Tensor Memory stores and their completion](#dep-tmem-store-value) (`DEP-TMEM-STORE-VALUE`)
    - [Tensor Memory words written by tcgen05.cp](#dep-tmem-copy-value) (`DEP-TMEM-COPY-VALUE`)
    - [the words tcgen05.shift leaves](#dep-tmem-shift-value) (`DEP-TMEM-SHIFT-VALUE`)
    - [identical-footprint D-write completion closure](#dep-tc-completion-closure) (`DEP-TC-COMPLETION-CLOSURE`)
  - [Values](#values)
    - [finite derivations of MMA accumulator values](#dep-tc-mma-value) (`DEP-TC-MMA-VALUE`)
      - [integer accumulation wraps modulo 2^32](#ext-tci8-wrap) (`EXT-TCI8-WRAP`)
      - [FP32 inputs of kind::tf32](#ext-tctf32) (`EXT-TCTF32`)
    - [the values that Tensor Memory loads and A reads return](#dep-tc-load-value) (`DEP-TC-LOAD-VALUE`)
  - [What counts as an error](#what-counts-as-an-error)
    - [every Tensor Memory read has a source](#err-tmem-read-source) (`ERR-TMEM-READ-SOURCE`)
    - [issue coverage and completed result coverage](#err-tc-mma) (`ERR-TC-MMA`)
    - [collector buffer reuse](#err-tc-collector-reuse) (`ERR-TC-COLLECTOR-REUSE`)
    - [Tensor Memory write conflicts](#err-tmem-race) (`ERR-TMEM-RACE`)
    - [one tcgen05 CTA-group qualifier per kernel](#prog-tc-cta-group) (`PROG-TC-CTA-GROUP`)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### Instructions and events

The qualifiers of the tcgen05 instructions, the events they produce, and the parts of an execution that record their asynchronous reads and completions.

<a id="c-ctagroup"></a>
#### `CtaGroup`

*inductive*

The `.cta_group` qualifier: an aligned block of one or two cluster ranks.

- `one`
- `two`

[Lean source: `Core/Isa/Tc.lean` L86-L89](../../Core/Isa/Tc.lean#L86-L89)

<a id="c-mmakind"></a>
#### `MmaKind`

*inductive*

The `.kind` qualifier of `tcgen05.mma`.

- `i8`
- `f16`
- `tf32`
- `f8f6f4`
- `mxf8f6f4`
- `mxf4`
- `mxf4nvf4`
- `ti16`

[Lean source: `Core/Isa/Tc.lean` L95-L98](../../Core/Isa/Tc.lean#L95-L98)

<a id="c-tcmmainstr"></a>
#### `TcMmaInstr`

*structure*

A `tcgen05.mma` instruction (PROG-ISA-TC-MMA).

- `group`
- `ws`: `.ws` (weight stationary, `cta_group::1` only).
- `kind`
- `d`: The register of `[d-tmem]`.
- `a`
- `bdesc`
- `idesc`
- `mask`: The disable-output-lane words, `4 * group size` of them.
- `enableD`
- `zeroColumnMask`: The 64-bit `zero-column-mask-desc` of `.ws`.
- `collectorA`
- `collectorB`
- `bBuffer`: The B collector buffer: `b<n>` of `.ws`, 0 otherwise.
- `ashift`
- `sparse`: `.sp`: the address of `[sp-meta-tmem]`.
- `scale`
- `lut`: `.decompress::lut::b`: the address of `[b-decompress-metadata]`.

[Lean source: `Core/Isa/Tc.lean` L130-L156](../../Core/Isa/Tc.lean#L130-L156)

<a id="c-mmacollector"></a>
#### `MmaCollector`

*inductive*

A collector buffer usage (§9.7.18.10.10.1): `fill` loads the matrix into the buffer, `use`
and `lastuse` may read it from the buffer (`lastuse` then frees it), and `discard` frees it.

- `fill`
- `use`
- `lastuse`
- `discard`

[Lean source: `Core/Isa/Tc.lean` L100-L104](../../Core/Isa/Tc.lean#L100-L104)

<a id="c-tccpshape"></a>
#### `TcCpShape`

*inductive*

A `tcgen05.cp` shape with its multicast: `.64x128b` with `.warpx2::02_13` (`warps0213`) or
`.warpx2::01_23`, and `.32x128b` with `.warpx4`.

- `s128x256b`
- `s128x128b`
- `s64x128b`
- `s32x128b`
- `s4x256b`

[Lean source: `Core/Isa/Tc.lean` L365-L373](../../Core/Isa/Tc.lean#L365-L373)

<a id="c-tcldred"></a>
#### `TcLdRed`

*structure*

The reduction of a `tcgen05.ld.red` and its destination `redval`.

- `isMax`
- `ty`
- `abs`
- `nan`
- `dst`

[Lean source: `Core/Isa/Tc.lean` L309-L316](../../Core/Isa/Tc.lean#L309-L316)

<a id="c-tcshape"></a>
#### `TcShape`

*inductive*

The access shape of `tcgen05.ld` and `tcgen05.st` (§9.7.18.8.3, §9.7.18.8.4: ".shape1 = {
.16x64b, .16x128b, .16x256b, .32x32b }", ".shape2 = { .16x32bx2 }"). `.16x32bx2` carries its
`immHalfSplitoff` operand. `packed16 s` is shape `s` with `.pack::16b` (`tcgen05.ld`) or
`.unpack::16b` (`tcgen05.st`): each register of `s` is two 16-bit halves in two adjacent columns
(THREAD-TC-PACK16).

- `s32x32b`
- `s16x64b`
- `s16x128b`
- `s16x256b`
- `s16x32bx2`
- `packed16`

[Lean source: `Core/Source/Instr.lean` L86-L98](../../Core/Source/Instr.lean#L86-L98)

<a id="c-tckind"></a>
#### `TcKind`

*inductive*

The `tcgen05` instructions as thread events: allocation management, MMA issue, commit, fence,
load, store, wait and copy (THREAD-TC-EVENT).

- `resource`: Allocation management: `tcgen05.alloc` (with the destination of the returned address), `tcgen05.dealloc` or `relinquish_alloc_permit`.
- `mma`: A dense MMA issue with its output-lane mask; actual operand reads belong to the async snapshot.
- `commit`: `tcgen05.commit`: one completion notification per selected cluster rank's mbarrier.
- `fenceBefore`
- `fenceAfter`
- `ld`: `tcgen05.ld` of shape `shape` from Tensor Memory address `a`, returning `vals`.
- `waitLd`: `tcgen05.wait::ld`.
- `st`: `tcgen05.st` of shape `shape` of `vals` to Tensor Memory address `a`.
- `waitSt`: `tcgen05.wait::st`.
- `cp`: `tcgen05.cp` of the copy `spec` (THREAD-TC-CP-CELLS); its source reads and completion are asynchronous effects.
- `shift`: `tcgen05.shift` of the shift `spec` (THREAD-TC-SHIFT-CELLS); its Tensor Memory reads, writes and completion are asynchronous effects.

[Lean source: `Core/Data/Types.lean` L100-L129](../../Core/Data/Types.lean#L100-L129)

<a id="c-execution-mmaissue"></a>
#### `Execution.MmaIssue`

*def*

An MMA issue fixes addresses and operation parameters, but no future read values.
Destination, accumulation and lane masks are preserved.

[Lean source: `Core/Data/Events.lean` L175-L179](../../Core/Data/Events.lean#L175-L179)

<a id="c-execution-cpissue"></a>
#### `Execution.CpIssue`

*def*

`e` issues the `tcgen05.cp` `c` (THREAD-TC-CP-CELLS). Its source reads and its completion are
asynchronous stages.

[Lean source: `Core/Data/Events.lean` L220-L223](../../Core/Data/Events.lean#L220-L223)

<a id="c-execution-tld"></a>
#### `Execution.TLd`

*def*

`e` is a `tcgen05.ld` of access shape `shape` from Tensor Memory address `a` that returns
the values `vals`.

[Lean source: `Core/Data/Events.lean` L207-L210](../../Core/Data/Events.lean#L207-L210)

<a id="c-execution-tst"></a>
#### `Execution.TSt`

*def*

`e` is a `tcgen05.st` of access shape `shape` that stores the values `vals` to Tensor Memory
address `a`.

[Lean source: `Core/Data/Events.lean` L215-L218](../../Core/Data/Events.lean#L215-L218)

<a id="c-execution-commit"></a>
#### `Execution.Commit`

*def*

`e` is a `tcgen05.commit` with specification `s`, which names its mbarrier and the cluster
ranks that receive a completion notification.

[Lean source: `Core/Data/Events.lean` L171-L173](../../Core/Data/Events.lean#L171-L173)

<a id="c-execution-tcasync"></a>
#### `Execution.TcAsync`

*def*

An asynchronous tcgen05 operation whose completion `tcgen05.commit` tracks: an MMA, a copy
or a shift (§9.7.18.6.2.1.1).

[Lean source: `Core/Data/Events.lean` L230-L234](../../Core/Data/Events.lean#L230-L234)

<a id="c-asynccopy-mmaoperands"></a>
#### `AsyncCopy.MmaOperands`

*structure*

Values returned by independent MMA operand reads. They are absent at issue.

- `a`
- `b`

[Lean source: `Core/Data/AsyncTypes.lean` L234-L237](../../Core/Data/AsyncTypes.lean#L234-L237)

### Descriptors

The shared matrix descriptor that locates an operand in shared memory, and the instruction descriptor that fixes the kind and shape of an MMA.

<a id="c-tcshared-descriptor"></a>
#### `TcShared.Descriptor`

*structure*

A decoded 64-bit shared matrix descriptor (§9.7.18.4.1 Table 49), which locates an MMA or
copy operand in shared memory. The address and offset fields are in bytes.

- `start`: The matrix start address: bits 0 to 14 times 16.
- `leading`: The leading dimension byte offset, or the absolute leading address when `leadingAbsolute` is set: bits 16 to 30 times 16.
- `stride`: The stride dimension byte offset: bits 32 to 45 times 16.
- `baseOffset`: The matrix base offset: bits 49 to 51.
- `leadingAbsolute`: Bit 52: the leading field holds an absolute address.
- `lutSecondSegment`: Bit 53: the lookup-table second-segment flag.
- `swizzle`: The swizzling mode: bits 61 to 63.

[Lean source: `Core/Tc/TcSharedDescriptor.lean` L70-L88](../../Core/Tc/TcSharedDescriptor.lean#L70-L88)

<a id="c-tcmma-f8f6f4"></a>
#### `TcMma.F8f6f4`

*inductive*

An element type of `kind::f8f6f4` (Table 51: "E4M3 = 0 E5M2 = 1 E2M3 = 3 E3M2 = 4 E2M1 =
5").

- `e4m3`
- `e5m2`
- `e2m3`
- `e3m2`
- `e2m1`

[Lean source: `Core/Tc/TcMmaDescriptor.lean` L66-L70](../../Core/Tc/TcMmaDescriptor.lean#L66-L70)

<a id="c-tcmma-kind"></a>
#### `TcMma.Kind`

*inductive*

The kind of a dense MMA with its element types, given by the `.kind` qualifier and the type
fields of the instruction descriptor.

- `i8`: `kind::i8`: unsigned or signed 8-bit inputs, 32-bit integer D, optionally saturating (descriptor bit 3).
- `f16`: `kind::f16`: FP16 or BF16 inputs, FP16 or FP32 D.
- `tf32`: `kind::tf32`: TF32 inputs in 32-bit containers, FP32 D.
- `f8f6f4`: `kind::f8f6f4`: 8-, 6- or 4-bit floating A and B in one-byte containers, FP16 or FP32 D.

[Lean source: `Core/Tc/TcMmaDescriptor.lean` L82-L94](../../Core/Tc/TcMmaDescriptor.lean#L82-L94)

<a id="c-tcmma-descriptor"></a>
#### `TcMma.Descriptor`

*structure*

A decoded instruction descriptor of a dense `tcgen05.mma` (§9.7.18.4.2 Table 51), together
with the CTA group and `.ws` mode of the instruction.

- `group`: The `.cta_group` of the instruction.
- `kind`: The kind and element types.
- `m`: The M dimension: bits 24 to 28 times 16.
- `n`: The N dimension: bits 17 to 22 times 8.
- `negateA`: Negate A (bit 13).
- `negateB`: Negate B (bit 14).
- `transposeA`: Transpose A (bit 15): A is MN-major.
- `transposeB`: Transpose B (bit 16): B is MN-major.
- `ws`: Weight-stationary issue (`tcgen05.mma.ws`, cta_group::1 only).

[Lean source: `Core/Tc/TcMmaDescriptor.lean` L110-L131](../../Core/Tc/TcMmaDescriptor.lean#L110-L131)

<a id="c-tcmma-valid"></a>
#### `TcMma.Valid`

*def*

The decoded descriptor is a supported dense MMA: a shape of Table 48 for its CTA group and
`.ws` mode, types and negation allowed for its kind, and transposition within the limits of
Table 63.

[Lean source: `Core/Tc/TcMmaDescriptor.lean` L169-L173](../../Core/Tc/TcMmaDescriptor.lean#L169-L173)

### Operands and results

Where the bytes of the A and B operands are read and where each element of D is written.

<a id="c-tcmma-operandspec"></a>
#### `TcMma.OperandSpec`

*structure*

Frozen addressing data of one issue; no operand values are captured here. `lowCta`
holds the first `extent / group.size` rows of each operand and `highCta` the rest; with
`cta_group::1` both are the issuer's CTA.

- `descriptor`: The decoded instruction descriptor.
- `a`: The shared matrix descriptor of A.
- `b`: The shared matrix descriptor of B.
- `lowCta`: The CTA holding the first half of the rows: the pair's even-rank CTA, or the issuer with `cta_group::1`.
- `highCta`: The CTA holding the second half of the rows: the pair's odd-rank CTA, or the issuer with `cta_group::1`.
- `aTmem`: `some address`: A is read from Tensor Memory at `address` (`[a-tmem]`); `s.a` is then unused. `none`: A is in shared memory.
- `collector`: The collector usage of the issue.

[Lean source: `Core/Tc/TcMmaOperands.lean` L82-L103](../../Core/Tc/TcMmaOperands.lean#L82-L103)

<a id="c-tcmma-collectors"></a>
#### `TcMma.Collectors`

*structure*

The collector usage of one issue: of A, and of B with its buffer (PROG-ISA-TC-MMA). The
collector rule is ERR-TC-COLLECTOR-REUSE; the operand locations do not depend on it.

- `a`
- `b`
- `bBuffer`

[Lean source: `Core/Tc/TcMmaOperands.lean` L74-L80](../../Core/Tc/TcMmaOperands.lean#L74-L80)

<a id="c-tcmma-cell"></a>
#### `TcMma.Cell`

*structure*

A 32-bit word of Tensor Memory: one lane and one column of the Tensor Memory of one CTA.

- `cta`: The CTA whose Tensor Memory holds the word.
- `lane`: The lane, from 0 to 127.
- `column`: The column.

[Lean source: `Core/Tc/TcMmaResultLayout.lean` L175-L183](../../Core/Tc/TcMmaResultLayout.lean#L175-L183)

<a id="c-tcmma-resultcell"></a>
#### `TcMma.resultCell`

*def*

The Tensor Memory cell of element (`row`, `col`) of D for an MMA with operands `s` and D
address `base`, by the layout of its shape (§9.7.18.10.5); `none` for an invalid shape, a lane
field that is not a permitted alignment, a coordinate out of range or columns past the 512th.

[Lean source: `Core/Tc/TcMmaResultLayout.lean` L205-L221](../../Core/Tc/TcMmaResultLayout.lean#L205-L221)

<a id="c-tcmma-writecell"></a>
#### `TcMma.writeCell`

*def*

The cell that element (`row`, `col`) of D is written to: its result cell, unless the bit of
its lane in the disable-output-lane mask is 1. The mask numbers 128 lanes per CTA of the group,
the first CTA's lanes first.

[Lean source: `Core/Tc/TcMmaResultLayout.lean` L257-L266](../../Core/Tc/TcMmaResultLayout.lean#L257-L266)

<a id="c-execution-mmacell"></a>
#### `Execution.MmaCell`

*def*

Potential TMEM writes exist at issue, with physical CTA/lane/column identity.
Only unmasked result elements contribute; this is not an assertion of completion.

[Lean source: `Core/Data/Events.lean` L181-L185](../../Core/Data/Events.lean#L181-L185)

<a id="c-execution-mmareadcell"></a>
#### `Execution.MmaReadCell`

*def*

Potential old-D reads when accumulation is enabled. Output lane masks suppress
writes; they are not taken as a guarantee that an old-D read is suppressed.

[Lean source: `Core/Data/Events.lean` L187-L191](../../Core/Data/Events.lean#L187-L191)

### Load, store and copy cells

The Tensor Memory cell of each register of a load or store, and the cells a copy writes.

<a id="c-tcdataaddressok"></a>
#### `tcDataAddressOk`

*def*

Scope of the address `address` of a load or store of shape `s` by thread `g`: a supported
half-split offset, and a lane field that keeps the shape's lanes in the warp's chunk. Both
accesses of `.16x32bx2` have the lane field of `address`.

[Lean source: `Core/Tc/TcDataAddress.lean` L216-L220](../../Core/Tc/TcDataAddress.lean#L216-L220)

<a id="c-tcdatacell"></a>
#### `tcDataCell`

*def*

Register slot `j` of a load or store of shape `s` at `address` by thread `g`, in its issuing
CTA. The issue rule establishes `tcDataAddressOk`; this total adapter does not itself assert that
an arbitrary raw address can issue an instruction.

[Lean source: `Core/Tc/TcDataAddress.lean` L226-L233](../../Core/Tc/TcDataAddress.lean#L226-L233)

<a id="c-tccopy-spec"></a>
#### `TcCopy.Spec`

*structure*

An issued copy: the Tensor Memory address, the decoded source descriptor, the shape, the
CTAs that copy, the even CTA first, and the decompression.

- `address`
- `src`
- `shape`
- `ctas`
- `fmt`

[Lean source: `Core/Tc/TcCopy.lean` L158-L166](../../Core/Tc/TcCopy.lean#L158-L166)

### Commit

The mbarriers that one `tcgen05.commit` signals.

<a id="c-tccommit-spec"></a>
#### `TcCommit.Spec`

*structure*

The targets of one `tcgen05.commit`: the addressed mbarrier, the multicast mask and the
issuer's cluster.

- `group`: The `.cta_group` of the commit.
- `mbar`: The addressed mbarrier, in shared memory of a CTA of the issuer's cluster.
- `mask`: The 16-bit multicast mask; bit `r` selects cluster rank `r`.
- `clusterBase`: The CTA number of rank 0 of the issuer's cluster.
- `clusterSize`: The number of CTAs in the cluster.

[Lean source: `Core/Tc/TcCommitTargets.lean` L31-L44](../../Core/Tc/TcCommitTargets.lean#L31-L44)

<a id="c-tccommit-target"></a>
#### `TcCommit.target`

*def*

The mbarrier that cluster rank `rank` receives an arrive-on at: the offset of the addressed
mbarrier in that rank's CTA, when the rank's mask bit is set.

[Lean source: `Core/Tc/TcCommitTargets.lean` L56-L61](../../Core/Tc/TcCommitTargets.lean#L56-L61)

### Ordering and completion

When one tcgen05 operation is ordered before another, and when an asynchronous operation has completed before an event.

<a id="c-execution-fencebefore"></a>
#### `Execution.FenceBefore`

*def*

`e` is a `tcgen05.fence::before_thread_sync`.

[Lean source: `Core/Data/Events.lean` L201-L202](../../Core/Data/Events.lean#L201-L202)

<a id="c-tcmma-commitobserved"></a>
#### `TcMma.CommitObserved`

*def*

The successful wait `w`, relaxed or acquire, observes the arrive-on of a commit that tracks
`mma`. The arrive-on has cluster scope; the wait's scope includes the committing thread, which
is the MMA's (`TracksMma`).

[Lean source: `Core/Tc/TcFence.lean` L140-L145](../../Core/Tc/TcFence.lean#L140-L145)

<a id="c-execorder"></a>
#### `ExecOrder`

*def*

EXT-TC-EXEC-ORDER: the execution ordering from `fence::before_thread_sync` `s` to
`fence::after_thread_sync` before `b`: base causality, or one mbarrier arrival
program-ordered after `s` observed by a wait followed by base causality.

[Lean source: `Core/Tc/TcFence.lean` L153-L157](../../Core/Tc/TcFence.lean#L153-L157)

<a id="c-tcmma-tcbefore"></a>
#### `TcMma.TcBefore`

*def*

tcgen05 operation `a` is ordered before tcgen05 operation `b`: by causality (program
order, or EXT-TCACQUIRE across threads) or by a fenced execution ordering.

[Lean source: `Core/Tc/TcFence.lean` L165-L168](../../Core/Tc/TcFence.lean#L165-L168)

<a id="c-tcmma-completedbefore"></a>
#### `TcMma.CompletedBefore`

*def*

Tensor Memory access `e` has completed before `d` by the completion mechanism of its kind:
a load by `wait::ld`, a store by `wait::st`, an MMA or copy by an observed commit.

[Lean source: `Core/Tc/TcMmaLifetime.lean` L113-L118](../../Core/Tc/TcMmaLifetime.lean#L113-L118)

<a id="c-tcmma-pipelined"></a>
#### `TcMma.Pipelined`

*def*

The pipelined pairs of §9.7.18.6.2: the access `cx` of the operation issued at `x` precedes
the access `cy` of the one issued at `y`. Each arm is one row of the table; a pipeline orders only
these Tensor Memory accesses, not the shared operands.

[Lean source: `Core/Tc/TcPipeline.lean` L79-L104](../../Core/Tc/TcPipeline.lean#L79-L104)

<a id="c-tcmma-pipeaccess"></a>
#### `TcMma.PipeAccess`

*inductive*

The Tensor Memory accesses that the rows of the pipeline table name: the A, C reads and D
writes of an MMA, the writes of a copy, and the writes of a store and reads of a load.

- `aRead`
- `cRead`
- `dWrite`
- `cpWrite`
- `stWrite`
- `ldRead`

[Lean source: `Core/Tc/TcPipeline.lean` L73-L77](../../Core/Tc/TcPipeline.lean#L73-L77)

<a id="c-tcmma-before"></a>
#### `TcMma.Before`

*def*

MMA `x`'s accumulator accesses precede MMA `y`'s: by completion or by the pipelined
C/D pairs (all three C/D rows share one condition).

[Lean source: `Core/Tc/TcMmaOrder.lean` L62-L65](../../Core/Tc/TcMmaOrder.lean#L62-L65)

<a id="c-tcmma-tmemwrite"></a>
#### `TcMma.TmemWrite`

*def*

A Tensor Memory write: an MMA result cell, a store, a copy or a shift.

[Lean source: `Core/Tc/TcMmaOrder.lean` L67-L69](../../Core/Tc/TcMmaOrder.lean#L67-L69)

<a id="c-tcmma-writebefore"></a>
#### `TcMma.WriteBefore`

*def*

Write `x` is ordered before `y`: an MMA by completion or pipeline, a store by
completion or pipeline, a copy by completion or the copy→A-read pipeline.

[Lean source: `Core/Tc/TcMmaOrder.lean` L71-L74](../../Core/Tc/TcMmaOrder.lean#L71-L74)

<a id="c-tcmma-readbefore"></a>
#### `TcMma.ReadBefore`

*def*

The read of kind `k` by the operation issued at `e` has happened before write `w`: by the
reader's completion mechanism, because `w` is the reading operation's own write, or by a
pipelined pair that starts at the read.

[Lean source: `Core/Tc/TcMmaOrder.lean` L91-L99](../../Core/Tc/TcMmaOrder.lean#L91-L99)

### Values

The value an MMA, a store or a copy leaves in a cell, and the value a load or a Tensor Memory A read returns.

<a id="c-tcmma-eval"></a>
#### `TcMma.eval`

*def*

The value of element (`row`, `col`) of D from the recorded A and B bytes and the old D
value: exact integer arithmetic for `kind::i8`, and for the floating kinds the first selected
numerical profile that gives a value.

[Lean source: `Core/Tc/TcMmaValue.lean` L146-L155](../../Core/Tc/TcMmaValue.lean#L146-L155)

<a id="c-tcmma-result"></a>
#### `TcMma.Result`

*inductive*

A logical result may be derived before its asynchronous completion is observed.
Publication to a consumer is a separate obligation.

- `overwrite`
- `accumulate`
- `accumulateStored`

[Lean source: `Core/Tc/TcMmaValue.lean` L157-L182](../../Core/Tc/TcMmaValue.lean#L157-L182)

<a id="c-tcmma-wrote"></a>
#### `TcMma.Wrote`

*def*

The value a Tensor Memory write leaves in `cell`.

[Lean source: `Core/Tc/TcMmaValue.lean` L236-L240](../../Core/Tc/TcMmaValue.lean#L236-L240)

<a id="c-tcmma-tmemread"></a>
#### `TcMma.TmemRead`

*inductive*

The kinds of Tensor Memory read: a register of a `tcgen05.ld`, the accumulator (C) read and
the A read of an MMA, and the read of a `tcgen05.shift`.

- `ld`
- `acc`
- `a`
- `shift`

[Lean source: `Core/Tc/TcMmaOrder.lean` L85-L89](../../Core/Tc/TcMmaOrder.lean#L85-L89)

<a id="c-tcmma-readsource"></a>
#### `TcMma.ReadSource`

*def*

`source` is the write whose word the read of kind `k` by `e` takes from `cell`: a write of
the cell, other than `e`, ordered before `e`, with every other write of the cell before the
source or after the read, and no release of the allocation between them.

[Lean source: `Core/Tc/TcMmaOrder.lean` L101-L109](../../Core/Tc/TcMmaOrder.lean#L101-L109)

<a id="c-tcmma-readok"></a>
#### `TcMma.ReadOk`

*def*

Loads and Tensor Memory A reads return the values of their sources.

[Lean source: `Core/Tc/TcMmaRead.lean` L69-L71](../../Core/Tc/TcMmaRead.lean#L69-L71)

### Safety

The checks whose failure makes an execution or a kernel unsafe.

<a id="c-tcmma-sourceunsafe"></a>
#### `TcMma.SourceUnsafe`

*def*

Some required Tensor Memory read has no source.

[Lean source: `Core/Tc/TcMmaRead.lean` L118-L120](../../Core/Tc/TcMmaRead.lean#L118-L120)

<a id="c-tcmma-instructionunsafe"></a>
#### `TcMma.InstructionUnsafe`

*def*

Some MMA or copy fails the checks of `InstructionSafe`.

[Lean source: `Core/Tc/TcMmaSafety.lean` L82-L84](../../Core/Tc/TcMmaSafety.lean#L82-L84)

<a id="c-tcmma-writesunsafe"></a>
#### `TcMma.WritesUnsafe`

*def*

Two Tensor Memory writes of one cell are ordered in neither direction.

[Lean source: `Core/Tc/TcMmaConflicts.lean` L52-L53](../../Core/Tc/TcMmaConflicts.lean#L52-L53)

<a id="c-tcmma-readsunsafe"></a>
#### `TcMma.ReadsUnsafe`

*def*

A read of the race check and a write of its cell are ordered in neither direction.

[Lean source: `Core/Tc/TcMmaConflicts.lean` L90-L91](../../Core/Tc/TcMmaConflicts.lean#L90-L91)

<a id="c-kernel-tcgroupuniform"></a>
#### `Kernel.TcGroupUniform`

*def*

The code of the kernel does not contain both `.cta_group::1` and `.cta_group::2`
instructions.

[Lean source: `Core/Tc/TcGroup.lean` L44-L46](../../Core/Tc/TcGroup.lean#L44-L46)

<a id="c-tcmma-collectorsafe"></a>
#### `TcMma.CollectorSafe`

*def*

Every reuse of a collector buffer has a fill that is still valid, a sole issuer and the
filling MMA's bytes.

[Lean source: `Core/Tc/TcMmaCollector.lean` L90-L97](../../Core/Tc/TcMmaCollector.lean#L90-L97)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers. The rules `DEP-TC-FENCE` and `ERR-TC-COMMIT-GROUP` are in the mbarrier chapter, and the rule `ERR-ALIGNED-MISMATCH` for the warp-collective instructions is in the barriers chapter.

### What a tcgen05 instruction does

The event each instruction produces, how its descriptors decode, and where its operands, results and register fragments lie.

<a id="prog-isa-tc-mma"></a>
#### tcgen05.mma forms (`PROG-ISA-TC-MMA`)

*Rule* · [Lean comment: `Core/Isa/Tc.lean` L18-L83](../../Core/Isa/Tc.lean#L18-L83)

A `tcgen05.mma` instruction is one value of `TcMmaInstr`: its CTA group, `.ws`, `.sp`, `.kind`, the D address, A in shared memory (a descriptor) or in Tensor Memory (an address), the B descriptor, the instruction descriptor, the disable-output-lane mask, `enable-input-d`, the zero-column mask, the collector usage of A and B, `.ashift`, the sparsity metadata address, the block-scale qualifier with the scale factor addresses, and the lookup-table address of `.decompress::lut::b`. Every `tcgen05.mma` entry of the `tc` family decodes to it.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`CtaGroup`](../../Core/Isa/Tc.lean#L86-L89) ([concept](#c-ctagroup)), [`CtaGroup.size`](../../Core/Isa/Tc.lean#L91-L93), [`MmaKind`](../../Core/Isa/Tc.lean#L95-L98) ([concept](#c-mmakind)), [`MmaCollector`](../../Core/Isa/Tc.lean#L100-L104) ([concept](#c-mmacollector)), [`MmaCollector.reuses`](../../Core/Isa/Tc.lean#L106-L109), [`TcMmaA`](../../Core/Isa/Tc.lean#L111-L115), [`MmaScaleVec`](../../Core/Isa/Tc.lean#L117-L120), [`MmaBlockScale`](../../Core/Isa/Tc.lean#L122-L128), [`TcMmaInstr`](../../Core/Isa/Tc.lean#L130-L156) ([concept](#c-tcmmainstr)), [`TcMmaInstr.dense`](../../Core/Isa/Tc.lean#L158-L162), [`Decode.ctaGroup?`](../../Core/Isa/Tc.lean#L167-L171), [`Decode.mmaKind?`](../../Core/Isa/Tc.lean#L173-L183), [`Decode.mmaCollectorA?`](../../Core/Isa/Tc.lean#L185-L191), [`Decode.mmaCollectorB?`](../../Core/Isa/Tc.lean#L193-L209), [`Decode.mmaScaleVec?`](../../Core/Isa/Tc.lean#L211-L219), [`Decode.tmemDst`](../../Core/Isa/Tc.lean#L221-L228), [`Decode.enableInput`](../../Core/Isa/Tc.lean#L230-L237), [`Decode.TcMmaInstr.ofRaw`](../../Core/Isa/Tc.lean#L239-L275), [`TcMmaInstr.rule`](../../Core/Isa/Tc.lean#L405-L411)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.10.10.1: "tcgen05.mma.cta_group.kind [d-tmem], a-desc, b-desc, idesc, {
    disable-output-lane }, enable-input-d {, scale-input-d};"
- §9.7.18.10.10.1: "If no .collector_a_usage qualifier is specified, then it defaults to
    .collector::a::discard ."
- §9.7.18.10.10.1: "If no .collector_b_usage qualifier is specified, then it defaults to
    .collector::b::discard ."
- §9.7.18.10.10.1: "The size of the vector is as follows: .cta_group Size of the vector
    disable-output-lane ::1 4 ::2 8"
- §9.7.18.10.10.2 (tcgen05.mma.sp)
- §9.7.18.10.10.3: "tcgen05.mma.ws.cta_group::1.kind{.collector_usage} [d-tmem], a-desc, b-desc,
    idesc, enable-input-d {, zero-column-mask-desc };"
- §9.7.18.10.10.3: "If no .collector_usage qualifier is specified, then it defaults to
    .collector::b0::discard ."
- §9.7.18.10.10.4 (tcgen05.mma.ws.sp)
- §4.5.3: "In PTX, integer constants may be used as predicates."

**Applies:** Every `tcgen05.mma` entry of the instruction table

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types.

**Effect:** Representation; `TcMmaInstr.rule` selects THREAD-TC for the forms with Core semantics. The D address and the Tensor Memory operands of the scale factors, the sparsity metadata and the lookup table are `[r]` or `[r+imm]`; the D address takes a register, written `[r]` or `[r+0]` (the zero offset is no offset), and the A address in Tensor Memory may carry a constant offset (THREAD-TC). Without the disable-output-lane operand (the `.ws` forms, the block-scaled forms and the forms of the ISA's examples that omit it) the mask is `4 * group size` zero words, so every lane is written. A missing collector qualifier is `discard`; the B collector of `.ws` is one of the buffers `b0` to `b3` (`bBuffer`), and the B collector without `.ws` is buffer 0. `.block32` and `.block16` are kept as written; which `.scale_vec::NX` they alias depends on the kind and K (§9.7.18.10.10.1). `TcMmaInstr.rule` gives THREAD-TC to the dense forms (no `.sp`, no `.block_scale`, no `.decompress::lut::b`, no `.ashift`) of `kind::i8`, `kind::f16`, `kind::tf32` and `kind::f8f6f4`, with any collector usage and with or without a zero-column mask. The other forms decode and have no rule, for these reasons. The block-scaled kinds (`kind::mxf8f6f4`, `kind::mxf4`, `kind::mxf4nvf4`): which Tensor Memory lanes and columns hold the scale factors of a row or column is given only by Figures 237 to 278 (§9.7.18.10.7.2, §9.7.18.10.7.3), and a rule needs, besides that layout, the scale factor reads of an MMA as Tensor Memory reads with their own sources, stability and conflicts, and the scale factor selectors of the instruction descriptor. `.sp`: the metadata layout in Tensor Memory is given only by Figures 287 to 292 (§9.7.18.10.9.4), and the metadata reads need the same Tensor Memory read rules. `.decompress::lut::b`: the lookup table layout and the compressed B layout are given only by Figures 279 to 282 (§9.7.18.10.8). `kind::ti16`: the text names the element type `.s1z4m11` ("a 16-bit signed integer with the range [-2 11 + 1, 2 11 - 1]") without its bit encoding. `.ashift`: the text says the rows of A are shifted down by one row "except for the last row in the Tensor Memory" without saying which rows form the matrix or what the first row then holds. A zero-column mask that generates a nonzero mask: Example 2 of §9.7.18.4.3 (Skip Span 2, Use Span 3, output `0b … 111 0000 111 0000`) starts with four used columns and continues with three zeroed columns, while Table 54 describes Skip Span as the count of used columns minus one and Use Span as the count of zeroed columns minus one, so the text and the example disagree on the mask.

</details>

<a id="prog-isa-tc-ld-red"></a>
#### tcgen05.ld.red (`PROG-ISA-TC-LD-RED`)

*Rule* · [Lean comment: `Core/Isa/Tc.lean` L279-L301](../../Core/Isa/Tc.lean#L279-L301)

A `tcgen05.ld.red` is a `tcgen05.ld` (`Op.tcLd`) with its reduction: `.min` or `.max`, the type `.u32`, `.s32` or `.f32`, the `.abs` and `.NaN` flags of the `.f32` form, and the destination `redval`. `.num` is at least `.x2`, and `redval` is not one of the loaded registers.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`TcRedType`](../../Core/Isa/Tc.lean#L304-L307), [`TcLdRed`](../../Core/Isa/Tc.lean#L309-L316) ([concept](#c-tcldred)), [`Decode.TcLdRed.ofRaw`](../../Core/Isa/Tc.lean#L321-L335)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.8.3: "tcgen05.ld.red.sync.aligned.shape3.num.redOp{.abs}{.NaN}.f32 r, redval, [taddr];"
- §9.7.18.8.3: "tcgen05.ld.red.sync.aligned.shape3.num.redOp.type r, redval, [taddr];"
- §9.7.18.8.3: ".redOp = { .min, .max } .type = { .u32, .s32 }"
- §9.7.18.8.3: "When .red qualifier is specified, .num modifier must be at least .x2 ."
- §6.4.3

**Applies:** The `tcgen05_ld_red` and `tcgen05_ld_red_split` entries

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at 32 bits.

**Effect:** Representation; the rule is THREAD-TC-LD-RED. The text does not say whether `redval` may be one of the loaded registers; the decoder rejects that case (stricter).

</details>

<a id="prog-isa-tc-cp"></a>
#### tcgen05.cp shapes and decompression (`PROG-ISA-TC-CP`)

*Rule* · [Lean comment: `Core/Isa/Tc.lean` L339-L362](../../Core/Isa/Tc.lean#L339-L362)

A `tcgen05.cp` is its CTA group, its shape with the multicast that the shape requires (`.128x256b`, `.4x256b`, `.128x128b`, `.64x128b.warpx2::02_13`, `.64x128b.warpx2::01_23`, `.32x128b.warpx4`), the Tensor Memory address `[taddr]`, the source descriptor and the decompression `.b8x16.b6x16_p32` or `.b8x16.b4x16_p64` when written.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`TcCpShape`](../../Core/Isa/Tc.lean#L365-L373) ([concept](#c-tccpshape)), [`TcCpFmt`](../../Core/Isa/Tc.lean#L375-L381), [`Decode.tcCpShape?`](../../Core/Isa/Tc.lean#L385-L394), [`Decode.tcCpFmt?`](../../Core/Isa/Tc.lean#L396-L401)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.9.2: "tcgen05.cp.cta_group.shape{.multicast}{.dst_fmt.src_fmt} [taddr], s-desc;"
- §9.7.18.9.2: ".shape = { .128x256b, .4x256b, .128x128b, .64x128b**, .32x128b*** }"
- §9.7.18.9.2: ".64x128b requires .warpx2::02_13 or .warpx2::01_23 .32x128b requires .warpx4"
- §9.7.18.9.2: ".src_fmt = { .b6x16_p32 , .b4x16_p64 } .dst_fmt = { .b8x16 }"

**Applies:** Every `tcgen05_cp` entry

**Premises:** The instruction is recognized by `Grammar.parse`.

**Effect:** Representation; the rule of a copy is THREAD-TC, its geometry THREAD-TC-CP-CELLS. A multicast written with another shape, or a shape written without the multicast it requires, is a decoding error; so is one of `.dst_fmt` and `.src_fmt` without the other (the table entry writes them as a pair).

</details>

<a id="thread-tc-event"></a>
#### Tensor Core operations as events (`THREAD-TC-EVENT`)

*Rule* · [Lean comment: `Core/Data/Types.lean` L66-L97](../../Core/Data/Types.lean#L66-L97)

Each `tcgen05` instruction is one event of a thread. An event records what the instruction names: the access shape of a load or store, the request of an allocation, or the destination, descriptors and output-lane mask of an MMA. The values that a load returns and the column that an allocation selects are left open, and the execution rules decide which are possible.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`TcKind`](../../Core/Data/Types.lean#L100-L129) ([concept](#c-tckind))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.1 (Tensor Memory)
- §9.7.18.7.1 (tcgen05.alloc, tcgen05.dealloc)
- §9.7.18.8.3 (tcgen05.ld)
- §9.7.18.8.4 (tcgen05.st)
- §9.7.18.8.5 (tcgen05.wait)
- §9.7.18.9.2 (tcgen05.cp)
- §9.7.18.10.10.1 (tcgen05.mma)
- §9.7.18.11.1 (tcgen05.fence)
- §9.7.18.12.1 (tcgen05.commit)

**Effect:** A `tcgen05` instruction is one event. A Tensor Memory address is a 32-bit value, lane in the high and column in the low 16 bits. What the hardware returns at a load is recorded in that event and left open. A load or store records its access shape (`TcShape`, with the `.16x32bx2` half-split offset), so every rule that reads its cells uses the same shape. An allocation event records the request only: the column is selected when the allocation completes, and is the value of the address store that follows it (THREAD-TC, OBJ-TMEM-ALLOC-RESULT). An MMA issue records its destination, its decoded descriptors with the CTA identities of its group, accumulation and output-lane mask; its operand bytes are recorded separately in the asynchronous snapshot when read. The execution rules (DEP-TC-MMA-VALUE, DEP-TC-LOAD-VALUE, OBJ-TMEM-ALLOC-RESULT) and reads-from constraints decide which observations are possible.

</details>

<a id="thread-tc"></a>
#### tcgen05 instructions (`THREAD-TC`)

*Rule* · [Lean comment: `Core/Tc/TcThread.lean` L21-L141](../../Core/Tc/TcThread.lean#L21-L141)

Each tcgen05 instruction produces one event of its thread after decoding its operands, and a form whose operands do not decode to a supported shape, descriptor or address has no rule. An MMA issue reads its descriptors and masks but no operand bytes, a load sets its destination registers at its own event to values that the execution rules decide, a store reads its 32-bit source registers at issue, and an allocation names only its request, after which lane 0 of the warp writes the allocated address, whose column the execution rules decide, to shared memory. `tcgen05.alloc` takes a 4-byte aligned shared address and a power of two from 32 to 512 columns. It is one request event per lane, which carries no column. Lane 0 then writes the address (lane 0, the column returned) to `dst` with a weak 32-bit generic-proxy store (§9.7.18.7.1: "The store operation in tcgen05.alloc is treated as a weak memory operation"; the text does not say which lane stores, the model says lane 0, EXT-TCALLOC-STORER). The thread state does not depend on the column. The stored column (the low 16 bits of the address) is open and is the allocator's result (OBJ-TMEM-ALLOC-RESULT). `tcgen05.dealloc` takes the same column counts. `tcgen05.mma` reads its destination address, both shared descriptors, the instruction descriptor, `4 * group size` output-lane mask words and the `enable-input-d` operand. It decodes the descriptors (THREAD-TC-SHARED-DESCRIPTOR, THREAD-TC-MMA-DESCRIPTOR) and resolves the group's CTAs from the launch (THREAD-TC-MMA-OPERANDS). A form it cannot decode has no rule, and shape, mask, address and lifetime coverage of a decoded issue are safety checks (ERR-TC-MMA). The `[a-tmem]` form reads A's Tensor Memory address, so the spec's `a` field is then unused. It is otherwise the same rule, except that a set Transpose A bit has no rule there (§9.7.18.10.6 gives the bit its M-major meaning for A in shared memory only, and nothing for A in Tensor Memory). With `.ws` and A in Tensor Memory it reads one A row per D lane when M < 128 (EXT-TCFIG). `tcgen05.mma.ws` (cta_group::1) has no lane-mask operand and is the same rule with an all-zero mask of four words (the decoder supplies it), so every lane is written. The issue records the collector usage of A and B in its operands (`TcMma.Collectors`). Which reuses are safe is ERR-TC-COLLECTOR-REUSE. A `.ws` zero-column mask descriptor is read at issue, and only one that generates the all-zero mask with no column shift (Table 54: "Value 0 indicates generated mask will have all 0s") has a rule (`zeroColumnMaskNone`). The issue is then that of the form without the operand. The mask that other values generate is described by Table 54 and its examples, whose start counts and spans the model does not decode, so they have no rule. The lane-mask operand of `tcgen05.mma` may be omitted: the ISA's own examples issue the instruction without it (§9.7.18.12.1: "tcgen05.mma.cta_group::2.kind::tf32 [taddr0], adesc, bdesc, idesc, p;"; §9.7.18.8.5: "tcgen05.mma.cta_group::1.kind::f16 [taddr0], a-desc, b-desc, idesc, p;"), and only a 1 bit of a supplied mask keeps a lane from being written (§9.7.18.10.10.1: "If a bit in the mask is 1, then the corresponding lane in the Tensor Memory for the resultant matrix D will not be updated."). Without it the decoder supplies `4 * group size` zero words, as for `.ws`, so every lane is written. `enable-input-d` is a predicate register, whose value must be a predicate, or an integer constant, false exactly when zero (§4.5.3: "In PTX, integer constants may be used as predicates. For predicate-type data initializers and instruction operands, integer constants are interpreted as in C, i.e., zero values are False and non-zero values are True ."). The same reading serves `.ws`. The A address of the `[a-tmem]` form may carry a constant offset, `[a-tmem+imm]` (the frozen FlashAttention-4 PTX uses `[tmem_a + 0x8]` to `[tmem_a + 0x38]`). A Tensor Memory address has no byte unit. It is a lane index (bits 31 to 16) and a column index (bits 15 to 0) (§9.7.18.1.1), so the address is the register with `imm` added to its column index, `r % 2^16 + imm` in lane field `r / 2^16` (`tmemOffset`). An offset that would leave the column field (below 0 or at `2^16` and above), and so carry into or borrow from the lane index, faults (stricter: the text gives no meaning to such a sum). The destination `[d-tmem]` takes a register only. `tcgen05.ld.<shape>.x<num>` of `n` registers (`n` is `.num` repetitions of the shape, Table 59, `TcShape.countOk`) takes its lane field as a lane of the issuing warp's chunk, absolute or relative, and a `.16x32bx2` half-split offset that stays in the column field. Each register's physical TMEM cell is selected by the shape's fragment, the warp's position within its warpgroup and the thread lane (THREAD-TC-DATA-ADDRESS, EXT-TMEM-LANE-FIELD). The event records the shape. It sets its destination registers at its own event, so a later instruction of the thread reads the loaded values whether or not a `tcgen05.wait::ld` comes between them. §9.7.18.6.4.5 gives this true register dependency: "For tcgen05.ld , an intra-thread ordering through true register dependency will be respected regardless of the presence or absence of other forms of synchronization." The same section says that it orders no memory access: "This form of register dependency does not imply any other form of ordering. For example, a register dependency does not imply that a dependee instruction’s memory accesses will be performed before a dependent instruction’s memory accesses. To enforce such memory orderings and avoiding anti-dependency hazards around tcgen05.ld , tcgen05.wait::ld must be used." The load's Tensor Memory read is therefore ordered before a later write of the cell only by the rules on Tensor Memory accesses: its thread's `tcgen05.wait::ld` followed by a tcgen05 order, or a later `tcgen05.st` of the same warp (`TcMma.ReadBefore .ld`, DEP-TC-READ-SOURCE, with DEP-TC-FENCE and EXT-TCACQUIRE). A write of a loaded cell that is not so ordered after the load leaves the register without a stable source and the execution unsafe (ERR-TMEM-READ-SOURCE), and a release needs the load completed by its `wait::ld` (`TcMma.CompletedBefore`, DEP-TC-COMPLETION). `tcgen05.st.<shape>.x<num>` has the same count, address and cell rules (Table 61) and reads its `n` source registers at issue (its Tensor Memory write is asynchronous). It moves data (§9.7.18.8: "The threads of the CTA can perform the loads and stores to the Tensor Memory of the CTA and move data between registers and Tensor Memory."; §9.7.18.8.4: "Instruction tcgen05.st asynchronously stores data from the source register r into the Tensor Memory"), so it reads each source as `st.shared` does (`storeTmpl`, THREAD-ACCESS): the register's value unchanged (`readValue`), a literal as its 32-bit pattern. A value that is not 4 bytes wide is a `typeMismatch` fault. The stored word is that value, so a packed pair of f16 payloads or an f32 payload reaches Tensor Memory without re-encoding. Fences and `tcgen05.wait::{ld,st}` are events. `tcgen05.cp` (single thread) reads its Tensor Memory address (lane field 0, the shape's columns in range) and decodes its shared descriptor. It copies into the issuer's CTA, or with `.cta_group::2` into both CTAs of the issuer's pair, which must be in the launch (THREAD-TC-CP-CELLS). `tcgen05.shift` (single thread) reads its Tensor Memory address (lane field 0, 8 columns in range) and shifts in the issuer's CTA, or with `.cta_group::2` in both CTAs of the pair (THREAD-TC-SHIFT-CELLS). An address out of range or a pair outside the launch is `badValue`.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`mmaEnable`](../../Core/Tc/TcThread.lean#L188-L195), [`tmemOffset`](../../Core/Tc/TcThread.lean#L197-L202), [`zeroColumnMaskNone`](../../Core/Tc/TcThread.lean#L204-L208), [`zeroColumnMaskOk`](../../Core/Tc/TcThread.lean#L210-L214), [`mmaSmemTmpl`](../../Core/Tc/TcThread.lean#L216-L235), [`mmaTmemTmpl`](../../Core/Tc/TcThread.lean#L237-L255), [`TcMmaInstr.collectors`](../../Core/Tc/TcThread.lean#L257-L259), [`mmaTmpl`](../../Core/Tc/TcThread.lean#L261-L270), [`tcTmpl`](../../Core/Tc/TcThread.lean#L415-L488), [`TcMmaInstr.rule_dense`](../../Core/Tc/TcThread.lean#L520-L525), [`tcTmpl_tcMma_smem`](../../Core/Tc/TcThread.lean#L527-L534), [`tcTmpl_tcMma_tmem`](../../Core/Tc/TcThread.lean#L536-L543)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.7.1 (tcgen05.alloc, tcgen05.dealloc)
- §9.7.18.10.10.1 (tcgen05.mma)
- §9.7.18.4 (descriptors)
- §9.7.18.5.1 (CTA pairs)
- §9.7.18.8.1 (access restrictions)
- §9.7.18.8.3 (tcgen05.ld)
- §9.7.18.8.4 (tcgen05.st)
- §9.7.18.8.5 (tcgen05.wait)
- §9.7.18.6.4.5 (register dependencies)
- §9.7.18.9.2 (tcgen05.cp)
- §9.7.18.9.3 (tcgen05.shift)
- §9.7.18.11.1 (tcgen05.fence)
- §9.7.18.12.1 (tcgen05.commit)
- §4.5.3 (predicate constants)
- §9.7.18.1.1: "Tensor Memory addresses are 32-bit wide and specify two components."
- EXT-TCALLOC-STORER

**Applies:** tcgen05.alloc, tcgen05.dealloc, tcgen05.relinquish_alloc_permit, the tcgen05.mma{.ws} forms that `TcMmaInstr.rule` names (kind::{i8,f16,tf32,f8f6f4}, dense) with shared A and B or with A in Tensor Memory (`[a-tmem]`, `[a-tmem+imm]`), with or without the lane-mask operand, with any collector usage and, for `.ws`, an optional zero-column mask, `enable-input-d` a predicate or a constant, tcgen05.fence, tcgen05.ld and tcgen05.st of every shape (`.32x32b`, `.16x64b`, `.16x128b`, `.16x256b`, `.16x32bx2`), with `.pack::16b` / `.unpack::16b` for the single-access shapes (THREAD-TC-PACK16), tcgen05.wait::ld, tcgen05.wait::st, tcgen05.cp of the shapes of PROG-ISA-TC-CP, tcgen05.shift

**Premises:** Operands read and decode to the supported forms below.

**Effect:** Event production and local faults. A warp is 32 consecutive threads (the CTA size must be a multiple of 32).

</details>

<a id="thread-tc-ld-red"></a>
#### the reduction value of tcgen05.ld.red (`THREAD-TC-LD-RED`)

*Rule* · [Lean comment: `Core/Tc/TcThread.lean` L272-L310](../../Core/Tc/TcThread.lean#L272-L310)

A `tcgen05.ld.red` sets its loaded registers as `tcgen05.ld` does and writes to `redval` the minimum or maximum of the values its thread loaded, as unsigned or signed 32-bit integers, or as FP32 numbers (their absolute values with `.abs`). The reduction runs over the registers of one thread, that is over the columns its lane loaded. The integer forms compare the 32-bit patterns as unsigned or two's-complement numbers. The `.f32` forms compare the FP32 numbers (THREAD-NUM). A loaded value that is not a 32-bit number, an FP32 NaN or infinity, and an FP32 extreme taken by values of different bits have no rule, and the thread's next event is `ub`.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`TcLdRed.reduceInt`](../../Core/Tc/TcThread.lean#L313-L324), [`TcLdRed.reduceF32`](../../Core/Tc/TcThread.lean#L326-L340), [`TcLdRed.reduce`](../../Core/Tc/TcThread.lean#L342-L347), [`ldResult`](../../Core/Tc/TcThread.lean#L349-L356), [`tcTmpl_tcLd_none`](../../Core/Tc/TcThread.lean#L490-L502)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.8.3: "The qualifier .red specifies that the reduction operation specified by .redOp is
    performed on the data that is loaded across columns in each lane."
- §9.7.18.8.3: "The result of the reduction operation is written into the corresponding thread’s
    32-bit destination register operand redVal ."
- §9.7.18.8.3: "If .abs qualifier is specified, the absolute values of the loaded data are
    considered for the reduction operation."
- §9.7.18.8.3: "If .NaN qualifier is specified, the result of the reduction operation is canonical
    NaN if either of the inputs to the reduction operation is NaN."

**Why it is not spec text:** The text does not say what a minimum or maximum of NaN is without `.NaN`. With `.NaN` the result is a NaN, which the model does not represent, so a NaN input has no rule in either case, as has an infinity (THREAD-NUM). The text does not order `-0` and `+0`, so when the extreme is taken by values of different bits (two zeros of opposite sign) there is no rule. With `.abs` the result is the absolute value, whose bits are determined.

**Applies:** tcgen05.ld.red of `.32x32b` and `.16x32bx2` with `.min` or `.max` and `.u32`, `.s32` or `.f32`

**Premises:** Every loaded value of the thread is a 4-byte value; for `.f32` each is a finite FP32 number, and without `.abs` the values that take the extreme have one bit pattern.

**Effect:** Local completion of the load's continuation (THREAD-TC): `redval` is set at the load's own event, with the loaded registers; a failed premise records the fault `noRule` for the thread's next event. A register dependency on `redval` orders like one on a loaded register (§9.7.18.6.4.5).

</details>

<a id="thread-tc-commit"></a>
#### full-completion commit issue (`THREAD-TC-COMMIT`)

*Rule* · [Lean comment: `Core/Tc/TcCommitThread.lean` L11-L31](../../Core/Tc/TcCommitThread.lean#L11-L31)

A `tcgen05.commit` produces one issue event that names its target mbarriers: without a multicast mask the addressed mbarrier, and with a mask the mbarrier at the same shared-memory offset in each selected CTA of the cluster. Each target receives its arrive-on when the asynchronous operations that the commit tracks complete.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`tcCommitTmpl`](../../Core/Tc/TcCommitThread.lean#L33-L44)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.12.1 (commit operands and multicast mask)

**Applies:** Full-completion commit, either cta_group, shared::cluster address, optional 16-bit multicast mask

**Premises:** The issuing thread exists, the mbarrier address is aligned shared memory in its cluster, and all selected ranks exist.

**Effect:** Issue event. Each target's arrival is an independent asynchronous effect. OBJ-MBAR-ORIGIN relates each arrive-on to the completion of the operations that the commit tracks.

</details>

<a id="thread-tc-commit-targets"></a>
#### 16-bit multicast target selection (`THREAD-TC-COMMIT-TARGETS`)

*Rule* · [Lean comment: `Core/Tc/TcCommitTargets.lean` L10-L29](../../Core/Tc/TcCommitTargets.lean#L10-L29)

Bit r of the 16-bit multicast mask of a `tcgen05.commit` selects the mbarrier at the addressed shared-memory offset in the CTA of cluster rank r, for every rank of the cluster, including ranks outside the issuer's CTA pair. A mask bit at or above the cluster size, or an mbarrier address outside the issuer's cluster, makes the issue fault.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcCommit.Spec`](../../Core/Tc/TcCommitTargets.lean#L31-L44) ([concept](#c-tccommit-spec)), [`TcCommit.resolve`](../../Core/Tc/TcCommitTargets.lean#L46-L54), [`TcCommit.target`](../../Core/Tc/TcCommitTargets.lean#L56-L61) ([concept](#c-tccommit-target))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.12.1 (tcgen05.commit multicast masks and same-offset targeting)

**Applies:** Full-completion tcgen05.commit; an unmasked commit selects only the addressed rank

**Premises:** A launched issuer, a shared mbarrier address in its cluster, whole-cluster launch topology, and selected mask ranks within the cluster.

**Effect:** Target addresses; each target has its own notification identity (OBJ-MBAR-ORIGIN) and receives its arrival at completion.

</details>

<a id="thread-tc-shared-descriptor"></a>
#### shared matrix descriptor fields (`THREAD-TC-SHARED-DESCRIPTOR`)

*Rule* · [Lean comment: `Core/Tc/TcSharedDescriptor.lean` L10-L38](../../Core/Tc/TcSharedDescriptor.lean#L10-L38)

A 64-bit shared matrix descriptor decodes into a start address, a leading and a stride byte offset (each encoded in 16-byte units), a base offset, the leading-absolute and LUT flags and one of five swizzling modes. The start and leading fields are bits 0–14 and 16–30, and the stride field is bits 32–45. A word with a set reserved bit, a version field other than 1 or an undocumented swizzle code does not decode, and the instruction that uses it has no rule.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcShared.Swizzle`](../../Core/Tc/TcSharedDescriptor.lean#L40-L44), [`TcShared.decodeSwizzle`](../../Core/Tc/TcSharedDescriptor.lean#L46-L53), [`TcShared.Swizzle.sectors`](../../Core/Tc/TcSharedDescriptor.lean#L55-L60), [`TcShared.Swizzle.offset`](../../Core/Tc/TcSharedDescriptor.lean#L62-L68), [`TcShared.Descriptor`](../../Core/Tc/TcSharedDescriptor.lean#L70-L88) ([concept](#c-tcshared-descriptor)), [`TcShared.decode`](../../Core/Tc/TcSharedDescriptor.lean#L90-L107)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.4.1 Table 49 and Table 50

**Applies:** 64-bit tcgen05 shared-memory matrix descriptors

**Premises:** The word has zero reserved bits, the fixed version field 001, and a documented swizzle code.

**Effect:** Field decoding, and the swizzle of each encoding (`Swizzle.sectors`, `Swizzle.offset`). The leading absolute-address flag is kept as a field, so absolute leading mode is never read as a relative offset, and the 32-byte-atomic swizzle has its own offset function, `TensorSwizzle.offset128x32`, distinct from the 16-byte-atomic one.

</details>

<a id="thread-tc-shared-address"></a>
#### canonical operand byte addresses (`THREAD-TC-SHARED-ADDRESS`)

*Rule* · [Lean comment: `Core/Tc/TcSharedAddress.lean` L10-L52](../../Core/Tc/TcSharedAddress.lean#L10-L52)

Element (row, k) of an MMA operand in shared memory lies at the offset that the canonical K-major or MN-major layout gives with the descriptor's strides and core matrices of 8 rows of 16 bytes, added to the start address and passed through the absolute-address XOR swizzle of the mode. No address exists for an absolute leading offset, the LUT mode, a nonzero base offset, the 32-byte-atomic 128-byte mode with a K-major operand or with MN-major 1- or 2-byte elements, or MN-major 4-byte elements in any other mode. A core-matrix row holds `16 / width` elements. K-major swizzled layouts ignore the leading stride, as the text specifies, and MN-major layouts use both strides. The 128-byte mode with 32-byte atomicity has swizzle atoms of 8 16-byte units along M or N by 4 along K, applies to MN-major layouts only, and is required exactly for 4-byte elements (the transposed kind::tf32 of Table 65).

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`TcShared.Major`](../../Core/Tc/TcSharedAddress.lean#L54-L58), [`TcShared.linear`](../../Core/Tc/TcSharedAddress.lean#L60-L76), [`TcShared.byteAddress`](../../Core/Tc/TcSharedAddress.lean#L78-L85)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.3.3 (canonical layouts: core matrices of 8 rows by 16 bytes, T = 16 / element bytes)
- §9.7.18.10.6 Table 67 (Layout for swizzle atoms, 128b element: the row for 128B swizzling with 32B
    atomicity gives 8x4 for M/N-major and no K-major atom; the row for 128B swizzling with 16B
    atomicity gives 8x8 for M/N-major and 8x8 for K-major)
- §9.7.18.10.3 Table 65 (for 32-bit elements, a transposed A or B is supported only with 128B
    swizzling with 32B atomicity; for 8-bit and 16-bit elements, a transposed A or B takes every
    swizzling mode except that one)
- §5.5.7 32-byte-atomicity pattern (THREAD-TENSOR-SWIZZLE); NVIDIA CUTLASS
    include/cute/arch/mma_sm100_desc.hpp make_umma_desc (Swizzle composed after shared pointer and
    layout; LayoutType::B128_BASE32B: Swizzle<2,5,2> o smem_ptr o ((8,n),(4,k)):((1,LBO),(8,SBO)),
    commented there as not applicable for Major-K)

**Applies:** 1-byte (kind::i8), 2-byte (kind::f16) and 4-byte (kind::tf32) elements in relative-leading canonical K-major or MN-major layouts, base-offset field zero; the 32-byte-atomic 128-byte mode only MN-major and only with 4-byte elements

**Premises:** Descriptor decoding and instruction shape checks are separate. The byte is within one element; absolute leading, LUT and shifted-pattern modes are not handled by this component.

**Effect:** Address calculation only. Unsupported modes return none, with no guessed address: K-major with the 32-byte-atomic mode, MN-major 4-byte elements with any other mode, and MN-major 1- and 2-byte elements with the 32-byte-atomic mode.

</details>

<a id="thread-tc-mma-descriptor"></a>
#### dense instruction descriptor and shape (`THREAD-TC-MMA-DESCRIPTOR`)

*Rule* · [Lean comment: `Core/Tc/TcMmaDescriptor.lean` L10-L64](../../Core/Tc/TcMmaDescriptor.lean#L10-L64)

The 32-bit instruction descriptor of a dense `tcgen05.mma` decodes into the element types, M, N and the negate and transpose flags, and is accepted only when the types fit the `.kind`, M and N form a shape of Table 48 for the CTA group and `.ws` mode, and the reserved, sparsity, K-dimension and shift bits are zero. K is fixed by the kind at 32 bytes per operand row: 32 8-bit, 16 16-bit or 8 TF32 elements, or 32 elements of `kind::f8f6f4` in one-byte containers.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`TcMma.F8f6f4`](../../Core/Tc/TcMmaDescriptor.lean#L66-L70) ([concept](#c-tcmma-f8f6f4)), [`TcMma.F8f6f4.eightBit`](../../Core/Tc/TcMmaDescriptor.lean#L72-L75), [`TcMma.F8f6f4.ofCode`](../../Core/Tc/TcMmaDescriptor.lean#L77-L80), [`TcMma.Kind`](../../Core/Tc/TcMmaDescriptor.lean#L82-L94) ([concept](#c-tcmma-kind)), [`TcMma.Kind.width`](../../Core/Tc/TcMmaDescriptor.lean#L96-L101), [`TcMma.Kind.k`](../../Core/Tc/TcMmaDescriptor.lean#L103-L108), [`TcMma.Descriptor`](../../Core/Tc/TcMmaDescriptor.lean#L110-L131) ([concept](#c-tcmma-descriptor)), [`TcMma.shapeOk`](../../Core/Tc/TcMmaDescriptor.lean#L133-L143), [`TcMma.typesOk`](../../Core/Tc/TcMmaDescriptor.lean#L145-L153), [`TcMma.transposeOk`](../../Core/Tc/TcMmaDescriptor.lean#L155-L167), [`TcMma.Valid`](../../Core/Tc/TcMmaDescriptor.lean#L169-L173) ([concept](#c-tcmma-valid)), [`TcMma.validDecidable`](../../Core/Tc/TcMmaDescriptor.lean#L175-L177), [`TcMma.decodeKind`](../../Core/Tc/TcMmaDescriptor.lean#L179-L196), [`TcMma.decode`](../../Core/Tc/TcMmaDescriptor.lean#L198-L215)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.2.1 Table 48
- §9.7.18.4.2 Table 51
- §9.7.18.10.1: "For .kind::tf32 , the transpose operations on matrices A and B are supported only
    with 128B swizzling mode with 32B swizzle-atomicity."
- §9.7.18.10.1 (Table 62)
- §9.7.18.10.1 Table 63 (N shapes for 8-bit transpose B, cta_group 1): "16 <= N <= 256, step 16"
- §9.7.18.10.1 Table 63 (N shapes for 8-bit transpose B, cta_group 2): "32 <= N <= 256, step 32"
- §9.7.18.10.3 Table 65
- §9.7.18.10.4.4: "Dense-K dimension Padding needed after 16 elements 32 Yes 64 No"
- §9.7.18.9.1.1: "A contiguous set of 16 elements of 4-bits each followed by 8 bytes of padding"
- §9.7.18.9.1.2: "A contiguous set of 16 elements of 6-bits each followed by 4 bytes of padding"
- EXT-TCFIG

**Applies:** Dense tcgen05.mma.cta_group::{1,2}.kind::{i8,f16,tf32,f8f6f4} and tcgen05.mma.ws.cta_group::1.kind::{i8,f16,tf32,f8f6f4}

**Premises:** The 32-bit descriptor has documented type and shape fields and zero reserved, sparse, K-dimension and shift bits; the saturate bit is zero except for kind::i8. Dense sparsity-selector bits are ignored. kind::f16 inputs are both FP16 or both BF16 and FP16 output requires FP16 inputs; kind::i8 inputs are U8 or S8 with S32 output and no negation; kind::tf32 inputs are TF32 (type 2) with F32 output; kind::f8f6f4 inputs are E4M3, E5M2, E2M3, E3M2 or E2M1, each operand its own, with FP16 or FP32 output.

**Effect:** Instruction-descriptor decoding. Floating numerical treatment belongs to the chosen arithmetic profile. With `.ws`, M is one of 32, 64 and 128 and N is one of 64, 128 and 256. Bits 2 (sparsity), 6 and 23 (reserved), 29 (K dimension: the dense value 0 of Table 51) and 30–31 (the `.ws` B-reuse shift field) must be zero, and no bit above 31 may be set. Bits 0–1 (the sparsity selector, meaningful only when sparse) are ignored, and bit 3 (saturate) is read for kind::i8 and must be zero for the other kinds. The remaining fields are bits 4–5 (D type), 7–9 (A type), 10–12 (B type), 13–16 (negation and transposition of A and B), 17–22 (N >> 3) and 24–28 (M >> 4). Table 51 lets bits 30–31 select a nonzero B-reuse shift for `.ws` and says nothing about them for the other forms, and the decoder rejects every nonzero value, which is stricter than the text for every form. kind::tf32 and kind::f8f6f4 have the shapes of kind::f16 (Table 48). Bit 29 is 0, so kind::f8f6f4 has its dense K of 32 elements; K = 64 (bit 29 set, sm_107f only) has no rule. Transposition (`transposeOk`): kind::i8 and the 8-bit types of kind::f8f6f4 with transposed B take the N shapes of Table 63. A 6- or 4-bit operand of kind::f8f6f4 is not transposed: Table 65 lists transposed layouts for 8-, 16- and 32-bit types only. kind::tf32 may be transposed only with 128B swizzling with 32B atomicity and the 8- and 16-bit kinds not with it (§9.7.18.10.3 Table 65). The swizzle is a field of the shared descriptor, so this descriptor accepts a transposed kind::tf32 and the pairing is enforced by THREAD-TC-SHARED-ADDRESS, which yields an address for an MN-major operand exactly when the 32B-atomic mode is paired with 4-byte elements.

</details>

<a id="thread-tc-mma-operands"></a>
#### shared operand locations of a CTA group (`THREAD-TC-MMA-OPERANDS`)

*Rule* · [Lean comment: `Core/Tc/TcMmaOperands.lean` L12-L44](../../Core/Tc/TcMmaOperands.lean#L12-L44)

Each byte of the A and B operands of an MMA is read from the shared memory of a CTA of the issuing group, at the address that the operand's shared matrix descriptor gives for its row, contraction element and byte. With `.cta_group::2` the first half of the rows of A (along M) and of B (along N) is read from the pair's even-rank CTA and the second half from its odd-rank CTA, and a transposed operand is addressed MN-major.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.Operand`](../../Core/Tc/TcMmaOperands.lean#L46-L49), [`TcMma.Operand.extent`](../../Core/Tc/TcMmaOperands.lean#L51-L55), [`TcMma.Operand.major`](../../Core/Tc/TcMmaOperands.lean#L57-L63), [`TcMma.Operand.rows`](../../Core/Tc/TcMmaOperands.lean#L65-L68), [`TcMma.Operand.bytes`](../../Core/Tc/TcMmaOperands.lean#L70-L72), [`TcMma.Collectors`](../../Core/Tc/TcMmaOperands.lean#L74-L80) ([concept](#c-tcmma-collectors)), [`TcMma.OperandSpec`](../../Core/Tc/TcMmaOperands.lean#L82-L103) ([concept](#c-tcmma-operandspec)), [`TcMma.OperandSpec.byteLoc`](../../Core/Tc/TcMmaOperands.lean#L105-L118), [`TcMma.OperandSpec.MatchesLaunch`](../../Core/Tc/TcMmaOperands.lean#L120-L123), [`TcMma.OperandSpec.matchesLaunch_iff`](../../Core/Tc/TcMmaOperands.lean#L135-L153), [`TcMma.makeOperands`](../../Core/Tc/TcMmaOperands.lean#L125-L132)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5.1 (CTA pairs)
- §9.7.18.10.6 (transpose); NVIDIA CUTLASS include/cute/atom/mma_traits_sm100.hpp SM100_MMA_*_SS and
    SM100_MMA_*_2x1SM_SS ALayout/BLayout
- EXT-TCFIG

**Applies:** Dense shared A and B operands in the represented canonical descriptor modes, for either CTA group

**Premises:** Valid instruction shape, the issuer's CTA group in the launch, in-range matrix coordinate and element byte, and supported shared descriptor addressing.

**Effect:** Computes a shared location only. Either CTA of a `cta_group::2` pair may issue. Transposition selects the local major order and leaves the CTA partition unchanged. A transposed operand of kind::tf32 requires the 128-byte swizzle with 32-byte atomicity, and a transposed operand of the other kinds excludes it (Table 65, THREAD-TC-SHARED-ADDRESS). The element width is that of the kind. With `.ws` and M below 128 the A read has one row per D lane, and lane `L` reads A row `L % M` (EXT-TCFIG). The same descriptor byte offset is interpreted in each participating CTA's shared memory. Group numbering is cluster-relative, including clusters larger than two; the partition and which CTA of the pair holds which half are EXT-TCFIG.

</details>

<a id="thread-tc-mma-result-layout"></a>
#### D matrix cells and lane masks (`THREAD-TC-MMA-RESULT-LAYOUT`)

*Rule* · [Lean comment: `Core/Tc/TcMmaResultLayout.lean` L10-L42](../../Core/Tc/TcMmaResultLayout.lean#L10-L42)

Element (i, j) of D occupies one 32-bit Tensor Memory word, also for FP16, at the lane and column that the layout of the shape and CTA group assigns (Layouts A, B, D, E, F and G of §9.7.18.10.5), counted from the D address. The D address is split into its lane field (`base / 2^16`) and column field (`base % 2^16`). A lane whose bit in the disable-output-lane mask is 1 is not written, and keeps its prior contents. A D address whose lane field is not a permitted alignment or whose columns pass the 512th has no cells.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.Cell`](../../Core/Tc/TcMmaResultLayout.lean#L175-L183) ([concept](#c-tcmma-cell)), [`TcMma.halfDatapath`](../../Core/Tc/TcMmaResultLayout.lean#L185-L188), [`TcMma.columnBlocks`](../../Core/Tc/TcMmaResultLayout.lean#L190-L191), [`TcMma.aCell`](../../Core/Tc/TcMmaResultLayout.lean#L223-L241), [`TcMma.operandRow`](../../Core/Tc/TcMmaResultLayout.lean#L243-L246), [`TcMma.LaneAligned`](../../Core/Tc/TcMmaResultLayout.lean#L193-L195), [`TcMma.laneAlignedDecidable`](../../Core/Tc/TcMmaResultLayout.lean#L197-L199), [`TcMma.resultColumns`](../../Core/Tc/TcMmaResultLayout.lean#L201-L203), [`TcMma.resultCell`](../../Core/Tc/TcMmaResultLayout.lean#L205-L221) ([concept](#c-tcmma-resultcell)), [`TcMma.OutputMaskValid`](../../Core/Tc/TcMmaResultLayout.lean#L248-L250), [`TcMma.outputMaskValidDecidable`](../../Core/Tc/TcMmaResultLayout.lean#L252-L255), [`TcMma.writeCell`](../../Core/Tc/TcMmaResultLayout.lean#L257-L266) ([concept](#c-tcmma-writecell))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.10.5 Table and Figures 211–222 (Layouts A, B, C, D, E, F; Layout G by the table's 1x4
    organization)
- §9.7.18.10.4.1 (unpacked subword D)
- §9.7.18.10.10.1 (disable-output-lane); NVIDIA CUTLASS (commit e406c186)
    include/cute/atom/mma_traits_sm100.hpp tmem_frg, include/cute/atom/mma_traits_sm100_frag.hpp
    tmem_frg N_SM=2, mma_traits_sm100.hpp tmem_frg_ws
- EXT-TCFIG

**Applies:** MMA with M = 128 per CTA of the group (Layouts A and D), M = 128 with cta_group::2 (Layout B), M = 64 with cta_group::1 (Layout F; Layout E with .ws) or M = 32 with .ws (Layout G), with a 32-bit, FP16 or FP32 D

**Premises:** A valid decoded instruction shape, an in-range matrix coordinate, a D address whose lane field is a permitted datapath lane alignment (0, or 16 for Layout F) and whose column range fits the 512 physical columns; write queries additionally require `4 * group size` 32-bit mask words.

**Effect:** Potential/result-write footprint only. Unsupported or out-of-range queries return none without aliasing another cell. CTA identities are supplied by makeOperands.

</details>

<a id="ext-tcfig"></a>
##### the operand and result layouts of tcgen05.mma (`EXT-TCFIG`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcMmaResultLayout.lean` L44-L173](../../Core/Tc/TcMmaResultLayout.lean#L44-L173)

The model makes seven readings of the layouts of `tcgen05.mma`. (1) D layouts given by figures. The model reads the D layouts that the ISA gives only by figures (Layouts D, F, E and G) as explicit coordinate maps. Layout D for M = 128 with cta_group::1 (Figures 217 and 218) puts row `i` of D in lane `i` and column `j` in column `base + j`. Layout F for M = 64 with cta_group::1 (Figures 221 and 222, and CUTLASS's 1SM M = 64 atom `((16,4),N):((1,32),128)`) puts row `i` in lane `alignment + i % 16 + 32 (i / 16)`. The `.ws` Layouts E (M = 64, Figures 219–220, 2x2) and G (M = 32, 1x4), as CUTLASS's `tmem_frg_ws` atoms `(64,(N/2,2)):(1,(128,64))` and `(32,(N/4,4)):(1,(128,32))` (lane stride 1, column stride 128), put element `(i, j)` in lane `i + r (j / (N r / 128))`, column `j % (N r / 128)` for `r` = 64 or 32. (2) Result layouts of a CTA pair. With `cta_group::2` and M = 256 (Layout A, Figures 211–212), row `i` of D is lane `i % 128` of the even CTA for `i < 128` and of the odd CTA otherwise, at column `base + j`. The pair's even-rank CTA holds the first half of the rows of D and the odd-rank CTA the second half. With M = 128 (Layout B, Figures 213–214) each CTA holds 64 rows in the 2x2 datapath organization of Layout E, with N split into two column blocks at lanes 0–63 and 64–127. The `disable-output-lane` mask of a pair has 8 words that number 256 lanes: bits 0–127 are the even CTA's lanes and bits 128–255 the odd CTA's lanes. Bit 0 of the first element of the mask is lane 0. (3) A in Tensor Memory. An A operand read from Tensor Memory (`[a-tmem]`) uses the same datapath organization as D (§9.7.18.10.5: half-datapath layouts "must use the same Tensor Memory lane alignment across matrices A , D"). It puts each row on the lane of the corresponding row of D. Its K-row bytes are packed contiguously into 32-bit words, the lower-numbered element in the lower bytes, as §9.7.18.10.4.3 states for 8-bit containers and as CUTLASS's `tmem_frg` for `SM100_MMA_*_TS` atoms lays out A with `sizeof_bits<uint32_t> / sizeof_bits<T>` elements per column. For 16-bit elements (kind::f16) a word holds two consecutive K elements, the lower-numbered one in its low half. With `cta_group::2` and M = 256 (Layout A) row `i` of A is lane `i % 128` of the even CTA of the pair for `i < 128` and of the odd CTA otherwise, as D's rows (reading 2), so each CTA's Tensor Memory holds the A rows of its own D rows. Layout B (M = 128 with `cta_group::2`), where CUTLASS duplicates A across subpartitions, has no A cells here, so such an issue is unsafe (ERR-TC-MMA). (4) `.ws` reads A per D lane. With `.ws` and M below 128, each lane of D reads its own copy of A: output (i, j) uses the A row on lane i + M (j / (N M / 128)), and with A in shared memory lane L reads row L mod M. Shared A is the same data for every lane of a row. (5) The operand partition of a CTA pair. With `.cta_group::2`, A is split along M and B along N; the first half of each is read from the shared memory of the pair's even-rank CTA and the second half from that of the odd-rank CTA, at the same descriptor offset in each. The pair's CTAs are the cluster ranks `2k` and `2k + 1` (that part is §9.7.18.5.1: "Any 2 CTAs within the cluster whose %cluster_ctarank differs by the last bit only is said to form a CTA pair"). (6) The layout of the 32-byte-atomic mode. In the 128-byte swizzling mode with 32-byte atomicity, an MN-major operand is laid out like in the other MN-major modes with swizzle atoms of 128 bytes along M or N by 4 rows along K, and the 32-byte-atomicity XOR of §5.5.7 is applied to the absolute address. Read with the K extent of the atom reduced from 8 to 4, this gives 128 contiguous bytes along M/N, four such rows per atom (row stride 128 bytes), a leading offset between M/N atoms and the stride offset between K groups of four, and the absolute-address XOR of the §5.5.7 32-byte-atomicity table (chunk bits 5-6 XOR row bits 7-8, CUTLASS Swizzle<2,5,2>). A K-major operand in this mode has no address. (7) Operand rows of kind::f8f6f4. A row of a `kind::f8f6f4` operand with K = 32 occupies 32 bytes for every element type, as the shared-memory packing that the ISA states for `kind::mxf8f6f4` with dense K = 32. An operand row of `kind::f8f6f4` with dense K = 32 is 32 bytes in shared memory and in Tensor Memory: one byte per element for E4M3 and E5M2, and for the 6- and 4-bit types each 16 elements packed into 12 or 8 bytes followed by 4 or 8 padding bytes. The model reads these 32 bytes as the operand's footprint, addresses them as 32 one-byte elements, and gives no element value to a 6- or 4-bit element: which bits of a 16-byte chunk hold which element is given only by Figures 207 and 208, so the arithmetic of those types is left to a kernel assumption.

Source:

- - §9.7.18.10.5.1 - §9.7.18.10.5.2 and their figures - §9.7.18.10.10.1: "corresponds to a lane of the Tensor Memory" - NVIDIA CUTLASS `include/cute/atom/mma_traits_sm100_frag.hpp` `tmem_frg` with `N_SM = 2` - NVIDIA CUTLASS (`include/cute/atom/mma_traits_sm100.hpp`, `SM100_MMA_*_2x1SM_SS` `ALayout` and `BLayout`); PTX ISA 9.5 §9.7.18.5.1 - §9.7.18.5.2 (the pair has an even and an odd CTA; the peer of one is the other) and §9.7.18.10 (B: "in Shared Memory of the current CTA and optionally in peer CTA" - §9.7.18.10.4.2: "The 6-bit and 4-bit floating point types have different packing format requirements for different MMA kinds in both Tensor memory and Shared memory." - §9.7.18.10.4.4 (the packing of `kind::mxf8f6f4` in shared memory) - §9.7.18.9.1.1 and §9.7.18.9.1.2 (the 16-element chunks with padding)

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** (1) The layouts are given by figures only, with no textual coordinate map. (2) The `cta_group::2` layouts are also given by figures only. The text does not say which CTA of the pair holds the first half of the rows of D, and it does not say how an 8-word `disable-output-lane` mask maps onto the two CTAs' lanes. (3) The sentence of §9.7.18.10.5 on the same Tensor Memory lane alignment states that A shares the datapath organization of D. It does not say that a row of A is on the lane of the same row of D. The text states the packing of K elements into 32-bit words for 8-bit containers only (§9.7.18.10.4.3), and it does not say which CTA of a pair holds which rows of A. (4) With `.ws` and M < 128 (Layouts E and G) the ISA does not say which lane's A a column block uses. (5) The text says that the pair's two CTAs take part and that an operand may be in the peer CTA's shared memory. It does not say along which dimension an operand is split or which half lies in which CTA of the pair. (6) Table 67 gives the swizzle atom (8 x 4 elements of 128 bits, M/N-major only; Figure 225), and the text states neither the strides of atoms nor the XOR in the MMA's address space. For 4-byte elements Table 65 lists "All swizzling modes" for K-major, and Table 67 has no K-major atom of this mode, so K-major with it is undefined here. (7) §9.7.18.10.4 states the packing for `kind::mxf8f6f4`, `kind::mxf4` and `kind::mxf4nvf4` only; `kind::f8f6f4` takes the same element types and the model gives it the `kind::mxf8f6f4` packing.

**Evidence:** (1) NVIDIA CUTLASS (commit e406c186) `include/cute/atom/mma_traits_sm100.hpp` gives the same maps (`tmem_frg`, `tmem_frg_ws`). (3) The figures and CuTe layouts of PTX ISA §9.7.18. CUTLASS `SM100_MMA_F16BF16_2x1SM_TS` (commit e406c186) lays A out with `tmem_frg_2sm<a_type, a_type, TmemAllocMode::Duplicated>`, whose allocation for 128 rows per CTA is that of D (its source comment: with 128 rows all datapaths are occupied and the allocation mode changes nothing) and whose `ALayout` gives SM `v` rows `v * M / 2` onward. Layout D is checked against a CPU reference on a B200 by `Kernels/TcGemm/run_tc_gemm.cu`, and the A packing (kind::i8, M = 128, 64 and 32) by `Tools/probes/tcgen05_ws_ts_i8.ptx` (MMA reading A written with `tcgen05.st`). The 16-bit packing and the `cta_group::2` row split rest on CUTLASS alone; no probe checks them. (4) On a B200 each D lane reads its own copy: output `(i, j)` uses lane `i + M (j / (N M / 128))`. In `Tools/probes/tcgen05_ws_ts_i8.ptx` (A in Tensor Memory, N = 64, decoys in every lane but row `i`'s), the lane of row `i` alone mismatched 2048 of 4096 (M = 64) and 1536 of 2048 (M = 32) outputs, and the per-lane model none (two seeds each); M = 128 cannot distinguish them. Layout F for A in Tensor Memory follows from the same alignment rule. (6) CUTLASS `make_umma_desc` (LayoutType::B128_BASE32B above, local checkout of include/cute/arch/mma_sm100_desc.hpp and `Layout_MN_SW128_32B_Atom` in include/cute/atom/mma_traits_sm100.hpp). (7) The manual states the shared-memory packing for `kind::mxf8f6f4` in §9.7.18.10.4.4 with Figures 207 and 208, and the Tensor Memory containers in Table 66 of §9.7.18.10.4.3. CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) gives `kind::f8f6f4` the same 32-byte row: it maps 6- and 4-bit inputs to the `*_unpacksmem_t` types (`sm1xx_kernel_input_element_to_mma_input_element` in include/cutlass/gemm/collective/builders/sm1xx_common.inl), allocates them as `uint8_t` in shared memory (sm100_umma_builder.inl), loads them with the TMA types `CU_TENSOR_MAP_DATA_TYPE_16U6_ALIGN16B` and `CU_TENSOR_MAP_DATA_TYPE_16U4_ALIGN16B` (16 packed elements, then a gap, in every 16 bytes) and fixes K = 32 in `MMA_Traits<SM100_MMA_F8F6F4_SS>`. The hardware probe txverify-archive/core-coverage/probes/tcgen05_f8f6f4/ runs an M = 128, N = 16 MMA for each type as A and as B, with the padding bytes set to 0xFF and to random values, and compares D with the product of the elements packed from bit 0 up. It ran on a B200 on 2026-11-16 and agreed in all 22 cases, with either padding.

**Effect:** The maps of readings 1 to 3 decide which Tensor Memory cells an MMA writes and which cells a later `tcgen05.ld` or `tcgen05.st` reads as which D element, and the A bytes an MMA reads from Tensor Memory. If the hardware maps differ, the proven results differ. The A elements of each D lane (reading 4) are fixed by the lane map; if the hardware lanes read other copies, the products differ from the ones proven. A different operand split of a CTA pair (reading 5) would make the value of D a different function of the shared bytes. The shared byte of each operand element in the 32-byte-atomic mode (reading 6) is fixed by its layout; if the hardware layout differs, the operand bytes an MMA reads differ from the ones proven. The bytes an MMA of `kind::f8f6f4` reads, and so its conflicts with other accesses, are fixed by the footprint of reading 7; if the hardware reads another footprint, a write the model orders after the read may change the operand. Disclosed by every kernel whose statement names `Op.tcMma`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

</details>

<a id="thread-tc-data-address"></a>
#### Tensor Memory cells of tcgen05.ld and tcgen05.st (`THREAD-TC-DATA-ADDRESS`)

*Rule* · [Lean comment: `Core/Tc/TcDataAddress.lean` L10-L71](../../Core/Tc/TcDataAddress.lean#L10-L71)

Register j of thread lane l of a `tcgen05.ld` or `tcgen05.st` is the Tensor Memory cell that the fragment of the shape assigns to (l, j), offset by the lane and column of the base address of the access, inside the 32-lane chunk of the issuing warp's position in its warpgroup. An address whose lanes would leave that chunk, or a `.16x32bx2` offset that would leave the column field, has no rule.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`laneBase`](../../Core/Tc/TcDataAddress.lean#L173-L174), [`tmemLaneFieldOk`](../../Core/Tc/TcDataAddress.lean#L176-L180), [`TcShape.base`](../../Core/Tc/TcDataAddress.lean#L182-L187), [`TcShape.laneIn`](../../Core/Tc/TcDataAddress.lean#L189-L196), [`TcShape.columnIn`](../../Core/Tc/TcDataAddress.lean#L198-L206), [`TcShape.splitOk`](../../Core/Tc/TcDataAddress.lean#L208-L214), [`tcDataAddressOk`](../../Core/Tc/TcDataAddress.lean#L216-L220) ([concept](#c-tcdataaddressok)), [`chunkOffset`](../../Core/Tc/TcDataAddress.lean#L222-L224), [`tcDataCell`](../../Core/Tc/TcDataAddress.lean#L226-L233) ([concept](#c-tcdatacell))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.1.1 (the address layout puts the lane index in bits 31 to 16)
- §9.7.18.8.1 (warp w of a warpgroup accesses lanes 32 w to 32 w + 31, and a lane is accessed by a
    single warp)
- §9.7.18.2.3.1.1 to §9.7.18.2.3.1.5: "A warp executing tcgen05{.ld,.st}.32x32b will access 32 lanes
    of the Tensor Memory."
- §9.7.18.2.3.1.1 to §9.7.18.2.3.1.5 (the `.16x64b`, `.16x128b`, `.16x256b` and `.16x32bx2` accesses
    cover 16 lanes)
- Figures 186 to 190 (which register of which thread is which cell; figures only,
    EXT-TMEM-LANE-FIELD)
- §9.7.18.8.3 and §9.7.18.8.4: "The shape .16x32bx2 performs two accesses into Tensor Memory of the
    shape .16x32b . The base address of the first access is specified by taddr and the base address
    of the second access is specified by taddr+immHalfSplitoff , where immHalfSplitoff is an
    immediate argument."
- EXT-TMEM-LANE-FIELD

**Applies:** Represented tcgen05.ld and tcgen05.st of every shape (`TcShape`)

**Premises:** The address lane field keeps every access of the shape inside the issuing warp's chunk (`tmemLaneFieldOk`, EXT-TMEM-LANE-FIELD); a `.16x32bx2` half-split offset stays in the column field (`TcShape.splitOk`, EXT-TMEM-LANE-FIELD).

**Effect:** One address adapter for issue and for every load, store, value, conflict, lifetime and allocation query (`tcDataCell`). Register `j` of thread lane `l` of warp `w` of its warpgroup is the cell at lane `32 w + o + TcShape.laneIn l j` and column `c + TcShape.columnIn l j`, where `o` and `c` are the chunk offset and the column field of the base address of the access the thread takes part in (`TcShape.base`). The fragment of each shape, with `k = j / regs` the repetition (`.num` index) and `r = j % regs` the register within it (`TcShape.regs`), as Figures 186 to 190 draw it: | shape | lane in the access | column from the base | | --- | --- | --- | | `.32x32b` | `l` | `k` | | `.16x64b` | `l / 4 + 8 (l % 2)` | `2 k + (l / 2) % 2` | | `.16x128b` | `l / 4 + 8 r` | `4 k + l % 4` | | `.16x256b` | `l / 4 + 8 (r / 2)` | `8 k + 2 (l % 4) + r % 2` | | `.16x32bx2` | `l % 16` | `k` | For `.16x32bx2` thread lanes 0 to 15 take part in the first access (base `taddr`) and lanes 16 to 31 in the second (base `taddr + immHalfSplitoff`). For every shape, distinct registers of one thread are distinct cells. `tmemLaneFieldOk L g field n` accepts the lane field of an access of `n ≥ 1` lanes when it is an offset within the warp's chunk (`field + n ≤ 32`, first lane `laneBase + field`) or an absolute lane inside the chunk (`laneBase ≤ field` and `field + n ≤ laneBase + 32`, first lane `field`). For warp 0 the two coincide; for a warp `w > 0` they are disjoint because `n ≥ 1` (`tmemLaneField_disjoint`), so the first lane is determined. In both readings the first lane is `laneBase + field % 32` (`laneBase` is a multiple of 32), at most `laneBase + 32 - n`; `chunkOffset` is that offset, bounded by `32 - n` so that the adapter is total. A `.32x32b` access covers 32 lanes, so its first lane is `laneBase`. Column allocation, conflicts and the collective's equal-operand requirement are separate rules (ERR-TMEM-ACCESS-LIFETIME, ERR-TMEM-RACE, ERR-ALIGNED-MISMATCH): a column past the allocation is an unsafe access, and two lanes of one `.16x32bx2` store that write one cell are an unordered write pair.

</details>

<a id="ext-tmem-lane-field"></a>
##### the layout readings of tcgen05.ld and tcgen05.st (`EXT-TMEM-LANE-FIELD`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcDataAddress.lean` L73-L170](../../Core/Tc/TcDataAddress.lean#L73-L170)

The model makes four readings of `tcgen05.ld` and `tcgen05.st`. (1) The register fragments of Figures 186 to 190 are explicit coordinate maps, the table of THREAD-TC-DATA-ADDRESS, with each further `.num` repetition of a fragment at the next columns. Thread lane `l`, register `j` of repetition `k = j / regs` and `r = j % regs` is lane `l` and column `k` for `.32x32b`; lane `l / 4 + 8 (l % 2)` and column `2 k + (l / 2) % 2` for `.16x64b`; lane `l / 4 + 8 r` and column `4 k + l % 4` for `.16x128b`; lane `l / 4 + 8 (r / 2)` and column `8 k + 2 (l % 4) + r % 2` for `.16x256b`; lane `l % 16` and column `k` of its half's access for `.16x32bx2`. (2) The lane field of a `tcgen05.ld` or `tcgen05.st` address is accepted either as an offset into the issuing warp's 32-lane chunk or as an absolute lane inside that chunk, provided every accessed lane stays in the chunk; any other lane field has no rule. For an access of `n ≥ 1` lanes issued by warp `w` of a warpgroup, the address lane field `f` is accepted when it is an offset into the warp's chunk (`f + n ≤ 32`, lanes `32 w + f` onward) or an absolute lane of that chunk (`32 w ≤ f`, `f + n ≤ 32 w + 32`, lanes `f` onward). (3) The second access of a `.16x32bx2` load or store starts `immHalfSplitoff` columns after the first, on the same 16 lanes, and thread lanes 16 to 31 take part in it as its lanes 0 to 15. The second access has the base address `taddr + immHalfSplitoff`, a Tensor Memory address read with its lane and column fields (§9.7.18.1.1). The model accepts only an offset that stays in the column field of `taddr` (`taddr % 2^16 + immHalfSplitoff < 2^16`), so both accesses have the lane field of `taddr` and cover the same 16 lanes. Any other offset is forbidden (no rule). (4) For `tcgen05.ld.<shape>.pack::16b` and `tcgen05.st.<shape>.unpack::16b` of a single-access shape, register `j` of thread lane `l` uses the lane of the unpacked fragment and the columns `c + 2 x` (low half of the register) and `c + 2 x + 1` (high half), with `x` the unpacked column offset. The 16-bit element in a column is the column's low 16 bits. An unpacking store leaves the high 16 bits of the written words unknown.

Source:

- - §9.7.18.2.3.1.1 to §9.7.18.2.3.1.5: "A warp executing tcgen05{.ld,.st}.32x32b will access 32 lanes of the Tensor Memory." - §9.7.18.1.1 (the address layout puts the lane index in bits 31 to 16) and §9.7.18.8.1: "A lane of the Tensor Memory can be accessed by a single warp in the warpgroup. … ID of the warp within the warpgroup Accessible Lanes 0 0-31 1 32-63 2 64-95 3 96-127" - §9.7.18.8.3: "The base address of the first access is specified by taddr and the base address of the second access is specified by taddr+immHalfSplitoff , where immHalfSplitoff is an immediate argument." - §9.7.18.2.3.1.5: "A warp executing tcgen05{.ld,.st}.16x32bx2 will access 16 lanes of the Tensor Memory." - Figure 190 (which draws threads T16 to T31 from the top of the second access, whose start the figure labels as the base address plus the immediate) - §9.7.18.8.2 to §9.7.18.8.4 and Figure 196

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** (1) The fragments are given by Figures 186 to 190 only, with no textual coordinate map. The figures draw `.x2` for `.32x32b` and `.16x64b`, and only `.x1` followed by "…" for the other shapes. The model reads every further repetition as the next `regs` registers at the next columns, as the drawn `.x2` cases do. (2) The text gives the lanes each warp may access. It does not say whether the address lane field is an absolute lane or an offset into the warp's chunk. (3) The text does not say how the immediate combines with the lane and column fields, and Figure 190 draws the second access at lanes 16 to 31 while the text says the warp accesses 16 lanes; the model takes the reading on which both hold for the offsets it accepts, and does not decide the others. That thread `16 + i` is lane `i` of the second access is read from the figure. (4) The text says that two 16-bit elements of adjacent columns form one register. It does not say which 16 bits of a column hold the element, which half of the register comes from the lower column, or where the columns of a multi-register fragment go. Figure 196 draws the `.16x128b` fragment with each register occupying two adjacent 16-bit columns, the register of thread `T0` in the first two, and the next thread's register in the next two; it does not mark the bit halves.

**Evidence:** (1) CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23), include/cute/atom/copy_traits_sm100.hpp, gives the same maps (`SM100_TMEM_LOAD_32dp32b1x`, `_16dp64b1x`, `_16dp128b1x`, `_16dp256b1x`, `_16dp32b1x`, and their `2x` forms). On a B200, the unpacked control lines of the probe txverify-archive/core-coverage/probes/tcgen05_pack16/ agreed with these maps for `.x1`, `.x2` and `.x4` of the four shapes. (2) https://docs.nvidia.com/cuda/parallel-thread-execution/#tcgen05-tensor-memory-ld-st-access-restrictions https://docs.nvidia.com/cuda/parallel-thread-execution/_images/tcgen05-mma-fragment-3232b.png https://docs.nvidia.com/cutlass/4.8.0/media/docs/pythonDSL/primitives.html#cutlass.experimental.primitives.tcgen05_ld (3) NVIDIA CUTLASS 4.1.0 `include/cute/arch/copy_sm100.hpp` issues `tcgen05.ld.sync.aligned.16x32bx2.x<n>.b32` with `immHalfSplitoff = n`, and its `include/cute/atom/copy_traits_sm100.hpp` layout `SM100_TMEM_LOAD_16dp32b1x` puts thread `t` at lane `t % 16`, 32-bit column `t / 16`. https://docs.nvidia.com/cuda/parallel-thread-execution/_images/tcgen05-mma-fragment-1632b2.png (4) (manual) Figure 196 (`_images/tcgen05-ld-st-pack-unpack.png`): a register of the `.16x128b` fragment maps to two adjacent 16-bit columns, in fragment order. (CUTLASS) CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23), include/cute/atom/copy_traits_sm100.hpp, `Copy_Traits<SM100_TMEM_LOAD_32dp32b1x_16b>` and the other `_16b` atoms: `ValID = Shape<Shape<_16, X>, lanes>, Stride<Stride<_1, _32>, DP_b>`, so logical bit `i` of a lane is Tensor Memory bit `32 (i / 16) + i % 16` (16-bit chunk `k` in the low half of column `k`), with the register map (`DstLayout`) of the unpacked atom of the same logical width; the `SM100_TMEM_STORE_*_16b` atoms use the same layouts. (B200) probe `txverify-archive/core-coverage/probes/tcgen05_pack16/`, which compares packed loads and unpacking stores of every single-access shape with this map. It ran on a B200 on 2026-11-16 and agreed for `.x1`, `.x2` and `.x4` of every shape. It also prints what the high 16 bits of the words an unpacking store writes hold, which the model leaves unknown; they were 0 in every case.

**Effect:** These maps decide which Tensor Memory cells a `tcgen05.ld` or `tcgen05.st` reads or writes as which register. If the hardware maps differ, the proven results differ. The lane field is a reading of how hardware interprets the field, and real kernels use both encodings. If hardware used only one interpretation, a program using the other would access another warp's lanes and be wrongly accepted. If the hardware placed the second access of a `.16x32bx2` elsewhere for a column offset, the cells the upper half-warp loads and stores, and so values and conflicts, would differ from the model's. If the hardware placed the halves or the columns of a packed access otherwise, the values a packed load returns and the cells an unpacking store writes would differ from the model's, and so would every value and conflict computed from them. Disclosed by every kernel whose statement names `Op.tcLd` or `Op.tcSt`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

</details>

<a id="thread-tc-pack16"></a>
#### tcgen05.ld .pack::16b and tcgen05.st .unpack::16b (`THREAD-TC-PACK16`)

*Rule* · [Lean comment: `Core/Tc/TcThread.lean` L358-L398](../../Core/Tc/TcThread.lean#L358-L398)

With `.pack::16b` a `tcgen05.ld` reads two adjacent columns for each register of the shape and sets the register to the low 16 bits of the first column's word followed by those of the second; with `.unpack::16b` a `tcgen05.st` writes the low and the high 16 bits of each source register as the low 16 bits of two adjacent columns and leaves the high 16 bits of those words without a known value. The access shape is `TcShape.packed16 s`. Its slot `2 j + h` (h = 0, 1) is the lane of register `j` of `s` and the column `c + 2 x + h`, where `c` is the address's column and `x` the column of register `j` of `s` from its base, so that the columns of `s` are spread over twice as many physical columns. A packed load's event returns one word per slot, and the thread sets register `j` to the pair of the low two bytes of slots `2 j` and `2 j + 1` (`TcPack16.pack`); the words are related to their sources by DEP-TC-LOAD-VALUE, so only their low two bytes matter. An unpacking store's event records, for slot `2 j + h`, the two bytes of register `j` at byte `2 h` (`TcPack16.unpack`), a 2-byte value, which DEP-TC-LOAD-VALUE (`WordContains`) reads as fixing the low two bytes of the word only.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcPack16.half`](../../Core/Tc/TcThread.lean#L401-L402), [`TcPack16.pack`](../../Core/Tc/TcThread.lean#L404-L408), [`TcPack16.unpack`](../../Core/Tc/TcThread.lean#L410-L413), [`tcTmpl_tcSt_plain`](../../Core/Tc/TcThread.lean#L504-L518)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.8.2: "Packing: two 16-bit chunks can be packed into a single 32-bit chunk in the register
    in tcgen05.ld"
- §9.7.18.8.2: "Unpacking: a single 32-bit chunk in the register can be unpacked into two 16-bit
    chunks in tcgen05.st"
- §9.7.18.8.3: "The optional qualifier .pack::16b can be used to pack two 16-bit elements from
    adjacent columns into a single 32-bit element during the load"
- §9.7.18.8.4: "The optional qualifier .unpack::16b can be used to unpack a 32-bit element in the
    register into two 16-bit elements and store them in adjacent columns"
- EXT-TMEM-LANE-FIELD

**Why it is not spec text:** The text does not say whether `immHalfSplitoff` counts packed or physical columns. `.16x32bx2` with packing therefore decodes to `Op.unmodeled`.

**Applies:** tcgen05.ld `.pack::16b` and tcgen05.st `.unpack::16b` of `.32x32b`, `.16x64b`, `.16x128b` and `.16x256b`

**Premises:** The premises of THREAD-TC for the shape without packing.

**Effect:** Event production: the load event records two words per register, at the cells of `TcShape.packed16` (THREAD-TC-DATA-ADDRESS); the store event records two 16-bit values per register.

</details>

<a id="thread-tc-cp-cells"></a>
#### shared source and Tensor Memory destination of tcgen05.cp (`THREAD-TC-CP-CELLS`)

*Rule* · [Lean comment: `Core/Tc/TcCopy.lean` L12-L61](../../Core/Tc/TcCopy.lean#L12-L61)

A `tcgen05.cp` copies, in each CTA of its group, a matrix of `rows` rows of `rowBytes` bytes, which a shared matrix descriptor locates in that CTA's shared memory as a K-major matrix of one-byte elements, into the Tensor Memory of the same CTA. Source row r lands, byte by byte in order, in the words of the address's columns at each lane the shape's multicast assigns to r (with decompression, the bytes of THREAD-TC-CP-DECOMPRESS). The address must have lane field 0, and a word is known only when the source bytes it depends on are known.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcCpShape.rows`](../../Core/Tc/TcCopy.lean#L135-L140), [`TcCpShape.rowBytes`](../../Core/Tc/TcCopy.lean#L142-L145), [`TcCpShape.sourceBytes`](../../Core/Tc/TcCopy.lean#L147-L148), [`TcCpShape.lanes`](../../Core/Tc/TcCopy.lean#L150-L156), [`TcCopy.Spec`](../../Core/Tc/TcCopy.lean#L158-L166) ([concept](#c-tccopy-spec)), [`TcCopy.AddressOk`](../../Core/Tc/TcCopy.lean#L168-L170), [`TcCopy.addressOkDecidable`](../../Core/Tc/TcCopy.lean#L172-L173), [`TcCopy.byteLoc`](../../Core/Tc/TcCopy.lean#L175-L182), [`TcCopy.cell`](../../Core/Tc/TcCopy.lean#L184-L187), [`TcCopy.byteValue`](../../Core/Tc/TcCopy.lean#L189-L190), [`TcCopy.word`](../../Core/Tc/TcCopy.lean#L192-L199)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.9.2: "When .cta_group::1 is specified, the data is copied into the Tensor Memory of the
    current CTA."
- §9.7.18.9.2: "A thread executing a tcgen05.cp instruction with .cta_group::2 causes both the
    current and peer CTA to copy data from their shared memory to Tensor Memory ."
- §9.7.18.9.2: "When the .multicast qualifier is specified as either .warpx2::02_13 or
    .warpx2::01_23 then the data being copied is multicasted into warp pairs and each warp in the
    warp pair receive half of the data."
- §9.7.18.9.2: ".warpx2::02_13 : warps 0 and 2 form a pair; warps 1 and 3 form a pair."
- §9.7.18.9.2: ".warpx2::01_23 : warps 0 and 1 form a pair; warps 2 and 3 form a pair."
- §9.7.18.9.2: "When the .multicast modifier is specified as .warpx4 then the data being copied is
    multicasted into all 4 warps."
- §9.7.18.2.3 (data movement shape `lane x size`)
- §9.7.18.8.1 (warp `w` of a warpgroup accesses lanes `32 w` to `32 w + 31`)
- §9.7.18.4.1 (shared matrix descriptor)
- EXT-TCCP

**Applies:** tcgen05.cp.cta_group::{1,2} of `.128x256b`, `.4x256b`, `.128x128b`, `.64x128b.warpx2::02_13`, `.64x128b.warpx2::01_23` and `.32x128b.warpx4`, with or without decompression (THREAD-TC-CP-DECOMPRESS)

**Premises:** A decoded shared descriptor of the represented canonical modes; a Tensor Memory address with lane field 0 and the shape's columns within the 512 physical ones; with `.cta_group::2`, the pair's CTAs in the launch.

**Effect:** Address and value geometry only; issue, completion and ordering are execution rules. `.128x256b` copies 128 rows of 32 bytes and `.128x128b` 128 rows of 16 bytes, row `r` to lane `r`. `.64x128b` copies 64 rows of 16 bytes: with `.warpx2::02_13` row `r` goes to lanes `r` and `r + 64` (the pair of warps 0 and 2 holds rows 0 to 31, the pair of warps 1 and 3 rows 32 to 63), and with `.warpx2::01_23` row `r` goes to lanes `r % 32 + 64 (r / 32)` and that lane plus 32 (the pair of warps 0 and 1 holds rows 0 to 31, the pair of warps 2 and 3 rows 32 to 63). `.32x128b` copies 32 rows of 16 bytes, row `r` to lanes `r`, `r + 32`, `r + 64` and `r + 96`. `.4x256b` copies 4 rows of 32 bytes, row `r` to lane `32 r`, the first lane of each warp's chunk. With `.cta_group::2` the copy is made in the pair's even and odd CTA alike, each from its own shared memory at the descriptor's offset to its own Tensor Memory at the address; the bytes read are recorded CTA by CTA, the even CTA's first.

</details>

<a id="ext-tccp"></a>
##### the row and lane maps and the decompression of tcgen05.cp (`EXT-TCCP`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcCopy.lean` L63-L132](../../Core/Tc/TcCopy.lean#L63-L132)

The model makes two readings of `tcgen05.cp`. (1) Row r of the canonical source layout of a `tcgen05.cp` is the Tensor Memory lanes its shape and multicast assign to r, with the row's bytes as the lane's bits in order, as CUTLASS numbers them, and a `.cta_group::2` copy reads each CTA's shared memory at the same descriptor offset. (2) For a decompressing `tcgen05.cp`, element `i` (`i < 16`) of a 16-byte source chunk is bits `4 i` to `4 i + 3` (`.b4x16_p64`) or `6 i` to `6 i + 5` (`.b6x16_p32`) of the chunk read as a little-endian number, and it is written to destination byte `i` of the chunk's 16 bytes, shifted left by 2 bits for 4-bit elements and unshifted for 6-bit elements, with zeros in the other bits. Destination byte `i` is `((X >> 4 i) % 16) * 4` for `.b4x16_p64` and `(X >> 6 i) % 64` for `.b6x16_p32`, where `X` is the little-endian value of the chunk's 16 source bytes.

Source:

- - §9.7.18.9.1.1 - §9.7.18.9.1.2 and Figures 197 to 201

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** (1) The ISA names the shapes (lanes x bits), says that the warps of a pair each receive half of the data and that `.warpx4` sends the data to all four warps, and that the source is described by a matrix descriptor, without a textual element map. CUTLASS (`include/cute/atom/copy_traits_sm100.hpp`) numbers source bits as `[core_matrix_strided, core_matrix_leading]` with Tensor Memory strides `(DP, 1)` for `SM100_UTCCP_128dp256bit_1cta` and `SM100_UTCCP_128dp128bit_1cta`, adds a broadcast mode of stride `64 DP` for `SM100_UTCCP_2x64dp128bitlw0213_1cta`, a repeat mode of stride `64 DP` and a broadcast mode of stride `32 DP` for `SM100_UTCCP_2x64dp128bitlw0123_1cta`, and a broadcast mode of stride `32 DP` for `SM100_UTCCP_4x32dp128bit_1cta`; the `_2cta` forms use the same map for both CTAs. The maps above are these. (2) The text says that 16 packed elements become 16 bytes and leaves the rest to the figures. Figure 198 (`_images/tcgen05-decompression-4b8b-individual.png`) draws the fields S, E2 and M1 of a 4-bit element in bits 5 to 2 of the byte with bits 7, 6, 1 and 0 zero; Figures 200 and 201 (`_images/tcgen05-decompression-6b8b-individual1.png` and `_images/tcgen05-decompression-6b8b-individual2.png`) draw the E3M2 and E2M3 fields of a 6-bit element in bits 5 to 0 with bits 7 and 6 zero. Figures 197 and 199 draw the packed elements of a chunk and their bytes in the same left-to-right order, without bit numbers. The model reads the packed elements from the least significant bit up.

**Evidence:** (1) The manual gives the shapes, the warp pairs and the `.warpx4` broadcast in the sentences quoted in THREAD-TC-CP-CELLS and no element map. In CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23; the ValID layouts named above in include/cute/atom/copy_traits_sm100.hpp) every row of the five shapes goes to the lanes `TcCpShape.lanes` gives, as the host script txverify-archive/core-coverage/probes/cutlass_check.py checks. The hardware probe txverify-archive/core-coverage/probes/tcgen05_cp/ compares every Tensor Memory byte with this map for each shape, `.cta_group::1` and `::2`, and five descriptors (no swizzle with two LBO/SBO pairs, and the 32-, 64- and 128-byte swizzles). It ran on a B200 on 2026-11-16 and agreed with this map in every byte of every case. For `.4x256b` the manual says only that the copy moves 4 lanes of 256 bits. In the same CUTLASS commit `Copy_Traits<SM100_UTCCP_4dp256bit_1cta>` (and `_2cta`, with the same `ValID`) has `ValID = Layout<Shape<_128, _256>, Stride<DP_b, _1>>` and `SrcLayout = DstLayout = Layout<Shape<_1, Shape<_4, _256>>, Stride<_0, Stride<_32, _128>>>`, which put bit `b` of source row `r` at logical bit `32 r + 128 b`, that is lane `32 r` and bit `b`; the model takes this map (`TcCpShape.lanes .s4x256b r = [32 r]`). The comment of that trait says that the copy refreshes `the last 4 lanes of each tmem subpartition`, which disagrees with its layout; the layout is taken. The probes txverify-archive/core-coverage/probes/tcgen05_cp/ (which prints the lanes `.4x256b` writes) and txverify-archive/core-coverage/probes/tcgen05_cp_ext/ (which compares every byte with `[32 r]` for both CTA groups and three descriptors) ran on a B200 on 2026-11-16 and found that the copy writes lanes 0, 32, 64 and 96 with row `r` in lane `32 r`, as the layout and the model say; the trait's comment is wrong. (2) (manual) the figures above. (CUTLASS) CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) has no `tcgen05.cp` atom with decompression; its sub-byte arrays (include/cutlass/array_subbyte.h) keep element `i` at bit `i * sizeof_bits` of the storage, the order the model takes for the packed elements. (B200) The probe txverify-archive/core-coverage/probes/tcgen05_cp_ext/ compares every destination byte of decompressing copies with this map. It ran on a B200 on 2026-11-16 and agreed for `.128x128b` and `.128x256b` with both formats, two descriptors and four random seeds each.

**Effect:** The Tensor Memory cells a `tcgen05.cp` writes and the bytes they hold are fixed by these maps. If the hardware map differs, the values a later load or MMA reads differ from the ones proven. If the hardware ordered the packed elements of a decompressing copy or placed their bits otherwise, the bytes that the copy leaves in Tensor Memory, and every value computed from them, would differ from the model's. Disclosed by every kernel whose statement names `Op.tcCp`: FlashMlaSparseDecodeH64.

</details>

<a id="thread-tc-cp-decompress"></a>
#### the bytes a decompressing tcgen05.cp writes (`THREAD-TC-CP-DECOMPRESS`)

*Rule* · [Lean comment: `Core/Tc/TmemStore.lean` L83-L112](../../Core/Tc/TmemStore.lean#L83-L112)

A `tcgen05.cp` with `.b8x16.b4x16_p64` or `.b8x16.b6x16_p32` reads and places its source rows as the copy of the same shape without decompression, and each 16-byte chunk of a source row becomes 16 destination bytes: destination byte `i` holds element `i` of the chunk, a 4-bit element in bits 5 to 2 and a 6-bit element in bits 5 to 0, the other bits zero. The copy reads the same source bytes as the copy without decompression, padding included. A chunk is bytes `16 q` to `16 q + 15` of a row, and its bits are the little-endian number of those bytes (`chunkBits`).

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcCopy.chunkBits`](../../Core/Tc/TmemStore.lean#L115-L119), [`TcCopy.decompressByte`](../../Core/Tc/TmemStore.lean#L121-L124), [`TcCopy.decompressedWord`](../../Core/Tc/TmemStore.lean#L126-L132), [`TcCopy.cpWord`](../../Core/Tc/TmemStore.lean#L134-L139), [`TcCopy.cpWord_none`](../../Core/Tc/TmemStore.lean#L141-L145)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.9.1.1: "A contiguous set of 16 elements of 4-bits each followed by 8 bytes of padding can
    be converted into 16 elements of 8-bits each as shown in Figure 197 ."
- §9.7.18.9.1.2: "A contiguous set of 16 elements of 6-bits each followed by 4 bytes of padding is
    decompressed into 16 elements of 8-bits each as shown in Figure 199 ."
- §9.7.18.9.2
- EXT-TCCP

**Applies:** tcgen05.cp of every shape with `.b8x16.b6x16_p32` or `.b8x16.b4x16_p64`

**Premises:** The premises of THREAD-TC-CP-CELLS.

**Effect:** Value geometry only: the word of each destination cell is a function of the 16 source bytes of its chunk, known only when all 16 have a bit pattern.

</details>

<a id="thread-tc-shift-cells"></a>
#### the Tensor Memory cells of tcgen05.shift (`THREAD-TC-SHIFT-CELLS`)

*Rule* · [Lean comment: `Core/Tc/TcCopy.lean` L205-L236](../../Core/Tc/TcCopy.lean#L205-L236)

A `tcgen05.shift` moves, in each CTA of its group and in each 32-lane chunk of the Tensor Memory, the 32 bytes (8 columns from the address's column) of lanes 1 to 31 of the chunk to the lane below; lane 31 of the chunk is not written and keeps its word. The address must have lane field 0 and its 8 columns within the 512 physical ones.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcShift.Spec`](../../Core/Tc/TcCopy.lean#L272-L276), [`TcShift.AddressOk`](../../Core/Tc/TcCopy.lean#L278-L280), [`TcShift.addressOkDecidable`](../../Core/Tc/TcCopy.lean#L282-L283), [`TcShift.Spec.cell`](../../Core/Tc/TcCopy.lean#L285-L286), [`TcShift.Spec.Writes`](../../Core/Tc/TcCopy.lean#L288-L291), [`TcShift.Spec.Reads`](../../Core/Tc/TcCopy.lean#L293-L295), [`TcShift.source`](../../Core/Tc/TcCopy.lean#L297-L299)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.9.3: "Instruction tcgen05.shift is an asynchronous instruction which initiates the
    shifting of 32-byte elements downwards across all the rows, except the last, by one row."
- §9.7.18.9.3: "The address operand taddr specifies the base address of the matrix in the Tensor
    Memory whose rows must be down shifted."
- §9.7.18.9.3: "When .cta_group::1 is specified, the shift operation is performed in the Tensor
    Memory of the current CTA."
- §9.7.18.9.3: "When .cta_group::2 is specified, the shift operation is performed in the Tensor
    Memory of both the current and the peer CTAs ."
- §9.7.18.2.3 (the shape `.31x256b (implicit)` of `.shift`)
- EXT-TCSHIFT

**Applies:** tcgen05.shift.cta_group::{1,2}.down

**Premises:** A Tensor Memory address with lane field 0 and columns `c` to `c + 7` within 512; with `.cta_group::2`, the pair's CTAs in the launch.

**Effect:** Cell geometry only; issue, completion, values and ordering are THREAD-TC and DEP-TMEM-SHIFT-VALUE. Lane `32 w + i` (i < 31) receives lane `32 w + i + 1`'s word in each of the 8 columns (`source`). Lane `32 w + 31` is outside `Spec.Writes`, so a later read of it takes the word of the write before the shift.

</details>

<a id="ext-tcshift"></a>
##### the rows and lanes of tcgen05.shift (`EXT-TCSHIFT`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcCopy.lean` L238-L269](../../Core/Tc/TcCopy.lean#L238-L269)

The model takes the rows of `tcgen05.shift` to be the lanes of each 32-lane chunk of the Tensor Memory and the 32-byte element to be 8 columns starting at the address's column. `tcgen05.shift.cta_group::N .down [taddr]` with lane field 0 moves, in every 32-lane chunk `32 w` to `32 w + 31` (w < 4) and in columns `c` to `c + 7` (`c` the column field of `taddr`), lane `32 w + i + 1` to lane `32 w + i` for `i` from 0 to 30; lane `32 w + 31` is the last row, which the text excludes from the shift, and keeps its word.

Source:

- - §9.7.18.9.3 and §9.7.18.2.3 (shape `.31x256b (implicit)`)

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text says that 32-byte elements of all rows but the last move down by one row and that the implicit shape is 31 x 256 bits; it does not say whether a row is a lane of the whole 128-lane matrix or of a 32-lane chunk, which lanes take part for a nonzero lane field, or whether moving down takes a row to a lower or a higher lane index. Thirty-one moved rows of 256 bits per 32-lane chunk agree with the shape.

**Effect:** If the hardware moved other lanes, the cells that a shift writes and the values it leaves would differ from the model's. Disclosed by every kernel whose statement names `Op.tcShift`: none.

**Evidence:** (manual) the sentences above; there is no figure. (CUTLASS) CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) issues no `tcgen05.shift`. (B200) The probe txverify-archive/core-coverage/probes/tcgen05_shift/ prints, for each destination lane, the source lane it holds after a shift with lane field 0 and 32 and two column fields. It ran on a B200 on 2026-11-16: in every 32-lane chunk, lane `32 w + i` (i < 31) received the old word of lane `32 w + i + 1` in columns `c` to `c + 7`, lane `32 w + 31` kept its old word, and no other cell changed. The result was the same for lane field 0 and 32, for column fields 0 and 8, and in both CTAs of `.cta_group::2`. The probe decided the direction and the chunk structure of this reading, and it agrees with the text that the last lane of each chunk keeps its word.

</details>

### Order and completion

When the asynchronous Tensor Memory accesses of tcgen05 operations are ordered, and when their completion is known.

<a id="dep-tc-collective"></a>
#### warp-collective tcgen05 instances (`DEP-TC-COLLECTIVE`)

*Rule* · [Lean comment: `Core/Data/Events.lean` L569-L587](../../Core/Data/Events.lean#L569-L587)

The `tcgen05` instructions that every lane of a warp executes together (allocation management, `ld`, `st` and the waits) are numbered within each thread, so the lanes of one collective instance share an ordinal.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`isTcColl`](../../Core/Data/Events.lean#L590-L594), [`Execution.TcK`](../../Core/Data/Events.lean#L596-L598)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.7.1
- §9.7.18.8.3
- §9.7.18.8.5 (.sync.aligned: all threads of the warp execute the same instruction)

**Applies:** Allocation management of either cta_group, tcgen05.ld, tcgen05.st and tcgen05.wait::{ld,st}

**Effect:** Projection used by the warp-collective blocking, agreement and allocation rules.

</details>

<a id="ext-tc-exec-order"></a>
##### the execution ordering of tcgen05 fences (`EXT-TC-EXEC-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcFence.lean` L91-L128](../../Core/Tc/TcFence.lean#L91-L128)

The execution ordering from a `tcgen05.fence::before_thread_sync` to a `tcgen05.fence::after_thread_sync` is base causality, or one mbarrier arrival after the first fence that a successful wait observes followed by base causality, where a relaxed arrival and wait count when each scope includes the other thread. A relay through a third thread, a relaxed wait followed by a relaxed arrival, orders nothing.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text names the execution ordering instructions by example ("like morally strong ld / st / atom instructions, mbarrier instruction, barrier instructions and so on") and does not define their composition. The model reads it with the shape of §8.9.5 ("Causality order combines base causality order with some non-transitive relations as follows: An operation X precedes an operation Y in causality order if: X precedes Y in proxy-preserved base causality order , or For some operation Z, X precedes Z in observation order, and Z precedes Y in proxy-preserved base causality order ."): base causality (`baseCausality`), or one mbarrier arrival observed by a successful wait followed by base causality. A relaxed arrival and a relaxed wait are morally strong when each scope includes the other thread (§8.7: "each operation is strong and specifies a scope that includes the thread executing the other operation"). The observed arrival is program-ordered after the `fence::before_thread_sync` (the fence orders the earlier operation before "all subsequent tcgen05 and the execution ordering operations"); the observing wait reaches the `fence::after_thread_sync` by base causality. An ordering holds at most one observation, so a relaxed wait followed in program order by a relaxed arrival is not an order (§8.10.4 permits load buffering): a relay through an intermediate thread, including the composed example of §9.7.18.6.4.4, orders nothing. Relaxed `barrier.cluster.arrive`, `atom` and relaxed `ld`/`st` flag protocols are not part of the ordering, since the model does not distinguish relaxed from weak generic accesses (MEM-LOCATION).

**Evidence:** The quoted sentences of §9.7.18.6.3 and §9.7.18.11.1, the canonical patterns 4.3 and 4.4 (Examples 1 and 2) of §9.7.18.6.4, each with one relaxed mbarrier synchronization, and the causality order of §8.9.5.

**Effect:** A single relaxed observation between the two fences orders the tcgen05 operations; if the hardware does not honour it, operations the model orders may overlap. Excluding relays through intermediate threads is stricter than the composed example of §9.7.18.6.4.4 (fewer ordered programs). Disclosed by every kernel whose statement names `Op.tcFenceBefore` or `Op.tcFenceAfter`: FlashMlaSparseDecodeH64, TcGemm.

</details>

<a id="dep-tc-completion"></a>
#### completion of Tensor Memory accesses (`DEP-TC-COMPLETION`)

*Rule* · [Lean comment: `Core/Tc/TcMmaLifetime.lean` L12-L46](../../Core/Tc/TcMmaLifetime.lean#L12-L46)

An MMA or copy has completed before a later event when a wait observes the arrive-on of a `tcgen05.commit` tracking it and reaches the event through causality to a `tcgen05.fence::after_thread_sync` before it, or, for an acquire wait, through causality alone; a load or store has completed before it when a later `tcgen05.wait::ld` or `tcgen05.wait::st` of its own thread is ordered before it.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.DoneBefore`](../../Core/Tc/TcMmaLifetime.lean#L101-L106), [`TcMma.WaitBefore`](../../Core/Tc/TcMmaLifetime.lean#L108-L111), [`TcMma.CompletedBefore`](../../Core/Tc/TcMmaLifetime.lean#L113-L118) ([concept](#c-tcmma-completedbefore))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.4 (completion handoff: "the producer threads that issue the asynchronous tcgen05
    instructions must explicitly wait for the instructions’ completion before synchronizing with the
    consumer threads"
- §9.7.18.8.5 (wait::ld)
- §9.7.18.12.1 (commit)
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

**Applies:** Every MMA, copy, Tensor Memory load and store, of either CTA group

**Premises:** An MMA completes through a `tcgen05.commit` whose arrive-on a successful wait observes; a load (store) completes through a later `tcgen05.wait::ld` (`tcgen05.wait::st`) of its thread; `CompletedBefore` selects the mechanism by the access kind. The completion is ordered before another tcgen05 operation either by a fenced chain (DEP-TC-FENCE: for an MMA the observing wait starts the chain, the commit performing the before-fence; for a load or store a `fence::before_thread_sync` after the wait starts it) or, under EXT-TCACQUIRE, by causality from an acquire wait observing the commit, or from the `wait::ld`. Allocation coverage of an access is OBJ-TMEM-LIFETIME (`Tmem.Pair.Covers`).

**Effect:** Relations used by the source, conflict, lifetime and access rules. The direction is `reading` because acceptance rests on named readings: EXT-TCACQUIRE and, through the fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path is stricter than the text.

</details>

<a id="ext-tcacquire"></a>
##### acquire synchronization orders tcgen05 operations (`EXT-TCACQUIRE`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcMmaLifetime.lean` L48-L98](../../Core/Tc/TcMmaLifetime.lean#L48-L98)

An acquire wait or `bar.sync` orders a thread's later asynchronous tcgen05 operations after the synchronization, and a release orders the thread's earlier completed tcgen05 operations before it, without a `tcgen05.fence`. On this route the completion of an MMA is observed by an acquire wait on the commit's mbarrier whose scope and the cluster scope of the arrive-on each include the other thread.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The canonical patterns of §9.7.18.6.4 synchronize with `.relaxed` mbarrier operations and the tcgen05 fences (DEP-TC-FENCE). §9.7.18.6.3 adds: "The standard memory consistency model synchronization mechanisms also apply to the tcgen05 family of instructions." The model reads this as a second, separate route: an acquire (a successful acquire `try_wait`, or `bar.sync`) orders the thread's later asynchronous tcgen05 operations after the synchronization, and a release (an arrival, or `bar.sync`) orders the thread's earlier, completed tcgen05 operations before it; this route needs no tcgen05 fence. It is the `baseCausality` disjunct of `TcMma.TcBefore` and the acquire disjunct of `DoneBefore`, whose observation requires an acquire wait (`AsyncCopy.AsyncObserved` with the acquire flag) whose scope meets the cluster scope of the commit's arrive-on (`ScopesMeet`, §8.7), as synchronization of the standard memory consistency model requires. A `.cta` wait in a peer CTA observes the completion but orders nothing. Completion is a separate requirement on both routes: an MMA completes through a `tcgen05.commit` and a successful wait on its mbarrier phase, a load through a later `tcgen05.wait::ld` of its thread. A relaxed wait reaches a later tcgen05 operation only through a `fence::after_thread_sync` (DEP-TC-FENCE). The shared-memory operand reads of an MMA are async-proxy accesses (MEM-MODEL-CAUSALITY); their completion is observed only through an acquire wait (`AsyncFinished`). The text that points the other way is §9.7.18.5 Table 55, row `.fence::*`: "A thread needs to fence all its accesses to the tensor memory that it wants to order with other accesses to the tensor memory from other threads. The following example shows that: Before attempting to deallocate Tensor Memory, it suffices to ensure that there are no concurrent Tensor Memory accesses from the Peer CTA ." Read literally, ordering a thread's tensor memory accesses with another thread's accesses needs `tcgen05.fence` (the route of DEP-TC-FENCE). The model reads acquire and release synchronization as replacing that fence: an acquire wait or `bar.sync` that causally follows the completion of the accesses orders them without a `tcgen05.fence`. This is a hardware and CUTLASS-practice assumption. It is not an inference from the text: the row quoted above says nothing of the standard synchronization mechanisms, and §9.7.18.6.3 says that they "also apply".

**Effect:** It accepts fence-free orderings that the Table 55 sentence, read literally, does not give; a program that is ordered only by this route is wrongly accepted if hardware needs the fence. Disclosed by every kernel whose statement names `Op.tcMma`, `Op.tcLd`, `Op.tcSt`, `Op.tcCp` or `Op.tcDealloc`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

**Evidence:** The sentence of §9.7.18.6.3, and CUTLASS (commit b2f249ac), which reads MMA results after an acquire `mbarrier.try_wait` without a fence (`include/cutlass/pipeline/sm100_pipeline.hpp`, `include/cutlass/epilogue/collective/sm100_epilogue_tma_warpspecialized.hpp`) and frees Tensor Memory after `tcgen05.wait::ld` and mbarrier arrive/wait without tcgen05 fences (`include/cutlass/gemm/kernel/sm100_gemm_tma_warpspecialized.hpp`). The ISA gives no example of the fence-free form.

</details>

<a id="dep-tc-pipeline"></a>
#### the pipelined pairs of tcgen05 operations (`DEP-TC-PIPELINE`)

*Rule* · [Lean comment: `Core/Tc/TcPipeline.lean` L11-L65](../../Core/Tc/TcPipeline.lean#L11-L65)

Two asynchronous tcgen05 operations of one warp access Tensor Memory in issue order without a completion wait only when they form one of the pipelined pairs of §9.7.18.6.2, and then only for the operands that the pair names. The represented pairs are the MMA and copy rows of the table and its three rows of `tcgen05.st` and `tcgen05.ld`.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.SameAccumulator`](../../Core/Tc/TcPipeline.lean#L68-L71), [`TcMma.PipeAccess`](../../Core/Tc/TcPipeline.lean#L73-L77) ([concept](#c-tcmma-pipeaccess)), [`TcMma.Pipelined`](../../Core/Tc/TcPipeline.lean#L79-L104) ([concept](#c-tcmma-pipelined)), [`TcMma.pipelined_cRead_dWrite`](../../Core/Tc/TcPipeline.lean#L106-L108), [`TcMma.pipelined_dWrite_cRead`](../../Core/Tc/TcPipeline.lean#L110-L112)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.2: "However, some specific pairs of the asynchronous tcgen05 instructions from the same
    warp form tcgen05 pipelines, where in the two asynchronous operations are guaranteed to access
    certain operands in tensor memory in the same order as the instructions that issued them."
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (A and metadata reads) -> tcgen05.mma.cta_group::N (D
    writes) (same N)"
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (A and metadata reads) -> tcgen05.cp.cta_group::N (writes)
    (same N)"
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (C reads) -> tcgen05.mma.cta_group::N (D writes) (same N
    and accumulator address and shape)"
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (D writes) -> tcgen05.mma.cta_group::N (C reads) (same N
    and accumulator address and shape)"
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (D writes) -> tcgen05.mma.cta_group::N (D writes) (same N
    and accumulator address and shape)"
- §9.7.18.6.2: "tcgen05.cp.<not .4x256b>.cta_group::N (writes) -> tcgen05.mma.cta_group::N (A and
    metadata reads) (same N and address)"
- §9.7.18.6.2: "tcgen05.st.sync.aligned -> tcgen05.ld.sync.aligned tcgen05.st.sync.aligned ->
    tcgen05.st.sync.aligned tcgen05.ld.sync.aligned -> tcgen05.st.sync.aligned"
- §9.7.18.6.2: "Instructions issued by different warps are always non-pipelined."
- §9.7.18.6.3: "The asynchronous tcgen05 instructions that are ordered across threads in the same
    warp also form a tcgen05 pipeline."
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

**Applies:** Represented MMAs of either CTA group and kind, `tcgen05.cp`, `tcgen05.ld` and `tcgen05.st`

**Premises:** Each pair requires the same warp, issue ordered by `TcBefore` (program order, a fenced chain, or EXT-TCACQUIRE) and the row's condition. The C/D rows require an equal accumulator address and shape (M, N) on the same physical CTAs. The A-read rows require an A operand in Tensor Memory. The copy→A-read row requires the copy's address as the A operand, and it excludes `.4x256b` copies. The rows of `tcgen05.st` and `tcgen05.ld` have no further condition. The table's same-N condition (the CTA group) holds by PROG-TC-CTA-GROUP.

**Effect:** `Pipelined` is the only statement of the table in the model. The write order (DEP-TC-READ-SOURCE, DEP-TMEM-STORE-VALUE), the read sources (DEP-TC-READ-SOURCE), the conflict check (ERR-TMEM-RACE) and the completion order (DEP-TC-COMPLETION-CLOSURE) use it. The direction is `reading` because the issue order rests on named readings: EXT-TCACQUIRE and, through the fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER.

</details>

<a id="dep-tc-read-source"></a>
#### Tensor Memory write order and read sources (`DEP-TC-READ-SOURCE`)

*Rule* · [Lean comment: `Core/Tc/TcMmaOrder.lean` L11-L59](../../Core/Tc/TcMmaOrder.lean#L11-L59)

A Tensor Memory write is ordered before a later access when its completion has been observed before the access, or when the two form a pipelined pair (DEP-TC-PIPELINE). A Tensor Memory read (a register of a `tcgen05.ld`, an accumulator or A read of an MMA, or a read of a `tcgen05.shift`) takes its word from a source: a write of the cell ordered before the reading operation, such that every other write of the cell comes before the source or after the read has happened, and no release of the cell's allocation separates source and read.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.Before`](../../Core/Tc/TcMmaOrder.lean#L62-L65) ([concept](#c-tcmma-before)), [`TcMma.TmemWrite`](../../Core/Tc/TcMmaOrder.lean#L67-L69) ([concept](#c-tcmma-tmemwrite)), [`TcMma.WriteBefore`](../../Core/Tc/TcMmaOrder.lean#L71-L74) ([concept](#c-tcmma-writebefore)), [`TcMma.SourceLive`](../../Core/Tc/TcMmaOrder.lean#L76-L83), [`TcMma.TmemRead`](../../Core/Tc/TcMmaOrder.lean#L85-L89) ([concept](#c-tcmma-tmemread)), [`TcMma.ReadBefore`](../../Core/Tc/TcMmaOrder.lean#L91-L99) ([concept](#c-tcmma-readbefore)), [`TcMma.ReadSource`](../../Core/Tc/TcMmaOrder.lean#L101-L109) ([concept](#c-tcmma-readsource)), [`TcMma.readSource_ld`](../../Core/Tc/TcMmaOrder.lean#L111-L120), [`TcMma.readSource_acc`](../../Core/Tc/TcMmaOrder.lean#L122-L146), [`TcMma.readSource_a`](../../Core/Tc/TcMmaOrder.lean#L148-L155), [`TcMma.readSource_shift`](../../Core/Tc/TcMmaOrder.lean#L157-L163)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.2: "The asynchronous tcgen05 operations may execute and complete in a different order
    than they were issued."
- §9.7.18.6.2.1.1: "Completion of the following instruction’s asynchronous operations is observed
    through the mbarrier based waiting mechanism: tcgen05.mma tcgen05.cp tcgen05.shift"
- §9.7.18.6.2.1.2: "Completion of the following instruction’s asynchronous operations is observed
    through tcgen05.wait based waiting mechanism: tcgen05.ld tcgen05.st"
- §9.7.18.6.4 (inter-thread synchronization; 4.1 and 4.3 are pipelines)
- §9.7.18.7.1 (allocation lifetime)
- DEP-TC-PIPELINE
- DEP-TC-COMPLETION
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

**Applies:** Every represented MMA, `tcgen05.cp`, `tcgen05.st` and `tcgen05.shift` write, and every register of a `tcgen05.ld`, accumulator and Tensor Memory A read of an MMA and read of a `tcgen05.shift`

**Premises:** A write is ordered before an event by its completion mechanism (an observed commit for an MMA or copy, a `tcgen05.wait::st` for a store) or by a pipelined pair. A read has happened before a write `w` by the reader's completion mechanism (a `tcgen05.wait::ld` for a load, an observed commit for an MMA or shift), when `w` is a write of the reading operation itself, or by the pipelined pairs that start at the read: ld→st for a load, C read→D write for an accumulator read, A read→D write and A read→copy for an A read. A source is a write other than the reading operation itself, and it survives all relevant releases: the reader completes (`CompletedBefore`) before each release of a covering allocation (`Tmem.Pair.Covers`), or the release precedes the source. Allocation coverage of the reader and the source is checked once, by ERR-TMEM-ACCESS-LIFETIME.

**Effect:** The relations of the write order and the read source. The value a read returns is DEP-TC-LOAD-VALUE (loads and A reads), DEP-TC-MMA-VALUE (accumulator reads) and DEP-TMEM-SHIFT-VALUE (shift reads); the requirement that a read has a source is ERR-TMEM-READ-SOURCE. The direction is `reading` because acceptance rests on named readings: EXT-TCACQUIRE and, through the fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path is stricter than the text.

</details>

<a id="dep-tmem-store-value"></a>
#### Tensor Memory stores and their completion (`DEP-TMEM-STORE-VALUE`)

*Rule* · [Lean comment: `Core/Tc/TmemStore.lean` L14-L45](../../Core/Tc/TmemStore.lean#L14-L45)

Register j of a `tcgen05.st` writes its 32-bit value to the cell that the fragment of the shape assigns to it. The write is ordered before a later event only through a later `tcgen05.wait::st` of the storing thread followed by tcgen05 ordering, or, for a later `tcgen05.ld` or `tcgen05.st` of the same warp, through the pipelined pairs of DEP-TC-PIPELINE.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.StoreCell`](../../Core/Tc/TmemStore.lean#L48-L51), [`TcMma.StoreValue`](../../Core/Tc/TmemStore.lean#L53-L56), [`TcMma.StoreDoneBefore`](../../Core/Tc/TmemStore.lean#L58-L63), [`TcMma.storeDoneBefore_iff`](../../Core/Tc/TmemStore.lean#L65-L81)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.2.3.1 (fragments of every shape)
- §9.7.18.8.4 (tcgen05.st)
- §9.7.18.6.1 (st is asynchronous)
- DEP-TC-PIPELINE (the pairs st→ld and st→st)
- §9.7.18.6.2.1.2 and §9.7.18.8.5 (wait::st)
- §9.7.18.6.3: "The asynchronous tcgen05 instructions that are ordered across threads in the same
    warp also form a tcgen05 pipeline."
- §9.7.18.6.4.2: "Example 1: tcgen05.st tcgen05.wait::st tcgen05.ld"
- §9.7.18.6.4.4 (completion handoff)
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

**Applies:** Represented tcgen05.st of every shape, in the storing thread's CTA

**Premises:** Register slot `j` is the cell of the store's recorded shape and address (`tcDataCell`, THREAD-TC-DATA-ADDRESS), with the register's 32-bit value read at issue.

**Effect:** Relations used by the Tensor Memory source, stability, conflict and lifetime rules. The direction is `reading` because acceptance rests on named readings: EXT-TCACQUIRE and, through the fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path is stricter than the text.

</details>

<a id="dep-tmem-copy-value"></a>
#### Tensor Memory words written by tcgen05.cp (`DEP-TMEM-COPY-VALUE`)

*Rule* · [Lean comment: `Core/Tc/TmemStore.lean` L147-L171](../../Core/Tc/TmemStore.lean#L147-L171)

A `tcgen05.cp` writes, in each CTA of its group, the lanes its shape assigns to each source row by the row's columns at its address, each word holding its four source bytes from that CTA in order, or with decompression the four bytes THREAD-TC-CP-DECOMPRESS gives, and unknown if a source byte it depends on is unknown. Its completion is observed like that of an MMA, through a `tcgen05.commit`. A `tcgen05.shift` writes and reads the cells that THREAD-TC-SHIFT-CELLS gives; the words it leaves are DEP-TMEM-SHIFT-VALUE.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.CpCell`](../../Core/Tc/TmemStore.lean#L174-L178), [`TcMma.CpValue`](../../Core/Tc/TmemStore.lean#L180-L187), [`TcMma.ShiftCell`](../../Core/Tc/TmemStore.lean#L189-L191), [`TcMma.ShiftReadCell`](../../Core/Tc/TmemStore.lean#L193-L195)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.9.2 (tcgen05.cp)
- §9.7.18.6.2.1.1 (commit-based completion)
- THREAD-TC-CP-CELLS
- THREAD-TC-CP-DECOMPRESS

**Applies:** Every represented tcgen05.cp (THREAD-TC-CP-CELLS, THREAD-TC-CP-DECOMPRESS) and tcgen05.shift

**Premises:** The copy's source bytes are its recorded asynchronous reads.

**Effect:** Writer and value relations used by the Tensor Memory source, stability, conflict and lifetime rules.

</details>

<a id="dep-tmem-shift-value"></a>
#### the words tcgen05.shift leaves (`DEP-TMEM-SHIFT-VALUE`)

*Rule* · [Lean comment: `Core/Tc/TcMmaValue.lean` L184-L219](../../Core/Tc/TcMmaValue.lean#L184-L219)

A `tcgen05.shift` leaves in a cell the word that the next lane of its chunk (index + 1) held when the shift read it: the value of an MMA result, a store or a copy of that cell that is ordered before the shift, that no other write of the cell follows before the shift has completed, and that no release of the allocation separates from the shift. A cell whose source is itself the result of a shift gets no value. The shift does not write the last lane of a 32-lane chunk, which keeps its word (THREAD-TC-SHIFT-CELLS).

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`TcMma.ShiftSource`](../../Core/Tc/TcMmaValue.lean#L222-L227), [`TcMma.ShiftValue`](../../Core/Tc/TcMmaValue.lean#L229-L234)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.9.3 (tcgen05.shift)
- §9.7.18.6.2.1.1: "Completion of the following instruction’s asynchronous operations is observed
    through the mbarrier based waiting mechanism: tcgen05.mma tcgen05.cp tcgen05.shift"
- THREAD-TC-SHIFT-CELLS
- EXT-TCSHIFT

**Why it is not spec text:** The text does not say when, between issue and completion, the shift reads its rows. A write of a source cell that is not ordered before the shift or after its completion therefore leaves the moved word without a value.

**Applies:** Every represented tcgen05.shift

**Premises:** The source cell is the cell of the next lane (index + 1) in the same chunk (`TcShift.source`), and its source write is ordered before the shift and stable until the shift completes (the read source of a shift read, `ReadSource .shift`, DEP-TC-READ-SOURCE).

**Effect:** A value relation used by DEP-TC-LOAD-VALUE; a load of a shifted cell without such a source has no read source, which ERR-TMEM-READ-SOURCE rejects. The model derives no value through two shifts in a row, since the source of a shift must be an MMA result, a store or a copy; this choice only rejects programs.

</details>

<a id="dep-tc-completion-closure"></a>
#### identical-footprint D-write completion closure (`DEP-TC-COMPLETION-CLOSURE`)

*Rule* · [Lean comment: `Core/Tc/TcMmaCompletion.lean` L11-L42](../../Core/Tc/TcMmaCompletion.lean#L11-L42)

When two MMAs issued in program order by one thread form a pipelined pair on the same accumulator and write the same nonempty set of cells, the later one has completed its Tensor Memory writes only if the earlier one has.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.SameWrites`](../../Core/Tc/TcMmaCompletion.lean#L45-L49), [`TcMma.CompletionPrecedes`](../../Core/Tc/TcMmaCompletion.lean#L51-L53), [`TcMma.CompletionClosed`](../../Core/Tc/TcMmaCompletion.lean#L55-L58)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.2: "The asynchronous tcgen05 operations may execute and complete in a different order
    than they were issued. However, some specific pairs of the asynchronous tcgen05 instructions
    from the same warp form tcgen05 pipelines, where in the two asynchronous operations are
    guaranteed to access certain operands in tensor memory in the same order as the instructions
    that issued them."
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (D writes) -> tcgen05.mma.cta_group::N (D writes) (same N
    and accumulator address and shape)"
- §9.7.18.6.4.1 (pipelined instructions, same thread)
- DEP-TC-PIPELINE

**Applies:** Pairs of the D→D pipeline (`Pipelined … .dWrite … .dWrite`) issued by one thread in program order whose Tensor Memory write footprints are the same nonempty set of cells.

**Premises:** `Pipelined L X .dWrite i .dWrite j` (same warp, `TcBefore`, equal accumulator address, M, N and physical CTAs); `i` and `j` are the same thread with `i` earlier; `SameWrites`: the two `writeCell` mappings agree on every row and column and write at least one cell.

**Effect:** CompletionClosed constrains asynchronous completion effects in Consistent. The completion of an operation extends a closed execution when all its qualifying predecessors are done. The text orders the D writes of the pair. With one footprint, the later operation writes every cell that the earlier one writes, after it, and this is the reading. `mmaDone` means that all Tensor Memory writes of the MMA have completed.

</details>

### Values

The values that MMAs compute and that loads and Tensor Memory A reads return.

<a id="dep-tc-mma-value"></a>
#### finite derivations of MMA accumulator values (`DEP-TC-MMA-VALUE`)

*Rule* · [Lean comment: `Core/Tc/TcMmaValue.lean` L12-L45](../../Core/Tc/TcMmaValue.lean#L12-L45)

The value of a result cell of a `kind::i8` MMA is the exact sum of the 32 products of its A row and B column, read from the recorded operand bytes as signed or unsigned, plus the old D value when accumulation is enabled, wrapped to 32 bits; with saturation a value is derived only when no partial sum can leave the s32 range. Every kind reads operand element `(r, k)` as the `kind.width` bytes at `(r * kind.k + k) * kind.width` of the row-major operand (`elementBytes`), with `k < kind.k`. The kind::i8 value is computed from the bit patterns of the operand bytes (THREAD-BYTES), and an unknown byte, or a byte without a bit pattern, gives no value. With saturation the products alone never leave the s32 range, and when a partial sum can leave it, the clamped value depends on the unspecified summation order and no value is derived. Core has no numerical profile for kind::f16, kind::tf32 and kind::f8f6f4, and the first selected profile gives their arithmetic. The floating kinds get values only from a selected numerical profile, and the old value of an accumulating MMA comes from an earlier MMA result or store that is its accumulator source.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.byteInt`](../../Core/Tc/TcMmaValue.lean#L92-L97), [`TcMma.s32`](../../Core/Tc/TcMmaValue.lean#L99-L100), [`TcMma.elementBytes`](../../Core/Tc/TcMmaValue.lean#L102-L106), [`TcMma.mmaTerms`](../../Core/Tc/TcMmaValue.lean#L108-L117), [`TcMma.SaturationFree`](../../Core/Tc/TcMmaValue.lean#L119-L121), [`TcMma.accumulateInt`](../../Core/Tc/TcMmaValue.lean#L127-L139), [`TcMma.intEval`](../../Core/Tc/TcMmaValue.lean#L141-L144), [`TcMma.eval`](../../Core/Tc/TcMmaValue.lean#L146-L155) ([concept](#c-tcmma-eval)), [`TcMma.Result`](../../Core/Tc/TcMmaValue.lean#L157-L182) ([concept](#c-tcmma-result)), [`TcMma.Wrote`](../../Core/Tc/TcMmaValue.lean#L236-L240) ([concept](#c-tcmma-wrote))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.10.10.1 (D = A*B + enable-input-d*C), Table 48 (kind::i8: s8 or u8 inputs, s32 D), Table
    51 bit 3 (saturate)
- EXT-TCI8-WRAP (integer overflow); explicitly selected numerical profile

**Applies:** Dense MMA result cells with recorded operand observations

**Premises:** Actual issue, unmasked physical cell, exact recorded A/B observations and successful evaluation. Accumulation additionally requires the old value, a finite MMA derivation or a stored word, and an accumulator read source (`ReadSource .acc`, DEP-TC-READ-SOURCE) for the same physical cell. Disabled accumulation needs no prior D. Enabled accumulation cannot invent a zero and cannot justify a value by itself or circularly.

**Effect:** This contract derives a result. It asserts no completion and filters no execution.

</details>

<a id="ext-tci8-wrap"></a>
##### integer accumulation wraps modulo 2^32 (`EXT-TCI8-WRAP`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcMmaValue.lean` L47-L70](../../Core/Tc/TcMmaValue.lean#L47-L70)

For `tcgen05.mma.kind::i8` without the saturate bit the s32 accumulator wraps modulo 2^32 on overflow, whatever the order of accumulation. With the saturate bit the model derives a value only when no partial sum in any order overflows.

Source:

- - §9.7.16.5.14: "The .satfinite qualifier indicates that on overflow, the accumulated value is limited to the range MIN_INT32 .. MAX_INT32 ... If .satfinite is not specified, the accumulated value is wrapped instead" - §9.7.17.5.2: "The .satfinite qualifier indicates that on overflow, the accumulated value is limited to the range MIN_INT32 .. MAX_INT32 ... If .satfinite is not specified, the accumulated value is wrapped instead" - §9.7.18.10.10.1 and Table 51 bit 3: "Saturate for integer types"

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The sentences are in the `mma` and `wgmma` descriptions, and the model reads them as the behaviour of the 5th-generation integer MMA. The `tcgen05.mma` text states the saturate bit and the s32 D type but no overflow behaviour.

**Effect:** The wrapped value is derived for a tcgen05 accumulation the text leaves open. If hardware clamped or wrapped differently, `Post` could differ from the result. Disclosed by every kernel whose statement names `MmaKind.i8`: TcGemm.

</details>

<a id="ext-tctf32"></a>
##### FP32 inputs of kind::tf32 (`EXT-TCTF32`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcMmaValue.lean` L72-L89](../../Core/Tc/TcMmaValue.lean#L72-L89)

The FP32 values in the 32-bit containers of a `kind::tf32` operand are converted to TF32 by truncating their low 13 mantissa bits.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The ISA calls kind::tf32 inputs TF32 without saying how the 32-bit containers' FP32 values are converted.

**Evidence:** On a B200 `Tools/probes/tcgen05_ws_ts_tf32.ptx` (`tcgen05.mma.ws` with A in Tensor Memory, M = 128, N = 64, K = 8, inputs with bits below the TF32 mantissa in A, and with `lowb` in B, every product and sum exact in FP32) matched truncation of the low 13 mantissa bits on all 8192 outputs (five runs), round-to-nearest-even on about 8% and no conversion on under 1%.

**Effect:** The FP32 input values of a tf32 MMA are fixed by this truncation. If the hardware converts differently, the products differ from the ones proven. Disclosed by every kernel whose statement names `MmaKind.tf32`: none.

</details>

<a id="dep-tc-load-value"></a>
#### the values that Tensor Memory loads and A reads return (`DEP-TC-LOAD-VALUE`)

*Rule* · [Lean comment: `Core/Tc/TcMmaRead.lean` L11-L39](../../Core/Tc/TcMmaRead.lean#L11-L39)

Each register of a `tcgen05.ld` returns the word that its read source (DEP-TC-READ-SOURCE) left in its cell. A 32-bit value fills the whole word, an FP16 result fixes only the low two bytes, and a byte of an A operand read from Tensor Memory is likewise the corresponding byte of the word its read source left.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.LoadCell`](../../Core/Tc/TcMmaRead.lean#L42-L46), [`TcMma.WordContains`](../../Core/Tc/TcMmaRead.lean#L48-L51), [`TcMma.LoadReadOk`](../../Core/Tc/TcMmaRead.lean#L53-L58), [`TcMma.AReadOk`](../../Core/Tc/TcMmaRead.lean#L60-L67), [`TcMma.ReadOk`](../../Core/Tc/TcMmaRead.lean#L69-L71) ([concept](#c-tcmma-readok))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.2.3.1 (fragments of every shape)
- §9.7.18.10.4.1 (unpacked subword D)
- §9.7.18.6.4 (completion observation and handoff)
- §9.7.18.8.5 (wait::ld)
- DEP-TC-READ-SOURCE
- DEP-TC-MMA-VALUE

**Applies:** Represented tcgen05.ld of every shape consuming dense MMA results, stored, copied or shifted words, and MMA A operands read from Tensor Memory

**Premises:** The actual load's register slot maps, by its recorded shape and address (`tcDataCell`), to the source cell in its own CTA. The source is a read source of the load (`ReadSource .ld`) or of the A read (`ReadSource .a`), and the value is the one it wrote (`Wrote`).

**Effect:** ReadOk is a Consistent field. Safety separately requires source existence (ERR-TMEM-READ-SOURCE), allocation coverage (ERR-TMEM-ACCESS-LIFETIME), instruction validity, resource lifetimes and conflict ordering. Completion of the load itself requires its own `tcgen05.wait::ld` before a later overwrite or release of the cell.

</details>

### What counts as an error

Executions and kernels that are rejected as unsafe because of a tcgen05 instruction.

<a id="err-tmem-read-source"></a>
#### every Tensor Memory read has a source (`ERR-TMEM-READ-SOURCE`)

*Rule* · [Lean comment: `Core/Tc/TcMmaRead.lean` L73-L102](../../Core/Tc/TcMmaRead.lean#L73-L102)

Every register that a Tensor Memory load returns, every accumulator cell that a completed accumulating MMA may read, and every Tensor Memory A byte that a completed MMA reads has a read source as DEP-TC-READ-SOURCE defines it, with a value: a completed and stable write of a live allocation. An execution in which such a read sees uninitialized Tensor Memory, reads across an unprotected release or reads an overwritten value is unsafe.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`TcMma.SourceRequired`](../../Core/Tc/TcMmaRead.lean#L105-L111), [`TcMma.SourceSafe`](../../Core/Tc/TcMmaRead.lean#L113-L116), [`TcMma.SourceUnsafe`](../../Core/Tc/TcMmaRead.lean#L118-L120) ([concept](#c-tcmma-sourceunsafe)), [`TcMma.sourceSafe_iff`](../../Core/Tc/TcMmaRead.lean#L122-L141)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.4 (completion)
- §9.7.18.6.3 (tcgen05 fences, DEP-TC-FENCE; standard synchronization also applies, EXT-TCACQUIRE)
- §9.7.18.7.1 (releases)
- DEP-TC-READ-SOURCE

**Applies:** Every register of every Tensor Memory load, and every accumulator and Tensor Memory A read of a completed MMA

**Premises:** Each such read has a read source (`ReadSource`) and a value written by it (`Wrote`). An accumulator read counts also for masked output lanes. The read of a `tcgen05.shift` needs no source of its own: the moved word has a value only with one (DEP-TMEM-SHIFT-VALUE), so a later load or MMA that reads the moved word without one fails this check.

**Effect:** Safety check (with the resource, lifetime, MMA instruction, conflict and commit checks, the Tensor Memory part of `Unsafe`). Writer order is ERR-TMEM-RACE; release at completion and access completion before release are ERR-TMEM-NOT-RELEASED and -ACCESS. Bulk copies and mbarriers instead use general object transitions, read-source constraints, proxy ordering and access-hazard checks, without a phase/count bound.

</details>

<a id="err-tc-mma"></a>
#### issue coverage and completed result coverage (`ERR-TC-MMA`)

*Rule* · [Lean comment: `Core/Tc/TcMmaSafety.lean` L13-L45](../../Core/Tc/TcMmaSafety.lean#L13-L45)

An execution is unsafe when an MMA has an invalid shape or mask, CTAs that do not match the launch, a shared descriptor that is not encoded or not supported, a D address with a wrong lane alignment or columns past the 512th, or an operand byte without an address. It is also unsafe when a completed MMA has an unmasked result without a derived value, when a `tcgen05.cp` reads an unsupported source, or when an MMA reuses a collector buffer against ERR-TC-COLLECTOR-REUSE.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`TcMma.SharedEncoded`](../../Core/Tc/TcMmaSafety.lean#L48-L51), [`TcMma.IssueShape`](../../Core/Tc/TcMmaSafety.lean#L53-L64), [`TcMma.CompletedValues`](../../Core/Tc/TcMmaSafety.lean#L66-L68), [`TcMma.CopySafe`](../../Core/Tc/TcMmaSafety.lean#L70-L73), [`TcMma.InstructionSafe`](../../Core/Tc/TcMmaSafety.lean#L75-L80), [`TcMma.InstructionUnsafe`](../../Core/Tc/TcMmaSafety.lean#L82-L84) ([concept](#c-tcmma-instructionunsafe))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.4.1 (descriptor encoding/alignment)
- §9.7.18.5 (issue granularity and active peer)
- §9.7.18.10.5 (D layout)
- §9.7.18.10.9.5 (alignment)
- §9.7.18.10.10.1 (MMA)
- DEP-TC-MMA-VALUE

**Applies:** Every represented dense MMA, including instructions with no subsequent load, and every represented tcgen05.cp

**Premises:** Launched issuer, valid decoded shape and masks, launch-derived CTA group, encoded shared fields, the same Layout F lane alignment for D and Tensor Memory A (§9.7.18.10.5), complete supported operand address mapping and in-range D. Every completed unmasked output has a finite numerical derivation; every collector reuse satisfies `CollectorSafe`. The sources of the accumulator and A reads of a completed MMA are required by ERR-TMEM-READ-SOURCE.

**Effect:** InstructionUnsafe enters Unsafe and does not filter executions. Base-offset, absolute and LUT modes are limited by the support scope of THREAD-TC-SHARED-ADDRESS. The checks apply to every result of a completed MMA, whether or not a later load reads it. The lifetimes of the operand CTAs are checked by ERR-SHARED-LIFETIME, whose completing stage is the completion of the MMA or copy.

</details>

<a id="err-tc-collector-reuse"></a>
#### collector buffer reuse (`ERR-TC-COLLECTOR-REUSE`)

*Rule* · [Lean comment: `Core/Tc/TcMmaCollector.lean` L11-L57](../../Core/Tc/TcMmaCollector.lean#L11-L57)

An MMA that may read A or B from a collector buffer (`::use`, `::lastuse`) is safe only when the latest earlier MMA of its thread that does not reuse that buffer fills it, no other thread issues MMAs on the CTAs of the issue, and the operand bytes it reads are those the filling MMA read. Any other reuse makes the execution unsafe.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`TcMma.CollectorId`](../../Core/Tc/TcMmaCollector.lean#L60-L64), [`TcMma.Collectors.op`](../../Core/Tc/TcMmaCollector.lean#L66-L69), [`TcMma.CollectorId.bytes`](../../Core/Tc/TcMmaCollector.lean#L71-L74), [`TcMma.SoleIssuer`](../../Core/Tc/TcMmaCollector.lean#L76-L80), [`TcMma.CollectorFill`](../../Core/Tc/TcMmaCollector.lean#L82-L88), [`TcMma.CollectorSafe`](../../Core/Tc/TcMmaCollector.lean#L90-L97) ([concept](#c-tcmma-collectorsafe)), [`TcMma.collectorSafe_of_noReuse`](../../Core/Tc/TcMmaCollector.lean#L99-L108)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.10: "The collector qualifier is used to give the TensorCore permission to reuse a
    previously loaded A or B matrix; however reuse is opportunistic in that the TensorCore may
    reload a matrix even when it has permission to reuse that matrix."
- §9.7.18.10: "Thus, the source memory of an A or B matrix must not be modified while the MMA
    instruction using those matrices has not completed - regardless of collector qualifier
    permissions."
- §9.7.18.10.10.1: ".collector::a::use , .collector::b::use Specified matrix can be read from the
    collector buffer."
- §9.7.18.10.10.1: "This requires a previous fill to the collector buffer to be still valid."
- §9.7.18.10.10.1: "This requires a previous fill to the collector buffer to be valid till the
    collector buffer is read."
- §9.7.18.10.10.1: "If no .collector_a_usage qualifier is specified, then it defaults to
    .collector::a::discard ."
- §9.7.18.10.10.3: "This requires a previous fill to the collector buffer #N to be still valid."

**Applies:** Every MMA issue whose collector usage of A or of a B buffer is `use` or `lastuse`

**Premises:** The thread's latest earlier MMA that names the buffer with another usage fills it; every MMA of the thread between them names the buffer with `use` or not at all; every MMA issue on a CTA of the issue is by the same thread; when both have read their operands, the reused operand's bytes equal those of the filling MMA.

**Effect:** `CollectorSafe` is a conjunct of `InstructionSafe` (ERR-TC-MMA); a violation makes the execution unsafe and filters none. An MMA reads its operands from memory in the model (DEP-TC-LOAD-VALUE, THREAD-TC-MMA-OPERANDS), whatever its collector usage. A reusing MMA on hardware reads either the buffer, which holds what the filling MMA read, or memory, since reuse is opportunistic. The two agree when the bytes this MMA reads equal those the filling MMA read, which is the last premise; when they may differ, the value of the result is not determined and the execution is unsafe. The text does not say which MMAs can invalidate a buffer: every MMA names the A buffer (`discard` by default), and the model counts every MMA of the thread between the fill and the reuse that names the buffer with an operation other than `use` as ending it. The non-`.ws` B buffer `::b` and the `.ws` buffer `::b0` are taken to be one buffer, and an MMA that names another `.ws` buffer leaves this one as it is. MMAs of other threads are not ordered with the issue by program order, so any MMA of another thread on a CTA of the issue makes a reuse unsafe. These choices only reject programs.

</details>

<a id="err-tmem-race"></a>
#### Tensor Memory write conflicts (`ERR-TMEM-RACE`)

*Rule* · [Lean comment: `Core/Tc/TcMmaConflicts.lean` L11-L44](../../Core/Tc/TcMmaConflicts.lean#L11-L44)

An execution is unsafe when two Tensor Memory writes of one cell (MMA results, stores, copies or shifts) are ordered in neither direction, or when an MMA's accumulator or A read, or a `tcgen05.shift`'s read, of a cell is ordered in neither direction with a write of that cell. Accumulator reads count also for masked output lanes, shift reads also when the moved words are never read, and the orders are observed completion and the pipelined pairs.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`TcMma.WritesSafe`](../../Core/Tc/TcMmaConflicts.lean#L47-L50), [`TcMma.WritesUnsafe`](../../Core/Tc/TcMmaConflicts.lean#L52-L53) ([concept](#c-tcmma-writesunsafe)), [`TcMma.RaceRead`](../../Core/Tc/TcMmaConflicts.lean#L55-L62), [`TcMma.ReadsSafe`](../../Core/Tc/TcMmaConflicts.lean#L64-L69), [`TcMma.readsSafe_iff`](../../Core/Tc/TcMmaConflicts.lean#L71-L88), [`TcMma.ReadsUnsafe`](../../Core/Tc/TcMmaConflicts.lean#L90-L91) ([concept](#c-tcmma-readsunsafe))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.2: "The asynchronous tcgen05 operations may execute and complete in a different order
    than they were issued."
- §9.7.18.6.2–4 (pipeline and explicit completion ordering)
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

**Applies:** Every unmasked MMA write, store, copy, shift write, enabled accumulator read, Tensor Memory A read and shift read, including masked lanes and results never loaded

**Premises:** Conflicts are equality of physical CTA, lane and column. A write is ordered before a read by `WriteBefore`, and a read before a write by `ReadBefore` of the read's kind: the reader's observed completion, the reading operation's own write, or a pipelined pair of §9.7.18.6.2 that starts at the read (C read→D write, A read→D write and A read→copy; the table has no pair that starts at a shift's read and ends at another operation's write). The registers of a `tcgen05.ld` are not in this check: ERR-TMEM-READ-SOURCE requires every write of the cell to be ordered with every load register.

**Effect:** WritesUnsafe and ReadsUnsafe enter Unsafe. The direction is `reading` because acceptance rests on named readings: EXT-TCACQUIRE and, through the fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path is stricter than the text.

</details>

<a id="prog-tc-cta-group"></a>
#### one tcgen05 CTA-group qualifier per kernel (`PROG-TC-CTA-GROUP`)

*Rule* · [Lean comment: `Core/Tc/TcGroup.lean` L10-L27](../../Core/Tc/TcGroup.lean#L10-L27)

A kernel is correct only if its code does not contain both instructions qualified `.cta_group::1` and instructions qualified `.cta_group::2`, counting predicated and unreachable instructions. Loads, stores, waits and fences name no group.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`Op.tcGroup`](../../Core/Tc/TcGroup.lean#L30-L37), [`Kernel.tcGroupUniform`](../../Core/Tc/TcGroup.lean#L39-L42), [`Kernel.TcGroupUniform`](../../Core/Tc/TcGroup.lean#L44-L46) ([concept](#c-kernel-tcgroupuniform))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.10.10.1 (all tcgen05 instructions within a kernel specify the same cta_group)

**Applies:** All represented source instructions with an explicit tcgen05 .cta_group qualifier

**Premises:** Inspect the whole source kernel, including predicated and unreachable instructions. Unqualified ld/wait/fence instructions contribute no group.

**Effect:** Static component of Correct.safe.

</details>
