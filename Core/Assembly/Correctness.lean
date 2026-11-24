-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Progress
public import Core.Tc.TcGroup

@[expose] public section

/-!
# The four correctness obligations

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## CORRECT-MAXIMAL — executions that cannot grow
Statement: An execution is maximal when it is possible and no possible execution that extends it has
  more counted events.

Defs: Maximal

Source:
- none

Direction: equal
-/

/-- `X` is possible and no possible execution extends `X` by more counted events
(`Execution.size`, which does not count failed polls). -/
def Maximal (K : Kernel) (A : List Assumption) (mem0 : Mem0) (X : Execution) : Prop :=
  Consistent L K A mem0 X ∧
    ∀ Y, Consistent L K A mem0 Y → X.le Y → Y.size L ≤ X.size L

/-! ## CORRECT-COMPLETE — launched threads exited, canceled clusters accounted for and work drained
Statement: An execution is complete when every launched thread has exited or belongs to a cluster
  that was canceled before it launched, every issued asynchronous operation has delivered its
  completion, and every paired Tensor Memory allocator request belongs to a completed collective
  operation.

Defs: AsyncDrained, asyncDrained_iff, Complete

Source:
- §9.7.14.6–7 (thread exit)
- §9.7.10.28.1 (asynchronous completion)
- §9.7.18.6.2.1.1 (the completion of `tcgen05.mma`, `tcgen05.cp` and `tcgen05.shift` is observed
    through the mbarrier based waiting mechanism)

Direction: equal

Effect: Every thread either exited or belongs to a canceled, unlaunched cluster. Every issued
  linear/tensor input or output copy (a linear copy without an mbarrier by its write),
  `cp.async.mbarrier.arrive` arrive-on, MMA, `tcgen05.cp` (`TcAsync`) and commit finished, and each
  CLC target received its completion notification. Every issued paired allocator request belongs to
  its recorded collective resource operation. A thread is accounted for only by a recorded exit (or
  its cluster's cancellation), and pending work only by its completion.
-/

/-- Every issued asynchronous operation has finished: every stage that completes it
(`AsyncCopy.FinalStage`, the table of DEP-ASYNC-STAGE-ORDER) is present. -/
def AsyncDrained (X : Execution) : Prop :=
  ∀ i p, AsyncCopy.FinalStage X i p → X.AsyncPresent i p

/-- `AsyncDrained` in its earlier form, one conjunct per kind of operation. -/
theorem asyncDrained_iff (X : Execution) : AsyncDrained X ↔
    ((∀ i s, X.Copy i s → match s.completion with
      | .mbarrier _ => (X.async.copies i).notified = true
      | _ => (X.async.copies i).writeBytes.isSome) ∧
    (∀ i m noinc, X.AsyncArrive i m noinc → X.async.arrived i = true) ∧
    (∀ i, X.TcAsync i → X.async.mmaDone i = true) ∧
    (∀ i s targets, X.ClcIssue i s targets → ∀ c ∈ targets, c ∈ (X.clc i).notified) ∧
    (∀ i mapAddress s, X.TensorIssue i mapAddress s →
      ∃ observation, X.tensor i = some observation ∧ observation.effects.notified = true) ∧
    (∀ i mapAddress s, X.TensorStoreIssue i mapAddress s →
      ∃ observation, X.tensorStores i = some observation ∧ observation.effects.fullDone = true) ∧
    ∀ i s rank m, X.Commit i s → TcCommit.target s rank = some m → rank ∈ X.tcNotified i) := by
  constructor
  · intro h
    refine ⟨fun i s hc => ?_, fun i m n ha => h i _ (.inr (.inr (.inl ⟨m, n, ha, rfl⟩))),
      fun i ht => h i _ (.inr (.inr (.inr (.inl ⟨ht, rfl⟩)))),
      fun i s t hc c hm => h i _ (.inr (.inr (.inr (.inr (.inl ⟨s, t, c, hc, hm, rfl⟩))))),
      fun i a s ht => h i _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨a, s, ht, rfl⟩)))))),
      fun i a s ht => h i _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨a, s, ht, rfl⟩))))))),
      fun i s r m hc ht => h i _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        ⟨s, r, m, hc, ht, rfl⟩)))))))⟩
    cases hs : s.completion with
    | mbarrier m => exact h i _ (.inl ⟨s, m, hc, hs, rfl⟩)
    | bulkGroup => exact h i _ (.inr (.inl ⟨s, hc, by simp [hs], rfl⟩))
    | asyncGroup => exact h i _ (.inr (.inl ⟨s, hc, by simp [hs], rfl⟩))
    | unobserved => exact h i _ (.inr (.inl ⟨s, hc, by simp [hs], rfl⟩))
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩ i p hp
    rcases hp with ⟨s, m, hc, hs, rfl⟩ | ⟨s, hc, hs, rfl⟩ | ⟨m, n, ha, rfl⟩ | ⟨ht, rfl⟩ |
      ⟨s, t, c, hc, hm, rfl⟩ | ⟨a, s, ht, rfl⟩ | ⟨a, s, ht, rfl⟩ | ⟨s, r, m, hc, ht, rfl⟩
    · have := h1 i s hc
      rw [hs] at this
      exact this
    · have := h1 i s hc
      cases hcs : s.completion with
      | mbarrier m => exact absurd hcs (hs m)
      | bulkGroup => rw [hcs] at this; exact this
      | asyncGroup => rw [hcs] at this; exact this
      | unobserved => rw [hcs] at this; exact this
    · exact h2 i m n ha
    · exact h3 i ht
    · exact h4 i s t hc c hm
    · exact h5 i a s ht
    · exact h6 i a s ht
    · exact h7 i s r m hc ht

/-- `X` is complete: every launched thread has exited or belongs to a canceled cluster, the
asynchronous work is drained (`AsyncDrained`), and every paired Tensor Memory allocator request
belongs to a completed collective operation (`Tmem.Pair.Drained`). -/
def Complete (X : Execution) : Prop :=
  (∀ g < L.threads, ClcCanceled L X g ∨ ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) ∧
    AsyncDrained X ∧ Tmem.Pair.Drained L X

/-! ## CORRECT-FINAL — memory after the kernel
Statement: The memory after a complete execution comes from a coherence order of its writes that
  orders every two overlapping morally strong writes and contains each coherence edge the execution
  determines in one direction only. A byte holds the value of its last write in that order, the
  common value of its last writes when they all agree, or its launch content when no write covers
  it.

Defs: FinalMem, CoStep, coStep_of_reduceReads, CoBefore, CoOrder, CoMaximal, IsFinal

Source:
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

Direction: stricter

Applies: Each byte of memory after a complete execution

Premises: The writes of the execution, `ByteCausality` between them, reads-from among the morally
  strong atomic read-modify-writes of one footprint, and the sources of reads that follow a write in
  `ByteCausality`.

Effect: Constrains `m` in CORRECT `result`. The end of the kernel follows every event of the
  kernel, including asynchronous writes completed after the last thread exit (EXT-LAUNCH; §8.9.4
  states it for the end of the threads), so a read of memory after the kernel reads a write that
  no other write follows in coherence order (§8.10.6). One order `co` serves every byte, so the
  bytes of one write that follows another in coherence order all hold its value. Three kinds of
  edges give the coherence order the execution determines (`CoStep`, closed transitively in
  `CoBefore`), each at a byte both writes cover:
  - `ByteCausality` from one write to another is causality (§8.10.1).
  - An atomic read-modify-write that reads a byte from another one, morally strong with it at the
    same footprint, follows it (MEM-ATOMICITY, `AtomicReads`). Over these operations this is the
    single reads-from chain of MEM-ATOMICITY, so concurrent `atom`s, `red`s or tensor reductions of
    one element (split-K) end with the result of the last one, which has applied every earlier one.
  - A write `W` that is `ByteCausality`-before a read reading from a different write `W’` morally
    strong with `W` precedes `W’`: the two are related in coherence order (§8.9.6), and `W’` before
    `W` is what §8.10.6 forbids.

Review: An order containing these edges and total on the morally strong pairs exists for every PTX
  execution (the coherence order itself). `CoOrder` asks for the edges whose reverse is not
  derivable, so such an order exists for every execution (`final_exists`). This includes executions
  whose reads the axioms would reject; there the final byte is less constrained. Racing writes are
  unrelated in coherence order (§8.9.6), so several writes to a byte can be co-maximal
  (`CoMaximal`). A read after the kernel reads one of them (§8.10.6), so when they all write the
  same value the byte holds it, whatever `co` leaves unordered. When they differ the byte is
  unconstrained, and less constrained than the text, which gives one of their values. The model
  leaves out the coherence edges §8.10.5 gives between the sources of two morally strong reads in
  program order (CoRR) and the single-copy atomicity of a morally strong read (§8.10.3). Without
  them the final byte is less constrained.
-/

/-- Memory after the kernel, per byte (`none` = not allocated). -/
abbrev FinalMem := Loc → Option (Option Byte)

/-- One coherence-order edge between two writes that cover a byte `l`: `ByteCausality` (causality,
§8.10.1); an atomic read-modify-write reading from another one morally strong with it at the same
footprint (MEM-ATOMICITY); or a write `ByteCausality`-before a read of `l` from another write
morally strong with it (§8.9.6, §8.10.6). -/
def CoStep (X : Execution) (w w' : AsyncCopy.Ref) : Prop :=
  ∃ l a bs a' bs', X.MemWrites w a bs ∧ a.Covers l ∧ X.MemWrites w' a' bs' ∧ a'.Covers l ∧
    (ByteCausality L X l w w' ∨
      (∃ p q k k', AtomicReads L X p q ∧ w = p.newRef k ∧ w' = q.newRef k') ∨
      (w ≠ w' ∧ MorallyStrong L X w w' a a' ∧ ∃ r ar rbs k, X.MemReads r ar rbs ∧ k < ar.size ∧
        ar.loc.at k = l ∧ X.rf r k = some w' ∧ ByteCausality L X l w r))

/-- Two reductions of one tensor element, the second reading a byte from the first, give the
coherence edge between their writes, when every tensor reduction has its issue event and every
issuing thread is a thread of the launch: the edge EXT-TMA-REDUCE-ATOMIC gave before MEM-ATOMICITY.
-/
theorem coStep_of_reduceReads {X : Execution} (hS : TensorStoreOk L X)
    (hout : ∀ g, L.threads ≤ g → X.tr g = []) {l : Loc} {a a' : Acc} {bs bs' : List Byte}
    {fp : Acc} {p q : EvId × Nat × Nat} {k k' : Nat}
    (hw : X.MemWrites (.async p.1 (.write (.store p.2.1 p.2.2 k))) a bs) (hl : a.Covers l)
    (hw' : X.MemWrites (.async q.1 (.write (.store q.2.1 q.2.2 k'))) a' bs') (hl' : a'.Covers l)
    (h : TensorStore.ReduceReads X fp p q) :
    CoStep L X (.async p.1 (.write (.store p.2.1 p.2.2 k)))
      (.async q.1 (.write (.store q.2.1 q.2.2 k'))) :=
  ⟨l, a, bs, a', bs', hw, hl, hw', hl', Or.inr (Or.inl ⟨.tensor p.1 p.2.1 p.2.2,
    .tensor q.1 q.2.1 q.2.2, k, k', atomicReads_of_reduceReads L hS hout h, rfl, rfl⟩)⟩

/-- The coherence order of the writes that the execution determines (§8.9.6). -/
def CoBefore (X : Execution) : AsyncCopy.Ref → AsyncCopy.Ref → Prop :=
  Relation.TransGen (CoStep L X)

/-- A coherence order of the execution's writes (§8.9.6): a strict order that relates every two
distinct overlapping morally strong writes and contains each `CoBefore` edge whose reverse is not
in `CoBefore`. -/
structure CoOrder (X : Execution) (co : AsyncCopy.Ref → AsyncCopy.Ref → Prop) : Prop where
  irrefl : ∀ w, ¬ co w w
  trans : ∀ u v w, co u v → co v w → co u w
  strong : ∀ w a bs w' a' bs' l, X.MemWrites w a bs → a.Covers l → X.MemWrites w' a' bs' →
    a'.Covers l → w ≠ w' → MorallyStrong L X w w' a a' → co w w' ∨ co w' w
  before : ∀ w w', CoBefore L X w w' → ¬ CoBefore L X w' w → co w w'

/-- `w` writes byte `l` and no write of `l` follows it in `co`. -/
def CoMaximal (X : Execution) (co : AsyncCopy.Ref → AsyncCopy.Ref → Prop) (l : Loc)
    (w : AsyncCopy.Ref) : Prop :=
  (∃ a bs, X.MemWrites w a bs ∧ a.Covers l) ∧
    ∀ w' a' bs', X.MemWrites w' a' bs' → a'.Covers l → ¬ co w w'

/-- `m` is the memory after `X`: for a coherence order `co` of `X`, each byte holds the write
that every other write to it precedes in `co`, the value all its co-maximal writes agree on, or
its launch content. -/
def IsFinal (mem0 : Mem0) (X : Execution) (m : FinalMem) : Prop :=
  ∃ co, CoOrder L X co ∧ ∀ l,
    (∀ w a bs, X.MemWrites w a bs → a.Covers l →
      (∀ w' a' bs', X.MemWrites w' a' bs' → a'.Covers l → w' = w ∨ co w' w) →
      m l = some (wbyte a bs l)) ∧
    ((∀ w a bs, X.MemWrites w a bs → ¬ a.Covers l) → m l = mem0 l) ∧
    ∀ b, (∃ w, CoMaximal X co l w) →
      (∀ w a bs, CoMaximal X co l w → X.MemWrites w a bs → wbyte a bs l = b) → m l = some b

/-! ## CORRECT-LAUNCH — launches the kernel's declarations admit
Statement: A launch is valid for a kernel when its counts are the products of its shapes and the
  grid is a whole number of clusters in each dimension, the CTA size is at most the product of the
  `.maxntid` extents and equals the `.reqntid` extents in each dimension, and every `.ptr` parameter
  is a multiple of its alignment. Correctness concludes nothing about any other launch.

Defs: Launch.Valid, Launch.oneDim_reqntid

Source:
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

Direction: reading

Applies: The launch `L` of kernel `K` in every CORRECT conclusion

Premises: None; this is the premise of the conclusions.

Effect: CORRECT concludes nothing about a launch outside `Launch.Valid`: hardware fails such a
  launch, no hardware launch has its counts and shapes, or the compiled code relies on what it
  violates.

Review: The `.maxntid` bound applies to the product of the extents because §11.5.2 says that the
  directive "does not guarantee that the limit in any particular dimension is not exceeded".
  `.reqntid nx[, ny[, nz]]` admits exactly the CTA shape `(nx, ny, nz)`, an extent not written being
  1. A launch of any shape is valid; a kernel whose precondition names `Launch.oneDimLaunch`
  restricts its own theorem to one-dimensional launches (PROG-CLUSTER). `Launch.explicitCluster` and
  the values of `Launch.sregInit` are not constrained here: a launch whose flag or values no
  hardware launch has only adds launches a theorem must cover. The pointer alignment is what the
  memory "is assumed to be aligned to"; the text gives no behaviour for a pointer that is not
  aligned and the compiler may rely on it, so such a launch is outside the theorem (reading). The
  state space of a `.ptr .space` parameter is recorded but not checked: `Launch.params` are raw
  bits, and that the value points into that space is part of EXT-LAUNCH.
-/

/-- The launch is one the kernel's declarations admit. -/
def Launch.Valid (K : Kernel) (L : Launch) : Prop :=
  L.clusterGridValid ∧
  (∀ n, K.maxThreads = some n → L.block ≤ n) ∧
  (∀ s, K.reqThreads = some s → s = (L.ntid.x, L.ntid.y, L.ntid.z)) ∧
  ∀ name p v, (name, p) ∈ K.ptrParams → L.params name = some v → v.toNat % p.align = 0

/-- In a one-dimensional launch a `.reqntid` shape is admitted exactly when it is `(block, 1, 1)`,
the condition of the one-dimensional model. -/
theorem Launch.oneDim_reqntid {L : Launch} (h : L.OneDim) (s : Nat × Nat × Nat) :
    s = (L.ntid.x, L.ntid.y, L.ntid.z) ↔ s = (L.block, 1, 1) := by
  rw [h.1]

/-!
Three readings apply to every kernel. They state how far the conclusion `Correct` carries to
real hardware.

### EXT-ISA — the toolchain implements the ISA

Statement: The model takes `ptxas` and the hardware to implement the PTX ISA, its memory consistency
  model included (§8), for the instructions a kernel uses. `ptxas` may reorder or combine
  instructions only as far as the memory model allows. The model's axioms are stated over PTX
  program order, so a theorem carries to hardware only as far as this holds. For the execution
  layer (DEP-ORDER), the model also trusts that `ptxas` and the hardware keep the program
  order of the synchronizing and blocking instructions and of the canonical spins, as listed under
  Review.

Source:
- §9.7.15.10: "vote.sync will cause executing thread to wait until all non-exited threads
    corresponding to membermask have executed vote.sync with the same qualifiers and same
    membermask value before resuming execution."
- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited threads
    from its warp and marks warps’ arrival at barrier."

Evidence: §1.1 ("PTX defines a virtual machine and ISA for general purpose parallel thread
  execution. PTX programs are translated at install time to the target hardware instruction set.")
  and §1.2 ("Provide a stable ISA that spans multiple GPU generations."): the ISA is the
  specification the translator and the hardware are documented to meet. That they meet it is
  trusted. The model does not check it. It covers only what the ISA text states; every reading the
  model takes beyond that text is a separate EXT note (indexed in `Core/README.md`), and each
  kernel's `Theorem.lean` lists the ones that apply to it (see Disclosure in `Core/README.md`).

Direction: trust (if `ptxas` or the hardware deviates from the ISA, no theorem transfers).

Review: The manual describes the PTX abstract machine; it does not say that `ptxas` keeps the
  order of instructions. The execution layer relies on these properties of the translation:
  - The synchronizing and blocking instructions (`bar`/`barrier`, `barrier.cluster`,
    `bar.warp.sync`, `vote`, `shfl`, `redux`, `match`, `elect`, the mbarrier operations, the
    `tcgen05` fences, commit, waits and allocation management, `setmaxnreg`, `griddepcontrol`, the
    `cp.async` and bulk group waits) keep their relative program order.
  - None of them is moved into or out of a canonical spin (DEP-CANONICAL-SPIN), and no instruction
    after the exit of a canonical spin is executed before the poll that exits it.
  - Where the manual says that a thread waits "before resuming execution", as in the sentences
    quoted under Source, no synchronizing, blocking or memory-ordering instruction that follows in
    PTX program order is executed before the wait completes.
  - Ordinary computation and the memory accesses that the memory model does not order may move
    freely. The model accounts for this by keeping the edges of the execution layer out of the
    memory layer (MEM-OBJECT-ORDER-CAUSALITY, DEP-ORDER).

Effect: Disclosed by every kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.

### EXT-LAUNCH — memory and parameters at launch

Statement: The model takes `mem0` to be the device memory when the kernel starts and the launch data
  (the shapes `Launch.nctaid`, `Launch.ntid`, `Launch.clusterNctaid` with their counts,
  `Launch.explicitCluster`, `Launch.params`, `Launch.paramObjects`, `Launch.tensorMaps`) to describe
  what the host passed. A theorem carries to a real launch only when that launch also meets the six
  obligations listed in this note, which the model does not check.

Effect: The memory and the parameters the kernel starts with. `mem0` is the device memory when the
  kernel starts, and `Launch.params` are the parameter values passed. The grid, CTA and cluster
  shapes are the dimensions the host launched with, and `Launch.explicitCluster` says whether it
  gave cluster dimensions. At a `.local` location `⟨.local, g, x⟩` it is byte `x` of thread `g`'s
  local memory (allocated or not), and at a `.const` location `⟨.const, 0, x⟩` byte `x` of the
  constant memory as the host initialized it. `Launch.paramObjects` supplies the actual by-value
  parameter declarations and their generic addresses; bindings must agree with `Kernel.paramObjects`
  and the launch ABI, including object identity, size, alignment and disjoint storage.
  `Launch.paramBytes name k`, when supplied, is byte `k` of the by-value parameter object `name` as
  the host passed it; how the host's argument is laid out in those bytes is the launch's. A
  `tensorMaps` entry at such an address must describe the actual descriptor passed by value in that
  parameter object. `Launch.tensorLargeAllocMinBytes`, when supplied, must equal the device-reported
  `CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE`. The descriptor allocation class must match
  the actual opaque tensor map. `Launch.tensorMaps` records the properties of actual host-created,
  immutable tensor maps at their addresses, published before launch. The host proof or review must
  establish these properties from descriptor construction; they are not conclusions about the
  kernel's output. Device-side updates are outside this launch-only interface. Writes before the
  launch are ordered before every event of the kernel, and every event of the kernel before the
  memory is read afterwards (§8.9.4: start and end of a kernel synchronize).

Evidence: CUDA C++ Programming Guide (kernel launch, stream ordering).

Review: Launches outside `Launch.Valid` (CORRECT-LAUNCH: `.maxntid`, `.reqntid`, `.ptr` alignment,
  whole clusters) are outside every theorem; they are not obligations. Six obligations follow from
  this interface; the model does not check them. Each kernel's `Theorem.lean` lists them, and the
  Fp16Gemm8192 README states how its launch meets them:
  - No aliases: no two distinct addresses of the kernel's address spaces map to one memory location
    (§8.2.2 defines aliases and does not exclude them); the model gives every byte one location
    (MEM-LOCATION). In particular the local memories of two threads do not overlap: a `.local`
    address names a byte of the issuing thread's own local memory, which no other thread can access
    (§5.1.5: "The local state space ( .local ) is private memory for each thread to keep its own
    data.").
  - Pointer state spaces: a `.ptr .space` parameter (recorded in `Kernel.ptrParams`) holds a value
    that points into that space (§5.1.6.3); `Launch.params` are raw bits and the model does not
    check this.
  - Tensor maps: every map in `Launch.tensorMaps` is host-created and not written while the kernel
    runs (in particular not through a global pointer to it; §8.9.4 requires a
    `fence.proxy.tensormap::generic` for such updates, which is not decoded). A map passed as a
    by-value kernel parameter lies in parameter storage, which no decoded store writes.
  - Tensor Memory requested by co-resident CTAs: the model gives each CTA its own 512 columns
    (OBJ-TMEM-ALLOCATOR). On hardware the Tensor Memory of an SM is shared by the CTAs resident on
    it; §9.7.18.1 gives the Tensor Memory per CTA, and §9.7.18.7.1 states: "The tcgen05.alloc
    blocks if the requested amount of Tensor Memory is not available and unblocks as soon as the
    requested amount of Tensor Memory becomes available for allocation." The launch must ensure
    that the total number of columns that the CTAs co-resident on one SM, of this or of any other
    kernel, may request through `tcgen05.alloc` at once never exceeds what one SM provides, so
    that every `tcgen05.alloc` of the kernel can be satisfied. The obligation counts requests, and
    columns held do not enter it: two co-resident CTAs that each request 512 columns and then wait
    for each other do not meet it. One CTA of the kernel per SM, with no co-resident CTA of another
    kernel that allocates Tensor Memory, suffices. Allocation progress relies on this.
  - No conflicting outside access, no PDL-dependent launch: while the kernel runs, (a) no other
    agent accesses (reads or writes) the memory the kernel writes, and (b) no other agent writes
    the memory the kernel reads or that its `Post` constrains. This covers kernels running
    concurrently in other streams or contexts, prerequisite or dependent grids running
    concurrently through programmatic dependent launch (PDL), host accesses (mapped memory) and
    peer devices. The kernel is not launched as a PDL dependent grid; §9.7.15.14 states: "If the
    prerequisite grid is using griddepcontrol.launch_dependents , then the dependent grid must use
    griddepcontrol.wait to ensure correct functional execution." Under this obligation
    `griddepcontrol` has no effect (EXT-GRIDDEP-SINGLE). Basis: the accesses of other agents are
    not events of the execution. In the model a read returns a write of this execution or the
    launch memory `mem0` (MEM-READS-FROM), the final memory is determined by this execution's writes
    alone (CORRECT-FINAL), and the race checks (ERR-DATA-RACE, ERR-MIXED-SIZE) compare only this
    execution's accesses. An outside read that overlaps a write of the kernel conflicts with it
    (§8.7.1: "Two overlapping memory operations are said to conflict when at least one of them is
    a write ."); if the two overlap partially, they form a mixed-size data-race, and §8.7.2
    states: "The axioms in the memory consistency model do not apply if a PTX program contains one
    or more mixed-size data-races ." The model cannot see such a race, so (a) excludes outside
    readers as well as writers.
  - No multimem addresses: no address the kernel accesses is a multimem address. §8.2.3 states:
    "Only multimem. * operations and fabric instructions with the .multimem qualifier are valid on
    multimem addresses. That is, the behavior of accessing a multimem address in any other memory
    operation is undefined." and §9.7.10.15 states: "Accessing a multimem address with ld , st or
    any other memory operations results in undefined behavior." The model has no multimem
    addresses; no instruction with `.multimem` is decoded.
  Disclosed by every kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.

Direction: trust (the six obligations are facts about the launch environment that the model does not
  check; for a launch that does not meet one of them, no theorem transfers).

### EXT-PREFERRED-CLUSTER — clusters of a preferred and a regular shape

Statement: The model takes a launch to place its clusters as the CUDA launch attributes allow: each
  cluster has the regular cluster shape or the preferred cluster shape, the clusters tile the grid,
  and each cluster's origin lies on the lattice of the regular shape. A launch may mix the two
  shapes in any such tiling, and the model's theorems cover every tiling. `Launch.clusterNctaid` is
  the cluster dimension (`clusterDim`) and `Launch.preferredNctaid` the preferred cluster dimension
  (`preferredClusterDim`) of the launch; without a preferred dimension the two are equal.
  `Launch.clusterPlaces` gives each cluster's origin `%ctaid`, its shape, and the `%clusterid` and
  `%nclusterid` its threads read. `Launch.clusterGridValid` admits a placement when each grid extent
  is a whole number of regular and of preferred extents, each preferred extent is a whole number of
  regular extents in `x` and `y` and equal to the regular extent in `z`, each cluster has one of the
  two shapes and lies in the grid with its origin a multiple of the regular extent in each
  dimension, the clusters have exactly the grid's CTAs with no `%ctaid` twice, and the clusters have
  distinct `%clusterid`, each below its `%nclusterid`. A grid of regular clusters is the special
  case `ClusterPlace.uniform`.

Evidence: CUDA Driver API, `CUlaunchAttributeValue` (CUDA 12.8 and later): for `clusterDim`, “x -
  The X dimension of the cluster, in blocks. Must be a divisor of the grid X dimension.” (and
  likewise for y and z); for `preferredClusterDim`, “x - The X dimension of the preferred cluster,
  in blocks. Must be a divisor of the grid X dimension, and must be a multiple of the x field of
  CUlaunchAttributeValue::clusterDim.” (and likewise for y), and for z “Must be equal to the z field
  of CUlaunchAttributeValue::clusterDim.” The CUDA Runtime API documentation of the preferred
  cluster dimension says that blocks are grouped into preferred clusters on a best-effort basis and
  that the device may launch the regular clusters instead.

Why it is not spec text: The PTX ISA does not mention preferred clusters. The CUDA documentation
  does not say whether one launch mixes the two shapes, how a mixed grid is tiled, which part of the
  grid gets which shape, or which `%clusterid` and `%nclusterid` the threads of a preferred cluster
  read. The model admits every tiling by the two shapes whose origins lie on the lattice of the
  regular shape, and leaves the identifiers to the launch apart from their being distinct and below
  their counts. The alignment to the regular lattice is the reading's choice; it follows from tiling
  when every cluster has the regular shape.

Direction: reading

Effect: A theorem holds for every placement `Launch.clusterGridValid` admits. If hardware places
  clusters outside this set (for example a preferred cluster whose origin is not on the regular
  lattice), the launch is outside the theorem. Each cluster's registers, peers, CTA pairs, multicast
  masks, cluster barrier and cluster launch control response are those of its own cluster
  (PROG-CLUSTER). Disclosed by every kernel whose statement names `Launch.preferredNctaid` or
  `Launch.clusterPlaces`: none.

### EXT-IMPORT — the source is the program

Statement: The model takes the Lean program of each kernel to be the parse of the `.ptx` file that
  the compiler produced for that kernel: `Kernels/<K>/Ptx.lean` is the parse of
  `Kernels/<K>/<k>.ptx`. The Python parser and exporter that produce it are outside Lean.

Evidence: `tests/test_semantics.py` regenerates `Ptx.lean` from the `.ptx` file, and the `.ptx` file
  from the `.cu` source with nvcc.

Effect: Disclosed by every kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.
-/

/-! ## CORRECT — total correctness
Statement: A kernel is correct for a launch, its launch memory and a postcondition when, if the
  launch is valid, the kernel uses one `tcgen05` CTA-group qualifier, no possible execution is
  unsafe, every maximal possible execution is complete, the possible executions have a common bound
  on their number of counted events, and the memory after every complete execution satisfies the
  postcondition.

Defs: Correct

Source:
- none (the statement of every theorem)

Direction: equal

Effect: For a launch the kernel admits (CORRECT-LAUNCH), the source obeys PROG-TC-CTA-GROUP. No
  possible execution is unsafe. An execution that cannot grow is complete, that is, every thread has
  exited or belongs to a canceled cluster, every asynchronous operation has finished, and every
  paired Tensor Memory allocator request belongs to a completed collective operation
  (CORRECT-COMPLETE). One bound covers the number of counted events. After a complete execution the
  memory satisfies `post`. Together, `progress` and `terminates` give that every fair run reaches a
  complete execution (CORRECT-FAIR, `Correct.exits`).
-/

/-- Total correctness of kernel `K` under assumptions `A`, for launch `L`, launch memory `mem0`
and postcondition `post` (CORRECT). Each field holds for a launch the kernel admits
(`Launch.Valid`). -/
structure Correct (K : Kernel) (A : List Assumption) (L : Launch) (mem0 : Mem0)
    (post : FinalMem → Prop) : Prop where
  /-- The kernel uses one `tcgen05` CTA-group qualifier (PROG-TC-CTA-GROUP), and no possible
  execution is unsafe (ERR-UNSAFE). -/
  safe : L.Valid K → K.TcGroupUniform ∧ ∀ X, Consistent L K A mem0 X → ¬ Unsafe L K A mem0 X
  /-- Every maximal possible execution is complete (CORRECT-MAXIMAL, CORRECT-COMPLETE). -/
  progress : L.Valid K → ∀ X, Maximal L K A mem0 X → Complete L X
  /-- One bound covers the number of counted events of every possible execution. -/
  terminates : L.Valid K → ∃ N, ∀ X, Consistent L K A mem0 X → X.size L ≤ N
  /-- The memory after every complete possible execution satisfies `post` (CORRECT-FINAL). -/
  result : L.Valid K → ∀ X m, Consistent L K A mem0 X → Complete L X → IsFinal L mem0 X m →
    post m

end

end PTX
