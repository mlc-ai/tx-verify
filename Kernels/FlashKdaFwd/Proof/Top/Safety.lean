-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Static
public import Lemmas.CtaBarrier.CtaBarrierFault
public import Lemmas.Kernel.Goals
public import Lemmas.Kernel.Safety.Lifetime
public import Lemmas.Kernel.Safety.Object
public import Lemmas.Kernel.Safety.Schedule
public import Lemmas.Matrix.Mma
public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # Safety by class, from stated premises (top-level skeleton)

`Correct.safe` asks that no consistent execution of the kernel is `Unsafe`
(`Core/Assembly/Execution.lean`): a disjunction of 28 classes of undefined behaviour. This file
is the fixed dispatcher over those classes. Fourteen classes are closed by the decoded program
alone (`Top/Static.lean`). The other fourteen are derived here, with the library lemma of each
class, from a structure of premises about one consistent execution, `SafetyFacts`. Each field
of the structure is one kernel-specific fact, stated in the vocabulary of the trusted model
(events, footprints, orders), so that it can be proved on its own from the thread layer (what
every event of a thread looks like) or from the protocol layer (which accesses are ordered).
`Top/Wire.lean` and `Top/Final.lean` fill the structure from the contracts of the layers
below.

Words used below. A *CTA* is one thread block: 192 threads, of which threads 0 to 127 (four
warps) are the *compute* threads, 128 to 159 the *load* warp and 160 to 191 the *store* warp. A
*lane* is a thread's index in its warp of 32 threads. An *mbarrier* is an 8-byte synchronization
object in shared memory; the kernel has eleven per CTA, at the offsets `98304 + 8 j` (`j < 11`)
of its shared-memory window, after 98304 bytes of data. *TMA* is the hardware copy engine: a
*tensor load* copies a box of a global tensor into shared memory and a *tensor store* copies
shared memory into a global tensor, both asynchronously. A *tile* is 16 consecutive tokens of
the CTA's sequence. An *intent* (`Execution.Intent`) is a memory access with its footprint,
whether already performed or still pending in an issued asynchronous operation.

The classes and the premises they use:

| class of `Unsafe` | library lemma | premises |
| --- | --- | --- |
| `HasUb` | (per role) | `computeNoUb`, `loadNoUb`, `storeNoUb` |
| `Unalloc` | (direct) | the five frames |
| `Race`, `Mixed` | `ConflictsOrdered.no_race`, `.no_mixed` | `accOrdered`, `bufOrdered`, frames |
| `BarMismatch` | `Frame.noBarMismatch_of_schedule` | `barShape` |
| `CtaBarFault` | `not_ctaBarFault` | `barShape` |
| `AlignedMismatch` | `Frame.noAlignedMismatch_of_schedule` | the four schedule fields |
| `TmaUnsafe` | `Frame.noTmaUnsafe_of_noCopy` | the three mbarrier history fields, frames |
| `MbarUninit` | (direct) | `mbarInitBefore` |
| assumption `ub` | (direct) | `writeFrame` |
| `SharedLifetimeUnsafe` | `noSharedLifetime_of_own` | `sharedOwn`, `asyncFinished` |
| `TensorUnsafe` | `TensorCopy.CopyOk.writes` | `loadFill` |
| `TensorAllocationUnsafe` | (direct) | `loadBounds`, `storeBounds` |
| `MatrixUnsafe` | `WarpMatrix.mma_ne_error` | `mmaOperands` |

The frames are `memSpaces`, `sharedFrame`, `globalReadFrame`, `writeFrame`, `globalWriteOnce` and
`mbarFrame`; the schedule fields are `barShape`, `wholeBars`, `matrixShape` and `matrixCount`;
the mbarrier history fields are `mbarInitFirst`, `mbarPublished` and `mbarFaultFree`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX PTX.Flow Recurrence

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ## The schedules of the barrier and matrix instructions -/

/-- The sequence that the CTA of thread `g` works on: the kernel reads it as `%ctaid.x`, which
`Pre.clusterPlaces` makes the CTA number modulo the number of sequences. -/
def seqOf (P : Params) (L : Launch) (g : Nat) : Nat := g / L.block % P.sequences

/-- The number of tiles of the sequence of thread `g`'s CTA: the trip count of the tile loop. -/
def tilesOf (P : Params) (L : Launch) (g : Nat) : Nat := tiles (P.length (seqOf P L g))

/-- The positions of the `bar.sync 0` instructions (barrier 0, the whole CTA), in code order. -/
def wholeBarPcs : List Nat :=
  (kernel.code.zipIdx.filter fun x => match x.1.op with | .barSync .. => true | _ => false).map
    (·.2)

/-- The positions of the `bar.sync id, count` instructions (a named barrier among a stated
number of threads), in code order. -/
def namedBarPcs : List Nat :=
  (kernel.code.zipIdx.filter fun x => match x.1.op with | .barSyncN .. => true | _ => false).map
    (·.2)

/-- The warp matrix instructions (`ldmatrix`, `stmatrix`, `movmatrix`, `mma.sync`) of the code,
in code order: position and operation. All of them are in the body of the tile loop, which has
no branch between the first and the last of them. -/
def matrixSites : List (Nat × MatrixOp) :=
  kernel.code.zipIdx.filterMap fun x => match x.1.op with
    | .matrix m => some (x.2, m.op)
    | _ => none

/-- The kernel has nine `bar.sync 0`, six of them before its one named barrier, which is in the
tile loop of the compute threads. -/
theorem barSites_shape : wholeBarPcs.length = 9 ∧ namedBarPcs.length = 1 ∧
    (wholeBarPcs.filter (· < namedBarPcs.getD 0 0)).length = 6 := by
  decide +kernel

/-- The kernel has 182 warp matrix instructions. -/
theorem matrixSites_length : matrixSites.length = 182 := by decide +kernel

/-- Every `bar.sync 0` is an aligned instruction (the PTX form `bar.sync` is
`barrier.sync.aligned`), so its events are the ones the exit clause of ERR-ALIGNED-MISMATCH
counts (`Kernel.isAlignedCtaBar`). -/
theorem wholeBars_aligned : wholeBarPcs.all kernel.alignedAt = true := by decide +kernel

/-- Every warp-level multiply-accumulate of the code is the form
`mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32` (`WarpMatrix.mma16`), the one form that
the library's value lemmas cover. -/
theorem matrixSites_mma : matrixSites.all (fun x => match x.2 with
    | .mma s => decide (s = WarpMatrix.mma16)
    | _ => true) = true := by
  decide +kernel

/-- **The barrier schedule**: the position, barrier id and thread count of the `k`-th barrier
event of thread `g` (counting from zero). Every thread arrives nine times on barrier 0 with the
whole CTA: six times before the tile loop and three times after it. A compute thread also
arrives once per tile, between the sixth and the seventh of these, on barrier 8 with the 128
compute threads. -/
def barSchedule (P : Params) (L : Launch) (g k : Nat) : Nat × Nat × Option Nat :=
  if g % L.block < 128 then
    if k < 6 then (wholeBarPcs.getD k 0, 0, none)
    else if k < 6 + tilesOf P L g then (namedBarPcs.getD 0 0, 8, some 128)
    else (wholeBarPcs.getD (k - tilesOf P L g) 0, 0, none)
  else (wholeBarPcs.getD k 0, 0, none)

/-- The number of warp matrix events of thread `g` in a complete run: 182 per tile for a compute
thread, none for the load and store warps. -/
def matrixTotal (P : Params) (L : Launch) (g : Nat) : Nat :=
  if g % L.block < 128 then 182 * tilesOf P L g else 0

/-- Two lanes of a warp have one barrier schedule: they are both compute threads or both not,
and their CTA has one sequence. -/
theorem barSchedule_sameWarp {g h : Nat} (hw : SameWarp L g h) :
    barSchedule P L g = barSchedule P L h := by
  obtain ⟨⟨-, -, hc⟩, hq⟩ := hw
  funext k
  unfold barSchedule tilesOf seqOf
  rw [hc]
  by_cases hg : g % L.block < 128
  · rw [ite_eq_left hg, ite_eq_left (show h % L.block < 128 by omega)]
  · rw [ite_eq_right hg, ite_eq_right (show ¬ h % L.block < 128 by omega)]

/-- Two lanes of a warp have one matrix total. -/
theorem matrixTotal_sameWarp {g h : Nat} (hw : SameWarp L g h) :
    matrixTotal P L g = matrixTotal P L h := by
  obtain ⟨⟨-, -, hc⟩, hq⟩ := hw
  unfold matrixTotal tilesOf seqOf
  rw [hc]
  by_cases hg : g % L.block < 128
  · rw [ite_eq_left hg, ite_eq_left (show h % L.block < 128 by omega)]
  · rw [ite_eq_right hg, ite_eq_right (show ¬ h % L.block < 128 by omega)]

/-- A scheduled barrier is barrier 0 of the whole CTA or barrier 8 of 128 threads: the barrier
id determines the count. -/
theorem barSchedule_count (P : Params) (L : Launch) (g k : Nat) :
    (barSchedule P L g k).2 = (0, none) ∨ (barSchedule P L g k).2 = (8, some 128) := by
  unfold barSchedule
  split_ifs <;> simp

/-! ## The premises -/

/-- **The kernel-specific facts about one consistent execution `X` from which every class of
`Unsafe` that the decoded program does not exclude is derived.** One group of fields per class;
some fields serve several classes. -/
structure SafetyFacts (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  -- ERR-UNDEFINED-INSTRUCTION (`HasUb`), one field per role. A thread makes an
  -- undefined-behaviour event when an instruction faults: a register read before it is written, an
  -- operand of the wrong kind or width, a misaligned address, a floating instruction on a value
  -- that is no finite number of its format, received bytes that do not form a value, an executed
  -- `brkpt`.
  /-- No compute thread (index below 128 in its CTA) makes an undefined-behaviour event. -/
  computeNoUb : ∀ g k pc f, g % L.block < 128 → X.get (g, k) ≠ some ⟨pc, .ub f⟩
  /-- No thread of the load warp (index 128 to 159) makes an undefined-behaviour event. -/
  loadNoUb : ∀ g k pc f, 128 ≤ g % L.block → g % L.block < 160 →
    X.get (g, k) ≠ some ⟨pc, .ub f⟩
  /-- No thread of the store warp (index 160 and above) makes an undefined-behaviour event. -/
  storeNoUb : ∀ g k pc f, 160 ≤ g % L.block → X.get (g, k) ≠ some ⟨pc, .ub f⟩
  -- The memory frames: where the accesses of the kernel lie. They serve ERR-UNALLOCATED-ACCESS,
  -- the race classes, the mbarrier lifetime class and the read-only assumption.
  /-- Every access, of a thread or of an asynchronous operation, pending or performed, is to
  shared or to global memory: the kernel uses no local and no constant memory. -/
  memSpaces : ∀ e a, X.MemTouches e a → a.loc.space = .shared ∨ a.loc.space = .global
  /-- Every access to shared memory is to the data part (the first 98304 bytes) of the
  shared-memory window of the issuing thread's own CTA. The mbarrier objects lie behind it. -/
  sharedFrame : ∀ e a, X.MemTouches e a → a.loc.space = .shared →
    a.loc.cta = e.issuer.1 / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304
  /-- Every byte of global memory that is read (by a load of the packed-offsets array or by the
  source read of a tensor load) is allocated and is no output byte and no final-state byte: the
  kernel reads only its inputs. -/
  globalReadFrame : ∀ e a l, X.MemTouches e a → ¬ X.Intent e a true → a.Covers l →
    l.space = .global → mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l
  /-- Every byte of global memory that some operation writes or will write (a store of the
  partial last tile, a byte of a tensor store) is an output byte of a token of the batch or a
  byte of the final state. -/
  writeFrame : ∀ w a l, X.Intent w a true → a.Covers l → l.space = .global →
    P.OutputByte l ∨ P.StateByte l
  /-- No byte of global memory has two writers: two write intents that cover one global byte are
  one access. (Different CTAs write different rows of the output and different planes of the
  final state; the tiles of one CTA write different tokens; the sixteen stores of a tile write
  different features; the slots of one store write different bytes.) -/
  globalWriteOnce : ∀ e f a b l, X.Intent e a true → X.Intent f b true → a.Covers l →
    b.Covers l → l.space = .global → e = f
  /-- Every mbarrier that an event names (an initialization, an arrival, a poll, the completion
  object of a tensor load) is one of the eleven mbarriers of the event's own CTA. -/
  mbarFrame : ∀ e m, X.UsesMbar e m → m.space = .shared ∧ m.cta = e.1 / L.block ∧
    ∃ j < 11, m.addr = P.sharedBase + 98304 + 8 * j
  -- ERR-DATA-RACE and ERR-MIXED-SIZE in shared memory.
  /-- Conflicting accesses of a byte of the bfloat16 state copy `state_acc` (the first 32768
  bytes of the window) are ordered: the conversion loop writes it, three CTA barriers later each
  compute lane reads and writes its own sixteen 16-byte rows with `ldmatrix` and `stmatrix`. -/
  accOrdered : ConflictsOrdered L X fun l => l.space = .shared ∧ l.addr < P.sharedBase + 32768
  /-- Conflicting accesses of a byte of the buffer region (from byte 32768 of the window: the
  FP32 state buffer, which shares its storage with the three input stages and the two output
  stages) are ordered: by the state mbarrier and CTA barriers in the prologue, by the load
  pipeline and the store pipeline with their proxy fences in the tile loop, and by CTA barriers,
  a proxy fence and the group wait in the epilogue. -/
  bufOrdered : ConflictsOrdered L X fun l => l.space = .shared ∧ P.sharedBase + 32768 ≤ l.addr
  -- ERR-BARRIER-MISMATCH, ERR-CTA-BARRIER and the barrier part of ERR-ALIGNED-MISMATCH.
  /-- Every barrier event of a thread is at the position and has the barrier id and thread count
  that `barSchedule` gives for its ordinal among the thread's barrier events. -/
  barShape : ∀ g k pc id cnt mode, X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ →
    (pc, id, cnt) = barSchedule P L g (((X.tr g).take k).countP Execution.isBar)
  /-- A thread arrives at most nine times on the whole-CTA barrier, and exactly nine times if it
  exits: no thread leaves while another still waits for it at a `bar.sync 0`. -/
  wholeBars : ∀ g, (X.tr g).countP kernel.isAlignedCtaBar ≤ 9 ∧
    ∀ j pc, X.get (g, j) = some ⟨pc, .exit⟩ → (X.tr g).countP kernel.isAlignedCtaBar = 9
  -- The matrix part of ERR-ALIGNED-MISMATCH, and ERR-WARP-MATRIX.
  /-- The `n`-th warp matrix event of a thread is at the `n mod 182`-th matrix instruction of
  the code and has its operation: the tile loop runs the 182 instructions in code order. -/
  matrixShape : ∀ g k pc op own recv, X.get (g, k) = some ⟨pc, .matrix op own recv⟩ →
    matrixSites[((X.tr g).take k).countP isMatrix % 182]? = some (pc, op)
  /-- A thread makes at most `matrixTotal` matrix events, and exactly that many if it exits: no
  lane leaves the tile loop while another lane of its warp is still at a matrix instruction. -/
  matrixCount : ∀ g, (X.tr g).countP isMatrix ≤ matrixTotal P L g ∧
    ∀ j pc, X.get (g, j) = some ⟨pc, .exit⟩ → (X.tr g).countP isMatrix = matrixTotal P L g
  /-- In every instance of a warp-level multiply-accumulate (all 32 lanes of a warp at their
  `n`-th matrix event, an `mma`), the instruction is the bf16 `m16n8k16` form and the registers
  the lanes contribute hold real matrices: the A and B registers are packed pairs of bfloat16
  payloads, and a C register is an FP32 payload or the zero word (`WarpMatrix.Operands`). -/
  mmaOperands : ∀ w n pc s parts, laneOf L w = 0 →
    WarpMatrix.WarpInstance X w n pc (.mma s) parts →
    s = WarpMatrix.mma16 ∧ ∃ ra rb rc a b c, WarpMatrix.Operands ra rb rc a b c ∧
      ∀ l < 32, parts l = WarpMatrix.mmaParts ra rb rc l
  -- ERR-OBJECT-LIFETIME (`TmaUnsafe`) and ERR-MBAR-UNINITIALIZED (`MbarUninit`).
  /-- The history of every mbarrier object that has a record starts with its one fault-free
  initialization. -/
  mbarInitFirst : ∀ m, X.objects m ≠ [] → ∃ c, PairTmaRing.InitFirst X m c
  /-- The initialization of an mbarrier is published to the issuer of every other record of
  its history (an arrival, a poll, the completion of a tensor load). -/
  mbarPublished : ∀ m e c, X.MbInit e m c → ∀ s ∈ X.objects m, (∀ n, s.action ≠ .init n) →
    InitPublished L X e s.id.issuer m
  /-- No record of an mbarrier history other than an initialization faults: no arrival
  underflows the pending count, none comes before its phase was observed, and the byte counts
  of the tensor loads of a phase add up to the expected count. -/
  mbarFaultFree : ∀ m r, r ∈ X.objects m → (∀ n, r.action ≠ .init n) → r.fault = none
  /-- Every event that names an mbarrier and is not an initialization of it comes, in the
  causal order of the memory model, after an initialization of that mbarrier. -/
  mbarInitBefore : ∀ e m, X.UsesMbar e m → (∀ count, ¬ X.MbInit e m count) →
    ∃ i count, X.MbInit i m count ∧ baseCausality L X i e
  -- ERR-SHARED-LIFETIME.
  /-- Every use of shared memory, by a thread or by an asynchronous stage, is of the shared
  memory of the issuing thread's own CTA. -/
  sharedOwn : ∀ e c, SharedUse L X e c → c = e.issuer.1 / L.block
  /-- Once all threads of a CTA have exited, every asynchronous use of its shared memory (each
  byte write and the completion of a tensor load, the end of the source reads of a tensor
  store) has occurred and completed before the exit of one of its threads. -/
  asyncFinished : ∀ i p c, SharedUse L X (.async i p) c → CtaExited L X c →
    SharedFinished L kernel Assumptions.all X (.async i p) c
  -- ERR-TENSOR-FILL-VALUE and ERR-TENSOR-LARGE-OOB.
  /-- Every tensor load goes through a map that fills out-of-bounds elements with zero and
  whose elements are not 64-bit floats (the nine load maps of `Pre` are bf16 or f32). -/
  loadFill : ∀ i address s, X.TensorIssue i address s →
    s.descriptor.fill = .zero ∧ s.descriptor.format ≠ .f64
  /-- A tensor load that selects an out-of-bounds element through a large-class map is a load
  of the values `v` or of the gate logits `beta`, the two arrays for which `Pre` supplies the
  device's backing. -/
  loadBounds : ∀ i address s, X.TensorIssue i address s →
    TensorHasOob s.descriptor s.origin s.rows → s.descriptor.allocationClass = .large →
    (s.descriptor.base = P.valuesBase ∧ P.allocation 0 = .large) ∨
      (s.descriptor.base = P.logitsBase ∧ P.allocation 1 = .large)
  /-- No tensor store selects an out-of-bounds element. -/
  storeBounds : ∀ i address s, X.TensorStoreIssue i address s →
    ¬ TensorHasOob s.descriptor s.origin s.rows

/-! ## Global memory: the ranges of the output and of the final state -/

/-- A token of a sequence of the batch is one of the `T_total` tokens. -/
theorem firstToken_add_lt {length : ℕ → ℕ} {n s t : ℕ} (hs : s < n) (ht : t < length s) :
    firstToken length s + t < firstToken length n := by
  have h1 : firstToken length (s + 1) = firstToken length s + length s := by
    unfold firstToken
    rw [Finset.sum_range_succ]
  have h2 : firstToken length (s + 1) ≤ firstToken length n := by
    unfold firstToken
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  omega

/-- An output byte is a byte of the array `out`. -/
theorem outputByte_range {l : Loc} (h : P.OutputByte l) :
    ∃ k < P.tokenBytes, l = ⟨.global, 0, P.outputBase + k⟩ := by
  obtain ⟨s, hs, hd, hhd, t, ht, v, k, hk, rfl⟩ := h
  have htok := firstToken_add_lt hs ht
  have hv := v.isLt
  have h1 : (firstToken P.length s + t) * P.heads + hd + 1 ≤
      firstToken P.length P.sequences * P.heads := by
    have h2 : (firstToken P.length s + t + 1) * P.heads ≤
        firstToken P.length P.sequences * P.heads := Nat.mul_le_mul_right _ (by omega)
    have h3 : (firstToken P.length s + t + 1) * P.heads =
        (firstToken P.length s + t) * P.heads + P.heads := by ring
    omega
  refine ⟨256 * ((firstToken P.length s + t) * P.heads + hd) + 2 * v.val + k, ?_, ?_⟩
  · unfold Params.tokenBytes Params.total
    omega
  · simp only [Params.outLoc, Loc.at, Loc.mk.injEq, true_and]
    omega

/-- A final-state byte is a byte of the final-state array. -/
theorem stateByte_range {l : Loc} (h : P.StateByte l) :
    ∃ k < P.stateBytes, l = ⟨.global, 0, P.finalBase + k⟩ := by
  obtain ⟨s, hs, hd, hhd, v, k, b, hb, rfl⟩ := h
  have hv := v.isLt
  have hk := k.isLt
  have h1 : s * P.heads + hd + 1 ≤ P.sequences * P.heads := by
    have h2 : (s + 1) * P.heads ≤ P.sequences * P.heads := Nat.mul_le_mul_right _ (by omega)
    have h3 : (s + 1) * P.heads = s * P.heads + P.heads := by ring
    omega
  refine ⟨65536 * (s * P.heads + hd) + 512 * v.val + 4 * k.val + b, ?_, ?_⟩
  · unfold Params.stateBytes
    omega
  · simp only [Params.stateLoc, Loc.at, Loc.mk.injEq, true_and]
    omega

/-- A byte that the kernel may write in global memory is allocated. -/
theorem written_allocated (hp : Pre P L mem0) {l : Loc} (h : P.OutputByte l ∨ P.StateByte l) :
    mem0 l ≠ none := by
  rcases h with h | h
  · obtain ⟨k, hk, rfl⟩ := outputByte_range h
    exact hp.outputAllocated k hk
  · obtain ⟨k, hk, rfl⟩ := stateByte_range h
    exact hp.finalAllocated k hk

/-- The name under which the read-only assumption looks up the packed-offsets pointer is the
name of parameter 15 in `Pre`. -/
theorem offsetsParam_eq : Assumptions.offsetsParam = param "15" := by
  unfold Assumptions.offsetsParam param
  rw [String.append_assoc]
  rfl

/-- A byte that the kernel may write in global memory is no byte of the packed-offsets array:
the output and the final state do not overlap it (`Pre.outputApartInputs`,
`Pre.finalApartInputs`). -/
theorem written_not_offset (hp : Pre P L mem0) {l : Loc}
    (h : P.OutputByte l ∨ P.StateByte l) : ¬ Assumptions.OffsetByte L l := by
  rintro ⟨-, -, base, hbase, hlo, hhi⟩
  rw [offsetsParam_eq, hp.paramOffsets] at hbase
  have hx : L.nctaid.x = P.sequences := by rw [hp.gridShape]
  have hr := hp.offsetsRange
  have hob : P.offsetBytes = 8 * (P.sequences + 1) := rfl
  have hto : base.toNat = P.offsetsBase := by
    rw [← Option.some.inj hbase, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hto] at hlo hhi
  rw [hx] at hhi
  rcases h with h | h
  · obtain ⟨k, hk, rfl⟩ := outputByte_range h
    have ha := hp.outputApartInputs.offsets
    unfold Apart at ha
    simp only at hlo hhi
    omega
  · obtain ⟨k, hk, rfl⟩ := stateByte_range h
    have ha := hp.finalApartInputs.offsets
    unfold Apart at ha
    simp only at hlo hhi
    omega

/-! ## The classes -/

/-- The CTA of a launched thread is a CTA of the grid. -/
theorem cta_lt {g : Nat} (hg : g < L.threads) : g / L.block < L.grid := by
  unfold Launch.threads at hg
  exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])

/-- The thread that issues an access is a thread of the launch. -/
theorem touches_issuer_lt (hX : Consistent L kernel Assumptions.all mem0 X) {e : AsyncCopy.Ref}
    {a : Acc} (h : X.MemTouches e a) : e.issuer.1 < L.threads := by
  rcases h with ⟨w, hi⟩ | ⟨i, bs, rfl, pc, he⟩
  · obtain ⟨ev, he, -⟩ := Frame.intent_issuer hi
    exact Frame.lt_of_get hX (g := e.issuer.1) (k := e.issuer.2) he
  · exact Frame.lt_of_get hX (g := i.1) (k := i.2) he

/-- **ERR-UNDEFINED-INSTRUCTION**: no thread of any of the three roles makes an
undefined-behaviour event. -/
theorem noUb (F : SafetyFacts P L mem0 X) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  by_cases h1 : g % L.block < 128
  · exact F.computeNoUb g k pc f h1 he
  by_cases h2 : g % L.block < 160
  · exact F.loadNoUb g k pc f (by omega) h2 he
  · exact F.storeNoUb g k pc f (by omega) he

/-- **ERR-UNALLOCATED-ACCESS**: a shared access lies in the allocated window of a launched CTA,
a global read reads an input, a global write writes the output or the final state, and every
mbarrier is one of the eleven objects of the window. -/
theorem noUnalloc (hp : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : SafetyFacts P L mem0 X) : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, hm, hl, h0⟩ | ⟨e, m, l, hu, hl, h0⟩)
  · obtain ⟨hsp, hcta, hlo, hhi⟩ := hl
    rcases F.memSpaces e a hm with hs | hg
    · obtain ⟨hc, hbase, hend⟩ := F.sharedFrame e a hm hs
      have hgrid := cta_lt (touches_issuer_lt hX hm)
      have hbyte : l.addr - P.sharedBase < sharedBytes := by
        unfold sharedBytes
        omega
      have hloc : l = ⟨.shared, e.issuer.1 / L.block, P.sharedBase + (l.addr - P.sharedBase)⟩ := by
        obtain ⟨sp, c, ad⟩ := l
        simp only at hsp hcta hlo hhi ⊢
        rw [hsp, hs, hcta, hc]
        congr 1
        omega
      rw [hloc] at h0
      exact hp.sharedAllocated _ hgrid _ hbyte h0
    · have hlg : l.space = .global := hsp.trans hg
      by_cases hw : X.Intent e a true
      · exact written_allocated hp (F.writeFrame e a l hw ⟨hsp, hcta, hlo, hhi⟩ hlg) h0
      · exact (F.globalReadFrame e a l hm hw ⟨hsp, hcta, hlo, hhi⟩ hlg).1 h0
  · obtain ⟨hms, hmc, j, hj, hma⟩ := F.mbarFrame e m hu
    obtain ⟨ev, hev, -⟩ := Frame.usesMbar_mbarOf hu
    have hgrid := cta_lt (Frame.lt_of_get hX (g := e.1) (k := e.2) hev)
    obtain ⟨hsp, hcta, hlo, hhi⟩ := hl
    simp only at hsp hcta hlo hhi
    have hbyte : l.addr - P.sharedBase < sharedBytes := by
      unfold sharedBytes
      omega
    have hloc : l = ⟨.shared, e.1 / L.block, P.sharedBase + (l.addr - P.sharedBase)⟩ := by
      obtain ⟨sp, c, ad⟩ := l
      simp only at hsp hcta hlo hhi ⊢
      rw [hsp, hms, hcta, hmc]
      congr 1
      omega
    rw [hloc] at h0
    exact hp.sharedAllocated _ hgrid _ hbyte h0

/-- **Every conflict is ordered.** A conflict in shared memory is in the bfloat16 state copy or
in the buffer region, whose protocols order it. Global memory has no conflict: a written byte
has one writer and is never read. -/
theorem conflictsOrdered (F : SafetyFacts P L mem0 X) : ConflictsOrdered L X fun _ => True := by
  intro e f a b l hc ha hb _
  have hc' := hc
  obtain ⟨hne, we, wf, hie, hif, hw, -⟩ := hc
  rcases F.memSpaces e a (.inl ⟨we, hie⟩) with hs | hg
  · have hl : l.space = .shared := ha.1.trans hs
    by_cases h : l.addr < P.sharedBase + 32768
    · exact F.accOrdered e f a b l hc' ha hb ⟨hl, h⟩
    · exact F.bufOrdered e f a b l hc' ha hb ⟨hl, by omega⟩
  · exfalso
    have hl : l.space = .global := ha.1.trans hg
    by_cases hwe : X.Intent e a true
    · by_cases hwf : X.Intent f b true
      · exact hne (F.globalWriteOnce e f a b l hwe hwf ha hb hl)
      · have hr := F.globalReadFrame f b l (.inl ⟨wf, hif⟩) hwf hb hl
        rcases F.writeFrame e a l hwe ha hl with ho | hst
        · exact hr.2.1 ho
        · exact hr.2.2 hst
    · have hwf : X.Intent f b true := by
        rcases hw with rfl | rfl
        · exact absurd hie hwe
        · exact hif
      have hr := F.globalReadFrame e a l (.inl ⟨we, hie⟩) hwe ha hl
      rcases F.writeFrame f b l hwf hb hl with ho | hst
      · exact hr.2.1 ho
      · exact hr.2.2 hst

/-- A barrier event is a `bar.sync`: the kernel has no `bar.arrive`. -/
theorem bar_sync (hX : Consistent L kernel Assumptions.all mem0 X) {g k pc id : Nat}
    {cnt : Option Nat} {mode : BarMode} (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    mode = .sync := by
  have h : X.IsBarrier (g, k) id cnt pc := hX.isBarrier_of_arrival noBarArrive ⟨mode, he⟩
  unfold Execution.IsBarrier at h
  rw [he] at h
  simpa using h

/-- **ERR-BARRIER-MISMATCH**: the lanes of a warp have one barrier schedule. -/
theorem noBarMismatch (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : SafetyFacts P L mem0 X) : ¬ BarMismatch L X :=
  Frame.noBarMismatch_of_schedule
    (fun g k => ((barSchedule P L g k).2.1, (barSchedule P L g k).2.2, .sync))
    (fun g k pc id cnt mode _ he => by
      have h := F.barShape g k pc id cnt mode he
      rw [← h, bar_sync hX he])
    (fun g h hw => by rw [barSchedule_sameWarp hw])

/-- **ERR-CTA-BARRIER**: all arrivals of a CTA at one barrier carry one thread count (barrier 0
the whole CTA, barrier 8 the 128 compute threads), and there is no `bar.arrive`. -/
theorem noCtaBarFault (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : SafetyFacts P L mem0 X) : ¬ CtaBarFault L X := by
  refine not_ctaBarFault hX fun e f id cnt cnt' pc pc' _ he hf => ?_
  have h1 := F.barShape e.1 e.2 pc id cnt .sync he
  have h2 := F.barShape f.1 f.2 pc' id cnt' .sync hf
  have c1 := barSchedule_count P L e.1 (((X.tr e.1).take e.2).countP Execution.isBar)
  have c2 := barSchedule_count P L f.1 (((X.tr f.1).take f.2).countP Execution.isBar)
  rw [← h1] at c1
  rw [← h2] at c2
  simp only [Prod.mk.injEq] at c1 c2
  rcases c1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases c2 with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
    first | rfl | omega

/-- A thread that has no event of a kind has none in its trace. -/
theorem countP_none {p : Event → Bool} {g : Nat}
    (h : ∀ k e, X.get (g, k) = some e → p e = false) : (X.tr g).countP p = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  obtain ⟨k, hk⟩ := List.getElem?_of_mem he
  simpa using h k e hk

/-- **ERR-ALIGNED-MISMATCH**. The aligned instructions of the kernel are its `bar.sync` and its
warp matrix instructions. The lanes of a warp perform them at the same positions (the barrier
schedule; the 182 matrix instructions in code order), every thread makes the same number of
whole-CTA barrier arrivals before it exits, and every lane of a warp the same number of matrix
events. The other three classes of aligned instructions do not occur. -/
theorem noAlignedMismatch (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : SafetyFacts P L mem0 X) : ¬ AlignedMismatch L kernel X := by
  have htc : ∀ g k e, X.get (g, k) = some e → isTcColl e = false := by
    intro g k ⟨pc, kd⟩ he
    cases hm : isTcColl ⟨pc, kd⟩
    · rfl
    · obtain ⟨a, rfl⟩ := isTcColl_kind hm
      exact absurd he (noTc hX _ _ _)
  have hcl : ∀ g k e, X.get (g, k) = some e → isCluster e = false := by
    intro g k ⟨pc, kd⟩ he
    cases hm : isCluster ⟨pc, kd⟩
    · rfl
    · obtain ⟨op, rfl⟩ := isCluster_kind hm
      exact (noClusterEvent hX he).elim
  have hrq : ∀ g k e, X.get (g, k) = some e → SetMaxNReg.isRequest e = false := by
    intro g k ⟨pc, kd⟩ he
    cases hm : SetMaxNReg.isRequest ⟨pc, kd⟩
    · rfl
    · obtain ⟨inc, n, inst, rfl⟩ := isRequest_kind hm
      exact (noRegisterEvent hX he).elim
  refine Frame.noAlignedMismatch_of_schedule
    (P := fun c g k => match c with
      | .bar => ((barSchedule P L g k).1, none)
      | .matrix => match matrixSites[k % 182]? with
        | some (pc, op) => (pc, some (.matrix op [] []))
        | none => (0, none)
      | _ => (0, none))
    ?_ ?_
    (fun c g => match c with
      | .bar => 9
      | .matrix => matrixTotal P L g
      | _ => 0)
    ?_ ?_ ?_
  · intro c g k pe ke he hm
    cases c with
    | tc =>
      change isTcColl ⟨pe, ke⟩ = true at hm
      rw [htc g k _ he] at hm
      cases hm
    | cluster =>
      change isCluster ⟨pe, ke⟩ = true at hm
      rw [hcl g k _ he] at hm
      cases hm
    | setMaxReg =>
      change SetMaxNReg.isRequest ⟨pe, ke⟩ = true at hm
      rw [hrq g k _ he] at hm
      cases hm
    | bar =>
      have hk : ∃ id cnt mode, ke = .bar id cnt mode := by
        cases ke <;> simp_all [AlignedClass.member, Execution.isBar]
      obtain ⟨id, cnt, mode, rfl⟩ := hk
      have h := F.barShape g k pe id cnt mode he
      simp only [AlignedClass.operands, AlignedClass.member]
      rw [← h]
    | matrix =>
      obtain ⟨op, own, recv, rfl⟩ := isMatrix_kind hm
      have h := F.matrixShape g k pe op own recv he
      simp only [AlignedClass.operands, AlignedClass.member, h]
  · intro c g h hw
    cases c with
    | bar => funext k; simp only [barSchedule_sameWarp hw]
    | _ => rfl
  · intro c g h hpar
    cases c with
    | matrix => exact matrixTotal_sameWarp hpar
    | _ => rfl
  · intro c g
    cases c with
    | tc => exact (countP_none (htc g)).le
    | cluster => exact (countP_none (hcl g)).le
    | setMaxReg => exact (countP_none (hrq g)).le
    | bar => exact (F.wholeBars g).1
    | matrix => exact (F.matrixCount g).1
  · intro c g j pc hx
    cases c with
    | tc => exact countP_none (htc g)
    | cluster => exact countP_none (hcl g)
    | setMaxReg => exact countP_none (hrq g)
    | bar => exact (F.wholeBars g).2 j pc hx
    | matrix => exact (F.matrixCount g).2 j pc hx

/-- **ERR-OBJECT-LIFETIME** (`TmaUnsafe`): no mbarrier is invalidated and there is no linear
copy (`Top/Static.lean`); every object is initialized first and its initialization is published
to its other operations, which do not fault; and no memory access touches the bytes of an
mbarrier, because the accesses of shared memory stay in the data part of the window. -/
theorem noTmaUnsafe (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : SafetyFacts P L mem0 X) : ¬ TmaUnsafe L mem0 X := by
  refine Frame.noTmaUnsafe_of_noCopy hX (noMbarInval hX) F.mbarInitFirst F.mbarPublished
    F.mbarFaultFree (fun e a w i m c l hint hi hla hlm => ?_) (noCopy hX)
  obtain ⟨hms, -, j, -, hma⟩ := F.mbarFrame i m (.of_init hi)
  obtain ⟨hsp, -, -, hhi⟩ := hla
  obtain ⟨hsp', -, hlo', -⟩ := hlm
  simp only at hsp' hlo'
  have hs : a.loc.space = .shared := by rw [← hsp, hsp', hms]
  obtain ⟨-, -, hend⟩ := F.sharedFrame e a (.inl ⟨w, hint⟩) hs
  omega

/-- **ERR-MBAR-UNINITIALIZED**: an initialization is published, through the causal order, to
every other event that names the mbarrier. -/
theorem noMbarUninit (F : SafetyFacts P L mem0 X) : ¬ MbarUninit L X := by
  rintro ⟨e, m, hu, hni, hno⟩
  obtain ⟨i, count, hi, hb⟩ := F.mbarInitBefore e m hu hni
  exact hno ⟨i, count, hi, .inl hb⟩

/-- **The assumptions declare no undefined behaviour**: no operation writes a byte of the
packed-offsets array (the `ub` clause of the read-only assumption). -/
theorem noAssumptionUnsafe (hp : Pre P L mem0) (F : SafetyFacts P L mem0 X) :
    ¬ ∃ a ∈ Assumptions.all, a.ub L mem0 X := by
  refine noAssumptionUb ?_
  rintro ⟨w, a, l, hi, hc, ho⟩
  exact written_not_offset hp (F.writeFrame w a l hi hc ho.1) ho

/-- **ERR-SHARED-LIFETIME**: every use of shared memory is of the issuer's own CTA, and the
asynchronous uses finish before the CTA has exited. -/
theorem noSharedLifetime (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : SafetyFacts P L mem0 X) : ¬ SharedLifetimeUnsafe L kernel Assumptions.all X :=
  noSharedLifetime_of_own hX F.sharedOwn F.asyncFinished

/-- **ERR-TENSOR-FILL-VALUE**: a tensor load writes copied bytes or the bytes of a bf16 or f32
zero. -/
theorem noTensorUnsafe (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : SafetyFacts P L mem0 X) : ¬ TensorUnsafe X := by
  rintro ⟨i, o, slot, content, ho, hw, hBad⟩
  obtain ⟨⟨address, hi⟩, hok, -⟩ := hX.tensor i o ho
  obtain ⟨hFill, hFormat⟩ := F.loadFill i address o.spec hi
  have he := hok.writes slot content hw
  unfold TensorCopy.source at he
  cases hLoc : o.spec.globalAddress slot with
  | none =>
    simp only [hLoc, hFill] at he
    subst content
    cases hf : o.spec.descriptor.format <;>
      simp_all [TensorCopy.Content.byte, TensorCopy.zeroValue]
  | some a =>
    rw [hLoc] at he
    obtain ⟨b, -, rfl⟩ := he
    cases hBad

/-- **ERR-TENSOR-LARGE-OOB**: only loads of `v` and `beta` reach out of bounds, and `Pre`
supplies their backing; there is no tensor prefetch. -/
theorem noTensorAllocation (hp : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (F : SafetyFacts P L mem0 X) :
    ¬ TensorAllocationUnsafe L mem0 X := by
  rintro ⟨i, ⟨address, s, hi, hBad⟩ | ⟨address, s, hi, hBad⟩ | ⟨address, s, hi, -⟩⟩
  · rcases F.loadBounds i address s hi hBad.2.1 hBad.1 with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact hBad.2.2 (hb ▸ hp.valuesBacking hc)
    · exact hBad.2.2 (hb ▸ hp.logitsBacking hc)
  · exact F.storeBounds i address s hi hBad.2.1
  · exact noTensorPrefetch hX hi

/-- The multiply-accumulate of the kernel is read by the ideal-real assumption `idealArith`,
the first of the list. -/
theorem idealMma : WarpMatrix.IdealMma Assumptions.all :=
  WarpMatrix.IdealMma.cons_idealReal _ _ (by simp [WarpMatrix.bfTypes]) _

/-- **ERR-WARP-MATRIX**: the result of every lane of every matrix instance can be computed. A
load, a store and a `movmatrix` only move bytes and have no failing case. A multiply-accumulate
is defined because its operands are real matrices in registers of the right kinds
(`mmaOperands`), which the ideal-real rule multiplies. -/
theorem noMatrixUnsafe (hp : Pre P L mem0) (F : SafetyFacts P L mem0 X) :
    ¬ MatrixUnsafe L Assumptions.all X := by
  rintro ⟨g, i, pc, op, own, recv, n, -, -, parts, f, hI, herr⟩
  have hb : L.block % 32 = 0 := by rw [hp.block]
  cases op with
  | move m => rw [WarpMatrix.matrixRecv_move] at herr; cases herr
  | transpose => rw [WarpMatrix.matrixRecv_transpose] at herr; cases herr
  | mma s =>
    have hI' : WarpMatrix.WarpInstance X (g - laneOf L g) n pc (.mma s) parts := hI
    obtain ⟨rfl, ra, rb, rc, a, b, c, hops, hparts⟩ :=
      F.mmaOperands _ n pc s parts (WarpMatrix.laneOf_base hb g) hI'
    exact WarpMatrix.mma_ne_error idealMma (hI'.congr hparts) hops hI'
      (Nat.mod_lt _ (by decide)) f herr

/-! ## Safety -/

/-- **No consistent execution with the premises is unsafe**: the 28 classes of `Unsafe` in
order, fourteen from the premises and fourteen from the decoded program. -/
theorem not_unsafe (hp : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : SafetyFacts P L mem0 X) : ¬ Unsafe L kernel Assumptions.all mem0 X := by
  have hord := conflictsOrdered F
  intro hu
  rcases hu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  · exact noUb F h
  · exact noUnalloc hp hX F h
  · exact hord.no_race h
  · exact hord.no_mixed h
  · exact noBarMismatch hX F h
  · exact noTmaUnsafe hX F h
  · exact noTmemSource hX h
  · exact noAssumptionUnsafe hp F h
  · exact noAlignedMismatch hX F h
  · exact noSharedLifetime hX F h
  · exact noClcUnsafe hX h
  · exact noTensorUnsafe hX F h
  · exact noTensorStoreUnsafe hX h
  · exact noTensorAllocation hp hX F h
  · exact noTmemResource hX h
  · exact noTmemRelease hX h
  · exact noPollShapeUnsafe hX h
  · exact noTmemAccess hX h
  · exact noTcCommit hX h
  · exact noTmemWrites hX h
  · exact noTmemInstruction hX h
  · exact noTmemReads hX h
  · exact noRegister hX h
  · exact noCtaBarFault hX F h
  · exact noClusterFault hX h
  · exact noWarpDivergent h
  · exact noMatrixUnsafe hp F h
  · exact noMbarUninit F h

/-- **Safety from the premises**: if every consistent execution of a launch that satisfies
`Pre` has the facts of `SafetyFacts`, the kernel is safe on that launch. -/
theorem safe_of_facts (hp : Pre P L mem0)
    (hF : ∀ X, Consistent L kernel Assumptions.all mem0 X → SafetyFacts P L mem0 X) :
    SafeGoal kernel Assumptions.all L mem0 :=
  ⟨kernel_groupUniform, fun X hX => not_unsafe hp hX (hF X hX)⟩

end PTX.Kernels.FlashKdaFwd.Proof.Top
