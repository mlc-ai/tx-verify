-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Export

@[expose] public section

/-!
# The safety facts of the kernel, from the contracts of the layers below

`Safety.lean` derives every class of undefined behaviour and race from the structure
`SafetyFacts` (25 fields about one consistent execution). This file says where each field comes
from, so that the layers below have one precise target each:

* ten fields follow from the contract of the protocol layer, `Protocol.Facts` (per-thread facts
  about barriers and mbarriers) and `Protocol.UnionFacts` (per-thread facts about the accesses
  of the buffer region), by the theorems of `Proof/Protocol/Export.lean`: the four mbarrier
  history fields, `barShape`, `wholeBars`, `sharedOwn`, `asyncFinished`, `accOrdered`, `bufOrdered`
  (the last four also use the field `sharedFrame`);
* `mbarFrame` follows from the same contract (`mbarFrame` below: an event names only one of
  the eleven mbarriers of its block);
* the other fourteen are the structure `DirectFacts` below: footprints, the schedule of the
  matrix instructions, the operands of tensor copies (the reference layer, `Proof/Ref`), and
  the absence of undefined-behaviour events together with the operands of the warp-level
  multiply-accumulate (the reference layer for the control side, the value layer,
  `Proof/Values`, for the data side).

`safetyFacts` puts the two together.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Facts UnionFacts Owners ctaTiles)

noncomputable section

/-- **The fields of `SafetyFacts` that the protocol contract does not give**: each is stated
exactly as in `SafetyFacts` (see the comments there). -/
structure DirectFacts (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  /-- No compute thread (index below 128 in its CTA) makes an undefined-behaviour event. -/
  computeNoUb : ∀ g k pc f, g % L.block < 128 → X.get (g, k) ≠ some ⟨pc, .ub f⟩
  /-- No thread of the load warp (index 128 to 159) makes an undefined-behaviour event. -/
  loadNoUb : ∀ g k pc f, 128 ≤ g % L.block → g % L.block < 160 →
    X.get (g, k) ≠ some ⟨pc, .ub f⟩
  /-- No thread of the store warp (index 160 and above) makes an undefined-behaviour event. -/
  storeNoUb : ∀ g k pc f, 160 ≤ g % L.block → X.get (g, k) ≠ some ⟨pc, .ub f⟩
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

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The offset of each of the eleven mbarriers is `98304 + 8 j` for a `j < 11`. -/
theorem bar_off (b : Protocol.Bar) : ∃ j < 11, b.off = 98304 + 8 * j := by
  cases b with
  | loadFull s => exact ⟨s.val, by omega, rfl⟩
  | loadEmpty s => exact ⟨3 + s.val, by omega, by simp only [Protocol.Bar.off]; omega⟩
  | storeFull o => exact ⟨6 + o.val, by omega, by simp only [Protocol.Bar.off]; omega⟩
  | storeEmpty o => exact ⟨8 + o.val, by omega, by simp only [Protocol.Bar.off]; omega⟩
  | state => exact ⟨10, by omega, rfl⟩

/-- **`SafetyFacts.mbarFrame`**, from the protocol contract: an event names only mbarriers of
its own block, and those are the eleven objects behind the data part of the window. -/
theorem mbarFrame (hP : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : Facts P L X) : ∀ e m, X.UsesMbar e m → m.space = .shared ∧ m.cta = e.1 / L.block ∧
      ∃ j < 11, m.addr = P.sharedBase + 98304 + 8 * j := by
  rintro ⟨g, k⟩ m hu
  obtain ⟨ev, he, hm⟩ := usesMbar_mbarOf hu
  obtain ⟨b, rfl⟩ := Protocol.mbar_bar F.init hX he hm
  obtain ⟨j, hj, hoff⟩ := bar_off b
  refine ⟨rfl, rfl, j, hj, ?_⟩
  simp only [Protocol.Bar.loc, hoff, hP.sharedBase]
  omega

/-- **The safety facts of one consistent execution**, from the protocol contract, the
classification of the buffer-region accesses, and the direct facts. -/
theorem safetyFacts (hP : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : Facts P L X) {O : Owners} (U : UnionFacts L X (ctaTiles P) O)
    (D : DirectFacts P L mem0 X) : SafetyFacts P L mem0 X where
  computeNoUb := D.computeNoUb
  loadNoUb := D.loadNoUb
  storeNoUb := D.storeNoUb
  memSpaces := D.memSpaces
  sharedFrame := D.sharedFrame
  globalReadFrame := D.globalReadFrame
  writeFrame := D.writeFrame
  globalWriteOnce := D.globalWriteOnce
  mbarFrame := mbarFrame hP hX F
  accOrdered := F.accOrdered hP hX D.sharedFrame
  bufOrdered := F.bufOrdered hP hX U D.sharedFrame
  barShape := F.barShape hX
  wholeBars := F.wholeBars hX
  matrixShape := D.matrixShape
  matrixCount := D.matrixCount
  mmaOperands := D.mmaOperands
  mbarInitFirst := F.mbarInitFirst hP hX
  mbarPublished := F.mbarPublished hP hX
  mbarFaultFree := F.mbarFaultFree hP hX
  mbarInitBefore := F.mbarInitBefore hP hX
  sharedOwn := F.sharedOwn hX D.sharedFrame
  asyncFinished := F.asyncFinished hP hX D.sharedFrame
  loadFill := D.loadFill
  loadBounds := D.loadBounds
  storeBounds := D.storeBounds

end

end PTX.Kernels.FlashKdaFwd.Proof.Top
