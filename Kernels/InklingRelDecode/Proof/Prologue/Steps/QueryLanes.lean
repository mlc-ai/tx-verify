-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Gen.StepPrologue
import Kernels.InklingRelDecode.Gen.StepPrologue02
import Kernels.InklingRelDecode.Gen.StepPrologue03
import Kernels.InklingRelDecode.Gen.StepPrologue04
import Lemmas.Flow.SegChain

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d

theorem seg_col : Seg kernel Assumptions.all L g 1 321 (F 321) 322 (F 322) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff]
    show Value.bits _ _ = _
    norm_bits [u64])

/-- Sixteen lane addresses of one row group. -/
theorem seg_lanes0 : Seg kernel Assumptions.all L g 16 322 (F 322) 338 (F 338) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, qLane, qOff]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd]
    show Value.bits _ _ = _
    norm_bits [u64])

theorem seg_lanes1 : Seg kernel Assumptions.all L g 16 338 (F 338) 354 (F 354) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, qLane, qOff]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd]
    show Value.bits _ _ = _
    norm_bits [u64])

theorem seg_lanes2 : Seg kernel Assumptions.all L g 16 354 (F 354) 370 (F 370) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, qLane, qOff]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd]
    show Value.bits _ _ = _
    norm_bits [u64])

theorem seg_lanes3 : Seg kernel Assumptions.all L g 16 370 (F 370) 386 (F 386) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, qLane, qOff]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd]
    show Value.bits _ _ = _
    norm_bits [u64])

/-- The query row pointers become the 64 lane addresses, up to the two moves of the loads. -/
theorem query_lanes_386 : SegU kernel Assumptions.all L g 320 (F 320) 386 (F 386) :=
  (cross (by decide +kernel : crossCheck 320 320 321)).comp
    (SegU.of_seg (seg_col.comp (((seg_lanes0.comp seg_lanes1).comp seg_lanes2).comp seg_lanes3)))

/-- The default of the bias words, a 16-bit zero (`mov.b16 %rs18, 0`). -/
theorem seg_dflt : Seg kernel Assumptions.all L g 1 386 (F 386) 387 (F 387) := by
  intro t ht
  seg_fp ht using (simp (disch := decide +kernel) only [valueOf_plain, registerValue]; rfl)

/-- The default and the two moves after it: the facts of pc 388. -/
theorem query_dflt : SegU kernel Assumptions.all L g 386 (F 386) 388 (F 388) :=
  (SegU.of_seg seg_dflt).comp (cross (by decide +kernel : crossCheck 387 387 388))

/-- The query row pointers become the 64 lane addresses of the loads. -/
theorem query_lanes : SegU kernel Assumptions.all L g 320 (F 320) 388 (F 388) :=
  query_lanes_386.comp query_dflt

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
