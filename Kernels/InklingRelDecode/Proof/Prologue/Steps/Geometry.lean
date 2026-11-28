-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain
import Lemmas.Flow.SignedBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d
local macro "row_close" ht:ident : tactic => `(tactic| (
  simp (disch := decide +kernel) only [valueOf_plain,registerValue,u16,b32,voteReg,
    Nat.reduceEqDiff,↓reduceIte]
  all_goals generalize eqt : _ % Launch.block _ = tid at $ht ⊢
  all_goals clear eqt; revert tid; decide +kernel))

theorem seg_lane_row (bound : g%L.block<256) :
    Seg kernel Assumptions.all L g 3 61 (F 61) 64 (F 64) := by
  intro t ht
  seg_fp ht using row_close bound

theorem seg_lane_col (bound : g%L.block<256) :
    Seg kernel Assumptions.all L g 2 64 (F 64) 66 (F 66) := by
  intro t ht
  seg_fp ht using row_close bound

theorem seg_groups (bound : g%L.block<256) :
    Seg kernel Assumptions.all L g 5 66 (F 66) 71 (F 71) := by
  intro t ht
  seg_fp ht using row_close bound

theorem seg_token_hi (bound : g%L.block<256) :
    Seg kernel Assumptions.all L g 4 71 (F 71) 75 (F 75) := by
  intro t ht
  seg_fp ht using row_close bound

theorem seg_token_lo (bound : g%L.block<256) :
    Seg kernel Assumptions.all L g 4 75 (F 75) 79 (F 79) := by
  intro t ht
  seg_fp ht using row_close bound

theorem row_segment (bound : g%L.block<256) :
    SegU kernel Assumptions.all L g 61 (F 61) 79 (F 79) :=
  (SegU.of_seg (seg_lane_row bound)).comp ((SegU.of_seg (seg_lane_col bound)).comp
    (SegU.of_seg (((seg_groups bound).comp (seg_token_hi bound)).comp (seg_token_lo bound))))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
