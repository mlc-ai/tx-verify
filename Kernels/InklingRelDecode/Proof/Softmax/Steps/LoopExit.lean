-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Header
import Kernels.InklingRelDecode.Gen.StepEpilogue
import Lemmas.Flow.BranchU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {d : D}
local notation "F" => facts e L g d

private theorem block_lt_one (n : Nat) (hn : n < 2^32) :
    PTX.compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 n))
      (truncBits 32 (BitVec.ofInt 64 1)) = decide (n = 0 ∨ 2^31 ≤ n) := by
  change PTX.compare .lt .s 32 _ (truncBits 32 (BitVec.ofNat 64 1)) = _
  simp only [PTX.compare,toSigned32_ofNat,Nat.mod_eq_of_lt hn]
  norm_num
  split <;> by_cases hz : n = 0 <;> simp (disch := omega) [hz] <;> omega

theorem loop_exit (h : e.Ok) :
    SegU kernel Assumptions.all L g 2560 (F 1049) 2565 (F 2565) := by
  have one : SegU kernel Assumptions.all L g 2560 (F 1049) 2561 (F 2561) := by
    apply SegU.of_seg (n := 1)
    intro t ht
    seg_fp ht using exact congrArg Value.pred (block_lt_one e.blocks h.blockWord)
  apply one.comp
  seg_ctl Lib.rulesFrame, Lib.hooks_ok using rfl

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
