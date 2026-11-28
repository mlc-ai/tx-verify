-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.PreIndex
import Kernels.InklingRelDecode.Gen.StepSoftmax01

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Carry}
local notation "F" => facts e L g (D.mk Softmax.Site.bar0 0 v)

theorem cmp_pos_signed (n : Nat) (bound : n < 2^32) :
    PTX.compare .gt .s 32 (truncBits 32 (BitVec.ofNat 64 n))
      (truncBits 32 (BitVec.ofInt 64 0)) = decide (0 < n ∧ n < 2^31) := by
  change PTX.compare .gt .s 32 _ (truncBits 32 (BitVec.ofNat 64 0)) = _
  simp only [PTX.compare,toSigned32_ofNat,Nat.mod_eq_of_lt bound]
  norm_num
  split
  · rename_i h
    simp [h]
  · rename_i h
    simp [h]
    omega


theorem pre_gate (ok : e.Ok) : SegU kernel Assumptions.all L g 611 (F 611) 615 (F 615) := by
  have range := ok.keyRange
  have bias := ok.bias
  have first : Seg kernel Assumptions.all L g 1 611 (F 611) 612 (F 612) := by
    intro t ht
    seg_fp ht using norm_cmp [valueOf,scalarValue]
  have valid : Seg kernel Assumptions.all L g 1 612 (F 612) 613 (F 613) := by
    intro t ht
    seg_fp ht using rfl
  have blocks : Seg kernel Assumptions.all L g 1 613 (F 613) 614 (F 614) := by
    intro t ht
    seg_fp ht using exact congrArg Value.pred (cmp_pos_signed e.blocks ok.blockWord)
  have mask : Seg kernel Assumptions.all L g 1 614 (F 614) 615 (F 615) := by
    intro t ht
    seg_fp ht using simp [valueOf,scalarValue,preEnabled,Bool.and_comm,Bool.and_left_comm,
      Bool.and_assoc]
  exact SegU.of_seg (((first.comp valid).comp blocks).comp mask)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
