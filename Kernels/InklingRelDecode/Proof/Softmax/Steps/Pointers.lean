-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Compare
import Kernels.InklingRelDecode.Gen.StepSoftmax11
import Kernels.InklingRelDecode.Gen.StepSoftmax12
import Kernels.InklingRelDecode.Gen.StepSoftmax13
import Lemmas.Flow.BranchU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {d : D}
local notation "F" => facts e L g d

theorem ptr_mad (n a : Nat) :
    Value.bits (2*32) (intBits (2*32)
      (intOf .s 32 (truncBits 32 (BitVec.ofNat 64 (n % 2^32))) *
        intOf .s 32 (truncBits 32 (BitVec.ofInt 64 2)) +
        intOf .s 64 (truncBits 64 (BitVec.ofNat 64 a)))) = u64 (sx n*2+a+2*0) := by
  change Value.bits 64 _ = Value.bits 64 _
  rw [ofInt_two,madwide_s32,sx_two]
  simp [sx]

private theorem pointers_1057 :
    SegU kernel Assumptions.all L g 1057 (F 1057) 1058 (F 1058) := by
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using
    simp only [valueOf,scalarValue,u32]
    all_goals seg_close [Nat.add_mul]

private theorem pointers_1058 :
    SegU kernel Assumptions.all L g 1058 (F 1058) 1059 (F 1059) := by
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using exact ptr_mad _ _

theorem ptr_add (n off : Nat) :
    Value.bits 64 (truncBits 64 (truncBits 64 (BitVec.ofNat 64 ((n+2*0) % 2^64)) +
      truncBits 64 (BitVec.ofInt 64 (off : Int)))) = u64 (n+off) := by
  change Value.bits 64 _ = Value.bits 64 _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [truncBits,BitVec.toNat_add,Nat.add_mod]

local macro "offsets" n:num : tactic => `(tactic| (
  apply SegU.of_seg (n := $n)
  intro t ht
  seg_fp ht using exact ptr_add _ _))

private theorem pointers_1059 : SegU kernel Assumptions.all L g 1059 (F 1059)
    1066 (F 1066) := by offsets 7

private theorem pointers_1066 : SegU kernel Assumptions.all L g 1066 (F 1066)
    1073 (F 1073) := by offsets 7

private theorem pointers_1073 : SegU kernel Assumptions.all L g 1073 (F 1073)
    1080 (F 1080) := by offsets 7

private theorem pointers_1080 : SegU kernel Assumptions.all L g 1080 (F 1080)
    1087 (F 1087) := by offsets 7

private theorem pointers_1087 : SegU kernel Assumptions.all L g 1087 (F 1087)
    1094 (F 1094) := by offsets 7

private theorem pointers_1094 : SegU kernel Assumptions.all L g 1094 (F 1094)
    1101 (F 1101) := by offsets 7

private theorem pointers_1101 : SegU kernel Assumptions.all L g 1101 (F 1101)
    1108 (F 1108) := by offsets 7

private theorem pointers_1108 : SegU kernel Assumptions.all L g 1108 (F 1108)
    1115 (F 1115) := by offsets 7

private theorem pointers_1115 : SegU kernel Assumptions.all L g 1115 (F 1115)
    1122 (F 1122) := by offsets 7

private theorem pointers_1122 : SegU kernel Assumptions.all L g 1122 (F 1122) 1124 (F 1124) := by
  seg_ctl Lib.rulesFrame, Lib.hooks_ok

theorem next_pointers : SegU kernel Assumptions.all L g 1057 (F 1057) 1124 (F 1124) := by
  apply pointers_1057.comp
  apply pointers_1058.comp
  apply pointers_1059.comp
  apply pointers_1066.comp
  apply pointers_1073.comp
  apply pointers_1080.comp
  apply pointers_1087.comp
  apply pointers_1094.comp
  apply pointers_1101.comp
  apply pointers_1108.comp
  apply pointers_1115.comp
  exact pointers_1122

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
