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

theorem limit_bound (h : e.Ok) : e.limit < 2^31 := by
  rw [h.limitEq]; split <;> omega

theorem next_block_bound (h : e.Ok) (hi : d.i ≤ e.limit) :
    e.split + d.i*e.splits + e.splits < 2^31 := by
  have hb := h.keyRange
  rw [Nat.add_mul,Nat.one_mul] at hb
  have := Nat.mul_le_mul_right e.splits hi
  omega

theorem loop_test (h : e.Ok) (hi : d.i ≤ e.limit) :
    SegU kernel Assumptions.all L g 1049 (F 1049)
      1050 ((91,.pred (decide (d.i=e.limit)))::F 1049) := by
  have small := limit_bound h
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using seg_close [valueOf,scalarValue,eq_comm]

theorem next_gate (h : e.Ok) (hi : d.i ≤ e.limit) :
    SegU kernel Assumptions.all L g 1051 (F 1049) 1057 (F 1057) := by
  have hb := next_block_bound h hi
  have h1 := h.bias
  have h2 := h.blockWord
  have h3 := limit_bound h
  have hn' : (e.split + d.i*e.splits+e.splits) % 2^32 =
      e.split + d.i*e.splits+e.splits := Nat.mod_eq_of_lt (by omega)
  have s1051 : Seg kernel Assumptions.all L g 1 1051 (F 1049) 1052 (F 1052) := by
    intro t ht
    seg_fp ht using
      simp only [valueOf,scalarValue,u32]
      all_goals seg_close []
  have s1052 : Seg kernel Assumptions.all L g 1 1052 (F 1052) 1053 (F 1053) := by
    intro t ht
    seg_fp ht using
      simp only [valueOf,scalarValue,Value.pred.injEq,Nat.reduceEqDiff,↓reduceIte,hn']
      all_goals exact cmp_ge_s32 _ _ hb h1
  have s1053 : Seg kernel Assumptions.all L g 1 1053 (F 1053) 1054 (F 1054) := by
    intro t ht
    seg_fp ht using
      simp only [valueOf,scalarValue,u32]
      all_goals seg_close []
  have s1054 : Seg kernel Assumptions.all L g 1 1054 (F 1054) 1055 (F 1055) := by
    intro t ht
    seg_fp ht using
      simp only [valueOf,scalarValue,Value.pred.injEq,Nat.reduceEqDiff,↓reduceIte]
      have hs : sx e.blocks < 2^64 := by
        unfold sx
        have := Nat.mod_lt e.blocks (by decide : 0 < 2^32)
        omega
      all_goals rw [Nat.mod_eq_of_lt hs]; exact cmp_lt_s64 _ _ (by omega) h2
  have s1055 : Seg kernel Assumptions.all L g 2 1055 (F 1055) 1057 (F 1057) := by
    intro t ht
    seg_fp ht using
      simp [valueOf,scalarValue,nextEnabled,Bool.and_assoc]
  exact SegU.of_seg ((((s1051.comp s1052).comp s1053).comp s1054).comp s1055)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
