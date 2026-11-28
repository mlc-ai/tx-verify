-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Bias
import Kernels.InklingRelDecode.Gen.StepSoftmax15
import Kernels.InklingRelDecode.Proof.Lib.MmaBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

theorem next_bias_tail (hi : i < 2^31) :
    SegU kernel Assumptions.all L g 1251 (facts e L g ⟨.nxt 63,i,v⟩ 1250)
      1257 (facts e L g ⟨.waitS,i,v⟩ 1257) := by
  apply SegU.of_seg (n := 6)
  intro t ht
  seg_fp ht using
    simp only [valueOf,scalarValue,u32]
    all_goals seg_close [Lib.bfe_u32,Nat.and_one_is_mod]

theorem step_last_nxt : (code e L g).StepAtU ⟨.nxt 63,i,v⟩ := by
  apply step_of_inv
  intro hi
  have lt := hi.loop (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (fun _ => nofun)
  change i < e.limit at lt
  have bound : e.limit = _ := hi.entry.limitEq
  have small : i < 2^31 := by split at bound <;> omega
  apply Bias.read_step (e := e) (L := L) (g := g) (i := i) (v := v) .nxt 63 .waitS
  · intro h
    refine ⟨h.entry,h.thread,h.bound,?_,fun _ => nofun,fun _ => nofun,nofun,fun _ _ _ _ => lt⟩
    rintro (a|a) <;> cases a
  · intro _; rfl
  · exact next_bias_tail small

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
