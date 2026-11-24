-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainSumRun
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Lemmas.Flow.SegJump
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The plain round's closing poll

The branch after the computed sum continues the loop or enters the final stores. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 40000000
set_option seg_sym.decideHeartbeats 40000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 xor32 addi scmpi) in
/-- **The loop tail into the next plain round.** -/
theorem pwW_loop (hp : Pre p L m) (v : V) (x r : ℝ)
    (hc : scmpi .ne .b (addi v.pl 1) 0 = true) : ∃ n, Seg kernel Assumptions.all L g n 7599
      ((7257, .float .f32 x) :: (7256, .float .f32 r) :: (1230, negS p) ::
        (441, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 441) ::
        (1062, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 1062) ::
        (1069, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 1069) ::
        (1215, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 1215) ::
        (2390, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 2390) ::
        (2535, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 2535) ::
        (5127, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 5127) ::
        (6495, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 6495) ::
        (6497, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 6497) ::
        (7133, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7133) ::
        (7253, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7253) ::
        (7254, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7254) ::
        (7258, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7258) ::
        (7500, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7500) ::
        (7501, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7501) ::
        (7502, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7502) ::
        (7503, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7503) ::
        (7506, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7506) ::
        (8692, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 8692) :: []) 6676
      (factsD p L g (D.mk' (.ws .plain) { v with
        mf := true, mr := r, rs := x, spar := xor32 v.spar (i32 1),
        ppar := xor32 v.ppar (i32 1), pl := addi v.pl 1 })) := by
  have hparams := params hp
  seg_sym using (soft_seg)

open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 xor32 addi scmpi) in
/-- **The loop exit to the final stores.** -/
theorem pwW_exit (hp : Pre p L m) (v : V) (x r : ℝ)
    (hc : ¬ scmpi .ne .b (addi v.pl 1) 0 = true) : ∃ n, Seg kernel Assumptions.all L g n 7599
      ((7257, .float .f32 x) :: (7256, .float .f32 r) :: (1230, negS p) ::
        (441, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 441) ::
        (1062, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 1062) ::
        (1069, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 1069) ::
        (1215, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 1215) ::
        (2390, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 2390) ::
        (2535, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 2535) ::
        (5127, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 5127) ::
        (6495, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 6495) ::
        (6497, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 6497) ::
        (7133, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7133) ::
        (7253, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7253) ::
        (7254, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7254) ::
        (7258, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7258) ::
        (7500, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7500) ::
        (7501, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7501) ::
        (7502, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7502) ::
        (7503, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7503) ::
        (7506, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 7506) ::
        (8692, valueOf p L g ⟨.pwend .plain, v, 0, []⟩ 8692) :: []) 7614
      (factsD p L g (D.mk' (.fin 0) { v with
        mf := true, mr := r, rs := x, spar := xor32 v.spar (i32 1),
        ppar := xor32 v.ppar (i32 1), pl := addi v.pl 1 })) := by
  have hparams := params hp
  seg_sym using (soft_seg)

theorem maxP_eq (p : Params) (v : V) : maxP p v = .float .f32 (maxR p v) := by
  unfold maxP maxR
  split
  · split <;> rfl
  · rfl

open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 xor32 addi scmpi) in
/-- **The closing poll of a plain round.** -/
theorem stepAt_pwend_plain (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.pwend .plain, v, 0, []⟩ := by
  have hparams := params hp
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_wait (dok := afterRound p L g ⟨.pwend .plain, v, 0, []⟩ .plain)
    (dfail := ⟨.pwend .plain, v, 0, []⟩) Flow.code_7463 (by fact_free)
    (fun _ _ _ _ => by next_simp [succ, afterRound]) (fun _ _ _ _ => by next_simp [succ]) rfl rfl
    ?_ ?_
  · dsimp only [afterRound, afterPlain]
    have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (uni := true)
        (pick := true) (F := (9886, .pred true) :: factsD p L g ⟨.pwend .plain, v, 0, []⟩)
        Flow.code_7464 (List.mem_cons_self) (fun t _ a ha => by
          simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
            List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        (Gen.segFree _ (by kernel_rfl))
    by_cases hc : scmpi .ne .b (addi v.pl 1) 0 = true
    · unfold D.ite; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      refine ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
      refine Seg.comp_ex ⟨1, hb⟩ (Seg.comp_ex (pw_rs hp v) ?_)
      rw [show pwH p L g v = (7256, .float .f32 (maxR p v)) :: (1230, negS p) ::
        factsFrom ctlPE (valueOf p L g ⟨.pwend .plain, v, 0, []⟩) by rw [pwH, maxP_eq]]
      exact pwW_loop hp v _ _ hc
    · unfold D.ite; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      refine ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
      refine Seg.comp_ex ⟨1, hb⟩ (Seg.comp_ex (pw_rs hp v) ?_)
      rw [show pwH p L g v = (7256, .float .f32 (maxR p v)) :: (1230, negS p) ::
        factsFrom ctlPE (valueOf p L g ⟨.pwend .plain, v, 0, []⟩) by rw [pwH, maxP_eq]]
      exact pwW_exit hp v _ _ hc
  · refine ⟨fun _ => ?_, rfl, rfl, fun h => h⟩
    have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (uni := true)
        (pick := false) (F := (9886, .pred false) :: factsD p L g ⟨.pwend .plain, v, 0, []⟩)
        Flow.code_7464 (List.mem_cons_self) (fun t _ a ha => by
          simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
            List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        (Gen.segFree _ (by kernel_rfl))
    have hj := seg_jmp (K := kernel) (A := Assumptions.all) (L := L) (g := g)
      (F := (9886, .pred false) :: factsD p L g ⟨.pwend .plain, v, 0, []⟩) Flow.code_7465
      (fun t _ a ha => by
        simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      (Gen.segFree _ (by kernel_rfl))
    exact ⟨2, (hb.comp hj).weaken_end fun R hR => hR.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
