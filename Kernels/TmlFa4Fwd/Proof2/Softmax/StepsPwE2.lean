-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPwEBias

@[expose] public section

/-! # The first round's closing poll

The successor runs the row sum and chooses the bias rounds, plain rounds or final stores. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (i32 sub32 addi scmpi add32 shrs shru sel scmp andi)
open PTX.Kernels.TmlFa4Fwd.Proof2.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- `r431` reads only the scan and the used-K length. -/
theorem r431_eq_of {v v' : V} (h1 : v'.sc = v.sc) (h2 : v'.ukw = v.ukw) :
    r431 p L g v' = r431 p L g v := by
  simp only [r431, r169, r299, r166, r168, r165, r1808, h1, h2]

theorem pwMid_head (v : V) (M : Value) (x : ℝ) :
    (630, Value.pred (scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1)) ∈
      pwMid p L g v M x := by
  unfold pwMid; exact List.mem_cons_self

/-- **The first round's closing poll**: a failed poll returns to the poll; a successful one runs
the row sum and enters the bias rounds, the plain rounds or the final stores. -/
theorem stepAt_pwend1 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.pwend .first, v, 0, []⟩ := by
  have hparams := params hp
  have e431 : ∀ (a b : BitVec 64) (c : Bool) (d e : ℝ),
      r431 p L g { v with ppar := a, spar := b, mf := c, mr := d, rs := e } = r431 p L g v :=
    fun _ _ _ _ _ => r431_eq_of rfl rfl
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_wait (dok := afterFirst p L g ⟨.pwend .first, v, 0, []⟩)
    (dfail := ⟨.pwend .first, v, 0, []⟩) Flow.code_4874 (by fact_free)
    (fun _ _ _ _ => by next_simp [succ, afterRound]) (fun _ _ _ _ => by next_simp [succ]) rfl rfl
    ?_ ?_
  · dsimp only [afterFirst]
    by_cases h1 : scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1 = true
    · unfold D.ite; rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      unfold plainEntry
      rw [e431]
      by_cases h2 : scmpi .lt .s (r431 p L g v) 1 = true
      · unfold D.ite; rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
        refine ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
        refine Seg.comp_ex (pw1_run hp v) ?_
        rcases foldF_cases p L g v with hF | ⟨r, hF⟩
        · rw [hF, finE_bot, EReal.toReal_bot, erealValue_bot]
          generalize rs1 p L g v = x
          exact Seg.comp_ex (pwA hp v x ninf32)
            (Seg.pred_ex (pwMid_head v _ x) h1 (pwFinN hp v x h1 h2))
        · rw [hF, finE_coe, EReal.toReal_coe, erealValue_coe]
          generalize rs1 p L g v = x
          exact Seg.comp_ex (pwA hp v x (.float .f32 r))
            (Seg.pred_ex (pwMid_head v _ x) h1 (pwFinR hp v x r h1 h2))
      · unfold D.ite; rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
        refine ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
        refine Seg.comp_ex (pw1_run hp v) ?_
        rcases foldF_cases p L g v with hF | ⟨r, hF⟩
        · rw [hF, finE_bot, EReal.toReal_bot, erealValue_bot]
          generalize rs1 p L g v = x
          exact Seg.comp_ex (pwA hp v x ninf32)
            (Seg.pred_ex (pwMid_head v _ x) h1 (pwPlN hp v x h1 h2))
        · rw [hF, finE_coe, EReal.toReal_coe, erealValue_coe]
          generalize rs1 p L g v = x
          exact Seg.comp_ex (pwA hp v x (.float .f32 r))
            (Seg.pred_ex (pwMid_head v _ x) h1 (pwPlR hp v x r h1 h2))
    · unfold D.ite; rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      refine ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
      refine Seg.comp_ex (pw1_run hp v) ?_
      rcases foldF_cases p L g v with hF | ⟨r, hF⟩
      · rw [hF, finE_bot, EReal.toReal_bot, erealValue_bot]
        generalize rs1 p L g v = x
        exact Seg.comp_ex (pwA hp v x ninf32)
          (Seg.pred_ex (pwMid_head v _ x) (Bool.eq_false_iff.mpr h1) (pwBiN hp v x h1))
      · rw [hF, finE_coe, EReal.toReal_coe, erealValue_coe]
        generalize rs1 p L g v = x
        exact Seg.comp_ex (pwA hp v x (.float .f32 r))
          (Seg.pred_ex (pwMid_head v _ x) (Bool.eq_false_iff.mpr h1) (pwBiR hp v x r h1))
  · refine ⟨fun _ => ?_, rfl, rfl, fun h => h⟩
    have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (uni := true)
      (pick := false) (F := (9753, .pred false) :: factsD p L g ⟨.pwend .first, v, 0, []⟩)
      Flow.code_4875 (List.mem_cons_self) (fun t _ a ha => by
        simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      (Gen.segFree _ (by kernel_rfl))
    have hj := seg_jmp (K := kernel) (A := Assumptions.all) (L := L) (g := g)
      (F := (9753, .pred false) :: factsD p L g ⟨.pwend .first, v, 0, []⟩) Flow.code_4876
      (fun t _ a ha => by
        simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      (Gen.segFree _ (by kernel_rfl))
    exact ⟨2, (hb.comp hj).weaken_end fun R hR => hR.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
