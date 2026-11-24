-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The counts at the pipeline's elections and commits -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- The counts across the election before a QK block. -/
theorem step_eq (_hp : Pre p L m) (b : Fin 4) : StepRef p L g (.eq b) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals fin_cases b
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | skip
  all_goals simp only [Option.some.injEq] at hn
  all_goals subst hn
  all_goals pre_r
  all_goals split
  all_goals exact refc_elect' hQ.1 hE (by decide) (by cnt_tac) (by cnt_tac) (by cnt_tac)
                  (by cnt_tac) (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide)

set_option maxHeartbeats 4000000 in
/-- The counts across the election before a PV block. -/
theorem step_ep (_hp : Pre p L m) (b : Fin 4) : StepRef p L g (.ep b) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals fin_cases b
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | skip
  all_goals simp only [Option.some.injEq] at hn
  all_goals subst hn
  all_goals pre_r
  all_goals split
  all_goals exact refc_elect' hQ.1 hE (by decide) (by cnt_tac) (by cnt_tac) (by cnt_tac)
                  (by cnt_tac) (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide)

set_option maxHeartbeats 4000000 in
/-- The counts across the election before a commit. -/
theorem step_ce (_hp : Pre p L m) (c : Fin 12) : StepRef p L g (.ce c) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  fin_cases c <;> simp only [Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | skip
  all_goals simp only [Option.some.injEq] at hn
  all_goals subst hn
  all_goals pre_r
  all_goals split <;> rename_i hl
  all_goals first
    | exact refc_win hQ.1 hE hl.symm (by decide) (by cnt_tac) (by cnt_tac) (by cnt_tac)
        (by cnt_tac)
    | exact ceNext_ref (refc_lose hQ.1 hE (Ne.symm hl) (by decide) (by cnt_tac) (by cnt_tac)
        (by cnt_tac) (by cnt_tac) (by decide) (by cnt_tac) (by cnt_tac))

set_option maxHeartbeats 4000000 in
/-- The counts across a commit. -/
theorem step_cm (hp : Pre p L m) (c : Fin 12) : StepRef p L g (.cm c) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  fin_cases c <;> simp only [Ev] at hev <;> shape_destruct hev
  all_goals first | exact absurd rfl (hub _) | skip
  all_goals simp only [succ] at hn
  all_goals simp only [Option.some.injEq] at hn
  all_goals subst hn
  all_goals pre_r
  all_goals rename_i hk hloc _
  all_goals subst hk
  all_goals rw [cm_loc hp _ (fun hc => hQ.1.regs (by revert hc; decide))] at hloc
  all_goals
    exact refc_commit_next hQ (by decide) (by decide) hloc (by cnt_tac) (by cnt_tac) (by cnt_tac)


end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
