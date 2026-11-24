-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The counts at the pipeline's polls -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- The counts across a poll outside the PV blocks. -/
theorem step_wt (hp : Pre p L m) (k : Fin 10) : StepRef p L g (.wt k) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  fin_cases k <;> simp only [Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | skip
  all_goals split at hn <;> rename_i hok <;> simp only [Option.some.injEq] at hn <;> subst hn
  all_goals pre_r
  all_goals first
    | (exact refc_quiet hQ (by simp_all [quietK]) (qmove_refl (ord_le _)) id
        (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) rfl)
    | (subst hok; loc_tac
       exact refc_poll hQ (by decide) (by decide) (by cnt_tac) (by cnt_tac) (by cnt_tac))

set_option maxHeartbeats 4000000 in
/-- The counts across the poll inside a PV block. -/
theorem step_mw (hp : Pre p L m) (b : Fin 4) (ld : Bool) : StepRef p L g (.mw b ld) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  fin_cases b <;> cases ld <;> simp only [Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | skip
  all_goals split at hn <;> rename_i hok <;> simp only [Option.some.injEq] at hn <;> subst hn
  all_goals pre_r
  all_goals first
    | (exact refc_quiet hQ (by simp_all [quietK]) (qmove_refl (ord_le _)) id
        (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) rfl)
    | (subst hok; rw [mw_loc hp]; simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
         ↓reduceIte] at *
       exact refc_poll hQ (by decide) (by decide) (by cnt_tac) (by cnt_tac) (by cnt_tac))


end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
