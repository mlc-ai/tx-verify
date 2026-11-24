-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bound.Ranks

@[expose] public section

/-! # The prologue's rank

The prologue's sites in the order every thread meets them (`ord`, below `60`): the three
shuffles, warp 12's election and initialization, the first fence, then warp 0's elections, each
followed by its group of initializations, with the rank broadcast after the second group, and
the second fence and the cluster barrier. Every prologue step moves to a later site
(`next_ord`); the step at the cluster wait leaves the prologue (`next_role`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof

noncomputable section

/-- The position of a prologue site along every run. -/
def ord : Site → Nat
  | .shfl0 => 0 | .shfl1 => 1 | .shfl2 => 2 | .elect12 => 3 | .init320 => 4 | .fence0 => 5
  | .elect e => 6 + e.val + (groupStart e).val + (if 2 ≤ e.val then 1 else 0)
  | .init j => 7 + (groupOf j).val + j.val + (if 2 ≤ (groupOf j).val then 1 else 0)
  | .shfl3 => 12 | .fence1 => 57 | .clArrive => 58 | .clWait => 59

theorem ord_lt (s : Site) : ord s < 60 := by
  cases s with
  | elect e => revert e; decide
  | init j => revert j; decide
  | _ => decide

theorem ord_groupStart : ∀ e : Fin 14, ord (.elect e) < ord (.init (groupStart e)) := by
  decide

theorem ord_afterGroup : ∀ e : Fin 14, ord (.elect e) < ord (afterGroup e) := by
  decide

theorem ord_initNext : ∀ j : Fin 36, ord (.init j) < ord (initNext j) := by
  decide

/-- **Every prologue step moves to a later site.** -/
theorem next_ord {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some (.inl d'))) : ord d.site < ord d'.site := by
  obtain ⟨s⟩ := d
  cases s <;> simp only [next] at h
  all_goals (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq,
    Sum.inl.injEq] at h <;> subst h
  all_goals first
    | (simp only [ord]; omega)
    | decide
    | exact ord_groupStart _
    | exact ord_afterGroup _
    | exact ord_initNext _

/-- The prologue leaves to a role only at the cluster wait. -/
theorem next_role {L : Launch} {g : Nat} {d : D} {e : Event} {k : RoleKind}
    (h : next L g d e = some (some (.inr k))) : d.site = .clWait := by
  obtain ⟨s⟩ := d
  cases s <;> simp only [next] at h
  all_goals (repeat' split at h) <;> simp_all

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
