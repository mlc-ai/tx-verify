-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderCountsBase

@[expose] public section

/-! # The loader's elections

Every lane of the loader makes the elections of its sites: before each copy of a use (`elC`),
and, on the leader CTA, before the use's arrival (`elA`) and the tail's arrival (`elTail`). Before
the event of a state there are `electOf` of them (none in the prologue): `E` per item
(`itemElects`), the uses' before the state's use (`preElects`, the trip's `2 r0 + 3` per trip done)
and those of the state's use before it (`elects_step`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- One on the leader CTA of the pair. -/
def r0 (L : Launch) (g : Nat) : Nat := if rank L g = 0 then 1 else 0

/-- The elections of a use: the arrival's on the leader CTA and one per copy. -/
def useElects (L : Launch) (g : Nat) (u : UseK) : Nat := r0 L g + u.copies

/-- The elections of an item: its first four uses and `n - 1` trips of a K and a V use. -/
def itemElects (L : Launch) (g : Nat) : Nat :=
  4 * r0 L g + 7 + (n L - 1) * (2 * r0 L g + 3)

/-- The elections of an item before use `u` at trip `t`. -/
def preElects (L : Launch) (g : Nat) (u : UseK) (t : Nat) : Nat :=
  match u with
  | .k0 => 0
  | .q0 => r0 L g + 2
  | .q1 => 2 * r0 L g + 4
  | .v0 => 3 * r0 L g + 6
  | .k => 4 * r0 L g + 7 + t * (2 * r0 L g + 3)
  | .v => 4 * r0 L g + 7 + t * (2 * r0 L g + 3) + (r0 L g + 2)

/-- The loader's elections before the event of state `d`. -/
def electOf (L : Launch) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .head => d.i * itemElects L g
  | .wait u | .elA u => d.i * itemElects L g + preElects L g u d.t
  | .arrive u => d.i * itemElects L g + preElects L g u d.t + 1
  | .elC u j => d.i * itemElects L g + preElects L g u d.t + r0 L g + j.val
  | .copy u j => d.i * itemElects L g + preElects L g u d.t + r0 L g + j.val + 1
  | .drain _ | .drainQ | .elTail => T L g * itemElects L g
  | .arriveTail => T L g * itemElects L g + 1
  | .exit => T L g * itemElects L g + r0 L g

/-- An election. -/
def isElectE (e : Event) : Bool :=
  match e.kind with
  | .elect .. => true
  | _ => false

/-- The election sites. -/
def Site.isElect : Site → Bool
  | .elA _ | .elC _ _ | .elTail => true
  | _ => false

/-- The elections of an item's end. -/
theorem electOf_itemEnd (d : D) (hit : d.i < T L g) :
    electOf L g (afterUse.itemEndOf L g d) = (d.i + 1) * itemElects L g := by
  unfold afterUse.itemEndOf
  split_ifs with h
  · simp [electOf]
  · simp only [electOf]
    rw [show T L g = d.i + 1 by omega]

/-- The elections of a use's end. -/
theorem electOf_afterUse (d : D) (u : UseK) (hit : d.i < T L g)
    (htr : (u = .k ∨ u = .v) → d.t + 2 ≤ n L) :
    electOf L g (afterUse L g d u) =
      d.i * itemElects L g + preElects L g u d.t + useElects L g u := by
  cases u <;> simp only [afterUse]
  · simp [electOf, preElects, useElects, UseK.copies]
  · simp [electOf, preElects, useElects, UseK.copies]; ring
  · simp [electOf, preElects, useElects, UseK.copies]; ring
  · split_ifs with hn
    · simp [electOf, preElects, useElects, UseK.copies]; ring
    · rw [electOf_itemEnd _ (by exact hit)]
      have hn1 : n L - 1 = 0 := by omega
      simp [preElects, useElects, UseK.copies, itemElects, hn1]; ring
  · simp [electOf, preElects, useElects, UseK.copies]; ring
  · have ht := htr (.inr rfl)
    split_ifs with hn
    · simp [electOf, preElects, useElects, UseK.copies]; ring
    · rw [electOf_itemEnd _ (by exact hit)]
      have hn1 : n L - 1 = d.t + 1 := by omega
      simp [preElects, useElects, UseK.copies, itemElects, hn1]; ring

/-- The elections after a copy or its skipped election. -/
theorem electOf_afterCopy (d : D) (u : UseK) (j : Fin 2) (hit : d.i < T L g)
    (htr : (u = .k ∨ u = .v) → d.t + 2 ≤ n L) (hj : j.val < u.copies) :
    electOf L g (afterCopy L g d u j) =
      d.i * itemElects L g + preElects L g u d.t + r0 L g + j.val + 1 := by
  unfold afterCopy
  split_ifs with h
  · have : j.val = 0 := by cases u <;> simp [UseK.copies] at h hj <;> omega
    simp [electOf, this]
  · rw [electOf_afterUse d u hit htr, useElects]
    cases u <;> simp [UseK.copies] at h hj ⊢ <;> omega

/-- **A loader step moves its elections by the site's.** -/
theorem electOf_next {d d' : D} {e : Event} (hi : Inv L g d)
    (hn : next L g d e = some (some d')) :
    electOf L g d' = electOf L g d + if d.site.isElect then 1 else 0 := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  have hit : site.inItem = true → i < T L g := hi.item
  have htrip : site.inTrip = true → tt + 2 ≤ n L := hi.trip
  have hlead : site.leadOnly = true → rank L g = 0 := hi.lead
  have hone := hi.one
  simp only at hit htrip hlead hone
  cases site <;> simp only [next] at hn <;>
    simp only [Site.isElect, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  case setMaxReg =>
    simp only [Option.some.injEq] at hn
    subst hn
    split_ifs with h
    · simp [electOf]
    · simp [electOf, show T L g = 0 by omega]
  case exit => cases hn
  case elC u j =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      have hj := hone u j (.inl rfl)
      split_ifs
      · simp [electOf]
      · rw [electOf_afterCopy _ u j (hit rfl) (fun h => htrip (by rcases h with rfl | rfl <;> rfl))
          hj]
        simp [electOf]
    · cases hn
  case copy u j =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      have hj := hone u j (.inr rfl)
      rw [electOf_afterCopy _ u j (hit rfl) (fun h => htrip (by rcases h with rfl | rfl <;> rfl))
        hj]
      simp [electOf]
    · cases hn
  case elA u =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      have hr := hlead rfl
      split_ifs <;> simp [electOf, r0, hr]
    · cases hn
  case arrive u =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      have hr := hlead rfl
      simp [electOf, r0, hr]
    · cases hn
  case elTail =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      have hr := hlead rfl
      split_ifs <;> simp [electOf, r0, hr]
    · cases hn
  case arriveTail =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      have hr := hlead rfl
      simp [electOf, r0, hr]
    · cases hn
  case wait u =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs <;> simp_all [electOf, r0]
    · cases hn
  case drainQ =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs <;> simp_all [electOf, r0]
    · cases hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp [electOf, preElects]

/-- **The elections after an event fired at a loader state.** -/
theorem elects_step {d d' : D} {pre : List Event} {e : Event}
    (hJ : pre.countP isElectE = electOf L g d) (hi : Inv L g d) (hev : Ev L g d e)
    (hn : next L g d e = some (some d')) :
    (pre ++ [e]).countP isElectE = electOf L g d' := by
  rw [List.countP_append, hJ, electOf_next hi hn, List.countP_singleton]
  obtain ⟨epc, k⟩ := e
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  cases site <;> (try cases ‹UseK›) <;> simp only [Ev, PollIs, ArriveIs] at hev <;>
    repeat' (first | (obtain rfl := hev) | (obtain ⟨rfl, -⟩ := hev) | (obtain ⟨_, hev⟩ := hev))
  all_goals simp [isElectE, Site.isElect]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
