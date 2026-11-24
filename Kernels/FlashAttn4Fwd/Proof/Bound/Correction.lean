-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bound.Ranks

@[expose] public section

/-! # The correction warps' rank

An item of a correction warp is its first generation (three events), `n - 1` loop trips and the
final part. A trip is 62 counted events, 31 per stage: the named barrier, the load of `α`, the
vote, eight rescale chunks (a load, its implicit wait, a store), the wait for the stores, the
O-free arrival and a credit; a trip has a block of `64` (`64 (n - t)` for trip `t`). The final
part is a credit and 88 events per stage: the named barrier, the load of `l`, a credit, the two
polls, eight chunks (a load, its wait, two four-element stores), the fence, the O-free and the
staged arrivals (`corrPos`, the events left in the item, below `178` after the loop). A failed
poll stays at the poll. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Bound
open PTX PTX.Proof Correction

noncomputable section

/-- The counted events left in the item from a correction site in trip `t` of `n`. -/
def corrPos (n t : Nat) : Correction.Site → Nat
  | .sync st .first => 64 * (n + 1) + 181 - 2 * st.val
  | .credit a =>
    if a.val = 0 then 64 * (n + 1) + 180
    else if a.val < 3 then 64 * (n - t) + 178 + 31 * (2 - a.val) + 2
    else if a.val = 3 then 177
    else 88 * (5 - a.val) + 86
  | .sync st .loop => 64 * (n - t) + 178 + 31 * (1 - st.val) + 31
  | .ldA st => 64 * (n - t) + 178 + 31 * (1 - st.val) + 30
  | .vote st => 64 * (n - t) + 178 + 31 * (1 - st.val) + 29
  | .rld st j => 64 * (n - t) + 178 + 31 * (1 - st.val) + 28 - 3 * j.val
  | .rldW st j => 64 * (n - t) + 178 + 31 * (1 - st.val) + 27 - 3 * j.val
  | .rst st j => 64 * (n - t) + 178 + 31 * (1 - st.val) + 26 - 3 * j.val
  | .rwait st => 64 * (n - t) + 178 + 31 * (1 - st.val) + 4
  | .oFree st false => 64 * (n - t) + 178 + 31 * (1 - st.val) + 3
  | .sync st .last => 88 * (1 - st.val) + 88
  | .ldL st => 88 * (1 - st.val) + 87
  | .oWait st => 88 * (1 - st.val) + 85
  | .fWait st => 88 * (1 - st.val) + 84
  | .fld st j => 88 * (1 - st.val) + 83 - 10 * j.val
  | .fldW st j => 88 * (1 - st.val) + 82 - 10 * j.val
  | .fst st j h el => 88 * (1 - st.val) + 81 - 10 * j.val - 4 * h.val - el.val
  | .fence st => 88 * (1 - st.val) + 3
  | .oFree st true => 88 * (1 - st.val) + 2
  | .staged st => 88 * (1 - st.val) + 1
  | .setMaxReg | .bar0 | .free _ | .tailWait | .barEnd | .exit => 0

/-- The correction warps' rank: the entry, the item's events and the tail. -/
def corrRank (L : Launch) (g : Nat) (d : Correction.D) : Nat :=
  let Q := perItem L
  let B := Correction.items L g
  match d.site with
  | .setMaxReg => Q * B + Q + 63
  | .bar0 => Q * B + Q + 62
  | .free st => Q * B + Q + 61 - st.val
  | .tailWait => 2
  | .barEnd => 1
  | .exit => 0
  | s => Q * (B - d.i) + 64 + corrPos (Correction.trips L) d.t s

theorem corrRank_entry (L : Launch) (g : Nat) {d : Correction.D} (h : d.site = .setMaxReg) :
    corrRank L g d ≤ cap L := by
  simp only [corrRank, h]
  exact (Nat.add_assoc _ _ _).le.trans (entry_le (StaticSchedule.count_le _ _ _) (by omega))

/-- One block freed by the next item. -/
theorem corr_item {L : Launch} {g i : Nat} (h : i + 1 < Correction.items L g) :
    perItem L * (Correction.items L g - i) =
      perItem L * (Correction.items L g - (i + 1)) + perItem L :=
  RankItems.mul_sub_succ _ h

/-- Closes a correction step (as `rk_close`, with the values of `Fin` literals). -/
macro "corr_close" : tactic => `(tactic| (
  (try rw [counts_wait (by assumption)])
  (try split_ifs) <;>
    simp only [corrRank, corrPos, Nat.sub_zero, Bool.false_eq_true, ↓reduceIte, Fin.val_mk,
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;>
    (try split_ifs) <;>
    (try have := corr_item (by assumption)) <;>
    (have _hQ := perItem_ge ‹Launch›) <;>
    first | omega | exact absurd trivial ‹¬True› | exact ‹False›.elim))

set_option maxRecDepth 100000 in
/-- **Every correction step lowers the rank by its count.** -/
theorem corrRank_step {L : Launch} {g : Nat} {d d' : Correction.D} {e : Event}
    (h : Correction.next L g d e = some (some d')) :
    corrRank L g d' + (if e.counts then 1 else 0) ≤ corrRank L g d := by
  have hc := counts_le e
  have hQ : perItem L = 256 * (Correction.trips L + 1) := rfl
  obtain ⟨s, i, t, aw, a, o⟩ := d
  rcases s with _ | _ | st | ⟨st, gn⟩ | c | s1 | s1 | ⟨s1, j⟩ | ⟨s1, j⟩ | ⟨s1, j⟩ | s1
    | ⟨st, fn⟩ | s1 | s1 | s1 | ⟨s1, j⟩ | ⟨s1, j⟩ | ⟨s1, j, hh, el⟩ | s1 | st | _ | _ | _
  all_goals (try fin_cases st) <;> (try fin_cases c) <;> (try cases gn) <;> (try cases fn)
  all_goals try have := s1.isLt
  all_goals try have := j.isLt
  all_goals try have := hh.isLt
  all_goals try have := el.isLt
  all_goals simp only [Correction.next] at h
  all_goals (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals (try simp only [Correction.nextItem, Correction.afterTrip])
  all_goals corr_close

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Bound
