-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedCorrSite
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpQuiet

@[expose] public section

/-! # The correction warps' votes against their site table

A correction warp's warp collectives are the prologue's four shuffles (at `0`, `2`, `4`, `24`)
and its votes. An item of `n` trips has `V = 2 (n - 1)` votes: vote `r` of item `i` is the vote
of stage `r % 2` in trip `r / 2`, in slot `r / 2 + 1`, band `C (r % 2)`, at `+4` (`voteS`); past
the cluster's `T` items the schedule is in the tail (`+4000`). The schedule `corrWS` is the
shuffles' times, then `voteS`. Consecutive collectives are more than one apart (`corrWS_gap`),
and all its times are even (`corrWS_even`), as are the correction's site times (`corr_even`).

A correction state before its vote `r = votePos 0 + votePos 1` of its item is at the vote's time
(a vote site) or earlier: in the same band before `+4`, in an earlier band or slot, before the next
item when the item's votes are done, before every slot (the role's entry), or in the tail before
the schedule's tail (`SiteOkW`, `siteW_ok`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time CorrTc

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace CorrW

/-- The time of a correction warp's vote `m` in a cluster of `T` items of `n` trips. -/
def voteS (n T m : Nat) : Nat :=
  if m < nV n * T then slotTime n (m / nV n) (m % nV n / 2 + 1) (bandC (m % nV n % 2) + 4)
  else tailTime n T (4000 + 2 * (m - nV n * T))

/-- The times of the prologue's shuffles. -/
def shflT : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | _ => 24

/-- **The warp collectives' schedule of a correction warp**: the prologue's shuffles, then its
votes. -/
def corrWS (n T k : Nat) : Nat := if k < 4 then shflT k else voteS n T (k - 4)

theorem voteS_at {n T i r : Nat} (hi : i < T) (hr : r < nV n) :
    voteS n T (nV n * i + r) = slotTime n i (r / 2 + 1) (bandC (r % 2) + 4) := by
  have hlt : nV n * i + r < nV n * T := by
    have := Nat.mul_le_mul_left (nV n) (show i + 1 ≤ T by omega)
    rw [Nat.mul_succ] at this
    omega
  obtain ⟨h1, h2⟩ := dec_eq (W := nV n) (i := i) hr
  simp only [voteS, hlt, ↓reduceIte, h1, h2]

theorem voteS_tail {n T : Nat} : voteS n T (nV n * T) = tailTime n T 4000 := by
  simp [voteS]

theorem voteS_ge (n T m : Nat) : base ≤ voteS n T m := by
  unfold voteS tailTime
  split <;> exact Progress.Time.base_le

theorem slot_item_le {n a b o : Nat} (h : a ≤ b) : slotTime n a 0 0 ≤ slotTime n b 0 o := by
  have := Nat.mul_le_mul_right (n + 1) h
  unfold slotTime gslot
  simp only [span, base]
  omega

/-- When the item's votes are done, the next vote is no earlier than the next item. -/
theorem voteS_next {n T i : Nat} (hi : i < T) :
    slotTime n (i + 1) 0 0 ≤ voteS n T (nV n * i + nV n) := by
  by_cases h : nV n * i + nV n < nV n * T
  · have hT : i + 1 < T := by
      by_contra hc
      have := Nat.mul_le_mul_left (nV n) (show T ≤ i + 1 by omega)
      rw [Nat.mul_succ] at this
      omega
    have hV : 0 < nV n := by
      rcases Nat.eq_zero_or_pos (nV n) with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    rw [show nV n * i + nV n = nV n * (i + 1) + 0 by ring, voteS_at hT hV]
    unfold slotTime gslot
    simp only [span, base, bandC]
    omega
  · unfold voteS tailTime
    rw [ite_eq_right h]
    exact slot_item_le (by omega)

theorem slot_succ_lt {n i i' s s' o o' : Nat} (h : slotTime n i s (o + 1) < slotTime n i' s' o') :
    slotTime n i s o + 1 < slotTime n i' s' o' := by
  unfold slotTime at *; omega

theorem voteS_gap (n T m : Nat) : voteS n T m + 1 < voteS n T (m + 1) := by
  by_cases h0 : m < nV n * T
  · have hV : 0 < nV n := by
      rcases Nat.eq_zero_or_pos (nV n) with hz | hz
      · rw [hz] at h0; simp at h0
      · exact hz
    obtain ⟨i, r, hr, rfl⟩ : ∃ i r, r < nV n ∧ m = nV n * i + r :=
      ⟨m / nV n, m % nV n, Nat.mod_lt _ hV, (Nat.div_add_mod m (nV n)).symm⟩
    have hi : i < T := by
      by_contra hc
      have := Nat.mul_le_mul_left (nV n) (show T ≤ i by omega)
      omega
    rw [voteS_at hi hr]
    rcases Nat.lt_or_ge (r + 1) (nV n) with h1 | h1
    · rw [show nV n * i + r + 1 = nV n * i + (r + 1) by omega, voteS_at hi h1]
      unfold slotTime gslot
      simp only [bandC, span, base]
      omega
    · rw [show r = nV n - 1 by omega, show nV n * i + (nV n - 1) + 1 = nV n * i + nV n by omega]
      refine lt_of_lt_of_le (slot_succ_lt (Progress.Time.lt_of_item (s' := 0) (o' := 0) ?_
        (Nat.lt_succ_self i) ?_)) (voteS_next hi)
      · simp only [nV] at *; omega
      · simp only [bandC, span]; omega
  · unfold voteS tailTime
    rw [ite_eq_right h0, ite_eq_right (by omega)]
    unfold slotTime
    omega

theorem corrWS_gap (n T k : Nat) : corrWS n T k + 1 < corrWS n T (k + 1) := by
  unfold corrWS
  rcases Nat.lt_or_ge k 3 with h | h
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide
  · rcases Nat.eq_or_lt_of_le h with rfl | h'
    · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
      show shflT 3 + 1 < voteS n T 0
      have := voteS_ge n T 0
      simp only [shflT, base] at *
      omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        show k + 1 - 4 = k - 4 + 1 by omega]
      exact voteS_gap n T (k - 4)

theorem voteS_even (n T m : Nat) : voteS n T m % 2 = 0 := by
  unfold voteS tailTime
  split <;> exact slot_even (by (try simp only [bandC]); omega)

theorem corrWS_even (n T k : Nat) : corrWS n T k % 2 = 0 := by
  unfold corrWS
  split
  · unfold shflT; split <;> rfl
  · exact voteS_even n T _

/-- Every correction time is even. -/
theorem corr_even (n T : Nat) (d : Correction.D) : correction n T d % 2 = 0 := by
  obtain ⟨s, i, t, aw, a, o⟩ := d
  cases s <;>
    simp only [correction, slotTime, tailTime, regT, bar0T, freeT, base, bandC, span] <;>
    (try split) <;> omega

/-! ### The sites against the votes -/

/-- The votes of the item before a correction state. -/
def rOfW (L : Launch) (d : Correction.D) : Nat :=
  Correction.votePos L 0 d + Correction.votePos L 1 d

/-- **A correction site against the votes.** -/
def SiteOkW (L : Launch) (n T : Nat) (d : Correction.D) : Prop :=
  rOfW L d ≤ nV n ∧
  (corrKind d.site = .warp → d.i < T ∧ rOfW L d < nV n ∧
    correction n T d = slotTime n d.i (rOfW L d / 2 + 1) (bandC (rOfW L d % 2) + 4)) ∧
  (corrKind d.site ≠ .warp →
    (d.i < T ∧ rOfW L d < nV n ∧
      correction n T d < slotTime n d.i (rOfW L d / 2 + 1) (bandC (rOfW L d % 2) + 4)) ∨
    (d.i < T ∧ rOfW L d = nV n ∧ correction n T d < slotTime n (d.i + 1) 0 0) ∨
    correction n T d < base ∨
    (d.i = T ∧ rOfW L d = 0 ∧ correction n T d < tailTime n T 4000))

/-- Close a site's comparison with the votes. -/
macro "vote_close" : tactic => `(tactic|
  (simp only [SiteOkW, rOfW, Correction.votePos, correction, corrKind, nV, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.val_zero, Fin.val_one, reduceCtorEq, ne_eq,
      not_false_eq_true, not_true_eq_false, false_implies, true_implies, true_and, and_true,
      Nat.add_zero, Nat.zero_add, ↓reduceIte] <;>
    simp only [slotTime, gslot, tailTime, Nat.add_mul, Nat.one_mul, bandC, span, base, regT,
      bar0T, freeT] <;>
    omega))

set_option maxHeartbeats 1000000 in
theorem siteW_ok {g : Nat} {d : Correction.D} (hn : 0 < Work.n L) (hi : Correction.Inv L g d) :
    SiteOkW L (Work.n L) (Work.T L g) d := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  have hitem := hi.item
  have htrip := hi.trip
  have htail := hi.tail
  have hstart := hi.start
  simp only at hitem htrip htail hstart
  rw [Corr.trips_eq] at htrip
  rw [Corr.items_eq] at htail hitem
  have hN : Correction.trips L = Work.n L := Corr.trips_eq
  cases site with
  | setMaxReg | bar0 | free st =>
    obtain rfl := hstart (by simp)
    vote_close
  | tailWait | barEnd | exit =>
    obtain rfl := htail (by simp [Correction.Site.inItem]) (by simp) (by simp) (by simp)
    vote_close
  | sync st gen =>
    have hiT := hitem rfl
    fin_cases st <;> cases gen <;> (try have ht := htrip rfl) <;> vote_close
  | credit c =>
    have hiT := hitem rfl
    rcases Corr.fin6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (try have ht := htrip rfl) <;> vote_close
  | ldA st | vote st | rwait st | ldL st | oWait st | fWait st | fence st | staged st =>
    have hiT := hitem rfl
    fin_cases st <;> (try have ht := htrip rfl) <;> vote_close
  | rld st j | rldW st j | rst st j | fld st j | fldW st j =>
    have hiT := hitem rfl
    have hj := j.isLt
    fin_cases st <;> (try have ht := htrip rfl) <;> vote_close
  | oFree st fin =>
    have hiT := hitem rfl
    fin_cases st <;> cases fin <;> (try have ht := htrip rfl) <;> vote_close
  | fst st j h el =>
    have hiT := hitem rfl
    have hj := j.isLt
    have hh := h.isLt
    have he := el.isLt
    fin_cases st <;> vote_close

end CorrW
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
