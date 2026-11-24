-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedCorrBlk
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarCorr

@[expose] public section

/-! # The correction sites against the blocks of their `tcgen05` events

A correction state's next warp-collective `tcgen05` event is event `oOf d` of block `rOf d` of
its item (`Thread/FactsSchedCorrBlk.lean`): in a rescale, the block of the trip's last vote
(the votes before the state less one) at the rescale's offset (`25 - tcLack`); elsewhere, the
block after the votes before the state, at the final part's offset `finTc` (zero outside a final
part). The site table (`Time.correction`) puts a state at a `tcgen05` site at that event's time,
and every other state before it, or, when the final part is complete (`oOf d = 32`), before the
first event of the next item (`site_ok`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace CorrTc

/-- One at the sites of a rescale (its events still to come), zero elsewhere. -/
def isRs (d : Correction.D) : Nat :=
  match d.site with
  | .rld _ _ | .rldW _ _ | .rst _ _ | .rwait _ => 1
  | _ => 0

/-- The offset of a rescale site's event in its rescale (zero elsewhere). -/
def rsO (d : Correction.D) : Nat :=
  match d.site with
  | .rld _ j => 3 * j.val
  | .rldW _ j => 3 * j.val + 1
  | .rst _ j => 3 * j.val + 2
  | .rwait _ => 24
  | _ => 0

/-- The block of a correction state's next warp-collective `tcgen05` event in its item. -/
def rOf (L : Launch) (d : Correction.D) : Nat :=
  Correction.votePos L 0 d + Correction.votePos L 1 d - isRs d

/-- The offset of a correction state's next warp-collective `tcgen05` event in its block. -/
def oOf (d : Correction.D) : Nat := Correction.finTc d + rsO d

/-- The events of a rescale still to come and its offset. -/
theorem tcLack_eq (d : Correction.D) :
    Correction.tcLack d + rsO d = 25 * isRs d ∧ (isRs d = 0 → Correction.tcLack d = 0) ∧
      (isRs d = 1 → Correction.finTc d = 0) ∧ isRs d ≤ 1 ∧ rsO d < 25 := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  cases site <;> simp [Correction.tcLack, rsO, isRs, Correction.finTc] <;> omega

/-- A rescale follows a vote of the item. -/
theorem rs_votes {d : Correction.D} (h : isRs d = 1) :
    1 ≤ Correction.votePos L 0 d + Correction.votePos L 1 d := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  cases site with
  | rld st j | rldW st j | rst st j | rwait st =>
    fin_cases st <;> simp [Correction.votePos] <;> omega
  | _ => simp [isRs] at h

/-- **A correction site against its block**: at a `tcgen05` site at the time of its event, in
a rescale (a block before the final part, the rescale's events still to come) or in the final
part; at another site before the event, or before the next item. -/
def SiteOk (L : Launch) (n T : Nat) (d : Correction.D) : Prop :=
  rOf L d ≤ nV n ∧
  (tcKind (corrKind d.site) = true →
    ((rOf L d < nV n ∧ oOf d < 25 ∧ isRs d = 1) ∨
      (rOf L d = nV n ∧ oOf d < 32)) ∧
    correction n T d = tmB n d.i (rOf L d) (oOf d)) ∧
  (tcKind (corrKind d.site) = false →
    (oOf d < 32 ∧ correction n T d < tmB n d.i (rOf L d) (oOf d)) ∨
      (oOf d = 32 ∧ rOf L d = nV n ∧ correction n T d < tmB n (d.i + 1) 0 0))

/-- The sites of warp-collective `tcgen05` events. -/
def isTcSite : Correction.Site → Bool
  | .rld _ _ | .rldW _ _ | .rst _ _ | .rwait _ | .fld _ _ | .fldW _ _ => true
  | _ => false

theorem tcKind_corr (s : Correction.Site) : tcKind (corrKind s) = isTcSite s := by
  cases s <;> rfl

/-- Close a site's comparison: unfold the tables to the slots' arithmetic. -/
macro "site_close" : tactic => `(tactic|
  (simp only [SiteOk, rOf, oOf, Correction.votePos, isRs, rsO, Correction.finTc,
      correction, tcKind_corr, isTcSite, nV, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.val_zero, Fin.val_one, lt_self_iff_false, Nat.lt_irrefl,
      reduceCtorEq, beq_self_eq_true, Bool.or_false, Bool.false_or, Bool.or_true,
      Bool.true_or, beq_iff_eq, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      true_implies, true_and, and_true, Nat.add_zero, Nat.zero_add, Nat.sub_zero,
      ↓reduceIte] <;>
    simp only [tmB, nV] <;>
    (try simp (disch := omega) only [ite_eq_left, ite_eq_right]) <;>
    (try split) <;>
    (try simp (disch := omega) only [ite_eq_left, ite_eq_right]) <;>
    simp only [slotTime, gslot, tailTime, Nat.add_mul, Nat.one_mul, bandC, span, base, regT,
      bar0T, freeT] <;>
    omega))

set_option maxHeartbeats 1000000 in
theorem site_ok {g : Nat} {d : Correction.D} (hn : 0 < Work.n L) (hi : Correction.Inv L g d) :
    SiteOk L (Work.n L) (Work.T L g) d := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  have htrip := hi.trip
  have htail := hi.tail
  have hstart := hi.start
  simp only at htrip htail hstart
  rw [Corr.trips_eq] at htrip
  rw [Corr.items_eq] at htail
  have hN : Correction.trips L = Work.n L := Corr.trips_eq
  cases site with
  | setMaxReg | bar0 | free st =>
    obtain rfl := hstart (by simp)
    site_close
  | tailWait | barEnd | exit =>
    obtain rfl := htail (by simp [Correction.Site.inItem]) (by simp) (by simp) (by simp)
    site_close
  | sync st gen =>
    fin_cases st <;> cases gen <;> (try have ht := htrip rfl) <;> site_close
  | credit c =>
    rcases Corr.fin6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (try have ht := htrip rfl) <;> site_close
  | ldA st | vote st | rwait st | ldL st | oWait st | fWait st | fence st | staged st =>
    fin_cases st <;> (try have ht := htrip rfl) <;> site_close
  | rld st j | rldW st j | rst st j | fld st j | fldW st j =>
    have hj := j.isLt
    fin_cases st <;> (try have ht := htrip rfl) <;> site_close
  | oFree st fin =>
    fin_cases st <;> cases fin <;> (try have ht := htrip rfl) <;> site_close
  | fst st j h el =>
    have hj := j.isLt
    have hh := h.isLt
    have he := el.isLt
    fin_cases st <;> site_close

end CorrTc
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
