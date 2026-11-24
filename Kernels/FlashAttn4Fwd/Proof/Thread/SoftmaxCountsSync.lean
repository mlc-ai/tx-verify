-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCounts

@[expose] public section

/-! # `Counts`: the polls, the P-ready arrivals and the named barriers

A step of the softmax machine adds one successful poll of the statistics (score) barrier
exactly at a successful `statsW` (`sW`) poll, one arrival on the leader's P-ready barrier at
`pArr`, one `bar.arrive` of the stage's named barrier at `gen`, and passes the start and end
barriers at `bar0` and `barEnd`; the position formulas follow the item, the trip and the
site. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}

set_option maxHeartbeats 8000000 in
theorem step_stats (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : okPolls (ownLoc L g (240 + 8 * stOf L g)) es =
      (trips L + 1) * d.i + (if d.site.inItem then statsPos d else tailPos d)) :
    okPolls (ownLoc L g (240 + 8 * stOf L g)) (es ++ [e]) =
      (trips L + 1) * d'.i + (if d'.site.inItem then statsPos d' else tailPos d') := by
  rw [okPolls_snoc, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [okPoll, sourceWaitSuccess, Site.inItem, Site.tile0, Site.inTrip, statsPos,
    tailPos, Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem step_score (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : okPolls (ownLoc L g (128 + 8 * stOf L g)) es = trips L * d.i + sPos d) :
    okPolls (ownLoc L g (128 + 8 * stOf L g)) (es ++ [e]) = trips L * d'.i + sPos d' := by
  rw [okPolls_snoc, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [okPoll, sourceWaitSuccess, Site.inItem, Site.tile0, Site.tile0Ld, Site.inTrip,
    sPos, Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem step_pReady (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : arrivals (leadLoc L g (144 + 8 * stOf L g)) es = trips L * d.i + pPos d) :
    arrivals (leadLoc L g (144 + 8 * stOf L g)) (es ++ [e]) = trips L * d'.i + pPos d' := by
  rw [arrivals_snoc, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [arrivesOn, sourceArrive, Site.inItem, Site.tile0, Site.inTrip, Site.afterP,
    pPos, tileNo, Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem step_gen (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : barEvents (kOf L g + 3 + 4 * stOf L g) 64 .arrive es = (trips L + 1) * d.i + genPos d) :
    barEvents (kOf L g + 3 + 4 * stOf L g) 64 .arrive (es ++ [e]) =
      (trips L + 1) * d'.i + genPos d' := by
  rw [barEvents, List.countP_append, ← barEvents, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [barIs, Site.inItem, Site.tile0, Site.inTrip, Site.afterGen, genPos, tileNo,
    Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem step_bar2 (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : barEvents 2 416 .sync es = bar2Sync d ∧ barEvents 2 416 .arrive es = bar2Arrive d) :
    barEvents 2 416 .sync (es ++ [e]) = bar2Sync d' ∧
      barEvents 2 416 .arrive (es ++ [e]) = bar2Arrive d' := by
  simp only [barEvents, List.countP_append] at h ⊢
  rw [h.1, h.2]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  soft_cases
  all_goals simp [barIs, bar2Sync, bar2Arrive]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
