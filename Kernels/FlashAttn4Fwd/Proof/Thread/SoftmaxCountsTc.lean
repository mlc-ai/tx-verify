-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCounts

@[expose] public section

/-! # `Counts`: Tensor Memory and the statistics word

A step of the softmax machine adds one load of the stage's score columns exactly at `ld`, one
store of its probability columns at `pst`, one `tcgen05.wait::st` at `pwait`, and one write of
the statistics word at `alphaSt` and `lSt`; with the implicit waits, fourteen warp-collective
`tcgen05` events per tile. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event} (hi : Inv L g d)
    (hev : Ev L g d e) (hn : next L g d e = some (some d'))
include hi hev hn

set_option maxHeartbeats 8000000 in
theorem step_tcLd (h : tcLdsIn (tmem L g 0) (tmem L g 128) es = 4 * trips L * d.i + ldPos d) :
    tcLdsIn (tmem L g 0) (tmem L g 128) (es ++ [e]) = 4 * trips L * d'.i + ldPos d' := by
  rw [tcLdsIn, List.countP_append, ← tcLdsIn, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [tcLdAt, Site.inItem, Site.tile0, Site.inTrip, ldPos, tileNo,
    Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem step_tcSt (h : tcStsIn (tmem L g 64) (tmem L g 128) es = 4 * trips L * d.i + stPos d) :
    tcStsIn (tmem L g 64) (tmem L g 128) (es ++ [e]) = 4 * trips L * d'.i + stPos d' := by
  rw [tcStsIn, List.countP_append, ← tcStsIn, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [tcStAt, Site.inItem, Site.tile0, Site.inTrip, stPos, tileNo,
    Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem step_waitSt (h : tcWaitSts es = 2 * trips L * d.i + waitPos d) :
    tcWaitSts (es ++ [e]) = 2 * trips L * d'.i + waitPos d' := by
  rw [tcWaitSts, List.countP_append, ← tcWaitSts, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [isWaitSt, Site.inItem, Site.tile0, Site.inTrip, waitPos, tileNo,
    Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem counts_step_word (h : writesAt (statsWord L g) es = trips L * d.i + wrPos d) :
    writesAt (statsWord L g) (es ++ [e]) = trips L * d'.i + wrPos d' := by
  rw [writesAt, List.countP_append, ← writesAt, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [writeAt, Site.inItem, Site.tile0, Site.inTrip, Site.afterAlpha, wrPos,
    Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem counts_step_tcColl (h : es.countP isTcColl = 14 * trips L * d.i + tcPos d) :
    (es ++ [e]).countP isTcColl = 14 * trips L * d'.i + tcPos d' := by
  rw [List.countP_append, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [isTcColl, Site.inItem, Site.tile0, Site.inTrip, tcPos, ldPos, wlPos, stPos,
    waitPos, tileNo, Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
