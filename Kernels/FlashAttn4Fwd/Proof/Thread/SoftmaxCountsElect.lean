-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCounts

@[expose] public section

/-! # `Counts`: the elected lane's arrivals

The arrivals on the leader's second P-ready barrier (`+160 + 8 st`) are issued by the elected
lane only: when every election of the trace returned this lane they follow the position
formula, when none did there are none; at the elected lane's arrival the last election
returned this lane (`lead`). The warp barrier, before the election, is counted here too
(`warpBar`), and so are the elections (`elects`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}

set_option maxHeartbeats 8000000 in
theorem step_pReady2 (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : ElectLead L g es →
      arrivals (leadLoc L g (160 + 8 * stOf L g)) es = trips L * d.i + p2Pos d) :
    ElectLead L g (es ++ [e]) →
      arrivals (leadLoc L g (160 + 8 * stOf L g)) (es ++ [e]) = trips L * d'.i + p2Pos d' := by
  intro hL
  have hld : ∀ m inst ld, e.kind = .elect m inst ld → ld = laneOf L g :=
    fun _ _ _ he => ((electLead_snoc_elect he).mp hL).2
  rw [arrivals_snoc, h hL.of_snoc]
  clear h hL
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl hld
  soft_cases
  all_goals (try (obtain rfl := hld _ _ _ rfl))
  all_goals (try contradiction)
  all_goals simp [arrivesOn, sourceArrive, Site.inItem, Site.tile0, Site.inTrip,
    Site.afterP2, p2Pos, tileNo, Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem step_pReady2Non (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : ElectNonLead L g es → arrivals (leadLoc L g (160 + 8 * stOf L g)) es = 0)
    (hl : ∀ lp, d.site = .p2Arr lp → ¬ ElectNonLead L g es) :
    ElectNonLead L g (es ++ [e]) →
      arrivals (leadLoc L g (160 + 8 * stOf L g)) (es ++ [e]) = 0 := by
  intro hN
  have hN0 := hN.of_snoc
  rw [arrivals_snoc, h hN0]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  simp only at hl
  soft_cases
  all_goals first
    | exact absurd hN0 (hl _ rfl)
    | simp [arrivesOn, sourceArrive]

set_option maxHeartbeats 8000000 in
theorem step_lead (hev : Ev L g d e) (hn : next L g d e = some (some d')) :
    ∀ lp, d'.site = .p2Arr lp → ¬ ElectNonLead L g (es ++ [e]) := by
  intro lp' hs' hN
  have hne : ∀ m inst ld, e.kind = .elect m inst ld → ld ≠ laneOf L g :=
    fun _ _ _ he => ((electNonLead_snoc_elect he).mp hN).2
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  simp only at hne
  clear hN
  soft_cases
  all_goals (try (exact hne _ _ _ rfl rfl))
  all_goals simp at hs'

set_option maxHeartbeats 8000000 in
theorem counts_step_warpBar (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : es.countP Execution.isWarpBar = trips L * d.i + wbPos d) :
    (es ++ [e]).countP Execution.isWarpBar = trips L * d'.i + wbPos d' := by
  rw [List.countP_append, h]
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [Execution.isWarpBar, Site.inItem, Site.tile0, Site.inTrip, Site.afterWB, wbPos,
    tileNo, Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

theorem counts_step_elects (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : es.countP isElectE = (if warpOf L g = 0 then 14 else 0) + trips L * d.i + elPos d) :
    (es ++ [e]).countP isElectE =
      (if warpOf L g = 0 then 14 else 0) + trips L * d'.i + elPos d' := by
  rw [List.countP_append, h]
  generalize (if warpOf L g = 0 then 14 else 0) = w0
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals simp [isElectE, Site.inItem, Site.tile0, Site.inTrip, Site.afterEl, elPos,
    tileNo, Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
