-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCounts

@[expose] public section

/-! # `Counts`: the rounds of the poll sites

A successful poll at a poll site's position is a successful poll of that site: no other site of
the role has its position (`pc_poll`). A step adds one round to the site exactly at its
successful poll, and the round formulas follow the item, the trip and the site. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A site at a poll site's position is that site. -/
theorem pc_poll (x s : Site) (hs : s.isPoll = true) (h : x.pc = s.pc) : x = s := by
  rcases s with _ | _ | w | lp | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals simp only [Site.isPoll, Bool.false_eq_true] at hs
  all_goals (try rcases fin4_cases w with rfl | rfl | rfl | rfl)
  all_goals (try cases lp)
  all_goals
    rcases x with _ | _ | w' | lp' | ⟨lp', c'⟩ | ⟨lp', c'⟩ | _ | j' | ⟨lp', c'⟩ | ⟨lp', c'⟩ |
      lp' | lp' | lp' | lp' | _ | _ | _
    all_goals (try rcases fin4_cases w' with rfl | rfl | rfl | rfl)
    all_goals (try rcases fin3_cases j' with rfl | rfl | rfl)
    all_goals (try rcases fin4_cases c' with rfl | rfl | rfl | rfl)
    all_goals (try rcases fin2_cases c' with rfl | rfl)
    all_goals (try cases lp')
    all_goals first | rfl | (simp only [Site.pc] at h; revert h; decide)

/-- A successful poll at a poll site's position, fired at the site of state `d`. -/
theorem okPollAt_site {d : D} {e : Event} {s : Site} (hs : s.isPoll = true)
    (hpc : e.pc = d.site.pc) :
    okPollAt s.pc e = (okPollAt d.site.pc e && decide (d.site = s)) := by
  obtain ⟨epc, ek⟩ := e
  simp only at hpc
  subst hpc
  by_cases h : d.site = s
  · subst h; simp
  · have hne : d.site.pc ≠ s.pc := fun h' => h (pc_poll _ _ hs h')
    cases ek <;> simp [okPollAt, h]
    all_goals split <;> simp_all

set_option maxHeartbeats 8000000 in
theorem counts_step_rounds {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}
    (hi : Inv L g d) (hev : Ev L g d e) (hpc : e.pc = d.site.pc)
    (hn : next L g d e = some (some d'))
    (h : ∀ s : Site, s.isPoll = true → es.countP (okPollAt s.pc) = roundOf L d s) :
    ∀ s : Site, s.isPoll = true → (es ++ [e]).countP (okPollAt s.pc) = roundOf L d' s := by
  intro s hs
  rw [List.countP_append, h s hs, List.countP_singleton, okPollAt_site hs hpc]
  clear h
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, w, m, l⟩ := d
  simp only at hpc
  subst hpc
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  simp only at htr hla ht0 hit hst htl ⊢
  rcases s with _ | _ | sw | slp | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals simp only [Site.isPoll, Bool.false_eq_true] at hs
  all_goals (try rcases fin4_cases sw with rfl | rfl | rfl | rfl)
  all_goals (try cases slp)
  all_goals soft_cases
  all_goals simp [okPollAt, roundOf, Site.inItem, Site.tile0, Site.inTrip, Site.afterS1,
    tailPos, Nat.mul_add] at htr hla ht0 hit hst htl ⊢
  all_goals omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
