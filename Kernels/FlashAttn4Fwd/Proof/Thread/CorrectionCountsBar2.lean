-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCounts

@[expose] public section

/-! # `Counts`: the start and end barriers

The start barrier (`bar.sync 2, 416`) is passed at `bar0`, the end barrier (`bar.arrive 2, 416`) at
`barEnd`; no other event of the role is on barrier 2. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxHeartbeats 4000000 in
theorem step_bar2 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    {es : List Event} (_hT : 1 ≤ trips L) (hi : Inv L g d) (hev : Ev L g d e)
    (hn : next L g d e = some (some d'))
    (h : barEvents 2 416 .sync es = bar2Sync d ∧ barEvents 2 416 .arrive es = bar2Arrive d) :
    barEvents 2 416 .sync (es ++ [e]) = bar2Sync d' ∧
      barEvents 2 416 .arrive (es ++ [e]) = bar2Arrive d' := by
  simp only [barEvents, List.countP_append] at h ⊢
  rw [h.1, h.2]
  obtain ⟨hpc, hk⟩ := hev
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, aw, a, o⟩ := d
  have htr := hi.trip
  have hs0 := hi.start
  simp only at htr hs0
  rcases site with _ | _ | st0 | ⟨st0, gen⟩ | a0 | st0 | st0 | ⟨st0, j⟩ | ⟨st0, j⟩ | ⟨st0, j⟩ |
    st0 | ⟨st0, fin⟩ | st0 | st0 | st0 | ⟨st0, j⟩ | ⟨st0, j⟩ | ⟨st0, j, hh, el⟩ | st0 | st0 |
    _ | _ | _
  all_goals (try fin_cases st0)
  all_goals (try fin_cases a0)
  all_goals (try cases gen)
  all_goals (try cases fin)
  all_goals simp only at hk
  all_goals repeat' (first | (obtain rfl := hk) | (obtain ⟨_, hk⟩ := hk))
  all_goals simp only [next, nextItem, afterTrip] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp [Site.inTrip, barIs, bar2Sync, bar2Arrive] at htr hs0 ⊢
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
