-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCounts
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # `Counts`: the named-barrier syncs

A step of the correction machine adds one sync of stage `st`'s named barrier exactly at
`sync st _`, and the position formula follows the item, the trip and the site. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxHeartbeats 4000000 in
theorem step_sync {L : Launch} {g : Nat} {d d' : D} {e : Event}
    {es : List Event} (hT : 1 ≤ trips L) (hi : Inv L g d) (hev : Ev L g d e)
    (hn : next L g d e = some (some d')) (st : Nat) (hst : st < 2)
    (h : barEvents (kOf L g + 3 + 4 * st) 64 .sync es =
      (trips L + 1) * d.i + syncPos L st d) :
    barEvents (kOf L g + 3 + 4 * st) 64 .sync (es ++ [e]) =
      (trips L + 1) * d'.i + syncPos L st d' := by
  rw [barEvents, List.countP_append, ← barEvents, h]
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
  all_goals (try rcases (show st = 0 ∨ st = 1 by omega) with rfl | rfl)
  all_goals simp [Site.inTrip, Nat.mul_add, barIs, syncPos] at htr hs0 ⊢
  all_goals omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
