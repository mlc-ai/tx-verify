-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCounts

@[expose] public section

/-! # `Counts`: the warp-collective `tcgen05` events

A rescale (a vote with a nonzero ballot) is followed by twenty-five warp-collective `tcgen05`
events (per chunk a load, its wait and a store; then the wait for the stores), and each stage of
an item's final part by sixteen (per chunk a load and its wait). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxHeartbeats 4000000 in
theorem step_tcColl {L : Launch} {g : Nat} {d d' : D} {e : Event}
    {es : List Event} (_hT : 1 ≤ trips L) (hi : Inv L g d) (hev : Ev L g d e)
    (hn : next L g d e = some (some d'))
    (h : es.countP isTcColl + tcLack d = 25 * es.countP isNzVote + 32 * d.i + finTc d) :
    (es ++ [e]).countP isTcColl + tcLack d' =
      25 * (es ++ [e]).countP isNzVote + 32 * d'.i + finTc d' := by
  simp only [List.countP_append] at h ⊢
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
  all_goals simp only [Site.pc] at hpc
  all_goals subst hpc
  all_goals repeat' (first | (obtain rfl := hk) | (obtain ⟨_, hk⟩ := hk))
  all_goals simp only [next, nextItem, afterTrip] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp [Site.inTrip, Nat.mul_add, isTcColl, isNzVote, tcLack, finTc] at htr hs0 h ⊢
  all_goals (first | omega | (split_ifs <;> omega) | (simp_all; done) | (simp_all; omega))
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
