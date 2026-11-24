-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedSoftTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCounts

@[expose] public section

/-! # The softmax `tcgen05` count in the schedule's form

`Counts.tcColl` counts the warp-collective `tcgen05` events by the load, wait, store and
`wait::st` positions of the site (`Softmax.tcPos`); at a state with the role's invariant this is
the schedule's offset table `Sched.Soft.tcPos` (at the item's end the trip is the last,
`Inv.last`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The two offset tables agree at a state with the role's invariant. -/
theorem Softmax.tcPos_sched {L : Launch} {g : Nat} {d : Softmax.D} (hi : Softmax.Inv L g d) :
    Softmax.tcPos d = Sched.Soft.tcPos L d := by
  have ht0 := hi.tile0
  have hla := hi.last
  obtain ⟨site, i, t, w, m, l⟩ := d
  simp only at ht0 hla
  rcases site with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, c⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin3_cases j with rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin2_cases c with rfl | rfl)
  all_goals (try cases lp)
  all_goals simp [Softmax.tcPos, Softmax.ldPos, Softmax.wlPos, Softmax.stPos, Softmax.waitPos,
    Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip, Sched.Soft.tcPos,
    Progress.Time.softSlot]
    at ht0 hla ⊢
  all_goals omega

/-- **The softmax count in the schedule's form** (`Sched.Soft.SoftTcCount`, with the role's
invariant at the state). -/
theorem Softmax.tcColl_sched {L : Launch} {g : Nat} {d : Softmax.D} {es : List Event}
    (hc : Softmax.Counts L g d es) (hi : Softmax.Inv L g d) :
    es.countP isTcColl = 14 * Softmax.trips L * d.i + Sched.Soft.tcPos L d := by
  rw [hc.tcColl, Softmax.tcPos_sched hi]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
