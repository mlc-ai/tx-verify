-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.KindRingOff
public import Lemmas.Protocol.GatedFaults

@[expose] public section

/-! # The gates of a ring of kinds with the empty side's poll offset a parameter

A proof tool, `Lemmas/Protocol/KindRingGate.lean` for `KRingOff`. An event of a producer after
`u + dE + 1` polls of the empty barrier follows, in the dependency order, every consumer's poll of
the full barrier with `u` earlier ones (`gateF`), and an event of a consumer after `t + 1` polls
of the full barrier (`1 ≤ t`) every producer's poll of the empty barrier with `t - 1 + dE` earlier
ones (`gateE`). Unlike `KRingOff.reachF`, the event need not be a counted item's, so the gates hold
of an update before its record is known to be fault-free. -/

namespace PTX.MbarRing
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

namespace KRingOff

variable {np nc nk dE : Nat}

/-- **A producer's event after `u + dE + 1` polls of `E`** follows every consumer's poll of `F`
with `u` earlier ones. -/
theorem gateF (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE) {a : Fin np}
    {i u : Nat} (hi : i < (X.tr (R.prod a)).length)
    (h : u + dE + 1 ≤ okPolls R.E ((X.tr (R.prod a)).take i)) (b : Fin nc) :
    Relation.TransGen (DepStep L K X) (.thread (R.cons b, Poll.nth X R.F (R.cons b) u), true)
      (.thread (R.prod a, i), false) := by
  have hg := Poll.guard R.spins hi h
  have he : u + 1 - 1 + dE = u + dE := by omega
  have hpres : X.RefPresent (.thread (R.prod a, Poll.nth X R.E (R.prod a) (u + 1 - 1 + dE))) := by
    rw [he]
    exact Round.Slot.present_of_guard hg
  obtain ⟨hyS, hyp⟩ := ((R.ring hX).content_empty hX.depAcyclic (a := a) (n := u) hpres).2 b
  have hg' : Resumes K X (R.prod a, Poll.nth X R.E (R.prod a) (u + 1 - 1 + dE)) (R.prod a, i) := by
    rw [he]
    exact hg
  exact ((((Relation.TransGen.single
      (DepStep.of_resumes L ((R.ring hX).guardM a (b, u) hyS u le_rfl))).trans_left
    ((R.ring hX).issue a (b, u) hyS)).tail
    (DepStep.of_witness L ((R.ring hX).obsE a (u + 1) (by omega) hpres (b, u) hyS hyp))).tail
    (DepStep.of_resumes L hg'))

/-- **A consumer's event after `t + 1` polls of `F`** follows every producer's poll of `E` with
`t - 1 + dE` earlier ones, when `1 ≤ t`. -/
theorem gateE (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE) {b : Fin nc}
    {i t : Nat} (hi : i < (X.tr (R.cons b)).length)
    (h : t + 1 ≤ okPolls R.F ((X.tr (R.cons b)).take i)) (ht : 1 ≤ t) (a : Fin np) :
    Relation.TransGen (DepStep L K X)
      (.thread (R.prod a, Poll.nth X R.E (R.prod a) (t - 1 + dE)), true)
      (.thread (R.cons b, i), false) := by
  have hg := Poll.guard R.spins hi h
  have hpres : X.RefPresent (.thread (R.cons b, Poll.nth X R.F (R.cons b) t)) :=
    Round.Slot.present_of_guard hg
  obtain ⟨k, hk⟩ := R.cover a
  obtain ⟨hxS, hxp⟩ := ((R.ring hX).content_full hX.depAcyclic (b := b) (j := t) hpres).2 k
  have hgp := (R.ring hX).guardP 0 (k, t) hxS t ht le_rfl
  have hgp' : Resumes K X (R.prod a, Poll.nth X R.E (R.prod a) (t - 1 + dE)) (R.opF k t) :=
    hk ▸ hgp
  exact ((((Relation.TransGen.single (DepStep.of_resumes L hgp')).trans_left
    ((R.ring hX).issueF 0 (k, t) hxS)).tail
    (DepStep.of_witness L ((R.ring hX).obsF b t hpres (k, t) hxS hxp))).tail
    (DepStep.of_resumes L hg))

end KRingOff

end
end PTX.MbarRing
