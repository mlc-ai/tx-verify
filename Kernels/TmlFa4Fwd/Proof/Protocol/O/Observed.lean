-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Kernels.TmlFa4Fwd.Proof.Protocol.S.Notify
import Lemmas.Protocol.MbarOneShot
import Lemmas.Protocol.ObservedSync
import Lemmas.Protocol.MultiProducer
import Lemmas.Protocol.MbarRingRound
import Lemmas.Protocol.ReachJoint
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The final O hand-off

A successful poll of stage `st`'s final O barrier (`144 + 8 st`) observes the notification of a
commit to it by a lane of the CTA's warp 12 (`o_handoff`, from the barrier's one-shot history), so
the notification is a witness of the poll's return (`o_witness`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The final O hand-off.** -/
theorem o_handoff (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (st : Fin 2) {h k pc : Nat} {acq : Bool} {sc : MbarScope}
    (hw : X.get (h, k) = some ⟨pc, .wait (obj L g (144 + 8 * st.val)) 0 true acq sc⟩) :
    ∃ y i pc' s rank, X.get (y, i) = some ⟨pc', .tc (.commit s)⟩ ∧ y < L.threads ∧
      y / L.block = g / L.block ∧ Prologue.warpIndex L y = 12 ∧
      s.mbar = obj L g (144 + 8 * st.val) ∧ rank ∈ X.tcNotified (y, i) ∧
      AsyncCopy.WaitObserves X (.async (y, i) (.tcNotify rank)) (h, k)
        (obj L g (144 + 8 * st.val)) acq sc ∧
      Witness L X (.async (y, i) (.tcNotify rank)) (h, k) := by
  obtain ⟨⟨y, i⟩, pc', s, rank, hc, ht⟩ := o_commit_exists hp hX hFw (st := st) (z := g) hw
  obtain ⟨hy, hcta, hw12, hb, -⟩ := mma_commit_of hp hX hFw hc ht
  have hob : obj L y (oOff st) = obj L g (oOff st) := obj_cta hcta _
  have hH := o_hist hp hX hFw (st := st) (z := y) hc (by rw [hob]; exact ht)
  rw [hob] at hH
  have hobs := hH.observes_arrive hX (List.mem_singleton_self _) hw
  obtain ⟨ir, jr, d, w, hd, hid, hdf, hjw, hwid, hwf, hww, hph, ho⟩ :=
    hH.poll_observes hX hw (.inl ⟨_, List.mem_singleton_self _, rfl⟩)
  obtain ⟨-, -, -, -, hr⟩ := MbarRing.Reach.notify_rec hX (List.mem_of_getElem? hd) hid
  have hda : CounterUpdate d.action := by
    cases AsyncCopy.record_source hX.tma.2.2.1 (List.mem_of_getElem? hd) with
    | commit hid' he' ht' ha' => rw [ha']; trivial
    | init hid' _ _ | inval hid' _ _ | arrive hid' _ _ | wait hid' _ _ | increment hid' _ _ =>
      rw [hid'] at hid; cases hid
    | tensor hid' _ _ _ | arriveOn hid' _ _ _ _ | bulk hid' _ _ _ _ | clc hid' _ _ _ _ =>
      rw [hid'] at hid; cases hid
  have hni : MBarrier.NoInval (X.objects (obj L g (oOff st))) :=
    AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _
  have hob := Consistent.observed_of_phase hX hni hd hdf hda hjw hww hph ho
  rw [hid, hwid] at hob
  exact ⟨y, i, pc', s, rank, hc, hy, hcta, hw12, hb, hr, ⟨⟨pc, 0, hw⟩, hobs⟩,
    Witness.of_mbarObserved hob⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
