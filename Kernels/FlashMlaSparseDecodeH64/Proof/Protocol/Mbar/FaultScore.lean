-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Count
public import Lemmas.Protocol.GatedFaults
public import Lemmas.Protocol.KindRingOffGate
public import Lemmas.Protocol.KindRingGate

@[expose] public section

/-! # The score ring's barriers do not fault

`soReady s` is a unit object of the 128 warpgroup-0 lanes: a lane's arrival of use `t ≥ 1` has
`t + 1` successful polls of `qkDone s` before it (`wg0_soArr`), so by the ring's gate
(`KRingOff.gateE`) it follows the MMA lane's poll of `soReady s` with `t - 1` earlier ones.
`qkDone s` is the commit object of the MMA lane: its commit of use `t ≥ 1` has `t` polls of
`soReady s` before it (`mma_qkArr`), so it follows the lanes' polls of `qkDone s` with `t - 1`
earlier ones (`KRingOff.gateF`). `svDone s` is the commit object of the MMA lane
(`svDone_fault`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **No record of `soReady s` faults.** -/
theorem soReady_fault (c : Nat) (s : Fin 2) :
    ∀ r ∈ X.objects (mbarLoc L c (.soReady s)), r.fault = none := by
  refine (soReady_obj hp hX hFw hR hI hB c s).fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {a i pc sc} he hpos => ?_)
  have hn : arrivals (mbarLoc L c (.soReady s)) ((X.tr (wg0Lane L c a)).take i) <
      okPolls (mbarLoc L c (.qkDone s)) ((X.tr (wg0Lane L c a)).take i) :=
    wg0_soArr hp hX hFw a.isLt he
  refine ⟨mmaLane L X c, ?_⟩
  have h := (scoreSlot hp hX hFw hR hI hB c s).gateE hX (b := a) (i := i)
    (t := arrivals (mbarLoc L c (.soReady s)) ((X.tr (wg0Lane L c a)).take i))
    (len_of_get he) (by simp only [scoreSlot]; omega) hpos 0
  simpa only [scoreSlot, Nat.add_zero] using h

/-- **No record of `qkDone s` faults.** -/
theorem qkDone_fault (c : Nat) (s : Fin 2) :
    ∀ r ∈ X.objects (mbarLoc L c (.qkDone s)), r.fault = none := by
  refine (qkDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c s).fault_free hX
    (Notify.gated_of_paths (K := kernel) (A := Assumptions.all) fun {i pc sp rank}
      hget hb ht hrec hpos => ?_)
  obtain ⟨r, hr, hid⟩ := hrec
  obtain ⟨-, -, -, -, hn⟩ := Reach.notify_rec hX hr hid
  have hq := mma_qkArr hp hX hFw (mma_commit_warp hp hX hFw hget) hget hb
  refine ⟨wg0Lane L c 0, ?_⟩
  have h := (scoreSlot hp hX hFw hR hI hB c s).gateF hX (a := 0) (i := i)
    (u := ((X.tr (mmaLane L X c)).take i).countP (commitsTo (mbarLoc L c (.qkDone s))) - 1)
    (len_of_get hget) (by simp only [scoreSlot]; omega) 0
  simp only [scoreSlot] at h
  exact h.tail (Reach.commit_notify (K := kernel) (L := L) hget hn)

end

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **No record of `svDone s` faults**: the MMA lane's commit of use `t ≥ 1` has `t + 1` polls of
`dequantReady s` before it (`DequantInputs.mmaSvArr`), so it follows the dequant lanes' polls of
`svDone s` with `t` earlier ones (`KRing.gateE`). -/
theorem svDone_fault (c : Nat) (s : Fin 2) :
    ∀ r ∈ X.objects (mbarLoc L c (.svDone s)), r.fault = none := by
  refine (svDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c s).fault_free_selected hX
    (Notify.selected_gated_of_paths (K := kernel) (A := Assumptions.all) fun {i pc sp rank}
      hget hb ht hrec hpos => ?_)
  obtain ⟨r, hr, hid⟩ := hrec
  obtain ⟨-, -, -, -, hn⟩ := Reach.notify_rec hX hr hid
  have hq := hN.mmaSvArr hget hb
  refine ⟨deqLane L c 0, (deqLane_warp hp c 0).1.trans' (by omega), ?_⟩
  have h := (dqSlot hp hX hFw hR hI hB hN c s).gateE hX (b := 0) (i := i)
    (t := ((X.tr (mmaLane L X c)).take i).countP (commitsTo (mbarLoc L c (.svDone s))) - 1 + 1)
    (len_of_get hget) (by simp only [dqSlot]; omega) (by omega) 0
  simp only [dqSlot] at h
  exact h.tail (Reach.commit_notify (K := kernel) (L := L) hget hn)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
