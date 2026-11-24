-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMaximum
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxMetadataReads
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxAffine
import Kernels.TmlFa4Fwd.Proof.Termination

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Thread

noncomputable section

set_option maxRecDepth 100000 in
private theorem openingNoticeFloor (offset : Fin 2) :
    (kernel.code.drop (4397+offset.val)).all
      (fun ins => staysPastEvent (4397+offset.val) ins.op) = true := by
  fin_cases offset <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem openingNoticeSegmentFloor : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (4398 ≤ seg.stop)
    | none => false) = true := by
  kernel_rfl

private theorem openingNoticeSegment (site : Nat) (hSite : site ∈ Assumptions.swExp2Sites)
    (seg : SegMatch CuteSlot) (hMatch : cuteExp2.matchAt kernel site = some seg) :
    4398 ≤ seg.stop := by
  have h := List.all_eq_true.mp openingNoticeSegmentFloor site hSite
  rwa [hMatch,decide_eq_true_eq] at h

private theorem openingNoticeIndex {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g batch wait notice id : Nat} {stage : Fin 2} {count : Option Nat} {mode : BarMode}
    (entry : OpeningFmaLane p l X g batch stage wait)
    (he : X.get (g,notice) = some ⟨4397,.bar id count mode⟩) :
    entry.pos ≤ notice := by
  have hFloor : (kernel.code.drop 4397).all (fun ins => staysPastEvent 4397 ins.op) = true :=
    openingNoticeFloor 0
  have before {j : Nat} {ev : Event} (hGet : X.get (g,j) = some ev) (hPc : ev.pc < 4397) :
      j < notice := by
    exact traceOrderOfSegmentFloor hX hFloor
      (fun site _ hs seg hm =>
        (by decide : 4397 ≤ 4398).trans (openingNoticeSegment site hs seg hm))
      hGet he hPc (by change 4397 ≤ 4397; decide)
  rw [entry.position]
  by_cases hLane : laneOf l g = 0
  · rw [ite_eq_left hLane]
    have h := before (entry.releasedBias hLane) (by change 3590 < 4397; decide)
    omega
  · rw [ite_eq_right hLane]
    have h := before entry.arrival.arrival (by change 3583 < 4397; decide)
    omega

/-- An actual first statistics notification has a canonical maximum even if the
original execution stops at that notice. Extending it supplies the opening rendezvous
witness, and the arithmetic cursor is restricted back to the original lane trace. -/
theorem openingMaximumOfNotice {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g notice id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g,notice) = some ⟨4397,.bar id count mode⟩) :
    ∃ (u : TState) (mx : Option ℝ) (ending : Option TState),
      At u 4397 [(7256,scoreValue mx)] ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take notice) u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop notice) ending := by
  obtain ⟨Y,hPrefix,hMax⟩ := maximalExtension hp hX
  have hFrame := hFootprint Y hMax.1
  have hEvent := Execution.le_get hPrefix he
  have hg := event_thread_lt hMax.1 hEvent
  obtain ⟨warp,hWarp,_,_,_,_,_,_⟩ := softmaxBodySuffix hp hMax.1 hEvent
    (by decide : 3420 ≤ 4397) (by decide : 4397 < 7742)
  let src := laneOf l g
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g src = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hWork := softmaxWorkOfActiveEvent hp hMax.1 hg (hWarp ▸ warp.isLt) hSrc
    (hFrame.metadataProtected hp).1 (hLane.symm ▸ hEvent)
    (by change 3207 < 4397; decide) (by change 4397 < 7738; decide)
  obtain ⟨batch,⟨hb,hLo,hHi⟩,_⟩ := tileBatch_existsUnique p hWork
  let stage := stageOf warp
  have hStage : warpIndex l g/4 = stage.val := by rw [← hWarp]; rfl
  obtain ⟨_,⟨lane⟩⟩ :=
    Progress.openingSoftmaxAffineOfAllStages hp hMax hFrame hg stage hStage hb hLo hHi
  have hIndex := openingNoticeIndex hMax.1 lane.entry hEvent
  have hMore : lane.entry.pos < (Y.tr g).length := hIndex.trans_lt (len_of_get hEvent)
  obtain ⟨u,mx,hu,hTail,_,hAfter,hPath⟩ := lane.maximumOfPrefix hp hb hLo hHi hMore
  have hEq : lane.entry.pos = notice := by
    by_contra hNe
    have hPast : lane.entry.pos+1 ≤ notice := by omega
    let target : Event := ⟨4397,.bar id count mode⟩
    have hSeen : target ∈ (Y.tr g).drop (lane.entry.pos+1) := by
      apply List.mem_of_getElem? (i := notice-(lane.entry.pos+1))
      rwa [List.getElem?_drop,Nat.add_sub_of_le hPast]
    obtain ⟨_,hWalk⟩ := Mma.walkFromRun hAfter
    have hPc : 4398 ≤ (next u).pc := by change 4398 ≤ u.pc+1; rw [hu.1]; decide
    have hFloor := eventTailEventsOfSegmentFloor (openingNoticeFloor 1)
      (fun site _ hs seg hm => openingNoticeSegment site hs seg hm) hWalk hPc target hSeen
    exact (by decide : ¬4398 ≤ 4397) hFloor
  rw [hEq] at hTail hPath
  obtain ⟨suffix,hSuffix⟩ := (hPrefix.1 g).drop notice
  rw [← hSuffix] at hTail
  obtain ⟨ending,hRun⟩ := hTail.prefix
  obtain ⟨extra,hExtra⟩ := hPrefix.1 g
  have ht : (Y.tr g).take notice = (X.tr g).take notice := by
    rw [← hExtra,List.take_append_of_le_length (len_of_get he).le]
  exact ⟨u,mx,ending,hu,ht ▸ hPath,hRun⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
