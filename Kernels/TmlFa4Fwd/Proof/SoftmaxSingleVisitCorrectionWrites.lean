-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters
import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue Correction

set_option maxRecDepth 100000 in
private theorem finalCorrectionCode :
    (kernel.code.drop 8447).all (fun i => Thread.staysPastEvent 8447 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem finalCorrectionSegments :
    ∀ site, 8447 ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, PTX.Assumption.cuteExp2.matchAt kernel site = some seg → 8447 ≤ seg.stop := by
  intro site hPc hSite
  have hSites : Assumptions.swExp2Sites.all (· < 8447) = true := by kernel_rfl
  have hLo := of_decide_eq_true (List.all_eq_true.mp hSites site hSite)
  omega

/-- The actual correction lane of a one-visit request skips both Tensor Memory rescale banks. -/
theorem singleVisitNoCorrectionStore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {batch : Nat} {i : EvId}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ i.1 / l.block)
    (hHi : i.1 / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (i.1 / l.block)).1 = 1)
    (stage : Fin 2) (chunk : Fin 8) {address : Nat} {vals : List Value} {shape : TcShape} :
    X.get i ≠ some ⟨rescaleStorePc stage chunk,.tc (.st address vals shape)⟩ := by
  intro he
  let pc := rescaleStorePc stage chunk
  have hRange : 7988 < pc ∧ pc < 8447 ∧ pc ∉ registerHintSites := by
    fin_cases stage <;> fin_cases chunk <;> decide
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < pc by omega) hRange.2.2
  change roleBodyPc (warpIndex l i.1) pc at hRole
  have hWarp : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l i.1
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l i.1 lane = i.1 :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hGet : X.get (warpLane l i.1 lane,i.2) = some ⟨pc,.tc (.st address vals shape)⟩ := by
    rwa [hSelf]
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨hCuQ,hUsedK⟩ := hFrame.metadataProtected hp
  obtain ⟨chosen,hChosen,hBegin,hEnd,_,_,_,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarp.1 hWarp.2 hl hWork
      (show 7884 < pc by omega) hGet
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hEq := (hUnique chosen ⟨hChosen,hBegin,hEnd⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst chosen
  have hRun := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨s,hs,hIndex,_,_,_,hSuffix⟩ :=
    correctionLaneBeforeRescaleOfEvent hp hX hb hLo hHi (active.checkpoint lane hl)
      hRun hUsedK hActive.before hRange.1 hGet
  obtain ⟨n,u,hLocal,hU⟩ := correctionLaneRescaleSetup hp hb hLo hHi hs
  have hUPc : u.pc = 8447 := by
    have h := hU.1
    simpa [hTrip] using h
  obtain ⟨visits,hWalk⟩ := Mma.walkFromRun hSuffix
  have hMem : (⟨pc,.tc (.st address vals shape)⟩ : Event) ∈
      (X.tr (warpLane l i.1 lane)).drop (active.pos lane + 6) := by
    apply List.mem_of_getElem? (i := i.2 - (active.pos lane + 6))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  rcases Mma.advanceWalkLocals hLocal hWalk with hNil | ⟨_,_,_,hRest⟩
  · rw [hNil] at hMem
    cases hMem
  have hPast := Thread.eventTailEventsOfSegmentFloor finalCorrectionCode finalCorrectionSegments
    hRest hUPc.ge _ hMem
  change 8447 ≤ pc at hPast
  omega

end PTX.Kernels.TmlFa4Fwd.Softmax
