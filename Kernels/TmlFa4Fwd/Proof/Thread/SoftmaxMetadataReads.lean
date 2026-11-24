-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxActiveGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
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
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxIdleProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Softmax Epilogue

/-- A softmax lane reads a selected request's two query offsets or its used-K length. -/
@[no_expose] def SoftmaxGeometryRead (X : Execution) (i : EvId) (which : Fin 3)
    (a : Acc) (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨(geometryReadSite which).pc,.rd a bytes⟩

/-- A role event before the idle drain requires work in its CTA. -/
theorem softmaxWorkOfActiveEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index : Nat} {target : Event} (hg : g < l.threads) (hWarp : warpIndex l g < 8)
    (hSrc : src < 32) (hCuQ : DrainCuQProtected p X)
    (he : X.get (warpLane l g src,index) = some target)
    (hEarly : 3207 < target.pc) (hBeforeIdle : target.pc < 7738) :
    g/l.block < tilePrefix p p.batch*p.heads := by
  obtain ⟨start,_,_,hWork,_,_,_⟩ :=
    activeGroupOfEventUnlessExhausted hp hX hg hWarp hSrc hCuQ he hEarly
      (fun _ _ _ hLast _ exhausted hFollow => by
        obtain ⟨terminal,hPos,_⟩ := idleTerminalAtFromExhausted hp hg hLast exhausted
        have hFollow' : WarpFollowsEvent l X g terminal.pos src index target :=
          hPos.symm ▸ hFollow
        have hRun := (terminal.continuation src hSrc).after_local_nonempty
          (terminal.localSteps src hSrc) hFollow'.nonempty
        obtain ⟨_,hWalk⟩ := Mma.walkFromRun hRun
        have hMem : target ∈ (X.tr (warpLane l g src)).drop (terminal.pos src) := by
          apply List.mem_of_getElem? (i := index-terminal.pos src)
          rwa [List.getElem?_drop,Nat.add_sub_of_le hFollow'.before]
        have hFloor := eventTailEventsOfSegmentFloor (floor := 7738) (by decide +kernel)
          (fun site hSiteLo hSite _ _ => by
            have hAudit : Assumptions.swExp2Sites.all (fun k => decide (k < 7738)) = true := by
              decide +kernel
            exact (Nat.not_lt_of_ge hSiteLo
              (of_decide_eq_true (List.all_eq_true.mp hAudit site hSite))).elim)
          hWalk (terminal.checkpoint src hSrc).1.ge target hMem
        exact (Nat.not_le_of_lt hBeforeIdle) hFloor)
  exact hWork.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left _ _)))

/-- The opening metadata load of an active softmax lane uses its assigned request,
including a prefix that has not reached the following instruction. -/
theorem SoftmaxGeometryRead.word {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {i : EvId} {which : Fin 3} {a : Acc} {bytes : List (Option Byte)}
    (hRead : SoftmaxGeometryRead X i which a bytes) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ i.1/l.block ∧
      i.1/l.block < tilePrefix p (batch+1) * p.heads ∧
      let index := batch+which.val
      let addr := if which = 2 then p.usedKBase+4*batch else p.cuQBase+4*index
      let value := if which = 2 then p.kLength batch else p.qOffset index
      a = {loc := globalLoc addr,size := 4} ∧ bytes = (b32 value).toBytes.map some := by
  obtain ⟨g,index⟩ := i
  let event : Event := ⟨(geometryReadSite which).pc,.rd a bytes⟩
  have he : X.get (g,index) = some event := hRead
  have hg := event_thread_lt hX he
  have hLate : 3367 ≤ event.pc := by
    change 3367 ≤ (geometryReadSite which).pc
    fin_cases which <;> decide
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < event.pc by omega)
    (by change (geometryReadSite which).pc ∉ registerHintSites; fin_cases which <;> decide)
  have hWarp : warpIndex l g < 8 := by
    change roleBodyPc (warpIndex l g) event.pc at hRole
    have hStop : event.pc < 7745 := by
      change (geometryReadSite which).pc < 7745
      fin_cases which <;> decide
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let src := laneOf l g
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g src = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have he' : X.get (warpLane l g src,index) = some event := hLane.symm ▸ he
  obtain ⟨hCuQ,hUsedK⟩ := hFrame.metadataProtected hp
  have hBeforeIdle : event.pc < 7738 := by
    change (geometryReadSite which).pc < 7738
    fin_cases which <;> decide
  have hWork := softmaxWorkOfActiveEvent hp hX hg hWarp hSrc hCuQ he' (by omega) hBeforeIdle
  obtain ⟨batch,_,hb,hLo,hHi,_,cur,hFollow⟩ :=
    activeTileOfEvent hp hX hg hWarp hSrc hWork hCuQ he' (by omega)
  have heDrop : ((X.tr (warpLane l g src)).drop (cur.pos src))[index-cur.pos src]? =
      some event := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hFollow.before]
    exact he'
  obtain ⟨t,ht,hR⟩ := activeGeometryInputs (cur.checkpoint src hSrc)
    ((cur.continuation src hSrc).after_local_nonempty (cur.localSteps src hSrc) hFollow.nonempty)
    heDrop hLate
  rw [hLane] at hR
  exact ⟨batch,hb,hLo,hHi,geometryReadOfObservedPrefix hp hX _ hb
    (assignedCoordinates_valid hp hLo hHi).1 which he hFollow.before ht
    (fun off hOff => hCuQ (batch+off) (by omega)) (hUsedK batch hb) hR⟩

end PTX.Kernels.TmlFa4Fwd.Thread
