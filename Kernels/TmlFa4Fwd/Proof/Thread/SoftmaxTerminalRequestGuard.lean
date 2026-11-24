-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainUpScan
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScanProgress
import all Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleTiles
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxLaneRegister
import all Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame Prologue Epilogue Thread

private def guardPreserved (ins : Instr) : Bool :=
  (ins.op.isLocal || scoreEventOp ins.op) &&
    !(writesRegs ins.op ++ scoreEventWrites ins.op).contains 441

private theorem guardCode :
    ((kernel.code.drop 3118).take (7617-3118)).all guardPreserved = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem guardDrainCode :
    ((kernel.code.drop 7617).take (7624-7617)).all guardPreserved = true := by
  decide +kernel

private theorem guardAt {pc : Nat} {ins : Instr} (hLo : 3118 ≤ pc) (hHi : pc < 7624)
    (hc : kernel.code[pc]? = some ins) : guardPreserved ins = true := by
  by_cases h : pc < 7617
  · apply List.all_eq_true.mp guardCode ins
    apply List.mem_of_getElem? (i := pc-3118)
    rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
  · apply List.all_eq_true.mp guardDrainCode ins
    apply List.mem_of_getElem? (i := pc-7617)
    rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le (by omega)]

private theorem guardStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 3118 ≤ s.pc) (hHi : s.pc < 7624) (hSub : s.sub ≤ 3)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    u.sub ≤ 3 ∧ u.regs 441 = s.regs 441 := by
  rcases hStep with ⟨rfl,hTau⟩ | ⟨_,rfl,hEvent⟩
  · obtain ⟨ins,hCode,_,hBody⟩ := tauScoreSource hTau
    rcases hBody with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
    · exact ⟨by simp [skip],rfl⟩
    rcases scoreExecLocal hLocal with hFrame | ⟨seg,hSite,hMatch,hExec⟩
    · have hKeep := (Bool.and_eq_true_iff.mp (guardAt hLo hHi hCode)).2
      have hNo : 441 ∉ writesRegs ins.op ++ scoreEventWrites ins.op := by simpa using hKeep
      refine ⟨?_,hFrame.regs _ (fun hr => hNo (List.mem_append_left _ hr))⟩
      exact hFrame.sub.trans_le hSub
    · have hAll : Assumptions.swExp2Sites.all (fun site =>
          match cuteExp2.matchAt kernel site with
          | some seg => !(scoreSegmentWrites seg).contains 441
          | none => false) = true := by
        set_option maxRecDepth 100000 in decide +kernel
      have hAudit := List.all_eq_true.mp hAll _ hSite
      rw [hMatch] at hAudit
      have hNo : 441 ∉ scoreSegmentWrites seg := by simpa using hAudit
      obtain ⟨_,hClear,_,hKeep⟩ := scoreSegmentFrame hExec
      exact ⟨by omega,hKeep _ hNo⟩
  · obtain ⟨ins,hCode,hNonlocal,_⟩ := estep_event_source hEvent
    have ha := guardAt hLo hHi hCode
    simp only [guardPreserved,Bool.and_eq_true,hNonlocal,Bool.false_or] at ha
    have hNo : 441 ∉ writesRegs ins.op ++ scoreEventWrites ins.op := by simpa using ha.2
    obtain ⟨hProgress,hReg⟩ := scoreEventStep hCode ha.1 hSub
      (fun h => hNo (List.mem_append_right _ h)) hEvent
    exact ⟨hProgress.sub,hReg⟩

private theorem guardFloorCode (floor : Nat) (h : floor = 3118 ∨ floor = 7624) :
    (kernel.code.drop floor).all (fun ins => staysPastEvent floor ins.op) = true := by
  rcases h with rfl | rfl <;> set_option maxRecDepth 100000 in decide +kernel

private theorem guardSegmentFloor : segmentFloor 3118 = true := by decide +kernel

private theorem noDrainSegments (site : Nat) (hLo : 7624 ≤ site)
    (hSite : site ∈ Assumptions.swExp2Sites) (seg : SegMatch CuteSlot)
    (_ : cuteExp2.matchAt kernel site = some seg) : 7624 ≤ seg.stop := by
  have hSiteBound : site < 7617 :=
    of_decide_eq_true (List.all_eq_true.mp noSegmentsInDrain site hSite)
  omega

private theorem guardAlong {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (hp : TraceReach kernel Assumptions.all l g s es u)
    (hStart : 3118 ≤ s.pc) (hStop : u.pc = 7623) (hSub : s.sub ≤ 3) :
    u.regs 441 = s.regs 441 := by
  have next {s t u : TState} {e : Option Event} {es : List Event}
      (hr : TraceReach kernel Assumptions.all l g t es u)
      (hStart : 3118 ≤ s.pc) (hSub : s.sub ≤ 3) (hStop : u.pc = 7623)
      (hStep : WStep kernel Assumptions.all l g s e t) :
      3118 ≤ t.pc ∧ t.sub ≤ 3 ∧ t.regs 441 = s.regs 441 := by
    have hFloor := guardFloorCode 3118 (.inl rfl)
    have hSegment := schedulerSegmentBound guardSegmentFloor
    have hNext := Thread.eventTailStep hFloor hSegment hStart hStep
    have hi : s.pc < 7624 := by
      by_contra! hs
      have hTail := guardFloorCode 7624 (.inr rfl)
      have hEnd := traceKeepsFloor hr hTail noDrainSegments
        (Thread.eventTailStep hTail noDrainSegments hs hStep)
      omega
    exact ⟨hNext,guardStep hStart hi hSub hStep⟩
  induction hp with
  | refl => rfl
  | tau hTau hTail ih =>
    obtain ⟨hStart',hSub',hReg⟩ := next hTail hStart hSub hStop (.inl ⟨rfl,hTau⟩)
    exact (ih hStart' hStop hSub').trans hReg
  | event hEvent hTail ih =>
    obtain ⟨hStart',hSub',hReg⟩ := next hTail hStart hSub hStop (.inr ⟨_,rfl,hEvent⟩)
    exact (ih hStart' hStop hSub').trans hReg

/-- The terminal scheduler reads its exact original per-lane request guard. -/
theorem terminalRequestGuardOfWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpReached l X g 7623 F shuffles votes ends) :
    ∀ lane < 32, (cur.state lane).regs 441 =
      some (.pred (terminalRequestGuard p l (warpLane l g lane))) := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  obtain ⟨_,⟨first⟩⟩ := firstWarpCursor hp hMax hg hw hCuQ
  obtain ⟨down⟩ := first.consumeShuffle (dst := 2683) hp hMax hg .down
    (fun lane => b32 (schedulerInputWord p lane)) (fun _ => 1) (fun _ => 31)
    (fun _ _ => by simp [schedulerFirstWarpFacts,schedulerLane,schedulerEntry,
      dispatchOutput,dispatchInput])
    (fun lane hl => schedulerFirstShuffleOut hp (first.checkpoint lane hl))
  intro lane hl
  let thread := warpLane l g lane
  have hb : l.block % 32 = 0 := by rw [hp.block]
  have hLane : laneOf l thread = lane := (Step.sameWarp_lane hb hg hl).2
  have hAt := down.checkpoint lane hl
  obtain ⟨hBegin,hFinish,_,_,_⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at hBegin hFinish
  have hInput : At (down.state lane) 3112
      [(1215,b32 lane),(7247,b32 p.batch),(7237,b32 (drainCuQ p lane)),
        (2683,b32 (drainCuQ p (shflSource .down lane 1 31).1))] := by
    refine hAt.mono ⟨?_,?_,?_,?_,trivial⟩
    · have h := hAt.2.2.2.2.2.1
      change (down.state lane).regs 1215 = some (b32 (laneOf l thread)) at h
      rwa [hLane] at h
    · exact hAt.2.2.2.2.2.2.2.1
    · rw [← schedulerWord_eq_drain]
      exact hAt.2.2.2.2.2.2.1
    · rw [← schedulerWord_eq_drain]
      exact hAt.2.2.2.2.1
  obtain ⟨s,hRun,hs⟩ := (firstTileGate l thread hl hp.shape.2.1 hBegin hFinish).apply hInput
  have hStart := (firstScanLocal (regs := []) (by decide) (by decide) hAt.1
    (by decide +kernel) (by decide +kernel) hRun).1
  have hNoBack (events : List Event) :
      ¬ TraceReach kernel Assumptions.all l thread (cur.state lane) events s := by
    intro h
    have hEnd := traceKeepsFloor h afterDrainFloorCode drainFloorSegments
      (show 7617 ≤ (cur.state lane).pc by rw [(cur.checkpoint lane hl).1]; decide)
    rw [hs.1] at hEnd
    omega
  obtain ⟨_,hActual⟩ := recordedCheckpointsPath (down.bounded lane hl) (cur.bounded lane hl)
    (down.recorded lane hl) ((down.localSteps lane hl).trans (run_rtg hStart))
    (cur.recorded lane hl) (cur.localSteps lane hl) hNoBack
  have hGuard := guardAlong hActual hs.1.ge (cur.checkpoint lane hl).1
    (by rw [hs.2.1]; decide)
  rw [hGuard,terminalRequestGuard,hLane]
  exact hs.2.2.2.2.2.2.2.1

end PTX.Kernels.TmlFa4Fwd.Softmax
