-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxCuQProgress
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import all Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame

private def laneRegisterAudit (ins : Instr) : Bool :=
  (ins.op.isLocal || scoreEventOp ins.op) &&
    !(writesRegs ins.op ++ scoreEventWrites ins.op).contains 1215

set_option maxRecDepth 100000 in
private theorem laneRegisterCode :
    ((kernel.code.drop 3111).take (7617-3111)).all laneRegisterAudit = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem laneRegisterSegments : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => !(scoreSegmentWrites seg).contains 1215
    | none => false) = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem beforeSchedulerFloorCode :
    (kernel.code.drop 3112).all (fun ins => Thread.staysPastEvent 3112 ins.op) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem afterDrainFloorCode :
    (kernel.code.drop 7617).all (fun ins => Thread.staysPastEvent 7617 ins.op) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem schedulerFloorCode :
    (kernel.code.drop 3111).all (fun ins => Thread.staysPastEvent 3111 ins.op) = true := by
  decide +kernel

private noncomputable def segmentFloor (floor : Nat) : Bool :=
  Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (floor ≤ seg.stop)
    | none => false)

private theorem traceKeepsFloor {l : Launch} {g floor : Nat} {s t : TState}
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events t)
    (hCode : (kernel.code.drop floor).all (fun ins => Thread.staysPastEvent floor ins.op) = true)
    (hSegments : ∀ site, floor ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop) (hs : floor ≤ s.pc) :
    floor ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau he _ ih => exact ih (Thread.eventTailStep hCode hSegments hs (.inl ⟨rfl,he⟩))
  | event he _ ih => exact ih (Thread.eventTailStep hCode hSegments hs (.inr ⟨_,rfl,he⟩))

private theorem laneRegisterAt {pc : Nat} {ins : Instr}
    (hLo : 3111 ≤ pc) (hHi : pc < 7617) (hc : kernel.code[pc]? = some ins) :
    laneRegisterAudit ins = true := by
  apply List.all_eq_true.mp laneRegisterCode ins
  apply List.mem_of_getElem? (i := pc-3111)
  rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]

private theorem laneRegisterStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 3111 ≤ s.pc) (hHi : s.pc < 7617) (hSub : s.sub ≤ 3)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    u.sub ≤ 3 ∧ u.regs 1215 = s.regs 1215 := by
  rcases hStep with ⟨rfl,hTau⟩ | ⟨_,rfl,hEvent⟩
  · obtain ⟨ins,hCode,_,hBody⟩ := tauScoreSource hTau
    rcases hBody with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
    · exact ⟨by simp [skip],rfl⟩
    rcases scoreExecLocal hLocal with hFrame | ⟨m,hSite,hMatch,hExec⟩
    · have hKeep := (Bool.and_eq_true_iff.mp (laneRegisterAt hLo hHi hCode)).2
      have hNo : 1215 ∉ writesRegs ins.op ++ scoreEventWrites ins.op := by simpa using hKeep
      refine ⟨?_,hFrame.regs _ (fun hr => hNo (List.mem_append_left _ hr))⟩
      rw [hFrame.sub]
      exact hSub
    · have hAudit := List.all_eq_true.mp laneRegisterSegments _ hSite
      rw [hMatch] at hAudit
      have hNo : 1215 ∉ scoreSegmentWrites m := by simpa using hAudit
      obtain ⟨_,hClear,_,hKeep⟩ := scoreSegmentFrame hExec
      exact ⟨by omega,hKeep _ hNo⟩
  · obtain ⟨ins,hCode,hNonlocal,_⟩ := estep_event_source hEvent
    have hAudit := laneRegisterAt hLo hHi hCode
    simp only [laneRegisterAudit,Bool.and_eq_true,hNonlocal,Bool.false_or] at hAudit
    have hKeep : 1215 ∉ writesRegs ins.op ++ scoreEventWrites ins.op := by
      simpa using hAudit.2
    obtain ⟨hProgress,hReg⟩ := scoreEventStep hCode hAudit.1 hSub
      (fun hr => hKeep (List.mem_append_right _ hr)) hEvent
    exact ⟨hProgress.sub,hReg⟩

private theorem lowerSegmentBound : segmentFloor 3111 = true := by decide +kernel

private theorem afterSchedulerSegmentBound : segmentFloor 3112 = true := by decide +kernel



private theorem noSegmentsInDrain :
    Assumptions.swExp2Sites.all (fun site => decide (site < 7617)) = true := by decide +kernel

private theorem drainFloorSegments (site : Nat) (hLo : 7617 ≤ site)
    (hSite : site ∈ Assumptions.swExp2Sites) (seg : SegMatch CuteSlot)
    (_ : cuteExp2.matchAt kernel site = some seg) : 7617 ≤ seg.stop := by
  have hLt := of_decide_eq_true (List.all_eq_true.mp noSegmentsInDrain site hSite)
  omega

private theorem schedulerSegmentBound {floor : Nat} (h : segmentFloor floor = true)
    (site : Nat) (_ : floor ≤ site) (hSite : site ∈ Assumptions.swExp2Sites)
    (seg : SegMatch CuteSlot) (hMatch : cuteExp2.matchAt kernel site = some seg) :
    floor ≤ seg.stop := by
  have hAudit := List.all_eq_true.mp h site hSite
  rw [hMatch] at hAudit
  exact of_decide_eq_true hAudit

private theorem laneRegisterAlong {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (hPath : TraceReach kernel Assumptions.all l g s events t)
    (hLo : 3111 ≤ s.pc) (hSub : s.sub ≤ 3) (hEnd : t.pc < 7617) :
    t.regs 1215 = s.regs 1215 := by
  have next {s u t : TState} {e : Option Event} {es : List Event}
      (hs : 3111 ≤ s.pc) (hSub : s.sub ≤ 3)
      (hStep : WStep kernel Assumptions.all l g s e u)
      (hRest : TraceReach kernel Assumptions.all l g u es t) (hEnd : t.pc < 7617) :
      3111 ≤ u.pc ∧ u.sub ≤ 3 ∧ u.regs 1215 = s.regs 1215 := by
    have hHi : s.pc < 7617 := by
      by_contra! hPast
      have hNext := Thread.eventTailStep afterDrainFloorCode drainFloorSegments hPast hStep
      exact (Nat.not_le_of_lt hEnd)
        (traceKeepsFloor hRest afterDrainFloorCode drainFloorSegments hNext)
    exact ⟨Thread.eventTailStepOfAudit schedulerFloorCode lowerSegmentBound hs hStep,
      laneRegisterStep hs hHi hSub hStep⟩
  induction hPath with
  | refl => rfl
  | tau hTau hRest ih =>
    obtain ⟨hL,hS,hReg⟩ := next hLo hSub (.inl ⟨rfl,hTau⟩) hRest hEnd
    exact (ih hL hS hEnd).trans hReg
  | event hEv hRest ih =>
    obtain ⟨hL,hS,hReg⟩ := next hLo hSub (.inr ⟨_,rfl,hEv⟩) hRest hEnd
    exact (ih hL hS hEnd).trans hReg

/-- Every actual checkpoint in the arithmetic body retains the lane index
initialized during the softmax scheduler startup. -/
theorem laneRegisterOfMaximalCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {g n : Nat} (hg : g < l.threads)
    (hw : Prologue.warpIndex l g < 8) {s t : TState}
    (hLo : 3112 ≤ t.pc) (hHi : t.pc < 7617) (hBound : n ≤ (X.tr g).length)
    (hRecorded : Run kernel Assumptions.all l g {} ((X.tr g).take n) (some s))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t) :
    t.regs 1215 = some (b32 (laneOf l g)) := by
  obtain ⟨j,b,u,_,_,hJ,_,_,hu,hPast,_,hSteps⟩ :=
    firstShuffleCursorOfMaximal hp hMax hg hw (hCuQ _)
  have hNoBack events : ¬ TraceReach kernel Assumptions.all l g t events u := by
    intro h
    have hFloor := traceKeepsFloor h beforeSchedulerFloorCode
      (schedulerSegmentBound afterSchedulerSegmentBound) hLo
    rw [hu.1] at hFloor
    omega
  obtain ⟨_,hPath⟩ := recordedCheckpointsPath hJ hBound hPast hSteps hRecorded hLocal hNoBack
  have hStart : 3111 ≤ u.pc := hu.1.ge
  have hSub : u.sub ≤ 3 := by rw [hu.2.1]; decide
  exact (laneRegisterAlong hPath hStart hSub hHi).trans hu.2.2.2.2.1

end PTX.Kernels.TmlFa4Fwd.Softmax
