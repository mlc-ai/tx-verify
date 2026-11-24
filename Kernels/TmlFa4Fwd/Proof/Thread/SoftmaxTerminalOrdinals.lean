-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalWarp
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxActiveScoreProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBallotWindow
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxLaneRegister
import all Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.NotShfl
import Lemmas.Flow.RecordedCheckpointPath
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame Prologue Epilogue Thread Correction

private theorem afterTerminalDown {l : Launch} {g : Nat} {s t : TState} {e : Event}
    (hc : s.pc = 7622) (he : EStep kernel Assumptions.all l g s e (some t)) :
    t.pc = 7623 := by
  obtain ⟨i,hCode,_,hFire⟩ := estep_event_source he
  rw [hc,Flow.code_7622] at hCode
  obtain rfl := Option.some.inj hCode
  change Fires s.pc (shflTmpl l g s .down 5815 none (.reg 7259)
    (.imm 1) (.imm 31) (.imm (-1))) e (some t) at hFire
  unfold shflTmpl at hFire
  split at hFire
  · split at hFire
    · split at hFire
      · obtain ⟨_,_,_,hRet⟩ := hFire
        rw [Option.some.inj hRet]
        simp only [next,setReg,hc]
      · simp [Fires] at hFire
    · simp [Fires] at hFire
  all_goals simp [Fires] at hFire

private theorem openingMarksInDrainInterval {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (hPath : TraceReach kernel Assumptions.all l g s events t)
    (hStart : 3274 ≤ s.pc) (hEnd : t.pc = 7622) :
    events.countP Execution.isShfl = 0 ∧ events.countP isFullWarpVote = 0 := by
  let span : RowDrainSpan := ⟨3274,7622,7623⟩
  have hLo : (kernel.code.drop 3274).all (fun i => staysPastEvent 3274 i.op) = true := by
    set_option maxRecDepth 100000 in decide +kernel
  have hSites : ∀ pc, 3274 ≤ pc → pc ∈ Assumptions.swExp2Sites → ∀ seg,
      cuteExp2.matchAt kernel pc = some seg → 3274 ≤ seg.stop :=
    schedulerSegmentBound (show segmentFloor 3274 = true by
      set_option maxRecDepth 100000 in decide +kernel)
  have hAfter : (kernel.code.drop 7623).all (fun i => staysPastEvent 7623 i.op) = true := by
    set_option maxRecDepth 100000 in decide +kernel
  have hEndSites : ∀ pc ∈ Assumptions.swExp2Sites, pc < 7623 := fun pc hm =>
    (of_decide_eq_true (List.all_eq_true.mp noSegmentsInDrain pc hm)).trans_le (by decide)
  have hCode : ((kernel.code.drop 3274).take (7622-3274)).all
      (fun i => !i.op.isShfl && !voteDataOp i.op) = true := by
    set_option maxRecDepth 100000 in decide +kernel
  have hStep {s u : TState} {e : Option Event} (hs : 3274 ≤ s.pc)
      (he : WStep kernel Assumptions.all l g s e u) : 3274 ≤ u.pc :=
    Thread.eventTailStep hLo hSites hs he
  induction hPath with
  | refl => exact ⟨rfl,rfl⟩
  | tau hTau _ ih => exact ih (hStep hStart (.inl ⟨rfl,hTau⟩)) hEnd
  | @event s u t events e he hTail ih =>
    have hNext := hStep hStart (.inr ⟨_,rfl,he⟩)
    have hBelow : s.pc < 7622 := by
      by_contra! h
      have hu : 7623 ≤ u.pc := by
        by_cases hEq : s.pc = 7622
        · rw [afterTerminalDown hEq he]
        · exact Thread.eventTailStep hAfter
            (fun pc hpc hm _ _ => (Nat.not_lt_of_ge hpc (hEndSites pc hm)).elim)
            (by omega : 7623 ≤ s.pc) (.inr ⟨_,rfl,he⟩)
      have hPast := span.traceAboveExit hTail hAfter hEndSites hu
      change 7623 ≤ t.pc at hPast
      rw [hEnd] at hPast
      omega
    obtain ⟨i,hAt,_,hFire⟩ := estep_event_source he
    have hMem : i ∈ (kernel.code.drop 3274).take (7622-3274) := by
      apply List.mem_of_getElem? (i := s.pc-3274)
      rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hStart]
    have hs := List.all_eq_true.mp hCode i hMem
    simp only [Bool.and_eq_true] at hs
    have hNoShuffle : Execution.isShfl e = false := by
      by_contra h
      have heOp := fires_shfl_op hFire (by simpa using h)
      have hBad := hs.1
      rw [heOp] at hBad
      cases hBad
    have hNoVote : isFullWarpVote e = false := by
      by_contra h
      have hVote : isVoteData e = true := by
        have hTrue : isFullWarpVote e = true := by simpa using h
        cases hKind : voteClass e.kind <;> simp [isWarpVote,isVoteData,hKind] at hTrue ⊢
      have heOp := fires_voteData_op hFire hVote
      have hBad := hs.2
      rw [heOp] at hBad
      cases hBad
    obtain ⟨hS,hV⟩ := ih hNext hEnd
    exact ⟨by simp [hNoShuffle,hS],by simp [hNoVote,hV]⟩

/-- Event-silent warp ordinals between selected active coordinates and the first terminal rescan. -/
theorem terminalOrdinalsOfActiveCursor {l : Launch} {X : Execution} {g : Nat}
    {F G : List (Nat × Value)} (source : OpeningTripCursor l X g 3274 F)
    (target : OpeningTripCursor l X g 7622 G) :
    let old := (X.tr g).take source.pos
    let new := (X.tr g).take target.pos
    new.countP Execution.isShfl = old.countP Execution.isShfl ∧
      new.countP isFullWarpVote = old.countP isFullWarpVote := by
  have hNoBack (events : List Event) :
      ¬TraceReach kernel Assumptions.all l g target.ready events source.ready := by
    intro h
    let span : RowDrainSpan := ⟨3274,7622,7622⟩
    have hFloor : (kernel.code.drop span.bypass).all
        (fun i => staysPastEvent span.bypass i.op) = true := by
      set_option maxRecDepth 100000 in decide +kernel
    have hSites : ∀ pc ∈ Assumptions.swExp2Sites, pc < span.bypass := fun pc hm =>
      (of_decide_eq_true (List.all_eq_true.mp noSegmentsInDrain pc hm)).trans_le (by decide)
    have hPast := span.traceAboveExit h hFloor hSites target.checkpoint.1.ge
    rw [source.checkpoint.1] at hPast
    exact (by decide : ¬7622 ≤ 3274) hPast
  obtain ⟨hPos,hPath⟩ := recordedCheckpointsPath source.bounded target.bounded source.recorded
    source.localSteps target.recorded target.localSteps hNoBack
  obtain ⟨hNoShfl,hNoVote⟩ := openingMarksInDrainInterval hPath source.checkpoint.1.ge
    target.checkpoint.1
  have hSplit : (X.tr g).take target.pos = (X.tr g).take source.pos ++
      ((X.tr g).drop source.pos).take (target.pos-source.pos) := by
    have h := List.take_append_drop source.pos ((X.tr g).take target.pos)
    simpa only [List.take_take,Nat.min_eq_left hPos,List.drop_take] using h.symm
  dsimp only
  simp only [hSplit,List.countP_append,hNoShfl,hNoVote,Nat.add_zero,and_self]

end PTX.Kernels.TmlFa4Fwd.Softmax
