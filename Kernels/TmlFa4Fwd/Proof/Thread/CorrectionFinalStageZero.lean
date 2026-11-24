-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitNormalizedRow
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsRead
import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
import Lemmas.Step.ExitLast
import Lemmas.Execution.EventFrameSource
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue Softmax
open _root_.PTX.Kernels.TmlFa4Fwd.Mma (walkFromRun)
open PTX.Kernels.TmlFa4Fwd.Correction

/-- The selected launch frame and both rescale address tables are resident across all visits. -/
def rescaleFinalFrame (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  rescaleStageAddresses l (warpLane l g lane) 0 ++
    rescaleStageAddresses l (warpLane l g lane) 1 ++ correctionBeforeRescale p l g batch lane

private def preservesFinalFrame (regs : List Nat) (ins : Instr) : Bool :=
  (ins.op.isLocal || correctionReturningOp ins.op) &&
    (regs.all fun reg => !((writesRegs ins.op ++ scoreEventWrites ins.op).contains reg)) &&
    match ins.op with
    | .bra target _ => decide (8006 ≤ target ∧ target ≤ 8447)
    | .brx .. => false
    | _ => true

private theorem finalFrameInstruction {p : Params} {l : Launch} {g batch lane pc : Nat}
    {ins : Instr} (hLo : 8006 ≤ pc) (hHi : pc < 8447)
    (hCode : kernel.code[pc]? = some ins) :
    preservesFinalFrame ((rescaleFinalFrame p l g batch lane).map Prod.fst) ins = true := by
  let code := (kernel.code.drop 8006).take (8447-8006)
  have hCheck :
      code.all (preservesFinalFrame ((rescaleFinalFrame p l g batch lane).map Prod.fst)) =
        true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hCheck ins
  apply List.mem_of_getElem? (i := pc-8006)
  dsimp only [code]
  rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,hCode]

private theorem heldFinalFrame {regs more : Nat → Option Value} {facts : List (Nat × Value)}
    (h : Holds regs facts) (hKeep : ∀ r ∈ facts.map Prod.fst, more r = regs r) :
    Holds more facts := by
  induction facts with
  | nil => trivial
  | cons rv facts ih =>
    refine ⟨?_,ih h.2 (fun r hr => hKeep r (List.mem_cons_of_mem _ hr))⟩
    rw [hKeep rv.1 (by simp)]
    exact h.1

def FinalCutFrame (p : Params) (l : Launch) (g batch lane : Nat) (s : TState) : Prop :=
  8006 ≤ s.pc ∧ s.pc ≤ 8447 ∧ s.sub ≤ 3 ∧ SetupScratch s ∧
    Holds s.regs (rescaleFinalFrame p l g batch lane)

theorem finalCutStep {p : Params} {l : Launch} {g batch lane : Nat} {s u : TState}
    {ev : Option Event} (hs : FinalCutFrame p l g batch lane s) (hCut : s.pc ≠ 8447)
    (hStep : WStep kernel Assumptions.all l (warpLane l g lane) s ev u) :
    FinalCutFrame p l g batch lane u := by
  obtain ⟨hLo,hHi,hSub,hScratch,hFrame⟩ := hs
  have hBefore : s.pc < 8447 := by omega
  have hScratchNext := (correctionScratchStep (by omega) (by omega) hSub hScratch hStep).1
  have hInstruction {i : Instr} (he : kernel.code[s.pc]? = some i) :=
    finalFrameInstruction (p := p) (l := l) (g := g) (batch := batch) (lane := lane)
      hLo hBefore he
  have hPreserve {i : Instr} (he : kernel.code[s.pc]? = some i)
      {r : Nat} (hr : r ∈ (rescaleFinalFrame p l g batch lane).map Prod.fst) :
      r ∉ writesRegs i.op ++ scoreEventWrites i.op := by
    have hAudit := hInstruction he
    simp only [preservesFinalFrame,Bool.and_eq_true] at hAudit
    simpa using List.all_eq_true.mp hAudit.1.2 _ hr
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false]
      omega
    obtain ⟨ins,he,_,hLocal | hExec⟩ := correctionTauFrame hOff hTau
    · obtain ⟨rfl,_⟩ := hLocal
      exact ⟨by change 8006 ≤ s.pc+1; omega,by change s.pc+1 ≤ 8447; omega,
        by change 0 ≤ 3; decide,hScratchNext,hFrame⟩
    · obtain ⟨_,_,hL⟩ := hExec
      have hAudit := hInstruction he
      simp only [preservesFinalFrame,Bool.and_eq_true] at hAudit
      have hRange := hL.pc
      have hBounds : 8006 ≤ u.pc ∧ u.pc ≤ 8447 := by
        cases hop : ins.op <;> simp only [hop,nextPc,BrxTarget,or_false] at hRange
        case bra target aligned =>
          rw [hRange]
          exact of_decide_eq_true (by simpa only [hop] using hAudit.2)
        case brx => simp [hop] at hAudit
        all_goals omega
      exact ⟨hBounds.1,hBounds.2,hL.sub.trans_le hSub,hScratchNext,
        heldFinalFrame hFrame (fun r hr =>
          hL.regs r (fun h => hPreserve he hr (List.mem_append_left _ h)))⟩
  · obtain ⟨i,he,hNonlocal,_⟩ := estep_event_source hEvent
    have hAudit := hInstruction he
    simp only [preservesFinalFrame,Bool.and_eq_true,hNonlocal,Bool.false_or] at hAudit
    have hNoZero : 0 ∉ scoreEventWrites i.op := by
      have hAll : ((kernel.code.drop 8006).take (8447-8006)).all
          (fun ins => !(scoreEventWrites ins.op).contains 0) = true := by
        set_option maxRecDepth 100000 in kernel_rfl
      have hMem : i ∈ (kernel.code.drop 8006).take (8447-8006) := by
        apply List.mem_of_getElem? (i := s.pc-8006)
        rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,he]
      simpa using List.all_eq_true.mp hAll i hMem
    have progress := (correctionEventProgress he hAudit.1.1 hSub hNoZero hEvent).1
    have hBounds : 8006 ≤ u.pc ∧ u.pc ≤ 8447 := by
      rcases progress.pc with ⟨hPc,_⟩ | ⟨hPc,_⟩ <;> omega
    refine ⟨hBounds.1,hBounds.2,progress.sub,hScratchNext,heldFinalFrame hFrame ?_⟩
    intro r hr
    exact (correctionEventProgress he hAudit.1.1 hSub
      (fun h => hPreserve he hr (List.mem_append_right _ h)) hEvent).2

private theorem finalCutWalk {p : Params} {l : Launch} {g batch lane : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hWalk : Walk kernel Assumptions.all l
      (warpLane l g lane) s es vs) (hs : FinalCutFrame p l g batch lane s) :
    (∀ e ∈ es, e.pc < 8447) ∨
      ∃ u pre rest more, es = pre ++ rest ∧ FinalCutFrame p l g batch lane u ∧ u.pc = 8447 ∧
        (∀ e ∈ pre, e.pc < 8447) ∧
        Walk kernel Assumptions.all l (warpLane l g lane) u rest more := by
  induction hWalk with
  | stop => exact .inl (by simp)
  | @tau t u es vs hTau hWalk ih =>
    by_cases hCut : t.pc = 8447
    · exact .inr ⟨t,[],es,_,rfl,hs,hCut,by simp,.tau hTau hWalk⟩
    exact ih (finalCutStep hs hCut (.inl ⟨rfl,hTau⟩))
  | @ev t u e es vs hEvent hWalk ih =>
    by_cases hCut : t.pc = 8447
    · exact .inr ⟨t,[],e::es,_,rfl,hs,hCut,by simp,.ev hEvent hWalk⟩
    have hSite := estep_source_pc hEvent
    have hPc : e.pc < 8447 := by have := hs.2.1; omega
    rcases ih (finalCutStep hs hCut (.inr ⟨e,rfl,hEvent⟩)) with hShort | hLong
    · exact .inl (fun event hm =>
        (List.mem_cons.mp hm).elim (fun h => h.symm ▸ hPc) (hShort event))
    · obtain ⟨v,pre,rest,more,hList,hV,hPC,hBefore,hAfter⟩ := hLong
      exact .inr ⟨v,e::pre,rest,more,by rw [hList]; rfl,hV,hPC,
        fun event hm => (List.mem_cons.mp hm).elim (fun h => h.symm ▸ hPc) (hBefore event),
        hAfter⟩
  | @last t e hEvent =>
    by_cases hCut : t.pc = 8447
    · exact .inr ⟨t,[],[e],_,rfl,hs,hCut,by simp,.last hEvent⟩
    exact .inl (by
      intro event hm
      obtain rfl := List.mem_singleton.mp hm
      have hSite := estep_source_pc hEvent
      have := hs.2.1
      omega)


private theorem terminalRunFromWalk {l : Launch} {g tag : Nat} {s : TState}
    {es : List Event} {visits : List Visit} (hWalk : Walk kernel Assumptions.all l g s es visits)
    (hExit : (⟨tag,.exit⟩ : Event) ∈ es) : Run kernel Assumptions.all l g s es none := by
  induction hWalk with
  | stop => cases hExit
  | tau hTau _ ih =>
    cases ih hExit with
    | step hLocal he hn => exact .step (.head hTau hLocal) he hn
    | last hLocal he => exact .last (.head hTau hLocal) he
  | ev hEvent _ ih =>
    obtain ⟨_,_,hFire⟩ := hEvent
    exact .step .refl ⟨_,by assumption,hFire⟩
      (ih ((List.mem_cons.mp hExit).resolve_left hFire.not_exit.symm))
  | last hEvent => exact .last .refl hEvent

/-- A completed correction lane retains its selected tile frame through all
rescale iterations and reaches the actual first terminal statistics cursor. -/
theorem observedFinalStageZeroEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    {g batch lane : Nat} (hg : g < l.threads)
    (hWarpLo : 8 ≤ warpIndex l g) (hWarpHi : warpIndex l g < 12) (hl : lane < 32)
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ pos u, At u (statsBarrierPc 0 false) (correctionFinalStageFacts p l g batch lane 0 0 0) ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop pos) none := by
  let thread := warpLane l g lane
  let blocks := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨hCuQ,hUsedK⟩ := hFootprint.metadataProtected hp
  have hWarp := (PTX.Step.sameWarp_lane (L := l) (by rw [hp.block]) hg hl).1
  have hThread : thread < l.threads := hWarp.1.2.1
  have hCta : thread/l.block = g/l.block := hWarp.1.2.2.symm
  have hRole : warpIndex l thread = warpIndex l g := hWarp.2.symm
  obtain ⟨finish,⟨pc,kind⟩,hExit,hKind⟩ := exitedOfComplete hX hDone hThread
  change kind = .exit at hKind
  subst kind
  have hLast := Execution.exit_last hX hThread hExit
  obtain ⟨arrival,_,_,hArrival⟩ :=
    finalAllocationArrivalBeforeExit hp hX (g := thread) (by omega) ⟨pc,hExit⟩
  have hAt := hArrival.correctionDecoded hp hX (hRole.symm ▸ hWarpLo) (hRole.symm ▸ hWarpHi)
  obtain ⟨index,address,words,he⟩ :=
    correctionFinalOutputLoadOfActiveTail hp hX (hRole.symm ▸ hWarpLo)
      (hRole.symm ▸ hWarpHi) (hCta.symm ▸ hWork) hAt
  obtain ⟨chosen,hChosen,hBegin,hEnd,ends,_,_,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarpLo hWarpHi hl hWork
      (by change 7884 < finalizeLoadPc 1 0; decide) he
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hEq := (hUnique chosen ⟨hChosen,hBegin,hEnd⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst chosen
  have hRun := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨s,hs,hIndex,_,_,_,hSuffix⟩ := correctionLaneBeforeRescaleOfEvent hp hX hb hLo hHi
    (active.checkpoint lane hl) hRun hUsedK hActive.before
    (by change 7988 < finalizeLoadPc 1 0; decide) he
  obtain ⟨_,u,hLocal,hU⟩ := correctionLaneRescaleSetup hp hb hLo hHi hs
  let start := active.pos lane+6
  let suffix := (X.tr thread).drop start
  have hLen : index < (X.tr thread).length := len_of_get he
  have hStart : start ≤ index := hIndex
  have hAtExit : suffix[finish-start]? = some ⟨pc,.exit⟩ := by
    unfold suffix
    rwa [List.getElem?_drop,Nat.add_sub_of_le (show start ≤ finish by omega)]
  have hEnded : ends lane = none := by
    cases h : ends lane with
    | none => rfl
    | some final =>
      rw [h] at hSuffix
      exact (hSuffix.no_exit hAtExit).elim
  rw [hEnded] at hSuffix
  have hRest := hSuffix.after_local (run_rtg hLocal)
  have hFinal : ∃ advanced t, At t 8447 (correctionBeforeRescale p l g batch lane) ∧
      Run kernel Assumptions.all l thread t ((X.tr thread).drop advanced) none := by
    change At u (if blocks < 2 then 8447 else 8006)
      (correctionRescaleSetupFacts p l g batch lane) at hU
    by_cases hSkip : blocks < 2
    · have hReady : At u 8447 (correctionBeforeRescale p l g batch lane) := by
        simpa only [blocks,correctionRescaleSetupFacts,ite_eq_left hSkip] using hU
      exact ⟨start,u,hReady,hRest⟩
    have hSetup : u.pc = 8006 := by simpa only [ite_eq_right hSkip] using hU.1
    have hHeld : Holds u.regs (rescaleFinalFrame p l g batch lane) := by
      have hHolds := hU.2.2.2.2
      unfold correctionRescaleSetupFacts at hHolds
      rw [ite_eq_right hSkip] at hHolds
      exact hHolds.2
    have hSeed : FinalCutFrame p l g batch lane u :=
      ⟨hSetup.ge,by omega,by rw [hU.2.1]; decide,
        SetupScratch.clear hU.2.1 hU.2.2.1,hHeld⟩
    obtain ⟨_,hWalk⟩ := walkFromRun (show Run kernel Assumptions.all l thread u suffix none
      from hRest)
    let target : Event := ⟨finalizeLoadPc 1 0,.tc (.ld address words .s32x32b)⟩
    have hTarget : target ∈ suffix := by
      apply List.mem_of_getElem? (i := index-start)
      rw [show suffix = (X.tr thread).drop start from rfl,List.getElem?_drop,
        Nat.add_sub_of_le hStart]
      exact he
    rcases finalCutWalk hWalk hSeed with hBefore | hAfter
    · have hBad := hBefore target hTarget
      exact ((by decide : ¬ finalizeLoadPc 1 0 < 8447) hBad).elim
    obtain ⟨v,pre,rest,_,hList,hV,hCut,hBefore,hTail⟩ := hAfter
    have hNeed : pre.length ≤ index-start := by
      by_contra! hSmall
      have hGet : pre[index-start]? = some target := by
        rw [← List.getElem?_append_left hSmall,← hList]
        rw [show suffix = (X.tr thread).drop start from rfl,List.getElem?_drop,
          Nat.add_sub_of_le hStart]
        exact he
      exact (by decide : ¬ finalizeLoadPc 1 0 < 8447) (hBefore target (List.mem_of_getElem? hGet))
    have hListRest : rest = (X.tr thread).drop (start+pre.length) := by
      rw [← List.drop_drop,show (X.tr thread).drop start = suffix from rfl,hList,List.drop_left]
    have hLateExit : (⟨pc,.exit⟩ : Event) ∈ rest := by
      rw [hListRest]
      apply List.mem_of_getElem? (i := finish-(start+pre.length))
      rw [List.getElem?_drop,Nat.add_sub_of_le (show start+pre.length ≤ finish by omega)]
      exact hExit
    have hLocalEnd := finalizeScaleInstruction
    obtain ⟨i,hCode,_,hLocalEnd⟩ := hLocalEnd
    have hClear := scratchLocal hV.2.2.2.1 (hCut.symm ▸ hCode) hLocalEnd
    have hFault : v.fault = none := by
      cases hError : v.fault with
      | none => rfl
      | some fault =>
        exfalso
        cases hTail with
        | stop => cases hLateExit
        | tau hTau _ => simp [Tau,out,hError] at hTau
        | ev hEvent _ =>
          obtain ⟨effect,hEffect,hFires⟩ := hEvent
          have hEq : effect = .ub fault := by simpa [out,hError] using hEffect.symm
          subst effect
          cases hFires.2
        | last hEvent =>
          obtain rfl := List.mem_singleton.mp hLateExit
          obtain ⟨effect,hEffect,hFires⟩ := hEvent
          have hEq : effect = .ub fault := by simpa [out,hError] using hEffect.symm
          subst effect
          cases congrArg Event.kind hFires.1
    have hHeld := (holds_append _ _ _).1 hV.2.2.2.2 |>.2
    exact ⟨start+pre.length,v,⟨hCut,hClear.1,hClear.2,hFault,hHeld⟩,
      hListRest ▸ terminalRunFromWalk hTail hLateExit⟩
  obtain ⟨pos,v,hV,hr⟩ := hFinal
  obtain ⟨w,hW,hTail⟩ := finalStageZeroEntry hp hV hr
  exact ⟨pos+1,w,hW,hTail⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
