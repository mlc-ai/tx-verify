-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFinalStageZero
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleVisitObserved
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleOrdinalWait
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsRead
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
import Lemmas.Step.ExitLast
import Lemmas.Flow.ContinuingEvent
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction

private theorem traceToReturningWalk {l : Launch} {g : Nat} {s t u : TState}
    {es : List Event} {e : Event}
    (ht : TraceReach kernel Assumptions.all l g s es t)
    (he : EStep kernel Assumptions.all l g t e (some u)) :
    ∃ visits, Walk kernel Assumptions.all l g s (es++[e]) visits := by
  induction ht with
  | refl => exact ⟨_,.ev he (.stop u)⟩
  | tau hLocal _ ih =>
    obtain ⟨_,hWalk⟩ := ih he
    exact ⟨_,.tau hLocal hWalk⟩
  | event hEvent _ ih =>
    obtain ⟨_,hWalk⟩ := ih he
    exact ⟨_,.ev hEvent hWalk⟩

set_option maxRecDepth 100000 in
private theorem finalizationFloor :
    (kernel.code.drop 8447).all (fun i => staysPastEvent 8447 i.op) = true := by kernel_rfl

variable {p : Params} {l : Launch}

private theorem keepFinalFrameThroughWait {g batch lane : Nat} {s t u : TState} {es : List Event}
    {event : Event} (ht : TraceReach kernel Assumptions.all l (warpLane l g lane) s es t)
    (he : EStep kernel Assumptions.all l (warpLane l g lane) t event (some u))
    (hEarly : event.pc < 8447) (hs : FinalCutFrame p l g batch lane s) :
    FinalCutFrame p l g batch lane t := by
  have hBefore {a : TState} {pre : List Event}
      (hPath : TraceReach kernel Assumptions.all l (warpLane l g lane) a pre t) :
      a.pc ≠ 8447 := by
    intro hSame
    obtain ⟨_,hWalk⟩ := traceToReturningWalk hPath he
    have hFloor := eventTailEventsOfSegmentFloor (floor := 8447)
      finalizationFloor (by
        intro site hs hm
        simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
        omega) hWalk hSame.ge event (by simp)
    omega
  induction ht with
  | refl => exact hs
  | tau hLocal hPath ih =>
    exact ih he (finalCutStep hs (hBefore (.tau hLocal hPath)) (.inl ⟨rfl,hLocal⟩)) hBefore
  | event hEvent hPath ih =>
    exact ih he (finalCutStep hs (hBefore (.event hEvent hPath)) (.inr ⟨_,rfl,hEvent⟩)) hBefore

private theorem returningEventWithPrefix {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {i : Nat} {e : Event} {endState : Option TState}
    (hr : Run kernel Assumptions.all l g s es endState)
    (he : es[i]? = some e) (hi : i+1 < es.length) :
    ∃ t u, TraceReach kernel Assumptions.all l g s (es.take i) t ∧
      EStep kernel Assumptions.all l g t e (some u) ∧
      Run kernel Assumptions.all l g u (es.drop (i+1)) endState := by
  induction hr generalizing i with
  | nil => simp at hi
  | last => simp at hi
  | step hLocal hEvent hRest ih =>
    cases i with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨_,_,TraceReach.of_local hLocal,hEvent,hRest⟩
    | succ i =>
      obtain ⟨t,u,hReach,hStep,hRun⟩ := ih (by simpa using he) (by simpa using hi)
      exact ⟨t,u,(TraceReach.of_local hLocal).append (.event hEvent hReach),hStep,hRun⟩

/-- The actual wait on one rescale generation retains the physical address
tables and the row's chosen work frame. -/
theorem rescaleWaitStateOfCompletedWork {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFootprint : OutputFootprint p X) {g batch lane pos : Nat} (hg : g < l.threads)
    (hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hl : lane < 32) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (stage : Fin 2)
    (hWait : CorrectionWaits X (warpLane l g lane,pos) .rescale stage) :
    ∃ t, At t (statsBarrierPc stage true) (rescaleFinalFrame p l g batch lane) ∧
      Run kernel Assumptions.all l (warpLane l g lane) t
        ((X.tr (warpLane l g lane)).drop pos) none := by
  let thread := warpLane l g lane
  let blocks := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨hCuQ,hUsedK⟩ := hFootprint.metadataProtected hp
  obtain ⟨e,he,hEvent⟩ := hWait
  have hTag : e.pc = statsBarrierPc stage true := correctionRescaleWaitSite hEvent
  have hEarlier : e.pc < 8447 := by rw [hTag]; fin_cases stage <;> decide
  have hLater : 7988 < e.pc := by rw [hTag]; fin_cases stage <;> decide
  have hWarp' := (PTX.Step.sameWarp_lane (L := l) (by rw [hp.block]) hg hl).1
  have hThread : thread < l.threads := hWarp'.1.2.1
  obtain ⟨endIndex,⟨endTag,k⟩,hEnd,hKind⟩ := exitedOfComplete hX hDone hThread
  change k = .exit at hKind
  subst k
  obtain ⟨selected,hSelected,hSLo,hSHi,ends,_,_,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarp.1 hWarp.2 hl hWork (by omega) he
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hSame := (hUnique selected ⟨hSelected,hSLo,hSHi⟩).trans
    (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst selected
  have hRun := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨s,hs,hPos,_,_,_,hSuffix⟩ := correctionLaneBeforeRescaleOfEvent hp hX hb hLo hHi
    (active.checkpoint lane hl) hRun hUsedK hActive.before hLater he
  obtain ⟨_,u,hLocal,hU⟩ := correctionLaneRescaleSetup hp hb hLo hHi hs
  let start := active.pos lane+6
  let suffix := (X.tr thread).drop start
  let relative := pos-start
  have hBefore : start ≤ pos := hPos
  have hLen : pos < (X.tr thread).length := len_of_get he
  have hLast : endIndex+1 = (X.tr thread).length := Execution.exit_last hX hThread hEnd
  have hNotExit : pos ≠ endIndex := by
    intro hSame
    have hBar := correctionStatsWait hp hX he hEvent
    have hSameEvent := congrArg Event.kind (Option.some.inj ((hSame ▸ he).symm.trans hEnd))
    rw [hBar] at hSameEvent
    cases hSameEvent
  have hGetExit : suffix[endIndex-start]? = some ⟨endTag,.exit⟩ := by
    rw [show suffix = (X.tr thread).drop start from rfl,List.getElem?_drop,
      Nat.add_sub_of_le (show start ≤ endIndex by omega)]
    exact hEnd
  have hEnding : ends lane = none := by
    cases hCase : ends lane with
    | none => rfl
    | some stop =>
      rw [hCase] at hSuffix
      exact (hSuffix.no_exit hGetExit).elim
  rw [hEnding] at hSuffix
  have hActual := hSuffix.after_local (run_rtg hLocal)
  have hGet : suffix[relative]? = some e := by
    unfold suffix relative
    rw [List.getElem?_drop,Nat.add_sub_of_le hBefore]
    exact he
  have hRoom : relative+1 < suffix.length := by
    dsimp [relative,suffix]
    rw [List.length_drop]
    omega
  obtain ⟨t,u',hReaches,hStep,hRest⟩ := returningEventWithPrefix hActual hGet hRoom
  have hTarget : t.pc = statsBarrierPc stage true := (estep_source_pc hStep).symm.trans hTag
  have hGe : 2 ≤ blocks := by
    obtain ⟨b,hb',hLo',hHi',hPositive,hWithin⟩ :=
      rescaleWaitOrdinalBoundsBeforeTerminal hp hX (hWarp'.1.2.2 ▸ hWork) hUsedK
        (show CorrectionWaits X (thread,pos) .rescale stage from ⟨e,he,hEvent⟩)
    have hOwner : g/l.block = thread/l.block := hWarp'.1.2.2
    rw [← hOwner] at hLo' hHi' hWithin
    have hSame := (hUnique b ⟨hb',hLo',hHi'⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
    subst b
    change _ < blocks at hWithin
    omega
  have hStart : u.pc = 8006 := by
    have hPC := hU.1
    split at hPC <;> omega
  have hHeld : Holds u.regs (rescaleFinalFrame p l g batch lane) := by
    have hFacts := hU.2.2.2.2
    unfold correctionRescaleSetupFacts at hFacts
    rw [ite_eq_right (show ¬ blocks < 2 by omega)] at hFacts
    exact hFacts.2
  have hSeed : FinalCutFrame p l g batch lane u :=
    ⟨hStart.ge,by omega,by rw [hU.2.1]; decide,
      SetupScratch.clear hU.2.1 hU.2.2.1,hHeld⟩
  have hFrame := keepFinalFrameThroughWait hReaches hStep hEarlier hSeed
  have hClean : t.fault = none := by
    cases hFault : t.fault with
    | none => rfl
    | some fault =>
      obtain ⟨effect,hOut,hFire⟩ := hStep
      have hEffect : effect = .ub fault := by simpa [out,hFault] using hOut.symm
      subst effect
      cases hFire.2
  have hCode := hTarget.symm ▸ statsBarrierCode stage true
  have hSub := hFrame.2.2.2.1.namedWaitSubZero hCode
  have hTail : Run kernel Assumptions.all l thread u' ((X.tr thread).drop (pos+1)) none := by
    have hIndex : start+(relative+1) = pos+1 := by dsimp [relative]; omega
    change active.pos lane+6+(relative+1) = pos+1 at hIndex
    simpa only [suffix,List.drop_drop,hIndex] using hRest
  have hDrop : (X.tr thread).drop pos = e::(X.tr thread).drop (pos+1) := by
    have h := List.drop_eq_getElem_cons hLen
    have hEq := Option.some.inj ((List.getElem?_eq_getElem hLen).symm.trans he)
    rwa [hEq] at h
  refine ⟨t,⟨hTarget,hSub,hFrame.2.2.2.1.clearAccumulator,hClean,hFrame.2.2.2.2⟩,?_⟩
  rw [hDrop]
  exact .step .refl hStep hTail

private theorem finalFrameForRescale (p : Params) (l : Launch) (g batch lane : Nat)
    (stage : Fin 2) :
    RescaleVisitFrame l (warpLane l g lane) stage (rescaleFinalFrame p l g batch lane) := by
  have hIn {rv : Nat × Value} (hm : rv ∈ correctionBeforeRescale p l g batch lane) :
      rv ∈ rescaleFinalFrame p l g batch lane :=
    List.mem_append.mpr (.inr hm)
  refine ⟨hIn ?_,hIn ?_,?_,hIn ?_,hIn ?_,?_,?_,?_⟩
  · fin_cases stage <;> simp [correctionBeforeRescale,tileSetupFrame,
      correctionTileGeometryFacts,statsBarrierReg]
  · simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts]
  · intro rv hm
    apply List.mem_append.mpr
    left
    apply List.mem_append.mpr
    fin_cases stage
    · exact .inl hm
    · exact .inr hm
  · fin_cases stage <;> simp [correctionBeforeRescale,tileSetupFrame,correctionActiveTileFacts,
      correctionTileFrame,afterCreditFacts,creditFacts,outputCreditReg,creditLoc]
  · fin_cases stage <;> simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts,
      correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,entryFacts,
      Prologue.nonzeroBarrierFacts,rescaleReuseReg,rescaleReuseLoc]
  · intro rv hm
    have hCheck : ((rescaleFinalFrame p l g batch lane).map Prod.fst).all
        (fun r => decide (r ≠ statsReg stage .alpha ∧ r ≠ rescalePredReg stage ∧
          r ≠ rescaleVoteReg stage ∧ r ≠ maskZeroReg stage)) = true := by
      fin_cases stage <;> rfl
    exact of_decide_eq_true (List.all_eq_true.mp hCheck _ (List.mem_map_of_mem hm))
  · intro chunk r hm
    unfold rescaleLocalKeeps
    have hCheck : ((rescaleFinalFrame p l g batch lane).map Prod.fst).all
        (fun r => decide (r ∉ rescaleDataRegs stage chunk ∧
          (∀ q ∈ rescalePacks stage chunk, q.1 ≠ r) ∧
          (∀ q ∈ rescaleMuls stage chunk, q.1 ≠ r) ∧
          (∀ q ∈ rescaleUnpacks stage chunk, q.2.1 ≠ r ∧ q.2.2 ≠ r))) = true := by
      fin_cases stage <;> fin_cases chunk <;> rfl
    exact of_decide_eq_true (List.all_eq_true.mp hCheck _ hm)
  · intro rv hm
    have hCheck : ((rescaleFinalFrame p l g batch lane).map Prod.fst).all
        (fun r => decide (r ≠ rescaleCountReg stage ∧ r ≠ rescaleSignalDst stage ∧
          r ≠ rescaleSignalDst stage+1)) = true := by
      fin_cases stage <;> rfl
    exact of_decide_eq_true (List.all_eq_true.mp hCheck _ (List.mem_map_of_mem hm))

/-- A finished correction lane supplies the real rescale decision, input
coefficient and optional stores for every positive visit. -/
theorem rescaleVisitOfCompletedWork {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFootprint : OutputFootprint p X) (hOperands : Safety.CompletedMmaOperandsAreBf16 X)
    (hStats : Protocol.Statistics.RescaleStoreValuesAreF32 X) {g batch visit : Nat} (stage : Fin 2)
    (hg : g < l.threads) (hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (hPos : 0 < visit)
    (hVisit : visit < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    ∃ pos alpha old word coefficient,
      RescaleVisit l X g pos stage alpha old word coefficient ∧
      RescaleFactorWord coefficient alpha ∧
      (correctionBefore X (g,pos)).barrier (statsBarrierId l g stage) = visit := by
  obtain ⟨pos,hWait,hOrdinal⟩ :=
    rescaleWaitOfCompletedVisit hp hX hDone hFootprint stage hg hWarp hb hLo hHi hPos hVisit
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  obtain ⟨t,hAt,hRun⟩ :=
    rescaleWaitStateOfCompletedWork hp hX hDone hFootprint hg hWarp hl hb hLo hHi
      stage (hSelf.symm ▸ hWait)
  obtain ⟨alpha,old,word,coefficient,_,hActual,hFactor,_,_⟩ :=
    rescaleVisitOfFiniteWords hp hX (hFootprint.metadataProtected hp).1 hOperands hStats
      stage hAt (finalFrameForRescale p l g batch lane stage) hRun
  exact ⟨pos,alpha,old,word,coefficient,hSelf ▸ hActual,hFactor,hOrdinal⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
