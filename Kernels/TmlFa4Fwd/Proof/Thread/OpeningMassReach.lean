-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityReplay
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstSum
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Lemmas.Step.ExitLast
import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights
import Kernels.TmlFa4Fwd.Proof.SoftmaxReference
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstLoopEntry
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityScoreCount
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningStatistics
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Numeric

private def openingCarryRegisters : List Nat :=
  [7256,1062,2535,1230,5127,7132] ++ firstTransitionRegs ++ exponentLive

private def openingTailAudit (pc : Nat) (ins : Instr) : Bool :=
  !Assumptions.swExp2Sites.contains pc && (ins.op.isLocal || scoreEventOp ins.op) &&
    (writesRegs ins.op ++ scoreEventWrites ins.op).all
      (fun r => !openingCarryRegisters.contains r) &&
    match ins.op with
    | .bra dst _ => decide (4826 ≤ dst ∧ dst ≤ 4877)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem openingTailChecked :
    (((kernel.code.drop 4826).take (4877-4826)).zipIdx 4826).all
      (fun (ins,pc) => openingTailAudit pc ins) = true := by kernel_rfl

private theorem openingTailAuditAt {pc : Nat} {ins : Instr}
    (hLo : 4826 ≤ pc) (hHi : pc < 4877) (hc : kernel.code[pc]? = some ins) :
    openingTailAudit pc ins = true := by
  apply List.all_eq_true.mp openingTailChecked (ins,pc)
  apply List.mem_of_getElem? (i := pc-4826)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem openingTailKeeps {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 4826 ≤ s.pc) (hHi : s.pc < 4877) (hSub : s.sub ≤ 3)
    (hw : WStep kernel Assumptions.all l g s e u) :
    4826 ≤ u.pc ∧ u.pc ≤ 4877 ∧
      (∀ r ∈ openingCarryRegisters, u.regs r = s.regs r) := by
  have hWrites {i : Instr} (hc : kernel.code[s.pc]? = some i) (r : Nat)
      (hr : r ∈ openingCarryRegisters) : r ∉ writesRegs i.op ++ scoreEventWrites i.op := by
    intro hw
    have h := openingTailAuditAt hLo hHi hc
    simp only [openingTailAudit,Bool.and_eq_true] at h
    have := List.all_eq_true.mp h.1.2 _ hw
    simp [hr] at this
  rcases hw with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
  · obtain ⟨i,hc,_,hBody⟩ := tauScoreSource ht
    rcases hBody with ⟨rfl,_⟩ | ⟨_,_,hx⟩
    · exact ⟨by change 4826 ≤ s.pc+1; omega,by change s.pc+1 ≤ 4877; omega,fun _ _ => rfl⟩
    rcases scoreExecLocal hx with hLoc | ⟨m,hSite,_,_⟩
    · have hPc := hLoc.pc
      have hRange : 4826 ≤ u.pc ∧ u.pc ≤ 4877 := by
        have hAudit := openingTailAuditAt hLo hHi hc
        cases hOp : i.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
        case bra dst uni =>
          rw [hPc]
          simp only [openingTailAudit,hOp,Bool.and_eq_true,decide_eq_true_eq] at hAudit
          exact hAudit.2
        case brx => simp [openingTailAudit,hOp] at hAudit
        all_goals omega
      exact ⟨hRange.1,hRange.2,fun r hr => hLoc.regs r (fun h =>
        hWrites hc r hr (List.mem_append_left _ h))⟩
    · have hAudit := openingTailAuditAt hLo hHi hc
      simp only [openingTailAudit,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
        decide_eq_false_iff_not] at hAudit
      exact (hAudit.1.1.1 hSite).elim
  · obtain ⟨i,hc,hNonlocal,_⟩ := estep_event_source he
    have h := openingTailAuditAt hLo hHi hc
    simp only [openingTailAudit,Bool.and_eq_true,hNonlocal,Bool.false_or] at h
    have hPc := softmaxReturningPc (by omega) (by omega) hSub he
    refine ⟨by rcases hPc with h | h <;> omega,by rcases hPc with h | h <;> omega,?_⟩
    intro r hr
    exact (scoreEventStep hc h.1.1.2 hSub (fun hm =>
      hWrites hc r hr (List.mem_append_right _ hm)) he).2

private theorem openingTailToSum {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hr : Run kernel Assumptions.all l g s events none)
    (hLo : 4826 ≤ s.pc) (hHi : s.pc ≤ 4877) (hSub : s.sub ≤ 3)
    (hScratch : ScoreScratchState s) (hClean : s.pc = 4877 → s.fault = none)
    (hDone : (⟨9205,.exit⟩ : Event) ∈ events) :
    ∃ n u, At u 4877 [] ∧
      TraceReach kernel Assumptions.all l g s (events.take n) u ∧
      Run kernel Assumptions.all l g u (events.drop n) none ∧
      (∀ r ∈ openingCarryRegisters, u.regs r = s.regs r) ∧
      (events.take n).countP scoreAcquireMark = 0 := by
  induction hw with
  | stop => cases hDone
  | @tau s u events visits hTau hWalk ih =>
    by_cases hAt : s.pc = 4877
    · have hC : ScoreScratchClear s := by
        simp only [ScoreScratchState,hAt,Flow.code_4877,Op.isLocal] at hScratch
        exact hScratch
      exact ⟨0,s,⟨hAt,hC.1,hC.2,hClean hAt,trivial⟩,.refl _,hr,(fun _ _ => rfl),rfl⟩
    · have hs : s.pc < 4877 := by omega
      have hStep : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,hTau⟩
      obtain ⟨hLower,hUpper,hKeep⟩ := openingTailKeeps hLo hs hSub hStep
      have hF := windowStepFrame .firstRoundCounters (by change 3425 ≤ s.pc; omega)
        (by change s.pc < 5006; omega) hSub hStep
      have hSc := softmaxScratchStep (by omega) (by omega) hSub hScratch hStep
      obtain ⟨n,w,hw,hPath,hRun,hRegs,hCount⟩ := ih (hr.after_local (.single hTau))
        hLower hUpper hF.2.2.1 hSc (fun h => hF.2.2.2.1.resolve_right (by omega)) hDone
      exact ⟨n,w,hw,.tau hTau hPath,hRun,(fun r h => (hRegs r h).trans (hKeep r h)),hCount⟩
  | @ev s u e events visits he hWalk ih =>
    by_cases hAt : s.pc = 4877
    · have hC : ScoreScratchClear s := by
        simp only [ScoreScratchState,hAt,Flow.code_4877,Op.isLocal] at hScratch
        exact hScratch
      exact ⟨0,s,⟨hAt,hC.1,hC.2,hClean hAt,trivial⟩,.refl _,hr,(fun _ _ => rfl),rfl⟩
    · have hs : s.pc < 4877 := by omega
      have hStep : WStep kernel Assumptions.all l g s (some e) u := .inr ⟨e,rfl,he⟩
      obtain ⟨hLower,hUpper,hKeep⟩ := openingTailKeeps hLo hs hSub hStep
      have hF := windowStepFrame .firstRoundCounters (by change 3425 ≤ s.pc; omega)
        (by change s.pc < 5006; omega) hSub hStep
      have hSc := softmaxScratchStep (by omega) (by omega) hSub hScratch hStep
      have hExit : (⟨9205,.exit⟩ : Event) ∈ events := by
        obtain ⟨_,_,hf⟩ := he
        exact (List.mem_cons.mp hDone).resolve_left (fun h => hf.not_exit h.symm)
      obtain ⟨n,w,hw,hPath,hRun,hRegs,hCount⟩ := ih (afterSoftmaxEvent he hr)
        hLower hUpper hF.2.2.1 hSc (fun h => hF.2.2.2.1.resolve_right (by omega)) hExit
      have hMark : scoreAcquireMark e = false := by
        have hPc := estep_source_pc he
        cases hKind : e.kind <;> simp [scoreAcquireMark,hKind]
        rename_i _ _ ok _ _
        have hA : e.pc ≠ 3425 := by omega
        have hB : e.pc ≠ 5109 := by omega
        have hC : e.pc ≠ 6676 := by omega
        cases ok <;> simp [hA,hB,hC]
      exact ⟨n+1,w,hw,.event he hPath,hRun,(fun r h => (hRegs r h).trans (hKeep r h)),
        by simp [List.take_succ_cons,hMark,hCount]⟩
  | @last s e he =>
    obtain rfl := List.mem_singleton.mp hDone
    have hPc := estep_source_pc he
    change 9205 = s.pc at hPc
    omega

/-- The floating weights at the recorded early store survive the tail, election, and correction
acknowledgement to the actual start of the first row sum. -/
theorem OpeningProbabilityWaitCursor.sumEntryWithResidentsOfExit {p : Params} {l : Launch} {m :
  Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {stage : Fin 2} (cursor : OpeningProbabilityWaitCursor p l X g stage)
    {last pc : Nat} (hExit : X.get (g,last) = some ⟨pc,.exit⟩) :
    ∃ j u, At u 4877 [] ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) none ∧
      (∀ i < 128, u.regs (1231+i) = cursor.state.regs (1231+i)) ∧
      (∀ r ∈ firstSumResidentRegs, u.regs r = cursor.state.regs r) ∧
      ((X.tr g).take j).countP scoreAcquireMark =
        ((X.tr g).take (cursor.statistics.index+2)).countP scoreAcquireMark := by
  let start := cursor.statistics.index+2
  obtain rfl := actualExitPc hX hExit
  have hLast : start ≤ last := by
    by_contra! hEarly
    have hGet : ((X.tr g).take start)[last]? = some ⟨9205,.exit⟩ := by
      rwa [List.getElem?_take_of_lt hEarly]
    exact (cursor.recorded.no_exit hGet).elim
  have hGet : ((X.tr g).drop start)[last-start]? = some ⟨9205,.exit⟩ := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hLast]
  have hRun : Run kernel Assumptions.all l g cursor.state ((X.tr g).drop start) none := by
    have h := cursor.continuation
    cases hEnd : cursor.statistics.ending with
    | none => exact hEnd ▸ h
    | some t => exact ((hEnd ▸ h).no_exit hGet).elim
  have hPc : cursor.state.pc = 4826 := cursor.site
  have hScratch : ScoreScratchState cursor.state := by
    simp only [ScoreScratchState,hPc,Flow.code_4826,Op.isLocal,ScoreScratchReady]
    exact ⟨.inl (by decide),cursor.acc⟩
  obtain ⟨_,hw⟩ := Mma.walkFromRun hRun
  obtain ⟨n,u,hu,hReach,hTail,hKeep,hCount⟩ := openingTailToSum hw hRun
    hPc.ge (by omega) (by rw [cursor.sub]; decide) hScratch (fun _ => cursor.fault)
    (List.mem_of_getElem? hGet)
  refine ⟨start+n,u,hu,?_,?_,?_,?_,?_⟩
  · rw [List.take_add]
    exact cursor.recorded.returning_reach.append hReach
  · rw [← List.drop_drop]
    exact hTail
  · intro i hi
    exact hKeep _ (List.mem_append_right _ (mem_exponentLive.mpr (by omega)))
  · intro r hr
    exact hKeep r (by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      · exact List.mem_append_left _ (List.mem_append_right _ hr))
  · rw [List.take_add,List.countP_append,hCount,Nat.add_zero]

/-- The first denominator is recorded before any repeated softmax iteration. -/
theorem OpeningProbabilityWaitCursor.firstMassWithResidentsOfExit {p : Params} {l : Launch} {m :
  Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {stage : Fin 2} (cursor : OpeningProbabilityWaitCursor p l X g stage)
    {last pc : Nat} (hExit : X.get (g,last) = some ⟨pc,.exit⟩)
    (hWeights : ∀ i < 128, cursor.state.regs (1231+i) = some (fl (cursor.values i))) :
    ∃ j v, At v 5006 [(7257,fl (∑ i ∈ Finset.range 128, cursor.values i))] ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) v ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop j) none ∧
      (∀ r ∈ firstSumResidentRegs, v.regs r = cursor.state.regs r) ∧
      ((X.tr g).take j).countP scoreAcquireMark =
        ((X.tr g).take (cursor.statistics.index+2)).countP scoreAcquireMark := by
  obtain ⟨j,u,hu,hReach,hTail,hCarry,hMaximum,hCount⟩ := cursor.sumEntryWithResidentsOfExit hX hExit
  have hW i hi := (hCarry i hi).trans (hWeights i hi)
  obtain ⟨v,hv,hLocal,hFrame⟩ := firstRowSumWithResidentsLocal cursor.values hu hW (l := l) (g := g)
  refine ⟨j,v,hv,?_,hTail.after_local hLocal,(fun r hr => (hFrame r hr).trans (hMaximum r hr)),
    hCount⟩
  simpa only [List.append_nil] using hReach.append (TraceReach.of_local hLocal)

private theorem openingMaximumCongr {lhs rhs : Nat → Option ℝ} {cols : List Nat}
    (hEq : ∀ i ∈ cols, lhs i = rhs i) :
    scoreMax lhs cols = scoreMax rhs cols := by
  induction cols with
  | nil => rfl
  | cons c cols ih =>
    change maxScore (lhs c) (scoreMax lhs cols) = maxScore (rhs c) (scoreMax rhs cols)
    rw [hEq c (List.mem_cons_self ..),ih (fun i hi => hEq i (List.mem_cons_of_mem _ hi))]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hRole : Prologue.warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {last pc : Nat}
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩)
    (hRow : 128*(2*(Epilogue.assignedCoordinates p batch (g/l.block)).1+stage.val)+
      (g%l.block)%128 < p.qLength batch)
include hp hMax hFrame hg stage hRole hb hLo hHi hExit hRow

/-- The actual first row sum agrees with the specification on a live row. -/
theorem openingMassWithRegistersOfMaximalExit :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
    let blocks := Mma.trips p batch coords.1
    let maximum := scoreMax (fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c))
      (List.range 128)
    let ref := firstReference p batch coords.2 row blocks
    let mass := (2 : ℝ)^(-ref)*maskedBlockSum (p.keyCount batch row) blocks 0
      (weight p batch coords.2 row)
    let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
    let past := p.kLength batch-p.qLength batch+256*coords.1
    ∃ j t, At t 5006 ((1228,b32 cap)::firstLoopStable blocks past maximum mass) ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) t ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop j) none ∧
      Thread.Scores.probabilityOrdinal l X (g/l.block) stage 0 (g,j) = 1 ∧
      Holds t.regs (openingDenominatorRegisters p l g) := by
  let coords := Epilogue.assignedCoordinates p batch (g/l.block)
  let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
  let blocks := Mma.trips p batch coords.1
  let maximum := scoreMax (fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c))
    (List.range 128)
  let ref := firstReference p batch coords.2 row blocks
  obtain ⟨_,_,⟨arrival⟩,hReleased⟩ :=
    Progress.openingSoftmaxBiasRendezvousOfAllStages hp hMax hFrame hg stage hRole hb hLo hHi
  obtain ⟨c,hLoop,hMaximum,hScores,hSetup⟩ :=
    arrival.statisticsWithScoresAndRegistersOfMaximal hp hMax hFrame hg
    hb hLo hHi (hReleased.imp_right (fun ⟨Y,hY,hTrace,_,hReady⟩ => ⟨Y,hY,hTrace,hReady⟩))
  have hRelease (hEnd : c.index+1 = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
    have hj : c.index = (X.tr g).length-1 := by omega
    exact Progress.openingStatisticsReleasedHistory hp hMax hFrame hg stage hRole hb hLo hHi
      (hj ▸ c.published)
  obtain ⟨cursor,_,hValues,hWeights,hCarry,hResident,hNegative⟩ :=
    c.probabilityWaitWithWeightsAndRegistersOfMaximal hp hg hRelease
  obtain ⟨j,t,ht,hReach,hTail,hLastMaximum,hCount⟩ := cursor.firstMassWithResidentsOfExit hMax.1
    hExit hWeights
  have hMx : scoreMax c.scores (List.range 128) = maximum :=
    openingMaximumCongr (fun col hc => hScores hRow ⟨col,List.mem_range.mp hc⟩)
  have hEqual (col : Nat) (hc : col < 128) :
      cursor.values col = shiftedWeight p batch coords.2 row (visitKey blocks 0 col) ref := by
    have hRef : abiFloat p.scaleLog2Bits*(scoreMax c.scores (List.range 128)).getD 0 = ref := by
      rw [hMx]
      rfl
    have hExponent := exponentOfOpeningWeight (abiFloat p.scaleLog2Bits) ref c.scores col
    rw [hScores hRow ⟨col,hc⟩, hardwareShiftedWeight hp] at hExponent
    rw [hValues,hRef]
    exact (Value.float.inj (Except.ok.inj hExponent)).2.symm
  have hSum := shiftedBlockProducts p batch coords.2 row blocks 0 ref (fun _ => 1)
  simp only [mul_one] at hSum
  have hMass := Finset.sum_congr rfl (fun i hi => hEqual i (Finset.mem_range.mp hi))
  have hKeep r (hr : r ∈ firstTransitionRegs) :=
    (hLastMaximum r (List.mem_append_right _ hr)).trans (hCarry r hr)
  obtain ⟨hPast,hBlocks,hCap,hLast,_⟩ := hLoop
  refine ⟨j,t,ht.mono ⟨(hKeep 1228 (by decide)).trans hCap,
      (hKeep 1226 (by decide)).trans hBlocks,(hKeep 1229 (by decide)).trans hLast,
      (hKeep 1225 (by decide)).trans hPast,?_,?_,trivial⟩,hReach,hTail,?_,?_⟩
  · exact (hKeep 7256 (by decide)).trans (by simpa only [hMx] using hMaximum)
  · simpa only [hMass,hSum] using ht.2.2.2.2.1
  · let k := cursor.statistics.index+2
    have hLe : k ≤ last := by
      by_contra! hBefore
      have hEarly : ((X.tr g).take k)[last]? = some ⟨pc,.exit⟩ := by
        rwa [List.getElem?_take_of_lt hBefore]
      exact (cursor.recorded.no_exit hEarly).elim
    have hk : k < (X.tr g).length := hLe.trans_lt (len_of_get hExit)
    have hOut := packedProbabilityStoreTemplate hp stage 0 cursor.values
      cursor.site cursor.fault cursor.sub (cursor.addresses 0) cursor.unpacked
    obtain ⟨he,_,_⟩ := probabilityCollectiveOfMaximal (m := m) hg (by omega : 0 < k)
      hk.le hOut rfl nofun cursor.recorded (.refl) cursor.continuation
      (fun hEnd => (Nat.ne_of_lt hk hEnd).elim)
    rw [cursor.site] at he
    have hPoll := Thread.Scores.firstProbabilityScoreCount hp hMax.1 stage hRole 0 he
    have hWarp : Prologue.warpIndex l g < 8 := by have := stage.isLt; omega
    have hReady := Thread.Scores.scoreCount (j := k) hp hMax.1 stage hWarp rfl hRole
    have hMark : phaseAcquired true = scoreAcquireMark := by
      funext e
      rw [scoreReadyMarkKind]
      rfl
    rw [hMark] at hReady
    have hScore := (hCount.trans hReady).trans hPoll
    have hj : j < (X.tr g).length := by
      by_contra! hTooLate
      have hEarly : ((X.tr g).take j)[last]? = some ⟨pc,.exit⟩ := by
        rwa [List.getElem?_take_of_lt ((len_of_get hExit).trans_le hTooLate)]
      obtain ⟨u,hReturned,_⟩ := hReach.returnedPrefix
      exact (hReturned.no_exit hEarly).elim
    rw [← Thread.Scores.earlyProbabilityCount hp hMax.1 stage hWarp hRole hj,
      ← scoreEarlyLedgerAtHead hReach (.inl ht.1)]
    exact hScore

  · obtain ⟨hWarp,hBase,hBar,_⟩ := hSetup
    exact ⟨(hLastMaximum 1062 (by decide)).trans ((hResident 1062 (by decide)).trans hWarp),
      (hLastMaximum 2535 (by decide)).trans ((hResident 2535 (by decide)).trans hBase),
      (hLastMaximum 5127 (by decide)).trans ((hResident 5127 (by decide)).trans hBar),
      (hLastMaximum 7132 (by decide)).trans ((hResident 7132 (by decide)).trans
        c.ready.2.2.2.2.2.1),
      (hLastMaximum 1230 (by decide)).trans hNegative,trivial⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
