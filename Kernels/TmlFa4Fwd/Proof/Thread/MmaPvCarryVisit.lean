-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvScoreRank
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
import Lemmas.Flow.Next
import Lemmas.Flow.NthEv
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFragmentHistory
import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.MmaLoopStep
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
import Kernels.TmlFa4Fwd.Proof.Thread.TailPvIssueOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.TcMma PTX.Assumption
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private theorem closingElectionsOfPv {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index use d : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec}
    {acc : Bool} {mask : List Nat} (hPv : PvInstruction X (g,index) block step d op acc mask)
    (hUse : Mma.LatestValueReadyUse l X g index use) :
    ElectOrd.siteOrdinal (· == carryMarker) X g index = use/2 := by
  let stage := (pvSite block).stage
  let election := (electSite (commitElection (qkCommitSite (if stage = 0 then 2 else 3)))).pc
  have hBounds : 2145 ≤ pvPc block step ∧ pvPc block step < 2768 ∧
      pvPc block step ≠ (slotWait 2).pc+1 := by
    fin_cases block <;> fin_cases step <;> decide
  have hKey := readyBalanceAtEvent hp hX 2 hPv.decoded hBounds.1 hBounds.2.1 hBounds.2.2
  have hScore := keyScoreBalanceAtEvent hp hX stage hPv.decoded hBounds.1 hBounds.2.1 hBounds.2.2
  have hBand : (if (slotWait 2).pc+2 < pvPc block step ∧ pvPc block step ≤ (slotElect 2).pc
      then 1 else 0 : Nat) =
      (if (slotWait 2).pc+2 < pvPc block step ∧ pvPc block step ≤ election then 1 else 0) := by
    fin_cases block <;> fin_cases step <;> rfl
  have hExact := hPv.valueUseOfScoreElections hp hX hUse
  change ElectOrd.siteOrdinal (· == election) X g index = use/2 at hExact
  change ((X.tr g).take index).countP (readyAtSite 2) =
    (if (slotWait 2).pc+2 < pvPc block step ∧ pvPc block step ≤ election then 1 else 0) +
      ElectOrd.siteOrdinal (· == election) X g index at hScore
  change ((X.tr g).take index).countP (readyAtSite 2) =
    (if (slotWait 2).pc+2 < pvPc block step ∧ pvPc block step ≤ (slotElect 2).pc then 1 else 0) +
      ElectOrd.siteOrdinal (· == carryMarker) X g index at hKey
  rw [hBand] at hKey
  omega

/-- The first PV fragment preserves D exactly when it has a preceding visit. -/
theorem PvInstruction.firstCarryOfValueUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index use d : Nat} {block : Fin 4} {op : OperandSpec}
    {acc : Bool} {mask : List Nat} (hPv : PvInstruction X (g,index) block 0 d op acc mask)
    (hUse : Mma.LatestValueReadyUse l X g index use) :
    acc = true ↔ 0 < use/2 := by
  have hCount := closingElectionsOfPv hp hX hPv hUse
  have hCarry := hPv.accumulatorUse hp hX
  have hLen : index < (X.tr g).length := len_of_get hPv.decoded
  let mark := ElectOrd.atSites (· == carryMarker)
  constructor
  · intro hAcc
    rcases hCarry.mp hAcc with h | prior
    · omega
    obtain ⟨j,hJ,e,hGet,hPc⟩ := prior.closingEvent
    obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hPv.decoded)
    obtain ⟨s,u,hStep,_⟩ := hRun.after_event hGet (by omega)
    obtain ⟨ins,hCode,_,hFires⟩ := estep_event_source hStep
    have hAt := (estep_source_pc hStep).symm.trans hPc
    change s.pc = 2520 at hAt
    rw [hAt,Flow.code_2520] at hCode
    obtain rfl := Option.some.inj hCode.symm
    obtain ⟨mask',inst,lead,hKind,_⟩ := fires_elect hFires
    have hMarked : mark e = true := by
      rw [hKind]
      simp [mark,ElectOrd.atSites,isElectEv,hAt,carryMarker]
    have hTrace : (X.tr g)[j]? = some e := hGet
    have hMono := countP_take_mono mark (X.tr g) (show j+1 ≤ index from hJ)
    rw [List.take_add_one,hTrace,Option.toList_some,List.countP_append,
      List.countP_singleton,ite_eq_left hMarked] at hMono
    change ((X.tr g).take j).countP mark+1 ≤ ElectOrd.siteOrdinal (· == carryMarker) X g index
      at hMono
    omega
  · intro hPositive
    obtain ⟨j,hJ,e,hGet,hMark,_⟩ := Flow.exists_nth mark (X.tr g)
      (k := index) (n := 0) (by change 0 < ElectOrd.siteOrdinal (· == carryMarker) X g index; omega)
    have hPc : e.pc = carryMarker := by
      unfold mark ElectOrd.atSites at hMark
      exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hMark).2
    obtain ⟨_,_,_,hBody,_,_,_⟩ := releaseBody hp hX hGet
      (by rw [hPc]; decide) (by rw [hPc]; decide)
    exact hCarry.mpr (.inr (PvPriorSteadyVisit.ofClosingEvent hBody hJ hGet hPc))

/-- A recurring score commit witnesses the last PV bank of the previous V use. -/
theorem Scores.ScoreCommit.previousValueUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hScore : Scores.ScoreCommit l X (g,index) (g/l.block) stage spec rank)
    (hPositive : 0 < Scores.scoreCommitOrdinal l X (g/l.block) stage (g,index)) :
    ∃ pos < index, ∃ priorUse d op acc mask,
      PvInstruction X (g,pos) (firstPvBlock true stage) 7 d op acc mask ∧
      Mma.LatestValueReadyUse l X g pos priorUse ∧
      priorUse/2+1 = Scores.scoreCommitOrdinal l X (g/l.block) stage (g,index) := by
  let block := recurringKeyBlock stage
  let site := (commitSite (qkCommitSite block)).pc
  let election := (electSite (commitElection (qkCommitSite block))).pc
  let mark := ElectOrd.atSites (· == election)
  obtain ⟨observed,hStage,hRepeat,hGet⟩ := Scores.positiveScoreCommitRepeats hp hX hScore hPositive
  have hBlock : observed = block := by
    have audit : ∀ (b : Fin 4) (s : Fin 2), b.val%2=s.val → 2 ≤ b.val →
        b = recurringKeyBlock s := by decide
    exact audit observed stage hStage hRepeat
  subst observed
  have hSite : site = if stage = 0 then 2418 else 2519 := by fin_cases stage <;> rfl
  have hRaw : X.get (g,index) = some ⟨if stage = 0 then 2418 else 2519,.tc (.commit spec)⟩ := by
    rw [← hSite]
    exact hGet
  obtain ⟨pos,hPos,hReady,d,op,acc,mask,hPv⟩ :=
    steadyPvBeforeRecurringScoreCommitWithReady hp hX stage hRaw
  obtain ⟨priorUse,hUse,_,_⟩ := Mma.valueFragmentUse hp hX hPv
  refine ⟨pos,hPos,priorUse,d,op,acc,mask,hPv,hUse,?_⟩
  have hSeen := Scores.recurringScoreExactOrdinal hp hX stage hGet
  obtain ⟨hIndex,inst,leader,hVote,_⟩ := scoreCommitLeader hp hX block hGet
  have hMarked : mark ⟨election,.elect (2^32-1) inst leader⟩ = true := by
    simp [mark,ElectOrd.atSites,isElectEv]
  have hEq : index-1+1 = index := by omega
  have hV : (X.tr g)[index-1]? = some ⟨election,.elect (2^32-1) inst leader⟩ := hVote
  have hVotes : ((X.tr g).take index).countP mark =
      ((X.tr g).take (index-1)).countP mark + 1 := by
    conv_lhs => rw [← hEq,List.take_add_one,hV]
    simp only [Option.toList_some,List.countP_append,List.countP_singleton,ite_eq_left hMarked]
  have hAt : 2145 ≤ site ∧ site < 2768 ∧ site ≠ (slotWait 1).pc+1 ∧
      site ≠ (slotWait 2).pc+1 := by fin_cases stage <;> decide
  have hAtScore : ¬ ((slotWait 2).pc+2 < site ∧ site ≤ election) := by
    fin_cases stage <;> decide
  have hCarryBand : (slotWait 2).pc+2 < site ∧ site ≤ (slotElect 2).pc := by
    fin_cases stage <;> decide
  have hVBand : (slotWait 1).pc+2 < site ∧ site ≤ (slotElect 2).pc := by
    fin_cases stage <;> decide
  have hKey := readyBalanceAtEvent hp hX 2 hGet hAt.1 hAt.2.1 hAt.2.2.2
  have hCur := keyScoreBalanceAtEvent hp hX stage hGet hAt.1 hAt.2.1 hAt.2.2.2
  have hValue := valueReadyBalanceAtEvent hp hX hGet hAt.1 hAt.2.1 hAt.2.2.1
  change ((X.tr g).take index).countP (readyAtSite 2) =
    (if (slotWait 2).pc+2 < site ∧ site ≤ (slotElect 2).pc then 1 else 0)+
      ElectOrd.siteOrdinal (· == (slotElect 2).pc) X g index at hKey
  have hElection : (if stage = 0 then 2 else 3 : Fin 4) = block := by
    fin_cases stage <;> rfl
  dsimp only at hCur
  rw [hElection] at hCur
  change ((X.tr g).take index).countP (readyAtSite 2) =
    (if (slotWait 2).pc+2 < site ∧ site ≤ election then 1 else 0)+
      ((X.tr g).take index).countP mark at hCur
  change ((X.tr g).take index).countP (readyAtSite 1) =
    (if (slotWait 1).pc+2 < site ∧ site ≤ (slotElect 2).pc then 1 else 0)+
      ElectOrd.siteOrdinal (· == (slotElect 2).pc) X g index at hValue
  rw [ite_eq_left hCarryBand] at hKey
  rw [ite_eq_right hAtScore] at hCur
  rw [ite_eq_left hVBand] at hValue
  have hExactAtPos := closingElectionsOfPv hp hX hPv hUse
  have hPvAt : 2145 ≤ pvPc (firstPvBlock true stage) 7 ∧
      pvPc (firstPvBlock true stage) 7 < 2768 ∧
      pvPc (firstPvBlock true stage) 7 ≠ (slotWait 1).pc+1 ∧
      (slotWait 1).pc+2 < pvPc (firstPvBlock true stage) 7 ∧
      pvPc (firstPvBlock true stage) 7 ≤ (slotElect 2).pc := by
    fin_cases stage <;> decide
  have hPrior := valueReadyBalanceAtEvent hp hX hPv.decoded hPvAt.1
    hPvAt.2.1 hPvAt.2.2.1
  change ((X.tr g).take pos).countP (readyAtSite 1) =
    (if (slotWait 1).pc+2 < pvPc (firstPvBlock true stage) 7 ∧
      pvPc (firstPvBlock true stage) 7 ≤ (slotElect 2).pc then 1 else 0)+
      ElectOrd.siteOrdinal (· == carryMarker) X g pos at hPrior
  rw [ite_eq_left hPvAt.2.2.2,hExactAtPos] at hPrior
  change Scores.scoreCommitOrdinal l X (g/l.block) stage (g,index) =
    1+((X.tr g).take (index-1)).countP mark at hSeen
  omega


private def steadyPvFloor (stage : Fin 2) (step : Fin 8) : Nat :=
  pvPc (firstPvBlock true stage) step+1

private def steadyPvFloorCode (floor : Nat) (instruction : Instr) : Bool :=
  match instruction.op with
  | .bra target _ => decide (floor ≤ target ∧ target ≤ carryMarker)
  | .brx .. => false
  | _ => true

private theorem steadyPvFloorAt (stage : Fin 2) (step : Fin 8) {pc : Nat} {i : Instr}
    (hLo : steadyPvFloor stage step ≤ pc) (hHi : pc < carryMarker)
    (hCode : kernel.code[pc]? = some i) :
    steadyPvFloorCode (steadyPvFloor stage step) i = true := by
  let floor := steadyPvFloor stage step
  let region := (kernel.code.drop floor).take (carryMarker-floor)
  have hAudit : region.all (steadyPvFloorCode floor) = true := by
    fin_cases stage <;> fin_cases step <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAudit i
  apply List.mem_of_getElem? (i := pc-floor)
  dsimp only [region,floor]
  rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,hCode]

private theorem steadyPvWindowTau {l : Launch} {g : Nat} {s u : TState}
    (stage : Fin 2) (step : Fin 8) (hLo : steadyPvFloor stage step ≤ s.pc)
    (hHi : s.pc ≤ carryMarker) (ht : Tau kernel Assumptions.all l g s u) :
    steadyPvFloor stage step ≤ u.pc ∧ u.pc ≤ carryMarker := by
  have hStart : 2291 ≤ steadyPvFloor stage step := by fin_cases stage <;> fin_cases step <;> decide
  have hStop : carryMarker < 2768 := by decide
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rwa [← out_eq_core (by omega) (by omega)]
  have hStrict : s.pc < carryMarker := by
    rcases hHi.lt_or_eq with h | he
    · exact h
    · change s.pc = 2520 at he
      have hCode : kernel.code[s.pc]? = _ := he.symm ▸ Flow.code_2520
      exact (tau_core_not_event hCode rfl ht').elim
  obtain ⟨ins,hCode⟩ := tau_core_has_code ht'
  rcases tau_core_frame hCode ht' with rfl | hExec
  · exact ⟨by change _ ≤ s.pc+1; omega,by change s.pc+1 ≤ _; omega⟩
  have hPc := hExec.pc
  have hAudit := steadyPvFloorAt stage step hLo hStrict hCode
  cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
  case bra target uniform =>
    rw [hPc]
    simpa [steadyPvFloorCode,hOp] using hAudit
  case brx => simp [steadyPvFloorCode,hOp] at hAudit
  all_goals
    exact ⟨by omega,by omega⟩

private theorem steadyPvWindowEvents {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (stage : Fin 2) (step : Fin 8)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hLo : steadyPvFloor stage step ≤ s.pc) (hHi : s.pc ≤ carryMarker)
    {j : Nat} {e : Event} (he : es[j]? = some e)
    (hNone : (es.take j).countP (ElectOrd.atSites (· == carryMarker)) = 0) :
    steadyPvFloor stage step ≤ e.pc ∧ e.pc ≤ carryMarker := by
  induction hw generalizing j with
  | stop => simp at he
  | tau ht hw ih =>
    obtain ⟨hLo',hHi'⟩ := steadyPvWindowTau stage step hLo hHi ht
    exact ih hLo' hHi' he hNone
  | @ev s u x es vs hStep hw ih =>
    have hPc := estep_source_pc hStep
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨hPc.symm ▸ hLo,hPc.symm ▸ hHi⟩
    | succ j =>
      change es[j]? = some e at he
      simp only [List.take_succ_cons,List.countP_cons] at hNone
      have hStrict : s.pc < carryMarker := by
        rcases hHi.lt_or_eq with h | hEq
        · exact h
        · obtain ⟨ins,hCode,_,hFires⟩ := estep_event_source hStep
          change s.pc = 2520 at hEq
          rw [hEq,Flow.code_2520] at hCode
          obtain rfl := Option.some.inj hCode.symm
          obtain ⟨mask,inst,leader,hEvent,_⟩ := fires_elect hFires
          have hMark : ElectOrd.atSites (· == carryMarker) x = true := by
            rw [hEvent]
            simp [ElectOrd.atSites,isElectEv,hEq,carryMarker]
          rw [ite_eq_left hMark] at hNone
          omega
      have hEntry : 2291 ≤ steadyPvFloor stage step := by
        fin_cases stage <;> fin_cases step <;> decide
      have hExit : carryMarker < 2530 := by decide
      have hNext := (steadyEventFrame (by omega) (by omega) hStep).1
      have hQuiet :
          (es.take j).countP (ElectOrd.atSites (· == carryMarker)) = 0 := by omega
      exact ih (by omega) (by omega) he hQuiet
  | last hStep =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      have hPc := estep_source_pc hStep
      exact ⟨hPc.symm ▸ hLo,hPc.symm ▸ hHi⟩
    | succ j => simp at he

private theorem valueTailFloor :
    (kernel.code.drop 2548).all (fun i => staysPastEvent 2548 i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem valueTailSegmentFloor :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2548 ≤ seg.stop)
      | none => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

/-- Within a V visit the same stage issues the eight fragments in strictly increasing order. -/
theorem pvFragmentsOrderedWithinValueUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j use d d' : Nat} (stage : Fin 2) (steady lateSteady : Bool)
    {step later : Fin 8} {op op' : OperandSpec} {acc acc' : Bool} {mask mask' : List Nat}
    (hPv : PvInstruction X (g,i) (firstPvBlock steady stage) step d op acc mask)
    (hLater : PvInstruction X (g,j) (firstPvBlock lateSteady stage) later d' op' acc' mask')
    (hBefore : i < j)
    (hUse : Mma.LatestValueReadyUse l X g i use)
    (hLaterUse : Mma.LatestValueReadyUse l X g j use) :
    step.val < later.val := by
  cases steady
  · cases lateSteady
    · rcases lt_trichotomy step.val later.val with h | h | h
      · exact h
      · have same : step = later := Fin.ext h
        subst later
        have hId := hPv.tailUnique hp hX stage hLater rfl
        exact (Nat.ne_of_lt hBefore (congrArg Prod.snd hId)).elim
      · have hReverse := hLater.tailTraceOrder hp hX stage hPv rfl h
        exact (Nat.not_lt_of_ge hBefore.le hReverse.2.1).elim
    · have hLo : pvPc (firstPvBlock true stage) later < 2548 := by
        fin_cases stage <;> fin_cases later <;> decide
      have hHi : 2548 ≤ pvPc (firstPvBlock false stage) step := by
        fin_cases stage <;> fin_cases step <;> decide
      have hOrder := traceOrderOfPcFloor hX valueTailFloor valueTailSegmentFloor
        hLater.decoded hPv.decoded hLo hHi
      omega
  · let mark := ElectOrd.atSites (· == carryMarker)
    let suffix := (X.tr g).drop (i+1)
    let offset := j-(i+1)
    have hCount := closingElectionsOfPv hp hX hPv hUse
    have hNextCount := closingElectionsOfPv hp hX hLater hLaterUse
    have he : (X.tr g)[i]? = _ := hPv.decoded
    have hStable : ((X.tr g).take (i+1)).countP mark = ((X.tr g).take i).countP mark := by
      rw [List.take_add_one,he,Option.toList_some,List.countP_append]
      simp [mark,ElectOrd.atSites,isElectEv]
    have hJoin : (X.tr g).take j = (X.tr g).take (i+1) ++ suffix.take offset := by
      dsimp [suffix,offset]
      conv_lhs => rw [← Nat.add_sub_of_le (show i+1 ≤ j from hBefore),List.take_add]
    change ((X.tr g).take i).countP mark = use/2 at hCount
    change ((X.tr g).take j).countP mark = use/2 at hNextCount
    rw [hJoin,List.countP_append,hStable,hCount] at hNextCount
    have hNone : (suffix.take offset).countP mark = 0 := by omega
    have hg := event_thread_lt hX hPv.decoded
    have hSize : j < (X.tr g).length := len_of_get hLater.decoded
    obtain ⟨_,hr⟩ := hX.thr g hg
    obtain ⟨s,u,hStep,hRun⟩ := hr.after_event hPv.decoded (by omega)
    have hReturn := (pvFieldsOfStep hg (firstPvBlock true stage) step hStep).2.2.2
    obtain rfl := Option.some.inj hReturn
    obtain ⟨_,hWalk⟩ := walkFromRun hRun
    have hEvent : suffix[offset]? = some
        ⟨pvPc (firstPvBlock lateSteady stage) later,.tc (.mma d' op' acc' mask')⟩ := by
      dsimp [suffix,offset]
      rw [List.getElem?_drop,Nat.add_sub_of_le (show i+1 ≤ j from hBefore)]
      exact hLater.decoded
    have hStart : (next s).pc = steadyPvFloor stage step := by
      exact congrArg (· + 1) (estep_source_pc hStep).symm
    have hHi : steadyPvFloor stage step ≤ carryMarker := by
      fin_cases stage <;> fin_cases step <;> decide
    obtain ⟨hFloor,hUpper⟩ := steadyPvWindowEvents stage step hWalk hStart.ge
      (hStart.symm ▸ hHi) hEvent hNone
    cases lateSteady
    · have hTail : carryMarker < pvPc (firstPvBlock false stage) later := by
        fin_cases stage <;> fin_cases later <;> decide
      exact (Nat.not_lt_of_ge hUpper hTail).elim
    · have audit : ∀ (s : Fin 2) (a b : Fin 8),
          steadyPvFloor s a ≤ pvPc (firstPvBlock true s) b → a.val < b.val := by decide
      exact audit stage step later hFloor


end PTX.Kernels.TmlFa4Fwd.Thread
