-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleGaps
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleDecision
import Kernels.TmlFa4Fwd.Proof.CorrectionRescalePrefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Lemmas.Flow.Determinism
import Kernels.TmlFa4Fwd.Flow.Code.Part125

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

private def rescaleVoteLabel (e : Event) : Option (Fin 2 × BitVec 32) :=
  match e.kind with
  | .vote _ _ word =>
    if e.pc = 8009 then some (0,word) else if e.pc = 8228 then some (1,word) else none
  | _ => none

/-- The actual rescale ballots of a finite correction path, in their recorded order. -/
@[no_expose] def rescaleVoteLabels (events : List Event) : List (Fin 2 × BitVec 32) :=
  events.filterMap rescaleVoteLabel

/-- The Tensor Memory sequence requested by the actual ordered ballot decisions. -/
@[no_expose] def rescaleVoteSchedule (decisions : List (Fin 2 × BitVec 32)) : List (Nat × Fin 4) :=
  decisions.flatMap fun (stage,word) => if word = 0 then [] else rescaleSchedule stage

theorem rescaleVoteLabelsNone {events : List Event}
    (h : ∀ e ∈ events, e.pc ≠ 8009 ∧ e.pc ≠ 8228) : rescaleVoteLabels events = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  have ⟨h0,h1⟩ := h e he
  unfold rescaleVoteLabel
  split <;> simp [h0,h1]

theorem rescaleVoteLabelsAppend (a b : List Event) :
    rescaleVoteLabels (a++b) = rescaleVoteLabels a ++ rescaleVoteLabels b := List.filterMap_append

theorem rescaleVoteScheduleAppend (a b : List (Fin 2 × BitVec 32)) :
    rescaleVoteSchedule (a++b) = rescaleVoteSchedule a ++ rescaleVoteSchedule b :=
  List.flatMap_append

private theorem voteLabelsAtSite (stage : Fin 2) {bit : Bool} {word : BitVec 32} :
    rescaleVoteLabels [⟨statsPc stage .alpha+2,.vote (2^32-1) bit word⟩] = [(stage,word)] := by
  fin_cases stage <;> rfl

private theorem noVotesInRescaleBody (stage : Fin 2) {events : List Event}
    (h : ∀ e ∈ events, rescaleLoadPc stage 0 ≤ e.pc ∧ e.pc < rescaleSkipPc stage) :
    rescaleVoteLabels events = [] := by
  apply rescaleVoteLabelsNone
  intro e he
  have hb := h e he
  fin_cases stage <;> dsimp [rescaleLoadPc,rescaleSkipPc] at hb <;> omega

private def beforeStage (stage : Fin 2) : RescaleGap :=
  if stage = 0 then .firstVote else .secondVote

private theorem noVotesInGap (gap : RescaleGap) {events : List Event}
    (h : ∀ e ∈ events, gap.start ≤ e.pc ∧ e.pc < gap.stop ∧ isTcData e = false) :
    rescaleVoteLabels events = [] := by
  apply rescaleVoteLabelsNone
  intro e he
  have hb := h e he
  cases gap <;> simp only [RescaleGap.start,RescaleGap.stop] at hb <;> omega

private theorem walkAfterRescaleDecision {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} {visits : List Visit}
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    events = [] ∨ ∃ rest, Walk kernel Assumptions.all l g t events rest := by
  induction hLocal using Relation.ReflTransGen.head_induction_on generalizing visits with
  | refl => exact .inr ⟨visits,hw⟩
  | head ht _ ih =>
    cases hw with
    | stop => exact .inl rfl
    | tau ht' hw =>
      obtain rfl := Out.tau.inj (ht.symm.trans ht')
      exact ih hw
    | ev he _ => exact (not_tau_of_stops (stops_of_estep he) ht).elim
    | last he => exact (not_tau_of_stops (stops_of_estep he) ht).elim

private theorem rescaleTensorNilOnVote (stage : Fin 2) (bit : Bool) (word : BitVec 32) :
    correctionTensorLabels [⟨statsPc stage .alpha+2,.vote (2^32-1) bit word⟩] = [] := by
  apply correctionTensorLabelsNone
  intro e he
  obtain rfl := List.mem_singleton.mp he
  rfl

private theorem rescaleScheduleSingleton (stage : Fin 2) (word : BitVec 32) :
    rescaleVoteSchedule [(stage,word)] = if word = 0 then [] else rescaleSchedule stage := by
  simp [rescaleVoteSchedule]

theorem rescaleScheduleNil : rescaleVoteSchedule [] = [] := by simp [rescaleVoteSchedule]

@[no_expose] def StageDecomposes (l : Launch) (g : Nat)
    (stage : Fin 2) (counter : Value) (events : List Event) : Prop :=
  (List.IsPrefix (correctionTensorLabels events) (rescaleVoteSchedule (rescaleVoteLabels events)) ∧
    (rescaleVoteLabels events).length ≤ 1) ∨
    ∃ u pre tail visits word, events = pre ++ tail ∧ u.pc = rescaleSkipPc stage ∧
      CorrectionRescaleFrame u counter ∧ correctionTensorLabels pre =
        rescaleVoteSchedule [(stage,word)] ∧ rescaleVoteLabels pre = [(stage,word)] ∧
      Walk kernel Assumptions.all l g u tail visits

private theorem emptyStageDecomposes (l : Launch) (g : Nat) (stage : Fin 2) (counter : Value) :
    StageDecomposes l g stage counter [] := by
  left
  have hNil := correctionTensorLabelsNone (events := []) (by simp)
  rw [hNil]
  exact ⟨⟨_,rfl⟩,Nat.zero_le _⟩

private theorem rescaleStageFromBallot {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {counter : Value} (stage : Fin 2)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hPc : s.pc = statsPc stage .alpha+2) (hFrame : CorrectionRescaleFrame s counter) :
    StageDecomposes l g stage counter events := by
  cases hw with
  | stop => exact emptyStageDecomposes l g stage counter
  | tau h _ => exact (correctionRescaleBallotNoTau stage hPc h).elim
  | @last _ e he =>
    obtain ⟨_,_,hf⟩ := he
    left
    rcases fires_none_ends hf with ⟨_,hFault⟩ | hExit
    · have hNil : correctionTensorLabels [e] = [] := by
        apply correctionTensorLabelsNone
        intro e' hMem
        obtain rfl := List.mem_singleton.mp hMem
        simp [isTcData,hFault]
      simp [hNil,rescaleVoteSchedule,rescaleVoteLabels,rescaleVoteLabel,hFault,List.IsPrefix]
    · have hNil : correctionTensorLabels [e] = [] := by
        apply correctionTensorLabelsNone
        intro e' hMem
        obtain rfl := List.mem_singleton.mp hMem
        simp [isTcData,hExit]
      simp [hNil,rescaleVoteSchedule,rescaleVoteLabels,rescaleVoteLabel,hExit,List.IsPrefix]
  | @ev s t e es vs he hw =>
    obtain ⟨bit,word,u,rfl,hAt,hSteps⟩ :=
      correctionRescaleActualBranch stage hPc hFrame.sub hFrame.acc hFrame.counter he
    let ballot : Event := ⟨statsPc stage .alpha+2,.vote (2^32-1) bit word⟩
    have hF : CorrectionRescaleFrame u counter := ⟨hAt.2.1,hAt.2.2.1,hAt.2.2.2.2.1⟩
    have hCons (tail : List Event) :
        correctionTensorLabels (ballot::tail) = correctionTensorLabels tail := by
      change correctionTensorLabels ([ballot]++tail) = _
      rw [correctionTensorLabelsAppend,rescaleTensorNilOnVote,List.nil_append]
    have hConsVote (tail : List Event) :
        rescaleVoteLabels (ballot::tail) = (stage,word)::rescaleVoteLabels tail := by
      change rescaleVoteLabels ([ballot]++tail) = _
      rw [rescaleVoteLabelsAppend,voteLabelsAtSite]
      rfl
    rcases walkAfterRescaleDecision hSteps hw with rfl | ⟨rest,hWalk⟩
    · left
      change List.IsPrefix (correctionTensorLabels (ballot::[])) _ ∧ _
      rw [hCons,hConsVote]
      have hNil := correctionTensorLabelsNone (events := []) (by simp)
      rw [hNil]
      exact ⟨⟨_,rfl⟩,Nat.le_refl 1⟩
    by_cases hZero : word = 0
    · right
      refine ⟨u,[ballot],es,rest,word,rfl,?_,hF,?_,voteLabelsAtSite stage,hWalk⟩
      · simpa only [hZero,↓reduceIte] using hAt.1
      · rw [rescaleTensorNilOnVote,rescaleScheduleSingleton,ite_eq_left hZero]
    have hBody : u.pc = rescaleLoadPc stage 0 := by simpa only [hZero,↓reduceIte] using hAt.1
    let P := fun t : TState => t.acc = [] ∧ t.regs 7278 = some counter
    have hP : P u := ⟨hF.acc,hF.counter⟩
    have hStable {x y : TState} {e : Option Event} (hLo : rescaleLoadPc stage 0 ≤ x.pc)
        (hHi : x.pc < rescaleSkipPc stage) (hSub : x.sub ≤ 1)
        (hX : P x) (hW : WStep kernel Assumptions.all l g x e y) : P y := by
      obtain ⟨hAcc,hCount⟩ := correctionRescaleBodyFrame stage hLo hHi hSub hX.1 hW
      exact ⟨hAcc,hCount.trans hX.2⟩
    rcases correctionRescaleBodyDecompose stage P hWalk hBody hF.sub hP hStable with
      ⟨hPrefix,hSites⟩ | ⟨v,pre,tail,visits,hSplit,hV,hSub,hP',hLab,hSites,hTail⟩
    · left
      change List.IsPrefix (correctionTensorLabels (ballot::es)) _ ∧ _
      rw [hCons,hConsVote,noVotesInRescaleBody stage hSites,rescaleScheduleSingleton,
        ite_eq_right hZero]
      exact ⟨hPrefix,Nat.le_refl 1⟩
    · right
      refine ⟨v,ballot::pre,tail,visits,word,?_,hV,⟨hSub,hP'.1,hP'.2⟩,?_,?_,hTail⟩
      · rw [hSplit,List.cons_append]
      · rw [hCons,hLab,rescaleScheduleSingleton,ite_eq_right hZero]
      · rw [hConsVote,noVotesInRescaleBody stage hSites]

/-- A single correction stage consumes its actual vote and exactly the scheduled Tensor Memory
sequence, or stops at a prefix of that sequence. -/
theorem correctionRescaleStageDecompose {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {counter : Value} (stage : Fin 2)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hp : s.pc = if stage = 0 then 8006 else 8222) (hFrame : CorrectionRescaleFrame s counter) :
    StageDecomposes l g stage counter events := by
  have hLo : s.pc = (beforeStage stage).start := by rw [hp]; fin_cases stage <;> rfl
  have hHi : s.pc ≤ (beforeStage stage).stop := by rw [hp]; fin_cases stage <;> decide
  rcases correctionRescaleGapDecompose (beforeStage stage) hw hLo.ge hHi hFrame with
    hOnly | ⟨u,pre,tail,rest,hs,hPc,hF,hPre,hWalk⟩
  · have hData := correctionTensorLabelsNone (fun e he => (hOnly e he).2.2)
    have hVote := noVotesInGap (beforeStage stage) hOnly
    left
    rw [hData,hVote,rescaleScheduleNil]
    exact ⟨⟨[],rfl⟩,by simp⟩
  have hNext : u.pc = statsPc stage .alpha+2 := by rw [hPc]; fin_cases stage <;> rfl
  have hData := correctionTensorLabelsNone (fun e he => (hPre e he).2.2)
  have hVote := noVotesInGap (beforeStage stage) hPre
  rcases rescaleStageFromBallot stage hWalk hNext hF with hPartial |
    ⟨v,body,after,visits,word,hSplit,hV,hFrame',hLab,hBallot,hRest⟩
  · left
    rw [hs,correctionTensorLabelsAppend,rescaleVoteLabelsAppend,hData,hVote,List.nil_append,
      List.nil_append]
    exact hPartial
  · right
    refine ⟨v,pre++body,after,visits,word,?_,hV,hFrame',?_,?_,hRest⟩
    · rw [hs,hSplit,List.append_assoc]
    · rw [correctionTensorLabelsAppend,hData,List.nil_append,hLab]
    · rw [rescaleVoteLabelsAppend,hVote,List.nil_append,hBallot]

private theorem rescalePlanAppend {a b : List Event}
    (ha : correctionTensorLabels a = rescaleVoteSchedule (rescaleVoteLabels a))
    (hb : List.IsPrefix (correctionTensorLabels b) (rescaleVoteSchedule (rescaleVoteLabels b))) :
    List.IsPrefix (correctionTensorLabels (a++b))
      (rescaleVoteSchedule (rescaleVoteLabels (a++b))) := by
  rw [correctionTensorLabelsAppend,rescaleVoteLabelsAppend,rescaleVoteScheduleAppend,ha]
  exact (List.prefix_append_right_inj _).2 hb

private theorem rescalePlanExactAppend {a b : List Event}
    (ha : correctionTensorLabels a = rescaleVoteSchedule (rescaleVoteLabels a))
    (hb : correctionTensorLabels b = rescaleVoteSchedule (rescaleVoteLabels b)) :
    correctionTensorLabels (a++b) = rescaleVoteSchedule (rescaleVoteLabels (a++b)) := by
  rw [correctionTensorLabelsAppend,rescaleVoteLabelsAppend,rescaleVoteScheduleAppend,ha,hb]

private theorem rescaleNoEventsPlan {events : List Event}
    (hData : correctionTensorLabels events = [])
    (hVotes : rescaleVoteLabels events = []) :
    correctionTensorLabels events = rescaleVoteSchedule (rescaleVoteLabels events) := by
  rw [hData,hVotes,rescaleScheduleNil]

private theorem rescalePlanExactToPrefix {events : List Event}
    (h : correctionTensorLabels events = rescaleVoteSchedule (rescaleVoteLabels events)) :
    List.IsPrefix (correctionTensorLabels events)
      (rescaleVoteSchedule (rescaleVoteLabels events)) :=
  ⟨[],(List.append_nil _).trans h⟩

private theorem rescalePassDecompose {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {counter : Value}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hPc : s.pc = 8006) (hFrame : CorrectionRescaleFrame s counter) :
    (List.IsPrefix (correctionTensorLabels events)
      (rescaleVoteSchedule (rescaleVoteLabels events)) ∧
      (rescaleVoteLabels events).length ≤ 2) ∨
    ∃ u pre tail rest, events = pre ++ tail ∧ u.pc = 8444 ∧
      CorrectionRescaleFrame u counter ∧
      correctionTensorLabels pre = rescaleVoteSchedule (rescaleVoteLabels pre) ∧
      (rescaleVoteLabels pre).length = 2 ∧ Walk kernel Assumptions.all l g u tail rest := by
  rcases correctionRescaleStageDecompose 0 hw hPc hFrame with ⟨hPrefix,hLen⟩ |
    ⟨u,pre,tail,rest,word,hSplit,hU,hF,hPlan,hVote,hWalk⟩
  · exact .inl ⟨hPrefix,hLen.trans (by decide)⟩
  have hPlan0 : correctionTensorLabels pre = rescaleVoteSchedule (rescaleVoteLabels pre) := by
    rwa [hVote]
  rcases correctionRescaleStageDecompose 1 hWalk hU hF with ⟨hPrefix,hLen⟩ |
    ⟨u',mid,tail',rest',word',hSplit',hU',hF',hPlan',hVote',hWalk'⟩
  · left
    rw [hSplit]
    refine ⟨rescalePlanAppend hPlan0 hPrefix,?_⟩
    rw [rescaleVoteLabelsAppend,hVote,List.length_append]
    change 1 + (rescaleVoteLabels tail).length ≤ 2
    omega
  have hPlan1 : correctionTensorLabels mid = rescaleVoteSchedule (rescaleVoteLabels mid) := by
    rwa [hVote']
  have hLatch : u'.pc = RescaleGap.latch.start := hU'
  have hLen : u'.pc ≤ RescaleGap.latch.stop := by rw [hLatch]; decide
  rcases correctionRescaleGapDecompose .latch hWalk' hLatch.ge hLen hF' with hOnly |
    ⟨v,after,remain,visits',hSplit'',hV,hF'',hOnly,hRemain⟩
  · have hNil := noVotesInGap .latch hOnly
    have hExact := rescaleNoEventsPlan
      (correctionTensorLabelsNone (fun e he => (hOnly e he).2.2)) hNil
    left
    rw [hSplit,hSplit']
    refine ⟨?_ , ?_⟩
    · exact rescalePlanAppend hPlan0 (rescalePlanAppend hPlan1 (rescalePlanExactToPrefix hExact))
    · rw [rescaleVoteLabelsAppend,rescaleVoteLabelsAppend,hVote,hVote',hNil]
      exact Nat.le_refl 2
  · have hNil := noVotesInGap .latch hOnly
    have hExact := rescaleNoEventsPlan
      (correctionTensorLabelsNone (fun e he => (hOnly e he).2.2)) hNil
    right
    refine ⟨v,pre++mid++after,remain,visits',?_,hV,hF'',?_,?_,hRemain⟩
    · simp only [hSplit,hSplit',hSplit'',List.append_assoc]
    · exact rescalePlanExactAppend (rescalePlanExactAppend hPlan0 hPlan1) hExact
    · rw [rescaleVoteLabelsAppend,rescaleVoteLabelsAppend,hVote,hVote',hNil]
      rfl

private theorem rescaleFaultedTrace {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {fault : Fault} (hFault : s.fault = some fault)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    correctionTensorLabels events = [] ∧ rescaleVoteLabels events = [] := by
  have hOut : out kernel Assumptions.all l g s = .ev (.ub fault) := by simp [out,hFault]
  cases hw with
  | stop =>
    exact ⟨correctionTensorLabelsNone (by simp),rfl⟩
  | tau ht _ =>
    have h := hOut.symm.trans ht
    cases h
  | ev he _ =>
    obtain ⟨_,hEq,hFire⟩ := he
    obtain rfl := Out.ev.inj (hOut.symm.trans hEq)
    cases hFire.2
  | last he =>
    obtain ⟨_,hEq,hFire⟩ := he
    obtain rfl := Out.ev.inj (hOut.symm.trans hEq)
    obtain rfl := hFire.1
    exact ⟨correctionTensorLabelsNone (by simp [isTcData]),rfl⟩

set_option maxRecDepth 10000 in
private theorem resumedRescaleAcc {l : Launch} {g : Nat} {s t : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hs : s.sub = 0) (hAcc : s.acc = []) (ht : t.pc = 8006) : t.acc = [] := by
  have start := Softmax.scratchStateOfClear ⟨hs,hAcc⟩
  have hScratch : Softmax.ScoreScratchState t := by
    clear ht
    induction h with
    | refl => exact start
    | tail _ hStep ih => exact Softmax.scoreScratchTau hStep ih
  have hClear : Softmax.ScoreScratchClear t := by
    simpa only [Softmax.ScoreScratchState,ht,Flow.code_8006, Op.isLocal, Bool.false_eq_true,
      ite_false, Softmax.ScoreScratchReady] using hScratch
  exact hClear.2

/-- The actual finite rescale trace follows its recorded ballot schedule. Reaching
finalization consumes all remaining rescale votes, while a prefix may stop in any stage. -/
theorem correctionRescaleTraceDecompose {l : Launch} {g steps : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hPc : s.pc = 8006) (hFrame : CorrectionRescaleFrame s (b32 (2^32-steps)))
    (hLo : 2 ≤ steps) (hHi : steps ≤ 2^32) :
    (List.IsPrefix (correctionTensorLabels events)
      (rescaleVoteSchedule (rescaleVoteLabels events)) ∧
      (rescaleVoteLabels events).length ≤ 2*(steps-1)) ∨
    ∃ u pre tail rest, events = pre ++ tail ∧ u.pc = 8447 ∧
      correctionTensorLabels pre = rescaleVoteSchedule (rescaleVoteLabels pre) ∧
      (rescaleVoteLabels pre).length = 2*(steps-1) ∧
      Walk kernel Assumptions.all l g u tail rest := by
  induction steps using Nat.strong_induction_on generalizing s events visits with
  | h steps ih =>
    rcases rescalePassDecompose hw hPc hFrame with ⟨hPrefix,hSize⟩ |
      ⟨u,pre,tail,rest,hSplit,hU,hF,hPre,hSize,hWalk⟩
    · exact .inl ⟨hPrefix,by omega⟩
    cases hFault : u.fault with
    | some fault =>
      obtain ⟨hEmpty,hNoVotes⟩ := rescaleFaultedTrace hFault hWalk
      have hExact := rescaleNoEventsPlan hEmpty hNoVotes
      left
      rw [hSplit]
      refine ⟨rescalePlanAppend hPre (rescalePlanExactToPrefix hExact),?_⟩
      rw [rescaleVoteLabelsAppend,List.length_append,hSize,hNoVotes]
      simp
      omega
    | none =>
      obtain ⟨v,hRun,hV,_,hSub,hCount⟩ := rescaleCounterStep hU hFault hF.counter hLo hHi
      rcases walkAfterRescaleDecision (run_rtg hRun) hWalk with rfl | ⟨visits',hRest⟩
      · left
        rw [hSplit,List.append_nil]
        exact ⟨rescalePlanExactToPrefix hPre,by omega⟩
      by_cases hEnd : steps = 2
      · have hFinal : v.pc = 8447 := by simpa only [hEnd,↓reduceIte] using hV
        exact .inr ⟨v,pre,tail,visits',hSplit,hFinal,hPre,by omega,hRest⟩
      have hBack : v.pc = 8006 := by simpa only [hEnd,↓reduceIte] using hV
      have hSub' : v.sub = 0 := by have hs := hF.sub; omega
      have hAcc' := resumedRescaleAcc (run_rtg hRun) hF.sub hF.acc hBack
      have hFrame' : CorrectionRescaleFrame v (b32 (2^32-(steps-1))) := ⟨hSub',hAcc',hCount⟩
      rcases ih (steps-1) (by omega) hRest hBack hFrame' (by omega) (by omega) with
        ⟨hPrefix,hBound⟩ | ⟨final,more,after,walk,hSplit',hFinal,hMore,hLen,hAfter⟩
      · left
        rw [hSplit]
        refine ⟨rescalePlanAppend hPre hPrefix,?_⟩
        rw [rescaleVoteLabelsAppend,List.length_append,hSize]
        omega
      · right
        refine ⟨final,pre++more,after,walk,by rw [hSplit,hSplit',List.append_assoc],
          hFinal,rescalePlanExactAppend hPre hMore,?_,hAfter⟩
        rw [rescaleVoteLabelsAppend,List.length_append,hSize,hLen]
        omega

private theorem rescaleVoteLabelEntry {events : List Event} {k : Nat} {label : Fin 2 × BitVec 32}
    (hk : (rescaleVoteLabels events)[k]? = some label) :
    ∃ j e, events[j]? = some e ∧ rescaleVoteLabel e = some label ∧
      (rescaleVoteLabels (events.take j)).length = k := by
  induction events generalizing k with
  | nil => simp [rescaleVoteLabels] at hk
  | cons e tail ih =>
    cases hHead : rescaleVoteLabel e with
    | none =>
      obtain ⟨j,x,hGet,hX,hLength⟩ := ih (by simpa [rescaleVoteLabels,hHead] using hk)
      refine ⟨j+1,x,by simpa using hGet,hX,?_⟩
      simpa [rescaleVoteLabels,hHead] using hLength
    | some head =>
      cases k with
      | zero =>
        refine ⟨0,e,rfl,?_,rfl⟩
        have h : head = label := by simpa [rescaleVoteLabels,hHead] using hk
        exact h ▸ hHead
      | succ k =>
        obtain ⟨j,x,hGet,hX,hLength⟩ := ih (by simpa [rescaleVoteLabels,hHead] using hk)
        refine ⟨j+1,x,by simpa using hGet,hX,?_⟩
        simpa [rescaleVoteLabels,hHead] using congrArg Nat.succ hLength

/-- A projected ballot label has its own event index and the exact projected count before it. -/
theorem rescaleVoteLabelsEntry {events : List Event} {k : Nat} {stage : Fin 2} {word : BitVec 32}
    (hk : (rescaleVoteLabels events)[k]? = some (stage,word)) :
    ∃ j site mask bit, events[j]? = some ⟨site,.vote mask bit word⟩ ∧
      site = (if stage = 0 then 8009 else 8228) ∧
      (rescaleVoteLabels (events.take j)).length = k := by
  obtain ⟨j,⟨site,kind⟩,hGet,hEvent,hLength⟩ := rescaleVoteLabelEntry hk
  cases kind <;> try (simp [rescaleVoteLabel] at hEvent)
  case vote mask bit ballot =>
    split_ifs at hEvent with h0 h1
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hEvent)
      exact ⟨j,site,mask,bit,hGet,h0,hLength⟩
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hEvent)
      exact ⟨j,site,mask,bit,hGet,h1,hLength⟩

/-- Before any later actual event, counting the two decoded vote stations counts exactly
the projected ballot labels, provided those stations emitted their actual votes. -/
theorem rescaleVoteLabelsCount {events : List Event}
    (h : ∀ e ∈ events, e.pc = 8009 ∨ e.pc = 8228 → ∃ mask bit word,
      e.kind = .vote mask bit word) :
    (rescaleVoteLabels events).length =
      events.countP (fun e => e.pc == 8009) + events.countP (fun e => e.pc == 8228) := by
  induction events with
  | nil => rfl
  | cons e tail ih =>
    have hTail := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases h0 : e.pc = 8009
    · obtain ⟨mask,bit,word,hVote⟩ := h e List.mem_cons_self (.inl h0)
      simp [rescaleVoteLabels, rescaleVoteLabel,hVote,h0] at hTail ⊢
      omega
    by_cases h1 : e.pc = 8228
    · obtain ⟨mask,bit,word,hVote⟩ := h e List.mem_cons_self (.inr h1)
      simp [rescaleVoteLabels, rescaleVoteLabel,hVote,h1] at hTail ⊢
      omega
    have hNone : rescaleVoteLabel e = none := by unfold rescaleVoteLabel; split <;> simp [h0,h1]
    simp [rescaleVoteLabels,hNone,h0,h1] at hTail ⊢
    omega

end PTX.Kernels.TmlFa4Fwd.Thread
