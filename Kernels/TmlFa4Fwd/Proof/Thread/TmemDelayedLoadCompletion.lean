-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TensorLoadSites
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Lemmas.Order.OrderBaseCausality
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
import Lemmas.Flow.Async

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Softmax

private def round (repeated : Bool) : Round := if repeated then .biased else .first

private def delayedWindow (repeated : Bool) : ScoreWindow :=
  if repeated then .biasedBody else .firstRoundCounters

private def windowStart (repeated : Bool) : Nat := (windowSite (delayedWindow repeated)).head

private def loadWaitSite (repeated : Bool) : Nat := probabilityPc (round repeated) 0

private def preservedRegister (repeated : Bool) : Nat := if repeated then 1062 else 1225

private def beforeLoadWait (repeated : Bool) (s : TState) : Prop :=
  windowStart repeated ≤ s.pc ∧ s.pc ≤ loadWaitSite repeated ∧ s.sub ≤ 3 ∧
    ScoreScratchState s ∧ (s.pc = loadWaitSite repeated → s.sub = 0)

private def checkedOp (repeated : Bool) (ins : Instr) : Bool :=
  (ins.op.isLocal || (scoreEventOp ins.op &&
    !(scoreEventWrites ins.op).contains (preservedRegister repeated))) &&
    match ins.op with
    | .bra target _ => target ≤ loadWaitSite repeated
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem beforeWaitCode (repeated : Bool) :
    ((kernel.code.drop (windowStart repeated)).take
      (loadWaitSite repeated - windowStart repeated)).all (checkedOp repeated) = true :=
  by cases repeated <;> decide +kernel

private theorem beforeWaitChecked {repeated : Bool} {pc : Nat} {ins : Instr}
    (hLo : windowStart repeated ≤ pc) (hHi : pc < loadWaitSite repeated)
    (hc : kernel.code[pc]? = some ins) : checkedOp repeated ins = true := by
  apply List.all_eq_true.mp (beforeWaitCode repeated) ins
  apply List.mem_of_getElem? (i := pc - windowStart repeated)
  rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]

private theorem beforeWaitSegment {repeated : Bool} {pc : Nat} {seg : SegMatch CuteSlot}
    (hLo : windowStart repeated ≤ pc) (hHi : pc < loadWaitSite repeated)
    (hs : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some seg) :
    seg.stop ≤ loadWaitSite repeated := by
  have hAll (b : Bool) : Assumptions.swExp2Sites.all (fun q =>
      if windowStart b ≤ q ∧ q < loadWaitSite b then
        match cuteExp2.matchAt kernel q with
        | some s => decide (s.stop ≤ loadWaitSite b)
        | none => false
      else true) = true := by cases b <;> decide +kernel
  have h := List.all_eq_true.mp (hAll repeated) _ hs
  rw [ite_eq_left ⟨hLo,hHi⟩, hm] at h
  exact of_decide_eq_true h

private theorem beforeLoadWaitStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    {repeated : Bool} (hs : beforeLoadWait repeated s) (hBefore : s.pc < loadWaitSite repeated)
    (he : WStep kernel Assumptions.all l g s e u) : beforeLoadWait repeated u := by
  let window := delayedWindow repeated
  have hsHi : s.pc < (windowSite window).stop := by
    have hEnd : loadWaitSite repeated < (windowSite window).stop := by cases repeated <;> decide
    omega
  have hSub := hs.2.2.1
  obtain ⟨hl, _, hU, _, _⟩ := windowStepFrame window hs.1 hsHi hSub he
  have hScratch := windowStepScratch window hs.1 hsHi hSub he hs.2.2.2.1
  refine ⟨hl, ?_, hU, hScratch, ?_⟩
  · rcases he with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
    · obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
      have hAudit := (Bool.and_eq_true_iff.mp (beforeWaitChecked hs.1 hBefore hc)).2
      rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
      · change s.pc + 1 ≤ _
        omega
      rcases scoreExecLocal hLocal with hFrame | ⟨seg, hSite, hMatch, hRun⟩
      · have hn := hFrame.pc
        cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hn
        case bra target uniform =>
          rw [hn]
          exact of_decide_eq_true (by simpa only [ho] using hAudit)
        case brx => simp [ho] at hAudit
        all_goals omega
      · exact (scoreSegmentFrame hRun).1.symm ▸ beforeWaitSegment hs.1 hBefore hSite hMatch
    · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
      have hAudit := (Bool.and_eq_true_iff.mp (beforeWaitChecked hs.1 hBefore hc)).1
      simp only [hLocal, Bool.false_or, Bool.and_eq_true] at hAudit
      have hn : preservedRegister repeated ∉ scoreEventWrites ins.op := by simpa using hAudit.2
      rcases (scoreEventStep hc hAudit.1 hSub hn he).1.pc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  · intro hHere
    rcases he with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
    · obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
      rcases hExec with ⟨rfl,_⟩ | ⟨_,hLocal,hExec⟩
      · rfl
      rcases scoreExecLocal hExec with hFrame | ⟨_,_,_,hRun⟩
      · exact hFrame.sub.trans (scratchClearOfLocal hc hLocal hs.2.2.2.1).1
      · exact (scoreSegmentFrame hRun).2.1
    · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
      have hAudit := (Bool.and_eq_true_iff.mp (beforeWaitChecked hs.1 hBefore hc)).1
      simp only [hLocal, Bool.false_or, Bool.and_eq_true] at hAudit
      have hn : preservedRegister repeated ∉ scoreEventWrites ins.op := by simpa using hAudit.2
      have hInitial : ScoreScratchReady ins.op s := by simpa [ScoreScratchState, hc, hLocal] using
        hs.2.2.2.1
      have hClear := scoreEventScratch hc hAudit.1 hSub hn he hInitial
      have hDifferent : u.pc ≠ s.pc := by omega
      exact (show ScoreScratchClear u from by simpa [hDifferent] using hClear).1

private theorem atLoadWaitCode (repeated : Bool) : ∃ ta ss,
    kernel.code[loadWaitSite repeated]? = some ⟨none, .tcSt ta ss .s32x32b⟩ := by
  obtain ⟨ss, _, hCode⟩ := probabilityCode (round repeated) 0
  exact ⟨probabilityReg (round repeated) 0, ss, hCode⟩

private theorem delayedWaitFires {p : Params} {l : Launch} {m : Mem0} {g : Nat}
    {s u : TState} {e : Event} (hp : Pre p l m) {repeated : Bool}
    (hs : beforeLoadWait repeated s) (hHere : s.pc = loadWaitSite repeated)
    (he : EStep kernel Assumptions.all l g s e (some u)) : e.kind = .tc .waitLd := by
  obtain ⟨ta, ss, hc⟩ := atLoadWaitCode repeated
  obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source he
  rw [hHere,hc] at hCode
  obtain rfl := Option.some.inj hCode.symm
  have hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = true := by
    rw [hHere, Assumptions.all_tcStWaitLd]
    cases repeated <;> decide
  rw [eventTmpl_tcSt_wait hHook (hs.2.2.2.2 hHere) (by rw [hp.block])] at hFire
  exact congrArg Event.kind hFire.1

private theorem delayedWaitInTail {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {events : List Event} {visits : List Visit} {repeated : Bool}
    (hw : Walk kernel Assumptions.all l g s events visits) (hs : beforeLoadWait repeated s)
    {finish : Nat} {endEvent : Event} (hEnd : events[finish]? = some endEvent)
    (hOutside : ¬ (windowStart repeated ≤ endEvent.pc ∧ endEvent.pc ≤ loadWaitSite repeated)) :
    ∃ k < finish, events[k]? = some ⟨loadWaitSite repeated, .tc .waitLd⟩ := by
  induction hw generalizing finish with
  | stop => simp at hEnd
  | @tau s u es vs ht _ ih =>
    have hBefore : s.pc < loadWaitSite repeated := by
      by_contra! hn
      have hHere : s.pc = loadWaitSite repeated := by have := hs.2.1; omega
      obtain ⟨ta, ss, hc⟩ := atLoadWaitCode repeated
      obtain ⟨ins, hCode, _, hExec⟩ := tauScoreSource ht
      rw [hHere,hc] at hCode
      obtain rfl := Option.some.inj hCode.symm
      rcases hExec with ⟨_,hh⟩ | ⟨_,hh,_⟩ <;> cases hh
    exact ih (beforeLoadWaitStep hs hBefore (.inl ⟨rfl,ht⟩)) hEnd
  | @ev s u e es vs he _ ih =>
    have hPositive : 0 < finish := by
      by_contra! hn
      have hZero : finish = 0 := by omega
      subst finish
      obtain rfl : e = endEvent := Option.some.inj hEnd
      rw [estep_source_pc he] at hOutside
      exact hOutside ⟨hs.1,hs.2.1⟩
    by_cases hHere : s.pc = loadWaitSite repeated
    · have hKind := delayedWaitFires hp hs hHere he
      have hPc := (estep_source_pc he).trans hHere
      obtain ⟨pc,kind⟩ := e
      change pc = loadWaitSite repeated at hPc
      cases hKind
      cases hPc
      exact ⟨0,hPositive,rfl⟩
    · have hBefore : s.pc < loadWaitSite repeated := by have := hs.2.1; omega
      cases finish with
      | zero => cases hPositive
      | succ finish =>
        obtain ⟨k,hk,hEvent⟩ :=
          ih (beforeLoadWaitStep hs hBefore (.inr ⟨_,rfl,he⟩)) hEnd
        exact ⟨k+1,by omega,hEvent⟩
  | last he =>
    have hLen := (List.getElem?_eq_some_iff.mp hEnd).1
    simp only [List.length_cons, List.length_nil] at hLen
    have hZero : finish = 0 := by omega
    subst finish
    obtain rfl := Option.some.inj hEnd
    rw [estep_source_pc he] at hOutside
    exact (hOutside ⟨hs.1,hs.2.1⟩).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem delayedScoreLoadWaitRecordedBeforeEvent {i : EvId} {repeated : Bool}
    {quarter : Fin 4} (hLoad : DelayedScoreLoad X i repeated quarter) {finish : Nat} {later : Event}
    (hLater : X.get (i.1,finish) = some later) (hBefore : i.2 < finish)
    (hOutside : ¬ (windowStart repeated ≤ later.pc ∧ later.pc ≤ loadWaitSite repeated)) :
    ∃ j, i.2 < j ∧ j < finish ∧
      X.get (i.1,j) = some ⟨if repeated then 6508 else 4826,.tc .waitLd⟩ := by
  obtain ⟨g,index⟩ := i
  obtain ⟨_,_,_,he⟩ := hLoad.decoded
  let site := scorePc (round repeated) quarter
  have hs : 3420 ≤ site ∧ site < 7742 ∧ windowStart repeated ≤ site+1 ∧
      site+1 < loadWaitSite repeated := (by decide : ∀ b q,
        3420 ≤ scorePc (round b) q ∧ scorePc (round b) q < 7742 ∧
        windowStart b ≤ scorePc (round b) q + 1 ∧ scorePc (round b) q + 1 < loadWaitSite b)
      repeated quarter
  have hLen : finish < (X.tr g).length := PTX.len_of_get hLater
  obtain ⟨t,u,_,_,hSub,hScratch,hStep,hw⟩ :=
    softmaxAfterRecordedEvent hp hX he hs.1 hs.2.1 (by omega)
  have ht : t.pc = site := (estep_source_pc hStep).symm
  obtain ⟨ds,_,hCode⟩ := scoreCode (round repeated) quarter
  obtain ⟨ins,hc,_,hFire⟩ := estep_event_source hStep
  rw [ht, hCode] at hc
  obtain rfl := Option.some.inj hc.symm
  have hPlain : decide (round repeated = .unbiased) = false := by cases repeated <;> decide
  have hHook : Assumptions.all.any (·.tcLdWait t.pc) = false :=
    ht.symm ▸ (scoreWaitHook (round repeated) quarter).trans hPlain
  obtain ⟨_,vs,_,_,hu⟩ := fires_tcLd (by intro _ h; cases h) hFire hHook
  have hPc : u.pc = site+1 := by rw [hu,setRegs_pc]; exact congrArg (·+1) ht
  have hStart : beforeLoadWait repeated u := ⟨by omega, by omega, hSub, hScratch,
    fun h => (by omega : False).elim⟩
  have hTerm : ((X.tr g).drop (index+1))[finish-(index+1)]? = some later := by
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega : index+1 ≤ finish)]
    exact hLater
  obtain ⟨k,hK,hWait⟩ := delayedWaitInTail hp hw hStart hTerm hOutside
  rw [List.getElem?_drop] at hWait
  have hRecorded : X.get (g,index+1+k) = some ⟨loadWaitSite repeated,.tc .waitLd⟩ := hWait
  have hSite : loadWaitSite repeated = if repeated then 6508 else 4826 := by
    cases repeated <;> decide
  exact ⟨index+1+k,by omega,by omega,hSite ▸ hRecorded⟩

/-- A biased score load's actual wait is recorded at its round's probability-store entry. -/
theorem delayedScoreLoadWaitRecordedBeforeRelease {i d : EvId} {repeated : Bool} {quarter : Fin 4}
    (hScope : i.1/l.block = d.1/l.block) (hLoad : DelayedScoreLoad X i repeated quarter)
    (hd : Deallocation X d) :
    ∃ j, i.2 < j ∧ X.get (i.1,j) = some ⟨if repeated then 6508 else 4826,.tc .waitLd⟩ ∧
      TcMma.WaitBefore l X .waitLd i d := by
  obtain ⟨g,index⟩ := i
  obtain ⟨_,_,_,he⟩ := hLoad.decoded
  have hData : TensorDataEvent X (g,index) := ⟨_,he,.inl rfl⟩
  obtain ⟨finish, mode, hLater, hFinal⟩ :=
    (tensorDataFinalArrivalBeforeDeallocation hp hX hScope hData hd).1
  obtain ⟨source, hSource, hFinalGet⟩ := hFinal.decoded
  have hOutside : ¬ (windowStart repeated ≤ source ∧ source ≤ loadWaitSite repeated) :=
    (by decide : ∀ b s, s ∈ [2764, 7741, 9204] →
      ¬ (windowStart b ≤ s ∧ s ≤ loadWaitSite b)) repeated source hSource
  obtain ⟨wait,hBefore,_,hRecorded⟩ := delayedScoreLoadWaitRecordedBeforeEvent hp hX hLoad
    hFinalGet (Nat.lt_of_succ_le hLater) hOutside
  have hWaitData : TensorDataEvent X (g,wait) := ⟨_,hRecorded,.inl rfl⟩
  exact ⟨wait,hBefore,hRecorded,⟨(g,wait),⟨_,hRecorded⟩,rfl,hBefore,
    .inl (tensorDataBeforeDeallocation hp hX hScope hWaitData hd)⟩⟩

/-- The selected softmax probability release is past the delayed score-load wait. -/
theorem delayedScoreLoadWaitThroughCredit {load credit consumer : EvId} {stage : Fin 2}
    {repeated : Bool} {quarter : Fin 4} (hLoad : DelayedScoreLoad X load repeated quarter)
    (hCredit : Scores.ProbabilityCredit l X credit (load.1/l.block) stage 0)
    (hBefore : TraceBefore X load credit) (hConsumer : baseCausality l X credit consumer) :
    TcMma.WaitBefore l X .waitLd load consumer := by
  obtain ⟨g,index⟩ := load
  obtain ⟨g',finish⟩ := credit
  have hSame : g = g' := hBefore.1
  subst g'
  obtain ⟨source,he⟩ := hCredit
  have hSite := actualProbabilityArrivalSite hp hX he
    (show 96+8*stage.val+16*(0 : Fin 2).val ∈ [96,104,112,120] by fin_cases stage <;> decide) rfl
  have hOutside : ¬ (windowStart repeated ≤ source ∧ source ≤ loadWaitSite repeated) := by
    rcases hSite with ⟨arrival,rfl⟩ | hSites
    · cases repeated <;> fin_cases arrival <;> decide
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hSites
      rcases hSites with rfl | rfl | rfl | rfl | rfl | rfl <;> cases repeated <;> decide
  obtain ⟨k,hK,hOrder,hWait⟩ := delayedScoreLoadWaitRecordedBeforeEvent hp hX hLoad
    he hBefore.2.1 hOutside
  have hPo := po_of_source_not_access (e := (g,k)) (f := (g,finish)) rfl hOrder
    (PTX.len_of_get he) (by rw [hWait]; rfl)
  exact ⟨(g,k),⟨_,hWait⟩,rfl,hK,.inl ((Relation.TransGen.single (.inl hPo)).trans hConsumer)⟩

/-- Every biased score load completes at the actual load wait before the probability store. -/
theorem delayedScoreLoadCompletedBeforeRelease {i d : EvId} {repeated : Bool} {quarter : Fin 4}
    (hScope : i.1/l.block = d.1/l.block) (hLoad : DelayedScoreLoad X i repeated quarter)
    (hd : Deallocation X d) :
    TcMma.WaitBefore l X .waitLd i d := by
  obtain ⟨_,_,_,hBefore⟩ := delayedScoreLoadWaitRecordedBeforeRelease hp hX hScope hLoad hd
  exact hBefore

/-- Every actual Tensor Memory load in the releasing CTA has completed before release. -/
theorem tensorLoadCompletedBeforeRelease {i d : EvId} {address : Nat} {values : List Value}
    {shape : TcShape} (hScope : i.1 / l.block = d.1 / l.block) (h : X.TLd i address values shape)
    (hd : Deallocation X d) : TcMma.WaitBefore l X .waitLd i d := by
  rcases tensorLoadCompletedBeforeReleaseOrDelayed hp hX hScope h hd with hDone | ⟨_,_,hDelayed⟩
  · exact hDone
  · exact delayedScoreLoadCompletedBeforeRelease hp hX hScope hDelayed hd

end PTX.Kernels.TmlFa4Fwd.Thread
