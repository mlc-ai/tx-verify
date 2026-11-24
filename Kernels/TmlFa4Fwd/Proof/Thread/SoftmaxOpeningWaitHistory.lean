-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreAcquire
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
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasPhase
import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption

private def openingWait (i : Fin 4) : Fin 10 := ⟨i.val, by omega⟩

set_option maxRecDepth 100000 in
private theorem openingFloor (i : Fin 4) :
    let floor := (waitSite (openingWait i)).pc + 3
    (kernel.code.drop floor).all (fun ins => Thread.staysPastEvent floor ins.op) = true ∧
    Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true := by
  fin_cases i <;> constructor <;> kernel_rfl

private theorem afterOpeningFloor {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (i : Fin 4) (hRun : TraceReach kernel Assumptions.all l g s events t)
    (hPc : (waitSite (openingWait i)).pc + 3 ≤ s.pc) :
    (waitSite (openingWait i)).pc + 3 ≤ t.pc := by
  have h := openingFloor i
  induction hRun with
  | refl => exact hPc
  | tau ht _ ih =>
    exact ih (Thread.eventTailStepOfAudit h.1 h.2 hPc (.inl ⟨rfl,ht⟩))
  | event he _ ih =>
    exact ih (Thread.eventTailStepOfAudit h.1 h.2 hPc (.inr ⟨_,rfl,he⟩))

private theorem openingWaitSuccessTau {l : Launch} {g : Nat} {s u : TState}
    {loc : Loc} {parity : Nat} {acq : Bool} {scope : MbarScope} (i : Fin 4)
    (hs : EStep kernel Assumptions.all l g s
      ⟨(waitSite (openingWait i)).pc,.wait loc parity true acq scope⟩ (some u)) :
    u.pc = (waitSite (openingWait i)).pc + 1 ∧
      ∃ v, Tau kernel Assumptions.all l g u v ∧ v.pc = (waitSite (openingWait i)).pc + 3 := by
  let site := openingWait i
  have hPc : s.pc = (waitSite site).pc := (estep_source_pc hs).symm
  obtain ⟨tm,hOut,hFire⟩ := hs
  have hHealthy : s.fault = none := by
    cases h : s.fault with
    | none => rfl
    | some f =>
      have hTm : tm = .ub f := Out.ev.inj (by simpa [out,h] using hOut.symm)
      subst tm
      exact False.elim (by rcases hFire with ⟨hBad,_⟩; cases congrArg Event.kind hBad)
  have hCode := (waitCode site).1
  rw [← hPc] at hCode
  have hTemplate := out_event (A := Assumptions.all) (L := l) (g := g) hHealthy hCode rfl rfl
  have hTm := Out.ev.inj (hOut.symm.trans hTemplate)
  subst tm
  cases hLoc : mbarLoc l g s (waitSite site).base 0 with
  | error f =>
    simp only [eventTmpl,tmaTmpl,hLoc,bind,Except.bind,ofExec,widenMbarScope,Fires] at hFire
    rcases hFire with ⟨hBad,_⟩
    cases congrArg Event.kind hBad
  | ok actual =>
    cases hRead : readBits l g s 32 (.reg (waitSite site).phase) with
    | error f =>
      simp only [eventTmpl,tmaTmpl,hLoc,hRead,bind,Except.bind,ofExec,widenMbarScope,Fires] at hFire
      rcases hFire with ⟨hBad,_⟩
      cases congrArg Event.kind hBad
    | ok word =>
      obtain ⟨ok,_,_,hEvent,hState⟩ := fires_wait_at hLoc hRead hFire
      have hOk : ok = true := (Kind.wait.inj (congrArg Event.kind hEvent)).2.2.1.symm
      subst ok
      obtain rfl := hState u rfl
      let after := next (setReg s (waitSite site).result (.pred true))
      have hAfter : after.pc = (waitSite site).pc + 1 := by simp [after,next,setReg,hPc]
      let v := { after with pc := (waitSite site).pc + 3 }
      refine ⟨hAfter,v,?_,rfl⟩
      have hc := (waitCode site).2.1
      rw [←hAfter] at hc
      have hExp : after.pc ∉ Assumptions.swExp2Sites := by
        rw [hAfter]
        fin_cases i <;> decide
      unfold Tau
      have hLd : after.pc ∉ Assumptions.tcLdDataflowSites := by
        rw [hAfter]
        fin_cases i <;> decide
      have hSt : after.pc ∉ Assumptions.delayedTmemSites := by
        rw [hAfter]
        fin_cases i <;> decide
      rw [Assumptions.out_all_eq_nil hExp hLd hSt hc rfl]
      have hFault : after.fault = none := hHealthy
      simp only [out,hFault,hc]
      simp [after,next,setReg,guardHolds,readReg,Op.isLocal,execLocalA,execLocalRule,
        execLocal,Op.rule,execBranch,pure,Except.pure,bind,Except.bind,v]

private theorem afterOpeningSuccess {l : Launch} {g : Nat} {s u t : TState}
    {loc : Loc} {parity : Nat} {acq : Bool} {scope : MbarScope} {events : List Event} (i : Fin 4)
    (hs : EStep kernel Assumptions.all l g s
      ⟨(waitSite (openingWait i)).pc,.wait loc parity true acq scope⟩ (some u))
    (hTail : TraceReach kernel Assumptions.all l g u events t) :
    (waitSite (openingWait i)).pc < t.pc := by
  obtain ⟨hU,v,hStep,hV⟩ := openingWaitSuccessTau i hs
  cases hTail with
  | refl => omega
  | tau ht tail =>
    have hEq := tau_det ht hStep
    subst v
    have hFloor := afterOpeningFloor i tail (hV.ge)
    omega
  | event he _ => exact False.elim (not_tau_of_stops (stops_of_estep he) hStep)

private theorem openingPollMissingAtCursor {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (i : Fin 4)
    (hReach : TraceReach kernel Assumptions.all l g s events t)
    (ht : t.pc = (waitSite (openingWait i)).pc) :
    ∀ e ∈ events, (waitSite (openingWait i)).pc + 3 ≤ e.pc ∨
      (e.pc = (waitSite (openingWait i)).pc ∧
        ∃ loc parity acq scope, e.kind = .wait loc parity true acq scope) → False := by
  induction hReach with
  | refl => simp
  | tau _ _ ih => exact ih ht
  | @event s u t es e hE hTail ih =>
    intro w hm h
    rcases List.mem_cons.mp hm with rfl | hm
    · rcases h with hLate | ⟨hPc,loc,q,acq,scope,hKind⟩
      · have hLo := (estep_source_pc hE).symm ▸ hLate
        have h := openingFloor i
        have hBound := Thread.eventTailStepOfAudit h.1 h.2 hLo (.inr ⟨_,rfl,hE⟩)
        have hEnd := afterOpeningFloor i hTail hBound
        omega
      · have hEq : w = ⟨(waitSite (openingWait i)).pc,.wait loc q true acq scope⟩ := by
          cases w
          simp_all
        rw [hEq] at hE
        have hEnd := afterOpeningSuccess i hE hTail
        omega
    · exact ih ht w hm h

/-- A lane stopped at the opening statistics acknowledgement has acquired no statistics credit. -/
theorem noStatisticsCreditAtOpeningCursor {l : Launch} {X : Execution} {g : Nat} {s t : TState}
    (hr : Run kernel Assumptions.all l g {} (X.tr g) (some s))
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (ht : t.pc = 3420) :
    ¬ ∃ pos, Thread.Scores.CreditAcquired X (g,pos) := by
  rintro ⟨pos,ha⟩
  obtain ⟨e,he,hMark⟩ := creditObservationOfAcquire ha
  have hMem : e ∈ X.tr g := List.mem_of_getElem? he
  unfold Thread.Scores.creditAcquired at hMark
  split at hMark
  · rename_i loc parity acq scope hKind
    have hSite : e.pc ∈ [3420,4874,6558,7463,7738] := List.contains_iff_mem.mp hMark
    have hStep := openingPollMissingAtCursor 0
      (hr.returning_reach.append (TraceReach.of_local hl)) ht e
      (by simpa only [List.append_nil] using hMem)
    apply hStep
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
    rcases hSite with h | h | h | h | h
    · exact .inr ⟨h,loc,parity,acq,scope,hKind⟩
    all_goals exact .inl (by rw [h]; decide)
  · cases hMark

/-- A lane stopped at the opening score wait has no successful opening score acquire. -/
theorem noScoreAtOpeningCursor {l : Launch} {X : Execution} {g : Nat} {s t : TState}
    (hr : Run kernel Assumptions.all l g {} (X.tr g) (some s))
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (ht : t.pc = 3425) (stage : Fin 2) :
    ¬ ∃ pos, Thread.Scores.FirstScoreAcquire l X (g,pos) stage := by
  rintro ⟨pos,ha⟩
  have hMem := List.mem_of_getElem? ha.decoded
  exact openingPollMissingAtCursor 1 (hr.returning_reach.append (TraceReach.of_local hl)) ht
    _ (by simpa only [List.append_nil] using hMem) (.inr ⟨rfl,_,0,true,.cta,rfl⟩)

/-- A lane stopped at the first Bias poll has not acquired its physical Bias buffer. -/
theorem noBiasAtOpeningCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat} {s t : TState}
    (hr : Run kernel Assumptions.all l g {} (X.tr g) (some s))
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (ht : t.pc = 3498) (stage : Fin 2) (hw : Prologue.warpIndex l g < 8)
    (hStage : Prologue.warpIndex l g / 4 = stage.val) :
    okPolls (Thread.Loader.biasReadyObject l (g/l.block) stage) (X.tr g) = 0 := by
  have hCount := Thread.Softmax.softmaxBiasSourceCount hp hX (j := (X.tr g).length)
    stage hw rfl hStage
  rw [List.take_length] at hCount
  rw [←hCount]
  apply List.countP_eq_zero.mpr
  intro e hm
  by_contra hNot
  have hMark : readSuccess e = true := by simpa only [Bool.not_eq_false] using hNot
  unfold readSuccess at hMark
  split at hMark
  · rename_i loc parity acq scope hKind
    simp only [Bool.or_eq_true,beq_iff_eq] at hMark
    have hStep := openingPollMissingAtCursor 2
      (hr.returning_reach.append (TraceReach.of_local hl)) ht e
      (by simpa only [List.append_nil] using hm)
    rcases hMark with h | h
    · exact hStep (.inr ⟨h,loc,parity,acq,scope,hKind⟩)
    · exact hStep (.inl (by rw [h]; decide))
  · cases hMark



private theorem openingStatisticsFloorInPath {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (hr : TraceReach kernel Assumptions.all l g s events t)
    (hs : 3423 ≤ s.pc) : ∀ e ∈ events, 3423 ≤ e.pc := by
  obtain ⟨_,hRun,_⟩ := hr.returnedPrefix
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hRun
  exact Thread.eventTailEvents (openingFloor 0).1 (openingFloor 0).2 hWalk hs

private theorem noOpeningStatisticsAfterSuccess {l : Launch} {g : Nat} {s u t : TState}
    {loc : Loc} {parity : Nat} {acq : Bool} {scope : MbarScope} {events : List Event}
    (hs : EStep kernel Assumptions.all l g s ⟨3420,.wait loc parity true acq scope⟩ (some u))
    (hr : TraceReach kernel Assumptions.all l g u events t) :
    ∀ e ∈ events, e.pc ≠ 3420 := by
  obtain ⟨_,v,hv,hPc⟩ := openingWaitSuccessTau 0 hs
  cases hr with
  | refl => simp
  | tau ht tail =>
    obtain rfl := tau_det hv ht
    intro e hm
    have hFloor := openingStatisticsFloorInPath tail (by rw [hPc]; decide) e hm
    omega
  | event he _ => exact (not_tau_of_stops (stops_of_estep he) hv).elim

private theorem creditCountAtOpeningAck {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (hr : TraceReach kernel Assumptions.all l g s events t)
    (ht : t.pc = 4874) : events.countP Thread.Scores.creditAcquired ≤ 1 := by
  induction hr with
  | refl => simp
  | tau _ _ ih => exact ih ht
  | @event s u t events e hStep hTail ih =>
    rw [List.countP_cons]
    by_cases hCredit : Thread.Scores.creditAcquired e = true
    · have onlyFirst {ev : Event} (hMem : ev ∈ e::events)
          (hCredit : Thread.Scores.creditAcquired ev = true) :
          ev.pc = 3420 ∧ ∃ loc q acq scope, ev.kind = .wait loc q true acq scope := by
        unfold Thread.Scores.creditAcquired at hCredit
        split at hCredit
        · rename_i loc q acq scope hk
          have hSite := List.contains_iff_mem.mp hCredit
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
          have hStop := openingPollMissingAtCursor 3 (.event hStep hTail) ht ev hMem
          refine ⟨?_,loc,q,acq,scope,hk⟩
          rcases hSite with h | h | h | h | h
          · exact h
          · exact (hStop (.inr ⟨h,loc,q,acq,scope,hk⟩)).elim
          all_goals exact (hStop (.inl (by rw [h]; decide))).elim
        · cases hCredit
      obtain ⟨hPc,loc,q,acq,scope,hKind⟩ := onlyFirst List.mem_cons_self hCredit
      have hEvent : e = ⟨3420,.wait loc q true acq scope⟩ := by
        cases e
        exact congrArg₂ Event.mk hPc hKind
      have hNo := noOpeningStatisticsAfterSuccess (hEvent ▸ hStep) hTail
      have hZero : events.countP Thread.Scores.creditAcquired = 0 := by
        apply List.countP_eq_zero.mpr
        intro ev hm
        cases hc : Thread.Scores.creditAcquired ev
        · decide
        · exact (hNo ev hm (onlyFirst (List.mem_cons_of_mem _ hm) hc).1).elim
      simp [hCredit,hZero]
    · simpa [hCredit] using ih ht

/-- A lane suspended at the first probability acknowledgement has at most the
opening statistics credit in its entire recorded trace. -/
theorem atMostOneCreditAtOpeningAck {l : Launch} {X : Execution} {g : Nat} {s t : TState}
    (hr : Run kernel Assumptions.all l g {} (X.tr g) (some s))
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (ht : t.pc = 4874) : (Thread.Scores.before X (g,(X.tr g).length)).credits ≤ 1 := by
  rw [Thread.Scores.beforeCredits,List.take_length]
  have hPath := hr.returning_reach.append (TraceReach.of_local hl)
  rw [List.append_nil] at hPath
  exact creditCountAtOpeningAck hPath ht

end PTX.Kernels.TmlFa4Fwd.Softmax
