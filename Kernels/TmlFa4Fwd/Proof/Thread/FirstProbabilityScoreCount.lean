-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
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
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Lemmas.Execution.EventFrameSource
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityGate
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Lemmas.Flow.NthEv
import Lemmas.Flow.Next
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame Prologue Softmax

set_option maxRecDepth 100000 in
private theorem repeatedScoreFloor :
    (kernel.code.drop 5009).all (fun i => staysPastEvent 5009 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem repeatedScoreSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (site < 5009 ∨ 5009 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstScoreSuccessFloor :
    (kernel.code.drop 3428).all (fun i => staysPastEvent 3428 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstScoreSuccessSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (3428 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem firstScoreSuccessLeavesPoll {l : Launch} {g : Nat} {s u : TState}
    {loc : Loc} {phase : Nat} {acq : Bool} {scope : MbarScope}
    (he : EStep kernel Assumptions.all l g s ⟨3425,.wait loc phase true acq scope⟩ (some u)) :
    ∃ v, v.pc = 3428 ∧ Tau kernel Assumptions.all l g u v := by
  have hs : s.pc = 3425 := (estep_source_pc he).symm
  have hClear : s.fault = none := by
    obtain ⟨event,hOut,hFire⟩ := he
    cases h : s.fault with
    | none => rfl
    | some bad =>
      simp only [out,h,Out.ev.injEq] at hOut
      subst event
      cases hFire.2
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  rw [hs,Flow.code_3425] at hCode
  obtain rfl := Option.some.inj hCode
  obtain ⟨obj,q,ok,mode,hEvent,rfl⟩ := fires_wait hFire
  have hOk : ok = true := (Kind.wait.inj (congrArg Event.kind hEvent)).2.2.1.symm
  subst ok
  let s' := next (setReg s 9751 (.pred true))
  have hp : s'.pc = 3426 := by simp [s',next,setReg,hs]
  have hf : s'.fault = none := by simp [s',next,setReg,hClear]
  have hReg : s'.regs 9751 = some (.pred true) := by simp [s',next,setReg]
  let v := {s' with pc := 3428}
  refine ⟨v,rfl,?_⟩
  change Tau kernel Assumptions.all l g s' v
  have hc : kernel.code[s'.pc]? = _ := hp.symm ▸ Flow.code_3426
  have hOff : s'.pc ∉ Assumptions.swExp2Sites := by rw [hp]; decide
  apply tauStep_iff.mp
  rw [Assumptions.tauStep_all_eq_nil hOff hc rfl]
  simp [tauStep,out,hc,hf,guardHolds,readReg,hReg,bind,Except.bind,pure,Except.pure,
    Op.isLocal,execLocalA,execLocalRule,execLocal,Op.rule,execBranch,v]

private theorem afterFirstScoreSuccess {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j k : Nat}
    {loc : Loc} {phase : Nat} {acq : Bool} {scope : MbarScope} {e : Event}
    (he : X.get (g,j) = some ⟨3425,.wait loc phase true acq scope⟩)
    (hf : X.get (g,k) = some e) (hOrder : j < k) : 3428 ≤ e.pc := by
  have hK : k < (X.tr g).length := len_of_get hf
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨_,u,hStep,hRest⟩ := hRun.after_event he (by omega)
  obtain ⟨v,hV,hLocal⟩ := firstScoreSuccessLeavesPoll hStep
  have hMem : e ∈ (X.tr g).drop (j+1) := by
    apply List.mem_of_getElem? (i := k-(j+1))
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega : j+1 ≤ k)]
    exact hf
  have hSuffix := hRest.after_local_nonempty (.single hLocal)
    (fun h => by rw [h] at hMem; cases hMem)
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hSuffix
  have hSegments site (_hLo : 3428 ≤ site) (hIn : site ∈ Assumptions.swExp2Sites) seg
      (hSeg : cuteExp2.matchAt kernel site = some seg) : 3428 ≤ seg.stop := by
    have hAudit := List.all_eq_true.mp firstScoreSuccessSegments site hIn
    rw [hSeg] at hAudit
    exact of_decide_eq_true hAudit
  exact eventTailEventsOfSegmentFloor firstScoreSuccessFloor hSegments hWalk hV.ge e hMem

private theorem scoreMarkBeforeFirstStore {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos store : Nat}
    (quarter : Fin 4) {address : Nat} {values : List Value} {shape : TcShape}
    (hStore : X.get (g,store) =
      some ⟨probabilityPc .first quarter,.tc (.st address values shape)⟩)
    {e : Event} (he : X.get (g,pos) = some e) (hMark : scoreAcquireMark e = true)
    (hEarlier : pos < store) :
    ∃ loc phase acq scope, e = ⟨3425,.wait loc phase true acq scope⟩ := by
  obtain ⟨site,kind⟩ := e
  cases kind <;> try cases hMark
  rename_i loc phase ok acq scope
  cases ok <;> try cases hMark
  have hCases : site = 3425 ∨ site = 5109 ∨ site = 6676 := by
    simpa [scoreAcquireMark,or_assoc] using hMark
  rcases hCases with rfl | hLate
  · exact ⟨loc,phase,acq,scope,rfl⟩
  · have hlo : probabilityPc .first quarter < 5009 := by fin_cases quarter <;> decide
    have hhi : 5009 ≤ site := by rcases hLate with rfl | rfl <;> decide
    have hSegments site (hSite : 5009 ≤ site) (hIn : site ∈ Assumptions.swExp2Sites) seg
        (hSeg : cuteExp2.matchAt kernel site = some seg) : 5009 ≤ seg.stop := by
      have h := List.all_eq_true.mp repeatedScoreSegments site hIn
      rw [hSeg] at h
      exact (of_decide_eq_true h).resolve_left (Nat.not_lt_of_ge hSite)
    have hAfter := traceOrderOfSegmentFloor hX repeatedScoreFloor hSegments hStore he hlo hhi
    omega

/-- Every first probability quarter has exactly one successful score acquire
in its producer's actual prefix. -/
theorem firstProbabilityScoreCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g store address : Nat} {values : List Value} {shape : TcShape} (stage : Fin 2)
    (hStage : warpIndex l g/4 = stage.val) (quarter : Fin 4)
    (hStore : X.get (g,store) =
      some ⟨probabilityPc .first quarter,.tc (.st address values shape)⟩) :
    okPolls (scoreReadyObject l (g/l.block) stage) ((X.tr g).take store) = 1 := by
  let obj := scoreReadyObject l (g/l.block) stage
  have hSoft : warpIndex l g < 8 := by have := stage.isLt; omega
  obtain ⟨j,e,_,_,_,he,hKind,_,hBefore⟩ :=
    softmaxProbabilityStoreScorePoll hp hX stage hSoft hStage .first quarter hStore
  have hExists : 0 < okPolls obj ((X.tr g).take store) := by
    apply List.countP_pos_iff.mpr
    refine ⟨e,List.mem_of_getElem? ((List.getElem?_take_of_lt hBefore.1.2.1).trans he),?_⟩
    simp [okPoll,sourceWaitSuccess,hKind,obj]
  have hCount := scoreCount (j := store) hp hX stage hSoft rfl hStage
  have hMark : phaseAcquired true = scoreAcquireMark := by
    funext e
    rw [scoreReadyMarkKind]
    rfl
  rw [hMark] at hCount
  have hAtMost : ((X.tr g).take store).countP scoreAcquireMark ≤ 1 := by
    by_contra! hTooMany
    obtain ⟨i0,h0,e0,he0,hM0,hRank0⟩ :=
      PTX.Flow.exists_nth scoreAcquireMark (X.tr g) (n := 0) (Nat.zero_lt_of_lt hTooMany)
    obtain ⟨i1,h1,e1,he1,hM1,hRank1⟩ := PTX.Flow.exists_nth scoreAcquireMark (X.tr g) hTooMany
    have hOrder : i0 < i1 := by
      by_contra! hReverse
      have hLe := countP_take_mono scoreAcquireMark (X.tr g) hReverse
      omega
    obtain ⟨loc0,q0,a0,s0,rfl⟩ := scoreMarkBeforeFirstStore hX quarter hStore he0 hM0 h0
    obtain ⟨loc1,q1,a1,s1,rfl⟩ := scoreMarkBeforeFirstStore hX quarter hStore he1 hM1 h1
    have hPast := afterFirstScoreSuccess hX he0 he1 hOrder
    change 3428 ≤ 3425 at hPast
    omega
  change okPolls obj ((X.tr g).take store) = 1
  rw [hCount] at hAtMost
  change okPolls obj ((X.tr g).take store) ≤ 1 at hAtMost
  omega

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
