-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOutputReadyTrace
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
public import Kernels.TmlFa4Fwd.Proof.SoftmaxExitPublications
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Lemmas.Flow.EventCont
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Assumption PTX.Flow PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Softmax

/-- An early packet credit from the plain softmax loop. -/
@[no_expose] def PlainProbabilityCredit (l : Launch) (X : Execution) (i : EvId)
    (cta : Nat) (stage : Fin 2) : Prop :=
  X.get i = some ⟨7437, .arrive (probabilityObject l cta stage 0) 0 1 true .cta⟩

theorem PlainProbabilityCredit.credit {l : Launch} {X : Execution} {i : EvId}
    {cta : Nat} {stage : Fin 2} (h : PlainProbabilityCredit l X i cta stage) :
    ProbabilityCredit l X i cta stage 0 :=
  ⟨_, h⟩

set_option maxRecDepth 100000 in
private theorem plainLoopFloor :
    (kernel.code.drop 6654).all (fun i => staysPastEvent 6654 i.op) = true := by kernel_rfl

private theorem plainLoopFloorSegments {site : Nat} (hs : 6654 ≤ site)
    (hm : site ∈ Assumptions.swExp2Sites) :
    ∀ seg, cuteExp2.matchAt kernel site = some seg → 6654 ≤ seg.stop := by
  intro seg he
  have hAudit : Assumptions.swExp2Sites.all (fun pc =>
      if 6654 ≤ pc then
        match cuteExp2.matchAt kernel pc with
        | some found => decide (6654 ≤ found.stop)
        | none => false
      else true) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAudit site hm
  simpa only [ite_eq_left hs, he, decide_eq_true_eq] using h

/-- A lane cannot return to either Bias fence once it publishes a plain probability packet. -/
theorem PlainProbabilityCredit.afterBiasFence {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {fence credit : EvId}
    {cta : Nat} {stage : Fin 2} (h : PlainProbabilityCredit l X credit cta stage)
    {repeated : Bool} (hf : BiasOperandFence X fence repeated) (hLane : fence.1 = credit.1) :
    baseCausality l X fence credit := by
  obtain ⟨g, f⟩ := fence
  obtain ⟨g', c⟩ := credit
  change g = g' at hLane
  subst g'
  have hEarly : biasFencePc repeated < 6654 := by cases repeated <;> decide
  have hTrace := traceOrderOfSegmentFloor hX plainLoopFloor
    (fun _ hs hm _ he => plainLoopFloorSegments hs hm _ he) hf.decoded
    (show X.get (g,c) = some ⟨7437, .arrive (probabilityObject l cta stage 0) 0 1 true .cta⟩
      from h) hEarly (show 6654 ≤ 7437 by decide)
  exact .single (.inl (po_of_not_access rfl hTrace (len_of_get h) (by rw [h]; rfl)))

private theorem softmaxEarlyCreditSite {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g j cta source tx n : Nat} {rel : Bool} {scope : MbarScope}
    (hw : Prologue.warpIndex l g < 8)
    (h : X.get (g,j) = some ⟨source, .arrive (probabilityObject l cta stage 0) tx n rel scope⟩) :
    source ∈ [4847,6532,7437] := by
  have ho : 96 + 8*stage.val ∈ [96,104,112,120] := by fin_cases stage <;> decide
  rcases actualProbabilityArrivalSite hp hX h ho (by rfl) with ⟨issue,rfl⟩ | hCorr
  · obtain ⟨_,_,_,_,_,hAt⟩ := probabilityArriveFacts hp hX issue h
    have hAddr := congrArg Loc.addr hAt
    change l.sharedBase + (96+8*stage.val) =
      l.sharedBase + ((probabilityArrivalSite issue).offset + 8*(Prologue.warpIndex l g/4))
      at hAddr
    have hW : Prologue.warpIndex l g/4 < 2 := by omega
    have hOff : (probabilityArrivalSite issue).offset ∈ [96,112] :=
      (by decide : ∀ site : Fin 6, (probabilityArrivalSite site).offset ∈ [96,112]) issue
    have hSame : (probabilityArrivalSite issue).offset = 96 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
      have := stage.isLt
      omega
    exact (by decide : ∀ site : Fin 6, (probabilityArrivalSite site).offset = 96 →
      (probabilityArrivalSite site).pc ∈ [4847,6532,7437]) issue hSame
  · have hWarp := (TmlFa4Fwd.Correction.correctionProbabilityCredit hp hX h hCorr).2.2.2.2.1
    omega

private theorem firstCreditOnce {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} :
    (X.tr g).countP (barrierMark 4847) ≤ 1 := by
  have hCode : (kernel.code.drop 4848).all (fun i => staysPastEvent 4848 i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hAudit : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (4848 ≤ seg.stop)
      | none => false) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  by_contra! hTooMany
  obtain ⟨e,he,hm,hCount⟩ := nthEv_spec (n := 0) (Nat.zero_lt_of_lt hTooMany)
  obtain ⟨f,hf,hfMark,hfCount⟩ := nthEv_spec hTooMany
  let a := nthEv X (barrierMark 4847) g 0
  let b := nthEv X (barrierMark 4847) g 1
  have hAB : a < b := by
    by_contra! hLate
    have hMono := (List.take_sublist_take_left (l := X.tr g) hLate).countP_le
      (p := barrierMark 4847)
    change ((X.tr g).take b).countP (barrierMark 4847) ≤
      ((X.tr g).take a).countP (barrierMark 4847) at hMono
    dsimp only [a, b] at hMono
    omega
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  have hb : b < (X.tr g).length := len_of_get hf
  obtain ⟨s,u,hStep,hTail⟩ := hr.after_event he (by omega)
  have hPc := (estep_source_pc hStep).symm.trans (beq_iff_eq.mp hm)
  obtain ⟨ins,hIns,_,hFire⟩ := estep_event_source hStep
  rw [hPc,Flow.code_4847] at hIns
  obtain rfl := Option.some.inj hIns.symm
  have hNext := congrArg TState.pc (fires_arrive_state hFire).1
  change u.pc = s.pc+1 at hNext
  obtain ⟨vs,hWalk⟩ := Mma.walkFromRun hTail
  have hIn : f ∈ (X.tr g).drop (a+1) := by
    apply List.mem_of_getElem? (i := b-(a+1))
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
    exact hf
  have hFloor : 4848 ≤ f.pc := eventTailEvents hCode hAudit hWalk (by omega) f hIn
  have hEnd : f.pc = 4847 := beq_iff_eq.mp hfMark
  omega

/-- At any completed active softmax lane, early packet ordinal eleven and later belong
to the plain loop. At most one priming and ten repeated biased credits can precede it. -/
theorem PlainProbabilityCredit.ofOrdinalAtExit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {credit : EvId} {cta : Nat} {stage : Fin 2} (hCredit : ProbabilityCredit l X credit cta stage 0)
    (hw : Prologue.warpIndex l credit.1 < 8)
    (hWork : cta < tilePrefix p p.batch*p.heads)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    (hExit : Exited X credit.1) (hOrd : 11 ≤ probabilityOrdinal l X cta stage 0 credit) :
    PlainProbabilityCredit l X credit cta stage := by
  obtain ⟨g,j⟩ := credit
  obtain ⟨site,he⟩ := hCredit
  have hg := event_thread_lt hX he
  have hOwner := (probabilityCreditRole hp hX stage 0 ⟨site,he⟩).1
  have hSite := softmaxEarlyCreditSite hp hX stage hw he
  by_cases hPlain : site = 7437
  · subst site
    exact he
  have hEarly : site < 6654 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
    omega
  let obj := probabilityObject l cta stage 0
  have hBool : arrivesOn obj ⟨site,.arrive obj 0 1 true .cta⟩ = true := by
    simp [arrivesOn,sourceArrive]
  have hAfter := countP_take_succ (p := arrivesOn obj) he hBool
  change ((X.tr g).take (j+1)).countP (arrivesOn obj) =
    probabilityOrdinal l X cta stage 0 (g,j)+1 at hAfter
  have hBound : ((X.tr g).take (j+1)).countP (arrivesOn obj) ≤
      ((X.tr g).take (j+1)).countP (fun e => barrierMark 4847 e || barrierMark 6532 e) := by
    apply List.countP_mono_left
    intro e hm hMarked
    obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp hm
    have hLt := (List.getElem?_eq_some_iff.mp hGet).1
    simp only [List.length_take] at hLt
    have hK : k < j+1 := by omega
    rw [List.getElem?_take_of_lt hK] at hGet
    obtain ⟨source,kind⟩ := e
    cases kind <;> try cases hMarked
    rename_i target tx count rel scope
    have hTarget : target = obj := of_decide_eq_true hMarked
    subst target
    have hSites := softmaxEarlyCreditSite hp hX stage hw hGet
    have hNo : source ≠ 7437 := by
      intro h
      subst source
      have hLater := traceOrderOfSegmentFloor hX plainLoopFloor
        (fun _ hs hm _ he => plainLoopFloorSegments hs hm _ he) he hGet hEarly
        (show 6654 ≤ 7437 by decide)
      omega
    simp [barrierMark] at hSites ⊢
    tauto
  have hMono := (List.take_sublist (l := X.tr g) (i := j+1)).countP_le
    (p := fun e => barrierMark 4847 e || barrierMark 6532 e)
  have hSum := (countP_or_disj (l := X.tr g) (p := barrierMark 4847) (q := barrierMark 6532)
    (by intro e _ h
        have h1 : e.pc = 4847 := beq_iff_eq.mp h.1
        have h2 : e.pc = 6532 := beq_iff_eq.mp h.2
        omega))
  have hFirst := firstCreditOnce hX (g := g)
  have hRest := exitedActiveBiasedCreditCap hp hX hg hw (hOwner.symm ▸ hWork)
    hCuQ (usedKProtected hp hX) hExit
  change (X.tr g).countP (barrierMark 6532) ≤ 10 at hRest
  omega

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
