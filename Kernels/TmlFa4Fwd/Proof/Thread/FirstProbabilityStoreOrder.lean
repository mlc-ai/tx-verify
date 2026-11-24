-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
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
import Lemmas.Flow.ElemAccess

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Softmax

set_option maxRecDepth 100000 in
private theorem afterFirstProbabilityCode :
    (kernel.code.drop 4827).all (fun i => Thread.staysPastEvent 4827 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterFirstProbabilitySegments :
    ∀ site, 4827 ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → 4827 ≤ seg.stop := by
  have hAudit : Assumptions.swExp2Sites.all (fun site =>
      if 4827 ≤ site then match cuteExp2.matchAt kernel site with
        | some seg => decide (4827 ≤ seg.stop)
        | none => false
      else true) = true := by kernel_rfl
  intro site hSite hMem seg hMatch
  have h := List.all_eq_true.mp hAudit site hMem
  simpa only [ite_eq_left hSite,hMatch,decide_eq_true_eq] using h

private theorem probabilityStoreAdvances {l : Launch} {g : Nat} {t u : TState}
    {round : Round} (q : Fin 4) {a : Nat} {vals : List Value} {sh : TcShape}
    (he : EStep kernel Assumptions.all l g t ⟨probabilityPc round q,.tc (.st a vals sh)⟩ (some u)) :
    u.pc = probabilityPc round q + 1 := by
  have hPc := (estep_source_pc he).symm
  obtain ⟨i,hCode,_,hFires⟩ := estep_event_source he
  obtain ⟨ss,_,hStore⟩ := probabilityCode round q
  rw [hPc,hStore] at hCode
  obtain rfl := Option.some.inj hCode
  have hCore : ∃ v, v.pc = t.pc ∧ Fires t.pc
      (tcTmpl l g v (.tcSt (probabilityReg round q) ss .s32x32b))
        ⟨probabilityPc round q,.tc (.st a vals sh)⟩ (some u) := by
    simp only [eventTmpl,tcStTmpl] at hFires
    split at hFires
    · split at hFires
      · split at hFires <;> cases (congrArg Event.kind hFires.1)
      · exact ⟨{t with sub := 0},rfl,hFires⟩
    · exact ⟨t,rfl,hFires⟩
  obtain ⟨v,hVPc,hf⟩ := hCore
  rw [tcTmpl_tcSt_plain (by intro _ h; cases h)] at hf
  cases hAddr : readBits l g v 32 (.reg (probabilityReg round q)) <;>
    cases hVals : ss.mapM (readValue l g v 32) <;>
    simp only [ofExec,hAddr,hVals,bind,Except.bind,pure,Except.pure,throw,throwThe,
      MonadExceptOf.throw] at hf
  all_goals split_ifs at hf <;> simp only [Fires, reduceCtorEq] at hf
  all_goals try (cases hf.2)
  change v.pc + 1 = _
  rw [hVPc,hPc]

/-- The observed first delayed load wait is before any probability store of its lane. -/
theorem firstProbabilityWaitBeforeStore {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g complete store : Nat} {round : Round} (q : Fin 4)
    {a : Nat} {vals : List Value} {sh : TcShape}
    (hWait : X.get (g,complete) = some ⟨4826,.tc .waitLd⟩)
    (hStore : X.get (g,store) = some ⟨probabilityPc round q,.tc (.st a vals sh)⟩) :
    complete < store := by
  have hg := event_thread_lt hX hWait
  obtain ⟨_,hRun⟩ := hX.thr g hg
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hRun
  let first : Event := ⟨probabilityPc round q,.tc (.st a vals sh)⟩
  let waiting : Event := ⟨4826,.tc .waitLd⟩
  have hStoreLower : 4826 ≤ first.pc := by
    change 4826 ≤ probabilityPc round q
    cases round <;> fin_cases q <;> decide
  have hNever {t : TState} {es : List Event} {vs : List Visit}
      (hw : Walk kernel Assumptions.all l g t es vs) {i j : Nat}
      (hi : es[i]? = some first) (hj : es[j]? = some waiting) (hOrder : i ≤ j) : False := by
    induction hw generalizing i j with
    | stop => simp at hi
    | tau _ _ ih => exact ih hi hj hOrder
    | @ev t u e es _ hFirst hw ih =>
      cases i with
      | zero =>
        obtain rfl := Option.some.inj hi
        cases j with
        | zero =>
          have hKind := congrArg Event.kind (Option.some.inj hj)
          cases hKind
        | succ j =>
          have hNext : 4827 ≤ u.pc := by
            rw [probabilityStoreAdvances q hFirst]
            exact Nat.succ_le_succ hStoreLower
          have hMember := List.mem_of_getElem? (List.getElem?_cons_succ.symm.trans hj)
          have hPast := Thread.eventTailEventsOfSegmentFloor afterFirstProbabilityCode
            afterFirstProbabilitySegments hw hNext waiting hMember
          exact (by decide : ¬ 4827 ≤ 4826) hPast
      | succ i =>
        cases j with
        | zero => omega
        | succ j =>
          exact ih (List.getElem?_cons_succ.symm.trans hi) (List.getElem?_cons_succ.symm.trans hj)
            (by omega)
    | last _ =>
      cases i <;> cases j <;> simp_all [first, waiting]
  exact Nat.lt_of_not_ge (hNever hWalk hStore hWait)

set_option maxRecDepth 100000 in
private theorem afterOpeningStoreCode (q : Fin 4) :
    (kernel.code.drop (probabilityPc .first q+1)).all
      (fun ins => Thread.staysPastEvent (probabilityPc .first q+1) ins.op) = true := by
  fin_cases q <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterOpeningStoreSegments (q : Fin 4) :
    ∀ site, probabilityPc .first q+1 ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → probabilityPc .first q+1 ≤ seg.stop := by
  let floor := probabilityPc .first q+1
  have hAudit : Assumptions.swExp2Sites.all (fun site =>
      if floor ≤ site then match cuteExp2.matchAt kernel site with
        | some seg => decide (floor ≤ seg.stop)
        | none => false
      else true) = true := by fin_cases q <;> kernel_rfl
  intro site hSite hMem seg hMatch
  have h := List.all_eq_true.mp hAudit site hMem
  simpa only [floor,ite_eq_left hSite,hMatch,decide_eq_true_eq] using h

/-- Each of the first visit's four stores can occur at most once in a lane's trace. -/
theorem openingProbabilityStoreUnique {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j : Nat} (q : Fin 4)
    {a b : Nat} {vals other : List Value} {shape shape' : TcShape}
    (hi : X.get (g,i) = some ⟨probabilityPc .first q,.tc (.st a vals shape)⟩)
    (hj : X.get (g,j) = some ⟨probabilityPc .first q,.tc (.st b other shape')⟩) : i = j := by
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hi)
  have hNotLater {v w : Nat} {x y : Nat} {xs ys : List Value} {sx sy : TcShape}
      (hV : X.get (g,v) = some ⟨probabilityPc .first q,.tc (.st x xs sx)⟩)
      (hW : X.get (g,w) = some ⟨probabilityPc .first q,.tc (.st y ys sy)⟩)
      (hBefore : v < w) : False := by
    have hWL : w < (X.tr g).length := len_of_get hW
    have hBound : v+1 < (X.tr g).length := by omega
    obtain ⟨_,u,hStep,hTail⟩ := hRun.after_event hV hBound
    obtain ⟨_,hWalk⟩ := Mma.walkFromRun hTail
    let later : Event := ⟨probabilityPc .first q,.tc (.st y ys sy)⟩
    have hSeen : later ∈ (X.tr g).drop (v+1) := by
      apply List.mem_of_getElem? (i := w-(v+1))
      rw [List.getElem?_drop,Nat.add_sub_of_le hBefore]
      exact hW
    have hAfter := probabilityStoreAdvances q hStep
    have hFloor := Thread.eventTailEventsOfSegmentFloor (afterOpeningStoreCode q)
      (afterOpeningStoreSegments q) hWalk hAfter.ge later hSeen
    change probabilityPc .first q+1 ≤ probabilityPc .first q at hFloor
    omega
  exact Nat.le_antisymm (Nat.le_of_not_gt (hNotLater hj hi))
    (Nat.le_of_not_gt (hNotLater hi hj))

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
