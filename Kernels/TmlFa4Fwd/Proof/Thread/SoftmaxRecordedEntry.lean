-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
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
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.RegisterHint
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue

private theorem commonDispatchRecorded {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e) (hLate : 173 < e.pc) :
    ∃ n t o, n ≤ index ∧ At t 174 [(1062,b32 (warpIndex l g)),(2535,b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take n) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop n) o := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  cases Nat.eq_zero_or_pos (warpIndex l g) with
  | inl hw =>
    obtain ⟨_,_,_,hBar,_,_⟩ := warp0InitializerPrefix hp hX hg hw he hLate.le
    obtain ⟨j,t,o,hRound,ht,_,hEarlier,hPast,hRun⟩ :=
      warp0CommonPrefixOfRendezvous hp hX hg hw hBar
    have hIndex : j+2 ≤ index := by
      by_contra! h
      exact (Nat.not_lt_of_ge (by omega : 174 ≤ e.pc)) (hEarlier index h _ he)
    refine ⟨j+2,t,o,hIndex,ht.mono ⟨?_,?_,trivial⟩,hPast,hRun⟩
    · exact hw.symm ▸ ht.2.2.2.2.1
    · exact holds_mem ht.2.2.2.2 (by simp [initFacts,initAddresses])
  | inr hw =>
    obtain ⟨_,_,hn,_,_,_,_,_⟩ := nonzeroCommonPrefixOfDemand hp hX hg hw he (.inl hLate)
    obtain ⟨t,o,ht,_,hPast,hRun⟩ := nonzeroCommonPrefix hp hX hg hw (hn.trans (len_of_get he).le)
    exact ⟨5,t,o,hn,ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,trivial⟩,hPast,hRun⟩

/-- The softmax role entry is reached by the recorded startup and hint events. -/
theorem softmaxRoleEntryRecorded {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hLate : 173 < e.pc) (hNotHint : e.pc ≠ 3102) (hWarp : warpIndex l g < 8) :
    ∃ w : Fin 8, w.val = warpIndex l g ∧ ∃ pos s o, pos ≤ index ∧
      At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)] ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take pos) s ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) o := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨pos,t,o,hIndex,ht,hPast,hRun⟩ := commonDispatchRecorded hp hX he hLate
  have hLength := len_of_get he
  have hNonempty : (X.tr g).drop pos ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hLength ((List.drop_eq_nil_iff.mp h).trans hIndex)
  let warp : Fin 16 := ⟨warpIndex l g,warpIndex_lt hp g⟩
  have hPc : registerHintPc warp = 3102 := by
    simp only [registerHintPc,dispatchParamPc,warp]
    split_ifs <;> omega
  obtain ⟨u,hU,hNext⟩ := firstRegisterHintNext hp hg warp ht
  obtain ⟨first,v,hFirst,hFires,hTail⟩ := hNext.continuing_at_nonempty (by
    rintro _ ⟨_,_,h⟩
    cases h) hRun hNonempty
  have hStep : EStep kernel Assumptions.all l g u first (some v) :=
    ⟨_,hNext.stop,hFires⟩
  obtain ⟨inst,rfl,hV⟩ := hFires
  obtain rfl := Option.some.inj hV
  let hint : Event := ⟨u.pc,.setMaxReg (registerHintOf warp.val).1
    (registerHintOf warp.val).2 inst⟩
  have hGet : X.get (g,pos) = some hint := hFirst
  have hLt : pos < index := by
    by_contra! h
    have hEq : pos = index := by omega
    rw [hEq] at hGet
    have hSame := congrArg Event.pc (Option.some.inj (hGet.symm.trans he))
    change u.pc = e.pc at hSame
    exact hNotHint (hSame.symm.trans (hU.1.trans hPc))
  have hTrace : (X.tr g).take (pos+1) = (X.tr g).take pos ++ [hint] := by
    change (X.tr g)[pos]? = some hint at hGet
    rw [List.take_add_one,hGet]
    rfl
  have hNextRun : Run kernel Assumptions.all l g t [hint] (some (next u)) :=
    .step hNext.steps hStep (.nil _)
  refine ⟨⟨warpIndex l g,hWarp⟩,rfl,pos+1,next u,o,by omega,?_,?_,hTail⟩
  · simpa only [hPc] using hU.next
  · rw [hTrace]
    exact hPast.returning_reach.append hNextRun.returning_reach

end PTX.Kernels.TmlFa4Fwd.Softmax
