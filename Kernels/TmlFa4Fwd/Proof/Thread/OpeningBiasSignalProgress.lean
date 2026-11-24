-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSignals
public import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Lemmas.Step.Object
import Lemmas.Kernel.ProgressDescent
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.AsyncCopy

/-- A maximal execution records the softmax lane's ordinary stage arrival once
the recorded predecessor can return. A release may come from an administrative
extension with the same trace. -/
theorem signalOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m)
    {g pos : Nat} (hg : g < l.threads) (stage : Fin 2) (site : Fin 8)
    {before t : TState} {ending : Option TState}
    (hPc : t.pc = (signalSite site).pc) (hFault : t.fault = none)
    (hBase : t.regs (signalSite site).base = some (b32 (l.sharedBase+8*stage.val)))
    (hCount : t.regs (signalSite site).count = some (b32 1))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before))
    (hTail : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g) :
    let state := next (mbarStateDest t (some (signalSite site).state))
    X.get (g,pos) = some ⟨(signalSite site).pc,.arrive (signalLoc l g stage site) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some state) ∧
      Run kernel Assumptions.all l g state ((X.tr g).drop (pos+1)) ending := by
  let target := signalLoc l g stage site
  let state := next (mbarStateDest t (some (signalSite site).state))
  let event : Event := ⟨t.pc,.arrive target 0 1 true .cta⟩
  have hOut := signalTemplate hp stage site (g := g) hPc hFault hBase hCount
  have hEvent : EStep kernel Assumptions.all l g t event (some state) := ⟨_,hOut,rfl,rfl⟩
  have hLt : pos < (X.tr g).length := by
    by_contra! hLong
    have hEq := Nat.le_antisymm hBound hLong
    obtain ⟨Y,hY,hTrace,hReady⟩ := hRelease hEq
    have hNonempty : Y.tr g ≠ [] := by
      intro h
      have hl : (X.tr g).length = 0 := by rw [← hTrace,h,List.length_nil]
      omega
    rw [List.take_of_length_le hLong,← hTrace] at hPrefix
    apply hY.not_grows
    refine Step.object_counted_extension_silent hY.1 (by trivial) hg (.inl hNonempty)
      hReady hPrefix hLocal hEvent ⟨trivial,fun _ h => by cases h⟩ (by trivial)
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rfl (mb := target) (act := .arrive 1 0)
      (fun _ _ h => by cases h) ?_ ?_
    · intro loc
      by_cases h : loc = target
      · subst loc
        simp [objectAction,snoc_get_new,event]
      · simp [objectAction,snoc_get_new,event,h,Ne.symm h]
    · intro rec
      exact Assumptions.wfStep.quiet hY.1
        (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  rw [List.drop_eq_getElem_cons hLt] at hTail
  have hn : Next kernel Assumptions.all l g before t (.arrive target 0 state 1 true .cta) :=
    ⟨hLocal,hOut⟩
  obtain ⟨_,⟨hGet,hReturned⟩,hRest⟩ := hn.continuing_event
    (by rintro ⟨_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hReturned
  refine ⟨?_,?_,hRest⟩
  · change (X.tr g)[pos]? = _
    rw [List.getElem?_eq_getElem hLt,hGet,hPc]
  · rw [List.take_succ_eq_append_getElem hLt,hGet]
    exact hPrefix.snoc hLocal hEvent

end PTX.Kernels.TmlFa4Fwd.Softmax
