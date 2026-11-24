-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcOwnership
public import Core.Assembly.Correctness
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Clc.TcReadClcStateFrame
public import Lemmas.TensorStore.TensorReduce
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! A real unresolved request may fail arbitration even while other tasks are
available. Arbitration does not itself write or notify, so its uncounted
extension must be combined with a later CLC effect to establish progress. -/
namespace PTX
noncomputable section

def Execution.failClc (X : Execution) (i : EvId) : Execution :=
  { X with clcState := { X.clcState with
      response := Function.update X.clcState.response (Clc.requestId i) (some none) } }

 theorem failClc_clcOk {L : Launch} {X : Execution} {i : EvId}
    {s : Clc.Spec} {targets : List Nat} (hX : ClcOk L X)
    (hi : X.ClcIssue i s targets)
    (hfresh : X.clcState.response (Clc.requestId i)=none) :
    ClcOk L (X.failClc i) := by
  have hstep : Clc.Step (Clc.ValidTask L) X.clcState (X.failClc i).clcState :=
    Clc.Step.failure X.clcState (Clc.requestId i) hfresh
  have hArb : Clc.ArbitrationOk L (X.failClc i).clcState :=
    hX.1.tail hstep
  refine ⟨hArb,?_,hX.2.2.1,?_,hX.2.2.2.2⟩
  · intro request answer hr
    by_cases he : request=Clc.requestId i
    · subst request
      have ha : answer=none := by
        simpa only [Execution.failClc,Function.update_self,Option.some.injEq] using hr.symm
      exact ⟨i,s,targets,rfl,hi⟩
    · have hr' : X.clcState.response request=some answer := by
        simpa only [Execution.failClc,Function.update_of_ne he] using hr
      exact hX.2.1 request answer hr'
  · intro j t ts hj
    obtain ⟨he,hnd,htarget⟩ := hX.2.2.2.1 j t ts hj
    refine ⟨⟨hArb,?_,he.writes,he.notified⟩,hnd,htarget⟩
    intro r hr
    obtain ⟨task,ht,heq⟩ := he.result r hr
    exact ⟨task,hstep.response_stable ht,heq⟩

theorem failClc_modelCausality {L : Launch} {X : Execution} {i : EvId}
    {l : Loc} {e f : AsyncCopy.Ref} :
    modelCausality L (X.failClc i) l e f ↔ modelCausality L X l e f := by
  cases e <;> cases f
  all_goals first
    | exact Iff.rfl
    | exact and_congr_right fun _ => AsyncChain.congr (X := X.failClc i) (Y := X)
        (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)

/-- The arbitration failure of an actual request preserves every Consistent
field. Arbitrary selected assumption profiles remain explicit, since their wf
predicates can inspect execution-level arbitration state. -/
theorem consistent_failClc {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {s : Clc.Spec} {targets : List Nat}
    (hX : Consistent L K A mem0 X) (hi : X.ClcIssue i s targets)
    (hfresh : X.clcState.response (Clc.requestId i)=none)
    (hasm : ∀a∈A,a.wf L mem0 (X.failClc i)) :
    Consistent L K A mem0 (X.failClc i) := by
  refine { hX with
    clc := failClc_clcOk hX.clc hi hfresh
    dependency := ⟨hX.dependency.ready, hX.dependency.acyclic⟩
    tcRead := (TcMma.readOk_clc _ _).mpr hX.tcRead
    noFuture := NoFuture.of_frame hX.noFuture (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context (X := X) (Y := X.failClc i) rfl rfl
        (fun h => (failClc_modelCausality.mp) h) (fun h => h))
    hidden := Hidden.of_frame hX.hidden (fun _ _ _ h => h) (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context (X := X) (Y := X.failClc i) rfl rfl
        (fun h => (failClc_modelCausality.mp) h) (fun h => h))
    reduce := ⟨hX.reduce.values, hX.reduce.copies⟩
    atomic := ⟨hX.atomic.unique, hX.atomic.acyclic⟩
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, hX.fenceSc.causal⟩
    asm := hasm }

 theorem failClc_le {X : Execution} {i : EvId}
    (hfresh : X.clcState.response (Clc.requestId i)=none) : X.le (X.failClc i) := by
  have hstep : Clc.Step (fun _ => True) X.clcState (X.failClc i).clcState :=
    Clc.Step.failure _ _ hfresh
  have h := Execution.le_refl X
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,⟨fun _ _ ho => ho,fun _ _ hr => hstep.response_stable hr⟩,
    h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2⟩

end
end PTX
