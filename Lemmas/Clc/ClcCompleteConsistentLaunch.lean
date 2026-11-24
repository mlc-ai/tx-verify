-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Clc.ClcCompleteConsistentArbitration
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

namespace PTX
noncomputable section

def Execution.launchClc (X : Execution) (task : Nat) : Execution :=
  { X with clcState := { X.clcState with
      owner := Function.update X.clcState.owner task (some .launched) } }

theorem launchClc_clcOk {L : Launch} {X : Execution} {task : Nat}
    (hX : ClcOk L X) (hv : Clc.ValidTask L task)
    (hfresh : X.clcState.owner task=none) :
    ClcOk L (X.launchClc task) := by
  have hstep : Clc.Step (Clc.ValidTask L) X.clcState (X.launchClc task).clcState :=
    Clc.Step.launch X.clcState task hv hfresh
  have hArb : Clc.ArbitrationOk L (X.launchClc task).clcState := hX.1.tail hstep
  refine ⟨hArb,hX.2.1,hX.2.2.1,?_,?_⟩
  · intro j t ts hj
    obtain ⟨he,hnd,htarget⟩ := hX.2.2.2.1 j t ts hj
    refine ⟨⟨hArb,?_,he.writes,he.notified⟩,hnd,htarget⟩
    intro r hr
    obtain ⟨answer,ht,heq⟩ := he.result r hr
    exact ⟨answer,hstep.response_stable ht,heq⟩
  · intro hi g hg hn
    exact hstep.owner_stable (hX.2.2.2.2 hi g hg hn)

theorem launchClc_modelCausality {L : Launch} {X : Execution} {task : Nat}
    {l : Loc} {e f : AsyncCopy.Ref} :
    modelCausality L (X.launchClc task) l e f ↔ modelCausality L X l e f := by
  cases e <;> cases f
  all_goals first
    | exact Iff.rfl
    | exact and_congr_right fun _ => AsyncChain.congr (X := X.launchClc task) (Y := X)
        (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)

theorem consistent_launchClc {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {task : Nat}
    (hX : Consistent L K A mem0 X) (hv : Clc.ValidTask L task)
    (hfresh : X.clcState.owner task=none)
    (hasm : ∀a∈A,a.wf L mem0 (X.launchClc task)) :
    Consistent L K A mem0 (X.launchClc task) := by
  refine { hX with
    clc := launchClc_clcOk hX.clc hv hfresh
    dependency := ⟨hX.dependency.ready, hX.dependency.acyclic⟩
    tcRead := (TcMma.readOk_clc _ _).mpr hX.tcRead
    reduce := ⟨hX.reduce.values, hX.reduce.copies⟩
    atomic := ⟨hX.atomic.unique, hX.atomic.acyclic⟩
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, hX.fenceSc.causal⟩
    tmemPairCompletion := Tmem.Pair.completionClosed_of_trace rfl rfl rfl hX.tmemPairCompletion
    mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
    noFuture := NoFuture.of_frame hX.noFuture (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context (X := X) (Y := X.launchClc task) rfl rfl
        (fun h => (launchClc_modelCausality.mp) h) (fun h => h))
    hidden := Hidden.of_frame hX.hidden (fun _ _ _ h => h) (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context (X := X) (Y := X.launchClc task) rfl rfl
        (fun h => (launchClc_modelCausality.mp) h) (fun h => h))
    asm := hasm }

theorem launchClc_le {X : Execution} {task : Nat}
    (hfresh : X.clcState.owner task=none) : X.le (X.launchClc task) := by
  have hstep : Clc.Step (fun _ => True) X.clcState (X.launchClc task).clcState :=
    Clc.Step.launch _ _ trivial hfresh
  have h := Execution.le_refl X
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,⟨fun _ _ ho => hstep.owner_stable ho,fun _ _ hr => hr⟩,
    h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem launchClc_size (L : Launch) (X : Execution) (task : Nat) :
    (X.launchClc task).size L=X.size L := rfl

end
end PTX
