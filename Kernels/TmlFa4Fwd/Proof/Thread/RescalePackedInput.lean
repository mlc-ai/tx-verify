-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleReferenceInputs
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedMax

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- Registers written by the repeated maximum and its finite-reference guard. -/
def rescaleMaxWrites (biased : Bool) : List Nat :=
  rWrites (repeatedMaxItems biased) ++ rescaleReferenceWrites biased

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (biased : Bool)
    {g pos : Nat} {t : TState} {ending : Option TState} {a : Acc} {data : List Byte}
    (scores : Nat → Option ℝ) (ht : At t (repeatedMaxStart biased) [])
    (hRead : ∀ r ∈ repeatedMaxDom biased,
      t.regs r = some (scalarValue scores (repeatedMaxInputs biased) r))
    (hAbi : t.regs (alphaSite biased).scale = some (b32 p.scaleLog2Bits))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (he : StatisticsStore X (g,pos) (rescaleStore biased) a data)
include hp biased scores ht hRead hAbi hr he

/-- The repeated max reduction and guard compute a canonical candidate from the
actual packed score words and the prior reference, including for a padded row. -/
theorem rescaleArithmeticEntryOfPackedScoresWithFrame :
    RescaleArithmeticEntryWith p l X (g,pos) biased
      (fun u => Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
        ∀ r ∉ rescaleMaxWrites biased, u.regs r = t.regs r) := by
  have hHead : ((X.tr g).drop pos)[0]? =
      some ⟨(statsStore (rescaleStore biased)).pc,.wr a data⟩ := by
    rw [List.getElem?_drop,Nat.add_zero]
    exact he
  have hMore : (X.tr g).drop pos ≠ [] := by
    intro h
    simp [h] at hHead
  obtain ⟨u,mx,hu,hLocal,_,hKeep⟩ := repeatedMaxLocal (g := g) biased scores ht hRead
  have hTail := hr.after_local_nonempty hLocal hMore
  have hPc : repeatedMaxStart biased+130 = (referenceSite (rescaleRound biased)).pc := by
    cases biased <;> rfl
  have hPrior : t.regs (alphaSite biased).prior = some (scoreValue (scores 0)) := by
    have h := hRead (repeatedMaxOld biased) List.mem_cons_self
    have hReg : repeatedMaxOld biased = (alphaSite biased).prior := by cases biased <;> rfl
    have hVal : repeatedMaxInputs biased (repeatedMaxOld biased) = some (.scalar [0]) := by
      simp [repeatedMaxInputs]
    rw [hReg] at h
    have hMax : maxScore (scores 0) none = scores 0 := by cases scores 0 <;> rfl
    simpa [scalarValue,← hReg,hVal,MaxDatum.value,scoreMax,hMax] using h
  have hPriorKeep : (alphaSite biased).prior ∉ rWrites (repeatedMaxItems biased) := by
    cases biased <;> decide +kernel
  have hScaleKeep : (alphaSite biased).scale ∉ rWrites (repeatedMaxItems biased) := by
    cases biased <;> decide +kernel
  have hReg : repeatedMaxNew biased = (alphaSite biased).candidate := by cases biased <;> rfl
  have hReference : At u (referenceSite (rescaleRound biased)).pc [] :=
    hPc ▸ (show At u (repeatedMaxStart biased+130) [] from hu.mono trivial)
  have hEntry := rescaleArithmeticEntryOfCanonicalMaximumsWithFrame hp biased (scores 0) mx
    hReference ((hKeep _ hPriorKeep).trans hPrior)
    (hReg ▸ hu.2.2.2.2.1) ((hKeep _ hScaleKeep).trans hAbi) hTail he
  refine hEntry.mono (fun w hw => ⟨hLocal.trans hw.1,fun r hr => ?_⟩)
  simp only [rescaleMaxWrites,List.mem_append,not_or] at hr
  exact (hw.2 r hr.2).trans (hKeep r hr.1)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
