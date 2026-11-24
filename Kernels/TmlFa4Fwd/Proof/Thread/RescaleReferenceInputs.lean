-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleArithmeticCursor
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleAbiScale

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- A rescale entry that also carries the caller's facts at the same actual cursor. -/
def RescaleArithmeticEntryWith (p : Params) (l : Launch) (X : Execution) (i : EvId)
    (biased : Bool) (frame : TState → Prop) : Prop :=
  ∃ t ending old candidate scaleWord,
    At t (alphaSite biased).pc [] ∧
    readEReal .f32 scaleWord = some (.ok (abiFloat p.scaleLog2Bits : EReal)) ∧
    (∀ r ∈ (alphaSite biased).inputs,
      t.regs r = some ((alphaSite biased).valuesOfWord scaleWord old candidate r)) ∧
    Run kernel Assumptions.all l i.1 t ((X.tr i.1).drop i.2) ending ∧ frame t

theorem RescaleArithmeticEntryWith.entry {p : Params} {l : Launch} {X : Execution}
    {i : EvId} {biased : Bool} {frame : TState → Prop}
    (h : RescaleArithmeticEntryWith p l X i biased frame) : RescaleArithmeticEntry p l X i biased :=
  let ⟨t,ending,old,candidate,scale,hAt,hScale,hValues,hRun,_⟩ := h
  ⟨t,ending,old,candidate,scale,hAt,hScale,hValues,hRun⟩

theorem RescaleArithmeticEntryWith.mono {p : Params} {l : Launch} {X : Execution}
    {i : EvId} {biased : Bool} {frame frame' : TState → Prop}
    (h : RescaleArithmeticEntryWith p l X i biased frame) (hf : ∀ t, frame t → frame' t) :
    RescaleArithmeticEntryWith p l X i biased frame' :=
  let ⟨t,ending,old,candidate,scale,hAt,hScale,hValues,hRun,hFrame⟩ := h
  ⟨t,ending,old,candidate,scale,hAt,hScale,hValues,hRun,hf t hFrame⟩

/-- The two reference-guard destinations are the only overwritten registers. -/
def rescaleReferenceWrites (biased : Bool) : List Nat :=
  let site := referenceSite (rescaleRound biased)
  [site.finite,site.pred]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (biased : Bool)
    {g pos : Nat} {t : TState} {ending : Option TState} {a : Acc} {data : List Byte}
    (prior candidate : Option ℝ) (ht : At t (referenceSite (rescaleRound biased)).pc [])
    (hPrior : t.regs (alphaSite biased).prior = some (scoreValue prior))
    (hCandidate : t.regs (alphaSite biased).candidate = some (scoreValue candidate))
    (hAbi : t.regs (alphaSite biased).scale = some (b32 p.scaleLog2Bits))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (he : StatisticsStore X (g,pos) (rescaleStore biased) a data)
include hp biased prior candidate ht hPrior hCandidate hAbi hr he

/-- At the recorded reference guard, only the two scalar maximum representations
remain to be established. The guard and the coefficient share the same suffix. -/
theorem rescaleArithmeticEntryOfCanonicalMaximumsWithFrame :
    RescaleArithmeticEntryWith p l X (g,pos) biased
      (fun u => Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
        ∀ r ∉ rescaleReferenceWrites biased, u.regs r = t.regs r) := by
  have hHead : ((X.tr g).drop pos)[0]? =
      some ⟨(statsStore (rescaleStore biased)).pc,.wr a data⟩ := by
    rw [List.getElem?_drop,Nat.add_zero]
    exact he
  have hMore : (X.tr g).drop pos ≠ [] := by
    intro h
    simp [h] at hHead
  have hReg : (referenceSite (rescaleRound biased)).maximum = (alphaSite biased).candidate := by
    cases biased <;> rfl
  obtain ⟨u,hU,hLocal,hKeep⟩ := finiteReferenceLocal (rescaleRound biased) candidate
    ht (hReg.symm ▸ hCandidate)
  have hRun := hr.after_local_nonempty hLocal hMore
  have hAt : At u (alphaSite biased).pc [] := by
    cases biased <;> exact hU.mono trivial
  refine ⟨u,ending,prior,candidate,b32 p.scaleLog2Bits,hAt,rescaleAbiScaleWord hp,
    ?_,hRun,hLocal,hKeep⟩
  intro r hMem
  cases biased
  · change r ∈ [7255,5509,5510,7133] at hMem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact (hKeep _ (by decide)).trans hPrior
    · exact hU.2.2.2.2.2.1
    · exact hU.2.2.2.2.1
    · exact (hKeep _ (by decide)).trans hAbi
  · change r ∈ [7251,4560,4561,7132] at hMem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact (hKeep _ (by decide)).trans hPrior
    · exact hU.2.2.2.2.2.1
    · exact hU.2.2.2.2.1
    · exact (hKeep _ (by decide)).trans hAbi

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
