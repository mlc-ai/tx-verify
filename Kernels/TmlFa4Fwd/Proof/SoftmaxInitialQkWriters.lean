-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitQkValues
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialQkIssuer
import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma

/-- The frozen single-CTA MMA instructions can write cells only in the issuer's CTA. -/
theorem mmaWriteCta {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {cell : Cell} (hWrite : X.MmaCell i cell) : cell.cta = i.1 / l.block := by
  obtain ⟨d,s,acc,mask,row,col,hIssue,hCell⟩ := hWrite
  obtain ⟨hGroup,members,hMembers,hLow,hHigh⟩ := Mma.actualMmaOwnership hX hIssue
  obtain ⟨_,he⟩ := hIssue
  rw [hGroup,Mma.singleCtaGroup hp (event_thread_lt hX he)] at hMembers
  obtain rfl := Option.some.inj hMembers.symm
  have hL : s.lowCta = i.1 / l.block := (Option.some.inj hLow).symm
  have hH : s.highCta = i.1 / l.block := (Option.some.inj hHigh).symm
  rcases resultCell_cta (writeCell_resultCell hCell) with h | h
  · exact h.trans hL
  · exact h.trans hH

/-- An actual initial QK writer to this score cell belongs to the consuming stage's bank.
The other stage has its own physical score columns. -/
theorem initialQkCompetingWriter {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer commit wait start : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    {output : EvId} {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : producer / l.block = output.1 / l.block)
    (hIssues : ∀ frag : Fin 8, X.get (producer,start+frag.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) frag 0))
    (q : Fin 4) (word : Fin 32) (writtenStage : Fin 2) (frag : Fin 8)
    {other : EvId} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get other = some
      ⟨Mma.qkPc (firstQkBlock writtenStage)+frag.val,.tc (.mma d op acc mask)⟩)
    (hWrite : X.MmaCell other (tcDataCell l consumer .s32x32b
      (scoreAddress l consumer stage q) word.val)) :
    ∃ f : Fin 8, other = (producer,start+f.val) := by
  have hScore : (tcDataCell l consumer .s32x32b
      (scoreAddress l consumer stage q) word.val).cta = consumer / l.block := by
    have hCol := scoreColumn_range stage
    have hQuarter := q.isLt
    rw [scoreAddress,tcDataCell_warp32 _ _ _ (by omega)]
  have hCta : other.1 / l.block = producer / l.block :=
    (mmaWriteCta hp hX hWrite).symm.trans (hScore.trans hPhase.sameCta.2.2.symm)
  by_cases hStage : writtenStage = stage
  · subst writtenStage
    exact ⟨frag,Thread.initialQkIssueUnique hp hX stage frag he (hIssues frag) hCta⟩
  · obtain ⟨base,hFrags⟩ :=
      Thread.initialCanonicalQkIssuesBeforeSecondOutputCommit hp hX hOutput writtenStage
    obtain ⟨_,hIssue,_⟩ := hFrags frag
    have hId : other = (output.1,base+frag.val) :=
      Thread.initialQkIssueUnique hp hX writtenStage frag he hIssue (hCta.trans hOutputCta)
    have hActual : X.MmaIssue other (scoreColumn writtenStage)
        (Mma.qkOperands l output.1 (firstQkBlock writtenStage) frag 0)
        (decide (frag.val ≠ 0)) (List.replicate 4 0) := by
      rw [hId]
      refine ⟨Mma.qkPc (firstQkBlock writtenStage)+frag.val,?_⟩
      have hGet : X.get (output.1,base+frag.val) =
          some (Mma.qkIssueEvent l output.1 (firstQkBlock writtenStage) frag 0) := hIssue
      simpa only [Mma.qkIssueEvent,firstQkBlock_stage] using hGet
    exact (scoreOtherStageDisjoint consumer stage writtenStage q word rfl
      hActual hStage hWrite).elim

end PTX.Kernels.TmlFa4Fwd.Softmax
