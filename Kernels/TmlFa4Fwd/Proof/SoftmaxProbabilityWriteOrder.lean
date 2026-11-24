-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityStoreOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma Prologue

/-- A probability store of this row and stage follows both the score-fragment completion
and the lane's score-load completion. Other rows and stages have disjoint addresses. -/
theorem scoreProbabilityWriteOrder {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer commit wait read complete : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    (hStage : consumer % l.block / 128 = stage.val)
    (hWaitRead : wait < read) (hReadComplete : read < complete)
    (hWaitLd : X.get (consumer,complete) = some ⟨4826,.tc .waitLd⟩)
    (q : Fin 4) (word : Fin 32) {round : Round} (quarter : Fin 4)
    {h write : Nat} {writtenStage : Fin 2}
    (hWrittenStage : h % l.block / 128 = writtenStage.val) {vals : List Value}
    (he : X.get (h,write) = some ⟨probabilityPc round quarter,
      .tc (.st (probabilityAddress l h writtenStage quarter) vals .s32x32b)⟩)
    (hLen : vals.length = 16)
    (hWrite : StoreCell l X (h,write)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    ReadBefore l X .ld (consumer,read) (h,write) ∧
      ∀ issue < commit, X.TcAsync (producer,issue) →
        ReadBefore l X .acc (producer,issue) (h,write) := by
  have hStore : X.TSt (h,write) (probabilityAddress l h writtenStage quarter) vals .s32x32b :=
    ⟨_,he⟩
  have hEqual : consumer / l.block = h / l.block ∧ tmemRow l consumer = tmemRow l h ∧
      stage = writtenStage := by
    by_contra hDifferent
    push Not at hDifferent
    by_cases hCta : consumer / l.block = h / l.block
    · by_cases hRow : tmemRow l consumer = tmemRow l h
      · exact scoreProbabilityDisjoint stage writtenStage q quarter word hStore hLen
          (.inr (.inr (hDifferent hCta hRow))) hWrite
      · exact scoreProbabilityDisjoint stage writtenStage q quarter word hStore hLen
          (.inr (.inl hRow)) hWrite
    · exact scoreProbabilityDisjoint stage writtenStage q quarter word hStore hLen
        (.inl hCta) hWrite
  have hLane : consumer = h := by
    have hWriteStage : consumer % l.block / 128 = h % l.block / 128 := by
      rw [hStage,hWrittenStage,hEqual.2.2]
    exact scoreSameLane ⟨hPhase.sameCta.2.1,event_thread_lt hX he,hEqual.1⟩
      hWriteStage hEqual.2.1
  subst h
  have hOrder := Thread.Scores.firstProbabilityWaitBeforeStore hX quarter hWaitLd he
  refine ⟨firstScoresBeforeLocalStore hWaitLd hReadComplete hStore hOrder,?_⟩
  intro issue hBefore hIssue
  have hj := (List.getElem?_eq_some_iff.mp he).1
  have hPo := po_of_not_access (show (consumer,wait).1 = (consumer,write).1 from rfl)
    (show wait < write by omega) hj (by rw [he]; rfl)
  exact .inr (.inl (.inl ⟨(consumer,wait),.cta,
    firstQkPhase_observed hX hPhase hIssue hBefore,
    MbarRing.Unit.Gate.scopesMeet hPhase.sameCta .cluster .cta,.single (.inl hPo)⟩))

end PTX.Kernels.TmlFa4Fwd.Softmax
