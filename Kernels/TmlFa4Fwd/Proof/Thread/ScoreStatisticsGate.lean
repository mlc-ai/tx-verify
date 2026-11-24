-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.PollSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof Prologue

private theorem rawNotice {e : Event} {round : Round} (h : notice e = some round) :
    if round = .final then e.pc = 7616 else Softmax.scoredStatisticsMark e = true := by
  obtain ⟨site,k⟩ := e
  cases k <;> simp [notice] at h
  rename_i id count mode
  cases mode <;> simp at h
  unfold noticeRound at h
  split at h
  all_goals cases h
  all_goals simp [Softmax.scoredStatisticsMark]

private theorem priorNoticesScored {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {round : Round} (hPub : Publishes X (g,j) round) :
    (before X (g,j)).notices ≤ ((X.tr g).take j).countP Softmax.scoredStatisticsMark := by
  rw [beforeNotices]
  apply List.countP_mono_left
  intro e he hm
  obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp he
  have hK := (List.getElem?_eq_some_iff.mp hk).1
  simp only [List.length_take] at hK
  have hLt : k < j := by omega
  rw [List.getElem?_take_of_lt hLt] at hk
  obtain ⟨prior,hNotice⟩ := Option.isSome_iff_exists.mp hm
  have hNonfinal : prior ≠ .final := by
    rintro rfl
    exact noPublicationAfterFinal hX (g := g) (i := k) ⟨e,hk,hNotice⟩ hLt hPub
  simpa [hNonfinal] using rawNotice hNotice

private theorem scoreAcquireMarksAgree :
    Softmax.scoreAcquireMark = Softmax.phaseAcquired true := by
  funext e
  rw [Softmax.scoreReadyMarkKind]
  rfl

/-- Each fresh statistics publication follows the successful score acquire of its ordinal.
The terminal statistics publication follows the last fresh score acquire. -/
theorem statisticsScoreAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j cta n : Nat} {round : Round} (stage : Fin 2)
    (hw : warpIndex l g < 8) (hCta : g / l.block = cta) (hStage : warpIndex l g / 4 = stage.val)
    (hPub : Publishes X (g,j) round)
    (hN : n + (if round = .final then 1 else 0) < (before X (g,j)).notices + 1) :
    let loc := scoreReadyObject l cta stage
    ∃ k e q acq scope, X.get (g,k) = some e ∧ e.kind = .wait loc q true acq scope ∧
      okPolls loc ((X.tr g).take k) = n ∧ Resumes kernel X (g,k) (g,j) := by
  have hPrev := priorNoticesScored hX hPub
  obtain ⟨e,he,hMarker⟩ := hPub
  let trace := (X.tr g).take j
  let loc := scoreReadyObject l cta stage
  have hCount : trace.countP Softmax.scoreAcquireMark = okPolls loc trace := by
    rw [scoreAcquireMarksAgree]
    exact scoreCount hp hX stage hw hCta hStage
  have hLength : n + 1 ≤ okPolls loc trace := by
    have hRaw := rawNotice hMarker
    change (before X (g,j)).notices ≤ trace.countP Softmax.scoredStatisticsMark at hPrev
    by_cases hf : round = .final
    · have hBudget := Softmax.precedingStatisticsScoreBudget hX he
      change trace.countP Softmax.scoredStatisticsMark ≤ trace.countP Softmax.scoreAcquireMark
        at hBudget
      rw [hCount] at hBudget
      simp only [hf, ↓reduceIte] at hN
      omega
    · simp only [hf, ↓reduceIte] at hRaw hN
      have hBudget := Softmax.actualStatisticsScoreBudget hp hX he hRaw
      change trace.countP Softmax.scoredStatisticsMark + 1 ≤
        trace.countP Softmax.scoreAcquireMark at hBudget
      rw [hCount] at hBudget
      omega
  obtain ⟨k, source, q, acq, scope, hK, hGet, hOrdinal⟩ := MbarRing.Poll.exists_nth hLength
  obtain ⟨exit,hSpin⟩ := actualCanonicalPoll hX hGet
  have hJ : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hTrace : TraceBefore X (g,k) (g,j) := ⟨rfl,hK,hJ⟩
  refine ⟨k,_,q,acq,scope,hGet,rfl,hOrdinal,hTrace,?_⟩
  simp only [hGet, Option.map_some, Kind.resume]
  exact ⟨source,exit,loc,q,acq,scope,hGet,hSpin,hTrace⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
