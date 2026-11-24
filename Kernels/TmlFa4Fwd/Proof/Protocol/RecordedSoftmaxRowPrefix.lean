-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityPublication
public import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleStatisticsSources
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNumerics
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Numeric Softmax Thread.Scores Thread.Correction

noncomputable section

/-- The actual probability tiles and coefficients accumulated along a scalar
softmax recurrence up to the current visit. -/
structure RecordedSoftmaxRowPrefix (p : Params) (l : Launch) (X : Execution)
    (producer batch head row : Nat) (stage : Fin 2) (blocks visited : Nat)
    (reference : Nat → Option ℝ) (sums : Nat → ℝ) : Prop where
  recurrence : SoftmaxSumPrefix p batch head row blocks visited reference sums
  probabilities : ∀ visit < visited, ObservedProbabilityTile l X producer stage visit (fun k =>
    shiftedWeight p batch head row (visitKey blocks visit k) ((reference visit).getD 0))
  factors : ∀ visit, 0 < visit → visit < visited →
    ∃ pos biased a word,
      StatisticsStore X (producer,pos) (Softmax.rescaleStore biased) a word.toBytes ∧
      (Thread.Scores.before X (producer,pos)).notices = visit ∧
      RescaleFactorWord word (maskedRescale (reference (visit-1)) (reference visit))

namespace RecordedSoftmaxRowPrefix

variable {p : Params} {l : Launch} {X : Execution} {producer batch head row : Nat}
  {stage : Fin 2} {blocks visited : Nat} {reference : Nat → Option ℝ} {sums : Nat → ℝ}

/-- The first tile has no earlier numerator to rescale. -/
theorem first (mx : Option ℝ) (sum : ℝ)
    (hRecurrence : SoftmaxSumPrefix p batch head row blocks 1 (fun _ => mx) (fun _ => sum))
    (hProb : ObservedProbabilityTile l X producer stage 0 (fun k =>
      shiftedWeight p batch head row (visitKey blocks 0 k) (mx.getD 0))) :
    RecordedSoftmaxRowPrefix p l X producer batch head row stage blocks 1
      (fun _ => mx) (fun _ => sum) := by
  refine ⟨hRecurrence,?_,?_⟩
  · intro visit hVisit
    have hZero : visit = 0 := by omega
    subst visit
    exact hProb
  · intro visit hPositive hVisit
    omega

/-- Attach the next actual probability tile and coefficient to the updated
recurrence while preserving the exact publications of all earlier visits. -/
theorem extend (h : RecordedSoftmaxRowPrefix p l X producer batch head row stage blocks
      visited reference sums) (hPositive : 0 < visited)
    (mx : Option ℝ) (sum : ℝ)
    (hRecurrence : SoftmaxSumPrefix p batch head row blocks (visited+1)
      (Function.update reference visited mx) (Function.update sums visited sum))
    (hProb : ObservedProbabilityTile l X producer stage visited (fun k =>
      shiftedWeight p batch head row (visitKey blocks visited k) (mx.getD 0)))
    (hFactor : ∃ pos biased a word,
      StatisticsStore X (producer,pos) (Softmax.rescaleStore biased) a word.toBytes ∧
      (Thread.Scores.before X (producer,pos)).notices = visited ∧
      RescaleFactorWord word (maskedRescale (reference (visited-1)) mx)) :
    RecordedSoftmaxRowPrefix p l X producer batch head row stage blocks (visited+1)
      (Function.update reference visited mx) (Function.update sums visited sum) := by
  classical
  refine ⟨hRecurrence,?_,?_⟩
  · intro visit hVisit
    by_cases hSame : visit = visited
    · subst visit
      simpa only [Function.update_self] using hProb
    · simpa only [Function.update_of_ne hSame] using h.probabilities visit (by omega)
  · intro visit hPos hVisit
    by_cases hSame : visit = visited
    · subst visit
      have hPrevious : visited-1 ≠ visited := by omega
      simpa only [Function.update_self,Function.update_of_ne hPrevious] using hFactor
    · have hPrevious : visit-1 ≠ visited := by omega
      simpa only [Function.update_of_ne hSame,Function.update_of_ne hPrevious] using
        h.factors visit hPos (by omega)

/-- Extend by the actual coefficient produced by the chosen reference, for either
biased or plain arithmetic. -/
theorem extendWithAlpha (h : RecordedSoftmaxRowPrefix p l X producer batch head row stage blocks
      visited reference sums) (hPositive : 0 < visited)
    (old candidate : Option ℝ) (sum : ℝ) (biased : Bool) {pos : Nat} {a : Acc}
    (hOld : reference (visited-1) = old.map (abiFloat p.scaleLog2Bits * ·)) :
    let scale := abiFloat p.scaleLog2Bits
    let mx := (chosenReference scale old candidate).map (scale * ·)
    SoftmaxSumPrefix p batch head row blocks (visited+1)
      (Function.update reference visited mx) (Function.update sums visited sum) →
    ObservedProbabilityTile l X producer stage visited (fun k =>
      shiftedWeight p batch head row (visitKey blocks visited k) (mx.getD 0)) →
    StatisticsStore X (producer,pos) (Softmax.rescaleStore biased)
      a (alphaWord scale old candidate).toBytes →
    (Thread.Scores.before X (producer,pos)).notices = visited →
    RecordedSoftmaxRowPrefix p l X producer batch head row stage blocks (visited+1)
      (Function.update reference visited mx) (Function.update sums visited sum) := by
  dsimp only
  intro hSums hTile hAlpha hOrdinal
  refine h.extend hPositive _ sum hSums hTile ⟨pos,biased,a,_,hAlpha,hOrdinal,?_⟩
  rw [hOld,← correctionAlpha_eq]
  exact Statistics.rescaleFactorOfSoftmaxWord _ _ _

end RecordedSoftmaxRowPrefix
end
end PTX.Kernels.TmlFa4Fwd.Protocol
