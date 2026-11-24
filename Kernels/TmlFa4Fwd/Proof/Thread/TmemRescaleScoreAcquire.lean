-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreStatisticsGate
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityScore

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.AsyncCopy Prologue

/-- Expose the publication guard as an acquiring score observation, indexed by its
actual successful-poll ordinal. -/
theorem statisticsScoreAcquireAtOrdinal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j cta n : Nat} {round : Round} (stage : Fin 2)
    (hw : warpIndex l g < 8) (hCta : g/l.block = cta) (hStage : warpIndex l g/4 = stage.val)
    (hPub : Publishes X (g,j) round)
    (hN : n + (if round = .final then 1 else 0) < (before X (g,j)).notices + 1) :
    let object := scoreReadyObject l cta stage
    let wait := (g,MbarRing.Poll.nth X object g n)
    n < okPolls object (X.tr g) ∧ ScoreAcquire X wait object ∧ Resumes kernel X wait (g,j) := by
  obtain ⟨k,⟨site,kind⟩,parity,acq,scope,hGet,hKind,hOrdinal,hResume⟩ :=
    statisticsScoreAcquire hp hX stage hw hCta hStage hPub hN
  change kind = _ at hKind
  subst kind
  obtain ⟨rfl,rfl⟩ := successfulScoreWaitIsAcquire hp hX stage hw hGet
  have hNth := MbarRing.Poll.nth_eq hGet
  rw [hOrdinal] at hNth
  have hHas : n < okPolls (scoreReadyObject l cta stage) (X.tr g) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  dsimp only
  rw [hNth]
  exact ⟨hHas,⟨_,_,hGet,rfl⟩,hResume⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
