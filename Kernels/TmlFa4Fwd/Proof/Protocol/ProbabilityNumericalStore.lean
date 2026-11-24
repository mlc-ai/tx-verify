-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityOperandSources
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityStoreOfCredit
import Kernels.TmlFa4Fwd.Proof.Thread.TmemConflictGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.TcMma Thread Thread.Scores

/-- A recorded probability word belongs to the selected source if its score
ordinal agrees with the observed PV packet. -/
theorem ProbabilityCellPublication.eq_of_publishedWord {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {reader store : EvId} {cell : Cell} (seen : ProbabilityCellPublication l X reader cell)
    (hRead : X.MmaACell reader cell)
    (hWord : PublishedProbabilityWord l X store cell seen.stage)
    (hScore : okPolls (scoreReadyObject l (reader.1/l.block) seen.stage)
      ((X.tr store.1).take store.2) = seen.phase+1) : store = seen.store := by
  have hLane := sameTensorStoreLane hp hX hWord.cellWritten seen.cellWritten
  have hCta : store.1/l.block = reader.1/l.block := by
    rw [hLane]
    exact seen.footprint.cta.symm.trans (mmaAOperandCta hp hX hRead)
  obtain ⟨_,_,_,hSeen⟩ := seen.exactScoreAndStoreCount hp hX hCuQ hRead
  rcases lt_trichotomy store.2 seen.store.2 with h | h | h
  · have hNew := hWord.later seen.store hLane.symm h seen.cellWritten
    rw [hCta,hScore,hSeen] at hNew
    exact (Nat.lt_irrefl _ hNew).elim
  · exact Prod.ext hLane h
  · have hNew := seen.laterStoreBudget store hWord.cellWritten hWord.footprint hLane.symm h
    rw [hScore] at hNew
    omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
