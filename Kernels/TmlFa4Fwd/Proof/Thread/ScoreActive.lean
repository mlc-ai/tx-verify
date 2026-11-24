-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryCredits
import Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX
open PTX.Kernels.TmlFa4Fwd.Mma (qkCommitSite commitSite firstQueryWaitBeforeGate
  firstQueryPollOperands)

/-- Every score commit follows the actual Q0 acquisition for its active work item. -/
theorem scoreCommitActive {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {i : EvId} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hCommit : ScoreCommit l X i (i.1 / l.block) stage spec rank) :
    i.1 / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨g, index⟩ := i
  obtain ⟨block, _, he⟩ := scoreCommitSite hp hX hCommit
  have audit : ∀ b : Fin 4, 2145 ≤ (commitSite (qkCommitSite b)).pc ∧
      (commitSite (qkCommitSite b)).pc ≤ 2642 := by decide
  obtain ⟨j, _, loc, parity, hGet, _⟩ :=
    firstQueryWaitBeforeGate hp hX he (audit block).1 (audit block).2
  obtain ⟨rfl, rfl⟩ := firstQueryPollOperands hp hX hGet
  obtain ⟨hWait, phase, _, hPhase⟩ := Protocol.queryAcquirePhaseOfZero hp hX
    (wait := (g,j)) (stage := 0) ⟨_, hGet, by simp [Output.queryObject]⟩
  obtain ⟨_, publisher, _, _, hPublished, _, _⟩ := hWait.hasTransactionPair hp hX hPhase
  obtain ⟨hCta, ⟨_, _, hBox⟩, _, _⟩ := hPublished
  exact hCta.symm ▸ hBox.active hp hX hCuQ

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
