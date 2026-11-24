-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.InputActualSources
public import Kernels.TmlFa4Fwd.Proof.LoaderProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
public import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
public import Kernels.TmlFa4Fwd.Proof.Progress.Completion
public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputDrain
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitTargets
public import Lemmas.Step.MmaDrainTmemA
public import Kernels.TmlFa4Fwd.Proof.Safety.StageOwnership
import Kernels.TmlFa4Fwd.Proof.Safety.SharedLifetime
import Kernels.TmlFa4Fwd.Proof.Safety.MmaSharedSources
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Safety.TmemAccumulatorSeparation
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

/-- With the output footprint established, a maximal execution finishes every issued
MMA and delivers each commit notification. -/
theorem mmaAndCommitsDrained (hFrame : OutputFootprint p X) :
    (∀ i, X.TcAsync i → X.async.mmaDone i = true) ∧
      ∀ i s rank target, X.Commit i s → TcCommit.target s rank = some target →
        rank ∈ X.tcNotified i := by
  have hGuarded := syncGuarded hp hMax.1 (hFrame.metadataProtected hp).1
  have hOperandSources : OperandByteSourcesT l X :=
    ⟨Thread.mmaWarpIssuerUnique hp hMax.1, fun _ _ _ _ _ hi hPending =>
      ⟨Safety.actualMmaDescriptorValid hp hMax.1 hi, fun _ _ _ hByte => by
        obtain ⟨src, hLoc, hOrder⟩ :=
          Safety.pendingSharedOperandSources hp hMax.1 hFrame hPending hByte
        exact ⟨src, hLoc, fun w a bytes hw hc => (hOrder w a bytes hw hc).imp_right
          (Or.imp ByteCausality.direct ByteCausality.direct)⟩⟩⟩
  have hDone (i : EvId) (hi : X.TcAsync i) : X.async.mmaDone i = true := by
    obtain ⟨_, _, _, _, hIssue⟩ := Thread.tcAsyncIsMma hMax.1 hi
    exact hMax.mma_all_done_tmemA_of_byte_sources Assumptions.wfStep hGuarded hOperandSources
      (Safety.mmaATmemApart hp hMax.1) (Mma.actualMmaLayoutInjective hMax.1) hIssue
  refine ⟨hDone, ?_⟩
  intro i s rank target hi hTarget
  refine Maximal.commit_notified_inOrder Assumptions.wfStep hMax ?_ hi hTarget ?_
  · intro g j j' site site' prior later r loc hj _ hj' _ hLater
    obtain ⟨loc', hTarget'⟩ := Thread.commitTargetSingle hp hMax.1 ⟨site', hj'⟩
    have hZero : r.val = 0 := by
      by_contra hNot
      rw [hTarget', ite_eq_right hNot] at hLater
      cases hLater
    obtain ⟨prev, hPrev⟩ := Thread.commitTargetSingle hp hMax.1 ⟨site, hj⟩
    exact ⟨prev, by rw [hPrev, ite_eq_left hZero]⟩
  · intro op hTracks
    exact hMax.1.tma.2.1.2 op (hDone op hTracks.2.2.1)

/-- Shared lifetime safety eliminates pending shared stages at exit. The only additional
maximality arguments finish ordinary copy arrivals and the global effects of output stores. -/
theorem asyncDrainedOfSafeExits (hExit : ∀ g < l.threads, Thread.Exited X g)
    (hLifetime : ¬ SharedLifetimeUnsafe l kernel Assumptions.all X) : AsyncDrained X := by
  have exits (owner : Nat) : CtaExited l X owner := Thread.ctaExited hMax.1 hExit
  have finish {i : EvId} {part : AsyncCopy.Part}
      (hStage : AsyncCopy.FinalStage X i part) (hUse : StageUses X i part (i.1 / l.block)) :
      X.AsyncPresent i part := by
    by_contra hPending
    apply hLifetime
    have hShared : SharedUse l X (.async i part) (i.1 / l.block) :=
      .inr (.inr (.inr (.inr ⟨i, part, rfl, hStage, hUse⟩)))
    exact ⟨_, _, hShared, .inr ⟨exits _, fun h => hPending h.1⟩⟩
  have copies (i : EvId) (s : AsyncCopy.Spec) (hi : X.Copy i s) :
      (X.async.copies i).writeBytes.isSome := by
    have hShape := actualCopyShape hMax.1 hi
    have hComp : s.completion = .asyncGroup := hShape.completion
    have hFinal : AsyncCopy.FinalStage X i (.write .copy) :=
      .inr (.inl ⟨s, hi, by simp [hComp], rfl⟩)
    exact finish hFinal ⟨s, hi, .inr hComp, .inl ⟨hShape.dstShared, (actualCopyFrame hMax.1 hi).2⟩⟩
  refine (asyncDrained_iff X).2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i s hi
    rw [(actualCopyShape hMax.1 hi).completion]
    exact copies i s hi
  · intro i loc noinc hi
    cases noinc with
    | false => exact (Loader.noIncrementingCopyArrival hMax.1 hi).elim
    | true =>
      cases hPending : X.async.arrived i
      · apply (hMax.not_grows (pending_cpAsyncArrive_extendsInOrder Assumptions.wfStep
          hMax.1 hi hPending ?_)).elim
        intro copy hTracked
        obtain ⟨s, hs, _⟩ := hTracked.2.2.1
        exact copies copy s hs
      · rfl
  · intro i hi
    obtain ⟨d, s, accum, mask, hMma⟩ := Thread.tcAsyncIsMma hMax.1 hi
    have hFinal : AsyncCopy.FinalStage X i .mmaDone := .inr (.inr (.inr (.inl ⟨hi, rfl⟩)))
    exact finish hFinal (.inl ⟨d, s, accum, mask, hMma, .inl (Safety.mmaOperandOwners hp
      hMax.1 hMma).1.symm⟩)
  · intro i s targets hi
    exact (noClcIssue hMax.1 hi).elim
  · intro i address s hi
    have hRoute := actualTensorRoute hMax.1 hi
    have hFinal : AsyncCopy.FinalStage X i (.notify .load) :=
      .inr (.inr (.inr (.inr (.inr (.inl ⟨address, s, hi, rfl⟩)))))
    exact finish hFinal ⟨address, s, hi, hRoute.2.2.1,
      Safety.sameClusterOwner hp hRoute.2.2.2.2.1⟩
  · intro i address s hi
    exact Protocol.Output.storeFullyDoneAtExit hMax hi hp (exits _)
  · intro i s rank target hi hTarget
    have hFinal : AsyncCopy.FinalStage X i (.tcNotify rank) :=
      .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨s, rank, target, hi, hTarget, rfl⟩))))))
    exact finish hFinal ⟨s, target, hi, hTarget, actualCommitTargetOwner hp hMax.1 hi hTarget⟩

/-- Exited threads and shared lifetime safety suffice for maximal execution completion. -/
theorem completeOfSafeExits (hExit : ∀ g < l.threads, Thread.Exited X g)
    (hLifetime : ¬ SharedLifetimeUnsafe l kernel Assumptions.all X) : Complete l X :=
  completeOfExitsAndEffects hMax.1 hExit (asyncDrainedOfSafeExits hp hMax hExit hLifetime)

/-- For the protected drain, exiting every role forces completion of every issued effect. -/
theorem completeOfExitedRoles (hCuQ : Epilogue.DrainCuQProtected p X)
    (hExit : ∀ g < l.threads, Thread.Exited X g) : Complete l X :=
  completeOfSafeExits hp hMax hExit (Safety.noSharedLifetimeUnsafe hp hMax.1 hCuQ)

end PTX.Kernels.TmlFa4Fwd.Progress
