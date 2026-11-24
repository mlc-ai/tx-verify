-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTailValue
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailPvProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSelectedUseBound
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketFacts
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningPvProbability
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningMainProbability
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityTail

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.MBarrier Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

/-- In a one-visit CTA only the priming V packet can publish to its ready object. -/
theorem singleVisitOpeningValuePhaseOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    let log := X.objects (Thread.Loader.readyObject l g 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  obtain ⟨s,hs,hPhase⟩ :=
    selectedValueReadyPhaseOfMaximal hp hMax hFrame (NamedBar.cta_lt hg) hb hLo hHi
  have hExact : s.phase = 1 := by
    by_contra! hNe
    have hLate : 1 < s.phase := by omega
    obtain ⟨id,hPub,hPositive⟩ := positivePublicationOfAdvancedReady hp hMax.1 1 hs hLate
    let n := Protocol.LoaderReady.generation l X id 1
    let use := 3*n+1
    have hGen : 0 < n := hPositive
    have hUse : 2 ≤ use := by dsimp [use]; omega
    have hSlot : Loader.kvUseStage use = 1 := by
      apply Fin.ext
      rw [Loader.kvUseStage_val]
      dsimp [use]
      omega
    have hDiv : use/3 = n := by dsimp [use]; omega
    have hCycle : (Thread.Loader.atPrefix l X id.1 id.2).published.countP
        (fun q => q.slot == Loader.kvUseStage use) = use/3 := by
      rw [hSlot,hDiv]
      rfl
    have hReady : X.AsyncArrive id
        (Thread.Loader.readyObject l g (Loader.kvUseStage use)) true := by
      rw [hSlot]
      exact hPub
    obtain ⟨group⟩ := Thread.Loader.publishedCopyGroup hp hMax.1 hPub
    have hNonempty : group.copies ≠ [] := by
      intro h
      have hLen := group.count
      rw [h] at hLen
      simp at hLen
    obtain ⟨⟨j,spec⟩,hMember⟩ := List.exists_mem_of_ne_nil _ hNonempty
    have hOwner : id.1/l.block = g/l.block :=
      (Protocol.LoaderReady.publicationCta hp hMax.1 hPub).symm
    have hRank := group.recurringUseBound hp hMax.1 hFrame hReady hCycle hUse hMember
      (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi)
    rw [hOwner,hSingle] at hRank
    omega
  exact ⟨s,hs,hExact⟩

/-- Every MMA lane on the selected one-visit path reaches its joint probability acquire
after recording the first value acquire. -/
theorem singleVisitOpeningProbabilityReachedOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∃ shuffles votes ends,
      Nonempty (Mma.OpeningTailProbabilityReached l X g shuffles votes ends) := by
  obtain ⟨shuffles,votes,ends,⟨cur⟩⟩ :=
    openingKeyReturnedWithTripsOfMaximal hp hMax hFrame hg hw hb hLo hHi
  obtain ⟨⟨ready⟩,_⟩ := Mma.openingTailValueReachedOfMaximal hp hMax hg (hSingle ▸ cur)
  have hPhase := singleVisitOpeningValuePhaseOfMaximal hp hMax hFrame hg hb hLo hHi hSingle
  obtain ⟨next,_⟩ := Mma.openingTailProbabilityReachedOfMaximal hp hMax hg ready hPhase
  exact ⟨shuffles,votes,ends,⟨next⟩⟩

/-- The single-visit lane path has no recurring score notification in its CTA. -/
theorem singleVisitOnlyOpeningScoreOfMaximal {cta batch : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1) {i : EvId} {stage : Fin 2}
    {spec : TcCommit.Spec} {rank : Fin 16}
    (hScore : Thread.Scores.ScoreCommit l X i cta stage spec rank) :
    Thread.Scores.scoreCommitOrdinal l X cta stage i = 0 := by
  obtain ⟨g,j⟩ := i
  obtain ⟨hCta,hWarp,_⟩ := Thread.Scores.scoreCommitActor hp hMax.1 hScore
  obtain ⟨_,he⟩ := hScore.1
  have hg := PTX.Proof.event_thread_lt hMax.1 he
  obtain ⟨_,_,_,⟨cur⟩⟩ := openingKeyReturnedWithTripsOfMaximal hp hMax hFrame hg hWarp hb
    (hCta.symm ▸ hLo) (hCta.symm ▸ hHi)
  have hTrip := hCta.symm ▸ hSingle
  exact Mma.scoreOrdinalZeroOfSingleVisitOpening hp hMax.1 (hTrip ▸ cur) hScore

/-- The opening softmax and correction cohorts complete probability phase one, and the
single-visit MMA route excludes every possible second phase. -/
theorem singleVisitOpeningMainProbabilityPhaseOfMaximal {cta batch : Nat} (hc : cta < l.grid)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1) (stage : Fin 2) :
    let log := X.objects (Thread.Scores.probabilityObject l cta stage 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  obtain ⟨s,hs,hLower⟩ := openingMainProbabilityAdvancedOfMaximal hp hMax hFrame hc stage hb hLo hHi
  have hCuQ : DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hUpper := Protocol.Scores.jointPhaseAtMostOneOfOnlyInitialScores hp hMax.1
    (Protocol.Scores.correctionJointGuardsOfCuQ hp hMax.1 hCuQ) stage
    (fun h => singleVisitOnlyOpeningScoreOfMaximal hp hMax hFrame hb hLo hHi hSingle h) hs
  exact ⟨s,hs,Nat.le_antisymm hUpper hLower⟩

/-- The selected one-visit MMA warp acquires its opening V and P packets
and completes the election for their first PV block. -/
theorem singleVisitFirstTailPvLeaderOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∃ shuffles votes ends, Nonempty (Mma.OpeningTailFirstPvElected l X g shuffles votes ends) := by
  obtain ⟨shuffles,votes,ends,⟨cur⟩⟩ :=
    singleVisitOpeningProbabilityReachedOfMaximal hp hMax hFrame hg hw hb hLo hHi hSingle
  have hReady := singleVisitOpeningMainProbabilityPhaseOfMaximal hp hMax hFrame
    (NamedBar.cta_lt hg) hb hLo hHi hSingle 0
  obtain ⟨main⟩ := Mma.openingTailMainReturnedOfMaximal hp hMax hg cur hReady
  exact ⟨shuffles+3,votes,ends,Mma.firstTailPvLeaderOfMaximal hp hMax hg main⟩

/-- Every completed opening tail object has phase one in a one-visit CTA. -/
theorem singleVisitOpeningTailProbabilityPhaseOfMaximal {cta batch : Nat} (hc : cta < l.grid)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1) (stage : Fin 2) :
    let log := X.objects (Thread.Scores.probabilityObject l cta stage 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  obtain ⟨s,hs,hLower⟩ := openingProbabilityTailAdvancedOfMaximal hp hMax hFrame hc stage hb hLo hHi
  have hUpper := Protocol.Scores.tailPhaseAtMostOneOfOnlyInitialScores hp hMax.1 stage
    (fun h => singleVisitOnlyOpeningScoreOfMaximal hp hMax hFrame hb hLo hHi hSingle h) hs
  exact ⟨s,hs,Nat.le_antisymm hUpper hLower⟩

end PTX.Kernels.TmlFa4Fwd.Progress
