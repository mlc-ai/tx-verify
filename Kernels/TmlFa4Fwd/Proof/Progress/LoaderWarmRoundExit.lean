-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundProgress
public import Kernels.TmlFa4Fwd.Proof.Progress.CacheDrainExit
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundDrainUses
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderWarmRoundBiasReady
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderCacheDrainEntry
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread.Loader Protocol.Loader Protocol.Bias
open PTX.Kernels.TmlFa4Fwd.Loader

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

set_option maxRecDepth 4096 in
/-- When the warm rounds cover all K/V trips, the warp goes from the warm tail directly to
the drain, with the final ring cursor `2*trips` and no recurring publication left. -/
theorem warmRoundsDrainEntry (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hShort : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 ≤ 10)
    (d : WarmRoundsDone p l X g batch) :
    let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
    CacheDrainEntry p l X g (2*n) ∧
      ∀ lane < 32, RecurringUsesBelow X (warpLane l g lane) (2*n) := by
  intro n
  have hSmall : n-1 ≤ 9 := by omega
  have hW : warmRounds p l g batch = n-1 := by unfold warmRounds; omega
  have hUse : cacheUseOfRound (n-1) = 2*n := by unfold cacheUseOfRound; omega
  obtain ⟨entry,hPos⟩ := d.reached.advanceLocalWithPosition (pc' := 1744)
    (G := fun lane => firstDrainTail p l (warpLane l g lane) (cacheUseOfRound (n-1))) (by
    intro lane hl
    let t := warpLane l g lane
    have hSame : warpIndex l g = warpIndex l t :=
      (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.2
    have hw' : warpIndex l t = 14 ∨ warpIndex l t = 15 := by
      have hLt := warpIndex_lt hp t
      omega
    have ht := d.reached.checkpoint lane hl
    have hRegs : Holds (d.reached.state lane).regs
        (warmCacheHeadFrame l (n-1) (n-1)
          (warmRoundCarry p l g batch (warmRounds p l g batch) lane)) := by
      have hEq : warmCacheHeadFrame l (warmRounds p l g batch) (n-1)
          (warmRoundCarry p l g batch (warmRounds p l g batch) lane) =
          warmCacheHeadFrame l (n-1) (n-1)
            (warmRoundCarry p l g batch (warmRounds p l g batch) lane) :=
        congrArg (fun r => warmCacheHeadFrame l r (n-1)
          (warmRoundCarry p l g batch (warmRounds p l g batch) lane)) hW
      exact hEq ▸ ht.2.2.2.2
    have hCarry : Holds (d.reached.state lane).regs (drainCarry l (cacheUseOfRound (n-1))) :=
      ((holds_append ..).mp hRegs.2.2).1
    have hF := ((holds_append ..).mp hRegs.2.2).2
    have hSeven : (d.reached.state lane).regs 7 = some (.pred false) := by
      have h := holds_mem hF (show (7,.pred (decide (10 < n) &&
          warmResidueFlag (vPrimingResidual p batch (assignedCoordinates p batch
            (g/l.block)).1))) ∈ warmRoundCarry p l g batch (warmRounds p l g batch) lane by
        simp [warmRoundCarry,n])
      rw [h]
      simp [show ¬ 10 < n by omega]
    have hWarp : (d.reached.state lane).regs 1062 = some (b32 (warpIndex l t)) := by
      rw [← hSame]
      exact holds_mem hF (by simp [warmRoundCarry,openingWarmFrame,warmStartFrame])
    have hSched : Holds (d.reached.state lane).regs (drainSchedulerFrame p l t) := by
      have hEq : warmRoundCarry p l g batch (warmRounds p l g batch) lane =
          [(7178,loaderPhaseWord (warmBiasPhase (warpIndex l g) (warmRounds p l g batch))),
            (1117,b32 (vPrimingResidual p batch (assignedCoordinates p batch
              (g/l.block)).1/2^31)),(1116,b32 (n-2)),
            (7,.pred (decide (10 < n) && warmResidueFlag (vPrimingResidual p batch
              (assignedCoordinates p batch (g/l.block)).1))),
            (164,.pred (warmResidueFlag (vPrimingResidual p batch (assignedCoordinates p batch
              (g/l.block)).1))),
            (7177,loaderPhaseWord (warmBiasPhase (warpIndex l g) (warmRounds p l g batch)))] ++
            openingWarmFrame p l g batch lane ++ drainSchedulerFrame p l t := rfl
      rw [hEq] at hF
      exact ((holds_append ..).mp hF).2
    exact warmExhaustedLocal hSmall hw' (ht.mono
      ⟨hRegs.2.1,hSeven,drainTailOfCarry hCarry ⟨hWarp,hSched⟩⟩))
  refine ⟨hUse ▸ ⟨d.shuffles,d.votes,d.ends,⟨entry⟩⟩,fun lane hl => ?_⟩
  apply recurringUsesBelowOfDrainCursor hp hX hFrame hg hw hl hb hLo hHi entry
  rw [d.rank,hW]
  omega

/-- Warp 14's Bias-empty readiness for every warm round, from softmax's releases. -/
theorem warmBiasReadyOfReleases (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hBias : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, ∀ stage,
      BiasEmptyReleased l X (g/l.block) stage (round+1)) :
    warpIndex l g = 14 → ∀ round < warmRounds p l g batch,
      WarmBiasEmptyReady l X g batch round := fun hw round hr =>
  warmBiasEmptyReadyOfReleases hp hX hFrame hg hw hb hLo hHi hTrips hr (hBias hw round hr)

/-- A loader lane whose K/V trips all fall in the warm rounds publishes every ring use and
exits. The hypotheses are facts about `X`: the MMA's release of every ring use, softmax's
release of every earlier Bias generation for warp 14, and, for warp 14, the final release of
the second query stage. -/
theorem warmRoundsLoaderExit (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hShort : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 ≤ 10)
    (hReleased : CacheUsesReleased l X g
      (2*Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1+3))
    (hBias : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, ∀ stage,
      BiasEmptyReleased l X (g/l.block) stage (round+1))
    (hQuery : warpIndex l g = 14 → UnitRelease X (secondQueryEmpty l (g/l.block))) :
    Thread.Exited X g := by
  let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have hW : warmRounds p l g batch = n-1 := by unfold warmRounds; omega
  obtain ⟨⟨done⟩,_⟩ := warmRoundsDoneOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips
    (fun use h1 h2 => hReleased use h1 (by rw [hW] at h2; omega))
    (warmBiasReadyOfReleases hp hMax.1 hFrame hg hb hLo hHi hTrips hBias)
  obtain ⟨hEntry,hUses⟩ := warmRoundsDrainEntry hp hMax.1 hFrame hg hw hb hLo hHi hTrips hShort
    done
  have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hUse := hUses (laneOf l g) (Nat.mod_lt _ (by decide))
  rw [hSelf] at hUse
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  apply cacheLoaderExitOfCompletedCredits hp hMax hg hw (hFrame.metadataProtected hp).1 hActive
    hEntry _ hQuery
  apply cacheReleaseCountsOfReleases hp hMax hg hw hUse (by omega)
  intro slot
  have hs := slot.isLt
  let use := 2*n+(3-(2*n)%3+slot.val)%3
  have hStage : kvUseStage use = slot := Fin.ext (by rw [kvUseStage_val]; dsimp only [use]; omega)
  have h := hReleased use (by dsimp only [use]; omega) (by dsimp only [use]; omega)
  rw [hStage] at h
  have hCount : (2*n+(2-slot.val))/3 = use/3 := by dsimp only [use]; omega
  rw [hCount]
  exact h

end PTX.Kernels.TmlFa4Fwd.Progress
