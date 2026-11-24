-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundExit
public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderSteadyRoundExit
public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundTailProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread.Loader Protocol.Loader Protocol.Bias
open PTX.Kernels.TmlFa4Fwd.Loader

/-- Both loader warps of a scheduled multi-visit CTA complete the K/V rounds `0..r`. Every
lane publishes each ring use below `cacheUseOfRound r+2`, warp 14 delivers the warm Bias
generations of the warm rounds through `r`, and, when round `r` is a steady round, warp 14
delivers the warm-tail Bias generation. The hypotheses are facts about `X` that those rounds
wait for: the MMA's release of their ring uses, softmax's release of the earlier Bias
generations of the warm rounds through `r`, and, for a steady round `r`, softmax's release
before the warm tail. -/
theorem loaderRoundsThrough {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (r : Nat) (hr : r+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : CacheUsesReleased l X g (cacheUseOfRound r+2))
    (hBias : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, round ≤ r → ∀ stage,
      BiasEmptyReleased l X (g/l.block) stage (round+1))
    (hTail : warpIndex l g = 14 → warmTailSkips p l g batch = false →
      warmRounds p l g batch ≤ r →
      BiasEmptyReleased l X (g/l.block) 0 (warmRounds p l g batch+1)) :
    (∀ lane < 32, ∀ use < cacheUseOfRound r+2,
      use-1 ≤ (X.tr (warpLane l g lane)).countP recurringPublicationMark) ∧
    (warpIndex l g = 14 → ∀ stage, ∀ round < warmRounds p l g batch, round ≤ r →
      BiasGenerationDelivered l X (g/l.block) stage (round+1)) ∧
    (warpIndex l g = 14 → warmTailSkips p l g batch = false → warmRounds p l g batch ≤ r →
      BiasGenerationDelivered l X (g/l.block) 0 (warmRounds p l g batch+1)) := by
  have hWarm : warmRounds p l g batch =
      min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9 := rfl
  have hRel : CacheUsesReleased l X g (2+2*(r+1)) :=
    hReleased.mono (by unfold cacheUseOfRound; omega)
  have hReady : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, round < r+1 →
      WarmBiasEmptyReady l X g batch round := fun h14 round hRound hle =>
    warmBiasEmptyReadyOfReleases hp hMax.1 hFrame hg h14 hb hLo hHi hTrips hRound
      (hBias h14 round hRound (by omega))
  have hDelivered : warpIndex l g = 14 → ∀ stage, ∀ round < warmRounds p l g batch,
      round ≤ r → BiasGenerationDelivered l X (g/l.block) stage (round+1) :=
    fun h14 stage round hRound hle => warmBiasGenerationsDelivered hp hMax hFrame hg h14 hb hLo
      hHi hTrips hRel (fun round hRound hle stage => hBias h14 round hRound (by omega) stage)
      stage round hRound (by omega)
  by_cases hCase : r < warmRounds p l g batch
  · refine ⟨fun lane hl use hu => ?_,hDelivered,fun _ _ h => by omega⟩
    obtain ⟨_,⟨value⟩,_⟩ := warmRoundsPublishedThrough hp hMax hFrame hg hw hb hLo hHi hTrips
      hRel hReady r hCase (by omega)
    have h := publicationCountOfPrefix
      (value.publicationCount hp hMax.1 hFrame hg hw hb hLo hHi lane hl)
    omega
  · have hW : warmRounds p l g batch = 9 := by omega
    obtain ⟨⟨d⟩,hTailDelivered⟩ := warmTailDoneOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips
      (hReleased.mono (by unfold cacheUseOfRound; omega))
      (fun h14 round hRound stage => hBias h14 round hRound (by omega) stage)
      (fun h14 hSkip => hTail h14 hSkip (by omega))
    obtain ⟨start⟩ := d.steadyHead hp hb hLo hHi (by omega)
    rw [hW] at start
    obtain ⟨head⟩ := steadyRoundHeadsOfMaximal hp hMax hFrame hg hw hb hLo hHi (bound := r)
      (hReleased.mono (by unfold cacheUseOfRound; omega)) start (r-9) (by omega) (by omega)
    have hRound : 9+(r-9) = r := by omega
    rw [hRound] at head
    obtain ⟨_,⟨value⟩⟩ := steadyRoundPublishedOfHead hp hMax hFrame hg hw hb hLo hHi hr
      hReleased head
    refine ⟨fun lane hl use hu => ?_,hDelivered,fun h14 hSkip _ => hTailDelivered h14 hSkip⟩
    have h := publicationCountOfPrefix
      (value.publicationCount hp hMax.1 hFrame hg hw hb hLo hHi lane hl)
    unfold cacheUseOfRound at h hu
    omega

end PTX.Kernels.TmlFa4Fwd.Progress
