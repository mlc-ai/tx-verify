-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasRound
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningValueAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The MMA has returned the earlier generations of every ring use below `bound`: the
empty object of the use's slot carries at least `use/3` completed units. -/
def CacheUsesReleased (l : Launch) (X : Execution) (g bound : Nat) : Prop :=
  ∀ use, 2 ≤ use → use < bound →
    use/3 ≤ Protocol.Loader.cacheEmptyUnits l X g (kvUseStage use)

theorem CacheUsesReleased.mono {l : Launch} {X : Execution} {g a b : Nat}
    (h : CacheUsesReleased l X g b) (hab : a ≤ b) : CacheUsesReleased l X g a :=
  fun use h2 hu => h use h2 (by omega)

/-- Before warm round `round`, each lane of warp 14 has elected `round` times at each
warm Bias site by every point after the previous round's Bias block. -/
def WarmBiasCounts (X : Execution) (l : Launch) (g batch round : Nat) : Prop :=
  ∀ lane < 32, ∀ k pos, (round = 0 ∨ primingSearchShuffleCount batch+96+64*(round-1) <
    ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl) →
    round ≤ warmBiasSiteCount X (warpLane l g lane) pos k

private theorem warpCases {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat}
    (hw : 14 ≤ warpIndex l g) : warpIndex l g = 14 ∨ warpIndex l g = 15 := by
  have := warpIndex_lt hp g
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

/-- One warm round from its head: both warps publish K and V, and warp 14 issues its two
Bias stages. The release hypothesis covers the K and V uses of the round. -/
theorem warmRoundPublishedOfHead {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (hRound : round < warmRounds p l g batch)
    (hReleased : CacheUsesReleased l X g (cacheUseOfRound round+2))
    (hReady : warpIndex l g = 14 → WarmBiasEmptyReady l X g batch round)
    (hCounts : warpIndex l g = 14 → WarmBiasCounts X l g batch round)
    (head : WarmRoundHead p l X g batch round) :
    Nonempty (WarmRoundKeyPublished p l X g batch round) ∧
      Nonempty (WarmRoundValuePublished p l X g batch round) ∧
      (warpIndex l g = 14 → WarmRoundBiasIssued p l X g batch round) := by
  have hKey : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)) :=
    hReleased _ (by unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega)
  have hValue : (cacheUseOfRound round+1)/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round+1)) :=
    hReleased _ (by unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega)
  obtain ⟨c⟩ := head.keyPublishedOfMaximal hp hMax hFrame hg hw hb hLo hHi hRound hKey
  rcases warpCases hp hw with h14 | h15
  · have hLower (lane : Nat) (hl : lane < 32) (k : Fin 6) :
        round ≤ warmBiasSiteCount X (warpLane l g lane) (c.reached.pos lane) k := by
      apply hCounts h14 lane hl k
      rcases Nat.eq_zero_or_pos round with h | h
      · exact .inl h
      · right
        rw [c.reached.ordinals.shfl lane hl,c.rank]
        omega
    obtain ⟨hV,hB⟩ := c.biasRoundOfMaximal hp hMax hFrame hg h14 hb hLo hHi hRound
      (hReady h14) hValue hLower
    exact ⟨⟨c⟩,hV,fun _ => hB⟩
  · exact ⟨⟨c⟩,c.valuePublishedSecondWarpOfMaximal hp hMax hFrame hg h15 hb hLo hHi hValue,
      fun h => by omega⟩

/-- Every warm round up to `bound` has a head, and warp 14's election counts reach the round
index. Only the K/V releases and Bias readiness of the warm rounds before `bound` are used. -/
theorem warmRoundHeadsOfMaximal {g batch bound : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : CacheUsesReleased l X g (2+2*bound))
    (hReady : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, round < bound →
      WarmBiasEmptyReady l X g batch round) :
    ∀ round < warmRounds p l g batch, round ≤ bound →
      Nonempty (WarmRoundHead p l X g batch round) ∧
      (warpIndex l g = 14 → WarmBiasCounts X l g batch round) := by
  intro round
  induction round with
  | zero =>
    intro _ _
    obtain ⟨start,hStart⟩ : ∃ c : WarmCacheStarted p l X g batch,
        c.shuffles = primingSearchShuffleCount batch+64 := by
      rcases warpCases hp hw with h | h
      · exact openingFirstLoaderWarmCacheWithRankOfMaximal hp hMax hFrame hg h hb hLo hHi hTrips
      · exact openingLoaderWarmCacheWithRankOfMaximal hp hMax hFrame hg h hb hLo hHi hTrips
    exact ⟨⟨start.roundHead hStart⟩,fun _ _ _ _ _ _ => Nat.zero_le _⟩
  | succ round ih =>
    intro hNext hBound
    obtain ⟨⟨head⟩,hCounts⟩ := ih (by omega) (by omega)
    obtain ⟨_,⟨published⟩,hBias⟩ := warmRoundPublishedOfHead hp hMax hFrame hg hw hb hLo hHi
      (by omega) (hReleased.mono (by unfold cacheUseOfRound; omega))
      (fun h => hReady h round (by omega) (by omega)) hCounts head
    refine ⟨(published.next hp hb hLo hHi (by omega)).1 hNext,fun h14 lane hl k pos hPos => ?_⟩
    rcases hPos with h | h
    · omega
    · exact (hBias h14).counted lane hl k pos (by simpa using h)

/-- Every warm round before `bound` publishes its K and V packets, and warp 14 issues its
Bias stages. Only the K/V releases and Bias readiness of those rounds are used. -/
theorem warmRoundsPublishedThrough {g batch bound : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : CacheUsesReleased l X g (2+2*bound))
    (hReady : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, round < bound →
      WarmBiasEmptyReady l X g batch round) :
    ∀ round < warmRounds p l g batch, round < bound →
      Nonempty (WarmRoundKeyPublished p l X g batch round) ∧
      Nonempty (WarmRoundValuePublished p l X g batch round) ∧
      (warpIndex l g = 14 → WarmRoundBiasIssued p l X g batch round) := by
  intro round hr hBound
  obtain ⟨⟨head⟩,hCounts⟩ := warmRoundHeadsOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips
    hReleased hReady round hr hBound.le
  exact warmRoundPublishedOfHead hp hMax hFrame hg hw hb hLo hHi hr
    (hReleased.mono (by unfold cacheUseOfRound; omega)) (fun h => hReady h round hr hBound)
    hCounts head

/-- All warm rounds publish their K and V packets, warp 14 issues every warm Bias stage, and
the warp reaches the warm tail. -/
theorem warmRoundsDoneOfMaximal {g batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : CacheUsesReleased l X g (2+2*warmRounds p l g batch))
    (hReady : warpIndex l g = 14 → ∀ round < warmRounds p l g batch,
      WarmBiasEmptyReady l X g batch round) :
    Nonempty (WarmRoundsDone p l X g batch) ∧
      (∀ round < warmRounds p l g batch,
        Nonempty (WarmRoundKeyPublished p l X g batch round) ∧
        Nonempty (WarmRoundValuePublished p l X g batch round) ∧
        (warpIndex l g = 14 → WarmRoundBiasIssued p l X g batch round)) := by
  have hW : 1 ≤ warmRounds p l g batch := by unfold warmRounds; omega
  have hRound (round : Nat) (hr : round < warmRounds p l g batch) :
      Nonempty (WarmRoundKeyPublished p l X g batch round) ∧
      Nonempty (WarmRoundValuePublished p l X g batch round) ∧
      (warpIndex l g = 14 → WarmRoundBiasIssued p l X g batch round) :=
    warmRoundsPublishedThrough hp hMax hFrame hg hw hb hLo hHi hTrips hReleased
      (fun h round hr _ => hReady h round hr) round hr hr
  obtain ⟨_,⟨last⟩,_⟩ := hRound (warmRounds p l g batch-1) (by omega)
  exact ⟨(last.next hp hb hLo hHi (by omega)).2 (by omega),hRound⟩

end PTX.Kernels.TmlFa4Fwd.Progress
