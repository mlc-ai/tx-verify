-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundUseRank
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringWaitProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage primingSearchShuffleCount recurringEmptyWait)

/-- The release history of a slot depends only on the CTA of the named lane. -/
theorem cacheEmptyUnits_sameCta {l : Launch} {X : Execution} {g h : Nat} (slot : Fin 3)
    (hCta : g/l.block = h/l.block) :
    Protocol.Loader.cacheEmptyUnits l X g slot = Protocol.Loader.cacheEmptyUnits l X h slot := by
  simp only [Protocol.Loader.cacheEmptyUnits,Protocol.Loader.cacheEmptyLog,
    Thread.Mma.Observation.emptyObject,hCta]

/-- The readiness condition of a recurring wait depends only on the CTA of the named lane. -/
theorem CacheEmptyReady.sameCta {l : Launch} {X : Execution} {g h use : Nat}
    (hCta : g/l.block = h/l.block) (hReady : CacheEmptyReady l X g use) :
    CacheEmptyReady l X h use := by
  unfold CacheEmptyReady at hReady ⊢
  have hLoc : emptyObject l g (kvUseStage use) = emptyObject l h (kvUseStage use) := by
    simp only [emptyObject,hCta]
  rw [hLoc] at hReady
  exact hReady

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch use shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hMax hFrame hg hw hb hLo hHi

/-- A recurring K or V gate for `use` returns in each lane that has not yet published when
the MMA has delivered `use/3` releases of the slot. The rank condition says that the warp has
performed at most `32*use` shuffles after its priming search, which bounds the ring positions
already published by each lane. -/
theorem RecurringCacheGate.readyOfReleases {site : Fin 4} {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : RecurringCacheGate l X g site use F shuffles votes ends)
    (hRank : shuffles ≤ primingSearchShuffleCount batch+32*use) (hTwo : 2 ≤ use)
    (hReleased : use/3 ≤ Protocol.Loader.cacheEmptyUnits l X g (kvUseStage use)) :
    ∀ lane < 32,
      (∀ j ≥ cur.pos lane, ∀ loc, ¬ X.AsyncArrive (warpLane l g lane,j) loc true) →
        CacheEmptyReady l X g use := by
  intro lane hl hQuiet
  let t := warpLane l g lane
  have hSame : SameWarp l g t := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  have ht : t < l.threads := hSame.1.2.1
  have hCta : g/l.block = t/l.block := hSame.1.2.2
  have hwt : 14 ≤ warpIndex l t := by
    have hEq := hSame.2
    change g % l.block / 32 = t % l.block / 32 at hEq
    rw [warpIndex,← hEq]
    exact hw
  have hShuffles := cur.ordinals.shfl lane hl
  have hUses := recurringUsesBelowOfShuffleRank hp hMax.1 hFrame hg hw hl hb hLo hHi
    (pos := cur.pos lane) (use := use) (by omega) hQuiet
  have hReady := Protocol.Loader.cacheEmptyReadyOfReleases hp hMax ht hwt hUses hTwo
    (by rw [← cacheEmptyUnits_sameCta (kvUseStage use) hCta]; exact hReleased)
  exact hReady.sameCta hCta.symm

/-- The gate passes its empty poll when the MMA has delivered the earlier generations of the
slot. -/
theorem RecurringCacheGate.acquireOfReleases (site : Fin 4) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : RecurringCacheGate l X g site use F shuffles votes ends)
    (hFresh : ∀ lane < 32, (recurringEmptyWait site).result ∉ (F lane).map Prod.fst)
    (hRank : shuffles ≤ primingSearchShuffleCount batch+32*use) (hTwo : 2 ≤ use)
    (hReleased : use/3 ≤ Protocol.Loader.cacheEmptyUnits l X g (kvUseStage use)) :
    ∃ done : RecurringCacheAcquired l X g site use F shuffles votes ends,
      ∀ lane < 32, (∃ index, cur.pos lane ≤ index ∧
        index+1 = done.pos lane ∧
        EmptyAcquire l X (warpLane l g lane,index) (kvUseStage use) (cacheEmptyParity use)) ∧
        ∀ i, cur.pos lane ≤ i → i < done.pos lane →
          ∀ a, ¬ X.Access (warpLane l g lane,i) a true :=
  cur.acquirePreservingLocalOfBlockedMaximal hp hMax hg site hFresh
    (cur.readyOfReleases hp hMax hFrame hg hw hb hLo hHi hRank hTwo hReleased)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
