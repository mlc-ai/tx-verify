-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundValuePacket
public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCacheDrainEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundDrainUses
import Lemmas.Flow.CountTake
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread.Loader Protocol.Loader
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The loader warp has left the last steady round and reached the drain at pc 1744 with the
ring cursor after all trips. -/
structure SteadyRoundsDone (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SteadyCacheDone l X g
    (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
    (steadyRoundCarry p l g batch) shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+64+
    64*(Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

set_option maxRecDepth 4096 in
/-- The steady tail moves from the V publication of steady round `round` to the head of the
next steady round, or leaves the steady loop after the last round. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.Loader.SteadyRoundValuePublished.next (hp : Pre p l m)
    {g batch round : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
    (c : SteadyRoundValuePublished p l X g batch round) :
    (round+1 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1 →
        Nonempty (SteadyRoundHead p l X g batch (round+1))) ∧
      (round+1 = Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1 →
        Nonempty (SteadyRoundsDone p l X g batch)) := by
  let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  have hTrips : n-1 < 2^31 := by omega
  have step := fun lane hl => steadyCacheTailLocal (l := l) (g := warpLane l g lane)
    (F := steadyRoundCarry p l g batch lane) hTrips hRound
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by simp [steadyRoundCarry,warmRoundCarry,openingWarmFrame,warmStartFrame])
    (c.reached.checkpoint lane hl)
  refine ⟨fun hMore => ?_,fun hLast => ?_⟩
  · obtain ⟨u⟩ := c.reached.advanceLocal (pc' := 1396)
      (G := fun lane => steadyCacheHeadFrame l (round+1) (n-1) (steadyRoundCarry p l g batch lane))
      (by
        intro lane hl
        obtain ⟨t,ht,htAt⟩ := step lane hl
        rw [ite_eq_left hMore] at htAt
        exact ⟨t,ht,htAt⟩)
    exact ⟨⟨c.shuffles,c.votes,c.ends,u,by rw [c.rank]; omega⟩⟩
  · obtain ⟨u⟩ := c.reached.advanceLocal (pc' := 1744)
      (G := fun lane => steadyCacheHeadFrame l (n-1) (n-1) (steadyRoundCarry p l g batch lane))
      (by
        intro lane hl
        obtain ⟨t,ht,htAt⟩ := step lane hl
        rw [ite_eq_right (show ¬ round+1 < n-1 by omega)] at htAt
        have hEq := congrArg (fun r => steadyCacheHeadFrame l r (n-1)
          (steadyRoundCarry p l g batch lane)) hLast
        exact ⟨t,ht,hEq ▸ htAt⟩)
    exact ⟨⟨c.shuffles,c.votes,c.ends,u,by rw [c.rank]; omega⟩⟩

/-- One steady round from its head: the warp publishes its K and V packets. The release
hypothesis covers the K and V uses of the round. -/
theorem steadyRoundPublishedOfHead (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : CacheUsesReleased l X g (cacheUseOfRound round+2))
    (head : SteadyRoundHead p l X g batch round) :
    Nonempty (SteadyRoundKeyPublished p l X g batch round) ∧
      Nonempty (SteadyRoundValuePublished p l X g batch round) := by
  have hKey : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)) :=
    hReleased _ (by unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega)
  have hValue : (cacheUseOfRound round+1)/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round+1)) :=
    hReleased _ (by unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega)
  obtain ⟨pages⟩ := head.refreshPagesOfMaximal hp hMax hFrame hg hw hb hLo hHi hRound
  obtain ⟨key⟩ := pages.keyPublishedOfMaximal hp hMax hFrame hg hw hb hLo hHi hRound hKey
  exact ⟨⟨key⟩,key.valuePublishedOfMaximal hp hMax hFrame hg hw hb hLo hHi hValue⟩

/-- From the head of steady round `first`, every later steady round up to `bound` has a head.
Only the K/V releases of the steady rounds before `bound` are used. -/
theorem steadyRoundHeadsOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch first bound : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReleased : CacheUsesReleased l X g (cacheUseOfRound bound))
    (start : SteadyRoundHead p l X g batch first) :
    ∀ k, first+k < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1 →
      first+k ≤ bound → Nonempty (SteadyRoundHead p l X g batch (first+k)) := by
  intro k
  induction k with
  | zero => exact fun _ _ => ⟨start⟩
  | succ k ih =>
    intro hk hBound
    obtain ⟨head⟩ := ih (by omega) (by omega)
    obtain ⟨_,⟨value⟩⟩ := steadyRoundPublishedOfHead hp hMax hFrame hg hw hb hLo hHi
      (by omega) (hReleased.mono (by unfold cacheUseOfRound; omega)) head
    rw [← Nat.add_assoc]
    exact (value.next hp hb hLo hHi (by omega)).1 (by omega)

/-- After the V publication of steady round `round`, each lane of the warp has made all
recurring publications up to and including that V use. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.Loader.SteadyRoundValuePublished.publicationCount
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch round : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (c : SteadyRoundValuePublished p l X g batch round) :
    ∀ lane < 32, cacheUseOfRound round ≤
      ((X.tr (warpLane l g lane)).take (c.reached.pos lane)).countP
        recurringPublicationMark := by
  intro lane hl
  obtain ⟨i,hi,he⟩ := c.published lane hl
  have hMark : recurringPublicationMark ⟨reuseArrival 3,
      .asyncArrive (readyObject l (warpLane l g lane) (kvUseStage (cacheUseOfRound round+1)))
        true⟩ = true := by
    apply (recurringPublicationMark_iff _).mpr
    exact ⟨3,_,rfl⟩
  have hRank := recurringPublicationShuffleRank hp hX hFrame hg hw hl hb hLo hHi he hMark
  have hShfl := countP_take_succ_false (p := Execution.isShfl) he rfl
  rw [hi,c.reached.ordinals.shfl lane hl,c.rank] at hShfl
  have hSucc := countP_take_succ he hMark
  rw [hi] at hSucc
  change _ = _ + 32 + 32*(2+((X.tr (warpLane l g lane)).take i).countP recurringPublicationMark)
    at hRank
  unfold cacheUseOfRound
  omega

set_option maxRecDepth 4096 in
/-- When steady rounds remain after the warm rounds, the loader warp passes the steady
counter gate, runs every steady round, and reaches the drain at pc 1744 with the final ring
cursor `2*trips`. Every lane has published all recurring ring uses below `2*trips`, and
no lane has published a ring use at or above it. -/
theorem steadyRoundsDrainEntry (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hLong : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : CacheUsesReleased l X g
      (2*Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1))
    (d : WarmTailDone p l X g batch) :
    let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
    CacheDrainEntry p l X g (2*n) ∧
      (∀ lane < 32, RecurringUsesBelow X (warpLane l g lane) (2*n)) ∧
      (∀ lane < 32, ∀ use < 2*n,
        use-1 ≤ (X.tr (warpLane l g lane)).countP recurringPublicationMark) := by
  intro n
  have hW : warmRounds p l g batch = 9 := by unfold warmRounds; omega
  obtain ⟨start⟩ := d.steadyHead hp hb hLo hHi (by omega)
  rw [hW] at start
  obtain ⟨last⟩ := steadyRoundHeadsOfMaximal hp hMax hFrame hg hw hb hLo hHi
    (bound := n-2) (hReleased.mono (by unfold cacheUseOfRound; omega)) start (n-11) (by omega)
    (by omega)
  have hLastRound : 9+(n-11) = n-2 := by omega
  rw [hLastRound] at last
  obtain ⟨_,⟨value⟩⟩ := steadyRoundPublishedOfHead hp hMax hFrame hg hw hb hLo hHi
    (by omega) (hReleased.mono (by unfold cacheUseOfRound; omega)) last
  obtain ⟨done⟩ := (value.next hp hb hLo hHi (by omega)).2 (by omega)
  have hUse : cacheUseOfRound (n-1) = 2*n := by unfold cacheUseOfRound; omega
  have hEntry : CacheDrainEntry p l X g (cacheUseOfRound (n-1)) := by
    apply cacheDrainEntryOfSteadyDone done.reached
    intro lane hl
    let t := warpLane l g lane
    have hSame : warpIndex l g = warpIndex l t :=
      (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.2
    have ht := done.reached.checkpoint lane hl
    have hRegs : Holds (done.reached.state lane).regs (steadyRoundCarry p l g batch lane) :=
      ((holds_append ..).mp ht.2.2.2.2).2
    have hF : Holds (done.reached.state lane).regs
        (warmRoundCarry p l g batch (warmRounds p l g batch) lane) :=
      ((holds_append ..).mp hRegs).2
    have hWarp : (done.reached.state lane).regs 1062 = some (b32 (warpIndex l t)) := by
      rw [← hSame]
      exact holds_mem hF (by simp [warmRoundCarry,openingWarmFrame,warmStartFrame])
    have hSched : Holds (done.reached.state lane).regs (drainSchedulerFrame p l t) :=
      steadyHoldsOfSubset hF (fun x hx => by simp [warmRoundCarry,hx,t])
    exact ⟨hWarp,hSched⟩
  refine ⟨hUse ▸ hEntry,fun lane hl => ?_,fun lane hl use hLt => ?_⟩
  · apply recurringUsesBelowOfDrainCursor hp hMax.1 hFrame hg hw hl hb hLo hHi done.reached
    rw [done.rank]
    omega
  · have h := publicationCountOfPrefix
      (value.publicationCount hp hMax.1 hFrame hg hw hb hLo hHi lane hl)
    unfold cacheUseOfRound at h
    omega

end PTX.Kernels.TmlFa4Fwd.Progress
