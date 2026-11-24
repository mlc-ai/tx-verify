-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundValueGate
import Lemmas.Flow.CountTake
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The registers that a warm round passes unchanged to the next round, with the Bias
phases of round `round`. The round counter and the ring cursor are excluded. -/
def warmRoundCarry (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  let co := assignedCoordinates p batch (g/l.block)
  let n := Mma.trips p batch co.1
  let residual := vPrimingResidual p batch co.1
  let bias := loaderPhaseWord (warmBiasPhase (warpIndex l g) round)
  [(7178,bias),(1117,b32 (residual/2^31)),(1116,b32 (n-2)),
    (7,.pred (decide (10 < n) && warmResidueFlag residual)),
    (164,.pred (warmResidueFlag residual)),(7177,bias)] ++
    openingWarmFrame p l g batch lane ++ drainSchedulerFrame p l (warpLane l g lane)

/-- The frame at the warm tail after the V publication of round `round`: the V stage and
parity, the round counter and the trip bound, followed by the carry of the next round. -/
def warmRoundTailFrame (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  warmCachePublishedFrame round (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
    (warmRoundCarry p l g batch (round+1) lane)

/-- Both packets of warm round `round` are published and the lane is at the warm tail. -/
structure WarmRoundValuePublished (p : Params) (l : Launch) (X : Execution)
    (g batch round : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 1343 (warmRoundTailFrame p l g batch round)
    shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+128+64*round
  published : ∀ lane < 32, ∃ i, i+1 = reached.pos lane ∧
    X.get (warpLane l g lane,i) = some ⟨reuseArrival 1,
      .asyncArrive (readyObject l (warpLane l g lane) (kvUseStage (cacheUseOfRound round+1)))
        true⟩

/-- The number of warm rounds of the selected tile. -/
def warmRounds (p : Params) (l : Launch) (g batch : Nat) : Nat :=
  min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9

/-- The loader has left the warm loop at the actual warm tail with the ring cursor of the
first use after the warm rounds. -/
structure WarmRoundsDone (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 1353 (fun lane =>
    warmCacheHeadFrame l (warmRounds p l g batch)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
      (warmRoundCarry p l g batch (warmRounds p l g batch) lane)) shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+64+64*warmRounds p l g batch

private theorem warmRoundFrameOfHead {R : Nat → Option Value} {p : Params} {l : Launch}
    {g batch round lane trips : Nat}
    (h : Holds R (warmCacheHeadFrame l round trips (warmRoundCarry p l g batch round lane))) :
    Holds R (warmRoundFrame p l g batch round lane) := by
  obtain ⟨h7174,_,_,h7179,h7180,h7178,h1117,h1116,h7,h164,h7177,hRest⟩ := h
  exact ⟨h7174,h7178,h7179,h7180,h1117,h1116,h7,h164,h7177,hRest⟩

set_option maxRecDepth 4096 in
/-- The actual warm tail moves from the V publication of round `round` to the head of the
next warm round, or leaves the warm loop after the last warm round. -/
theorem WarmRoundValuePublished.next {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round < warmRounds p l g batch)
    (c : WarmRoundValuePublished p l X g batch round) :
    (round+1 < warmRounds p l g batch → Nonempty (WarmRoundHead p l X g batch (round+1))) ∧
      (round+1 = warmRounds p l g batch → Nonempty (WarmRoundsDone p l X g batch)) := by
  let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  have hTrips : n-1 < 2^31 := by omega
  have step := fun lane hl => warmCacheTailLocal (l := l) (g := warpLane l g lane)
    (F := warmRoundCarry p l g batch (round+1) lane) hTrips hRound
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by simp [warmRoundCarry,openingWarmFrame,warmStartFrame]) (c.reached.checkpoint lane hl)
  refine ⟨fun hMore => ?_,fun hLast => ?_⟩
  · obtain ⟨u⟩ := c.reached.advanceLocal (pc' := 917)
      (G := fun lane => warmRoundFrame p l g batch (round+1) lane) (by
        intro lane hl
        obtain ⟨t,ht,htAt⟩ := step lane hl
        rw [ite_eq_left (show round+1 < min (n-1) 9 from hMore)] at htAt
        exact ⟨t,ht,htAt.mono (warmRoundFrameOfHead htAt.2.2.2.2)⟩)
    exact ⟨⟨c.shuffles,c.votes,c.ends,u,by rw [c.rank]; omega⟩⟩
  · obtain ⟨u⟩ := c.reached.advanceLocal (pc' := 1353)
      (G := fun lane => warmCacheHeadFrame l (warmRounds p l g batch) (n-1)
        (warmRoundCarry p l g batch (warmRounds p l g batch) lane)) (by
        intro lane hl
        obtain ⟨t,ht,htAt⟩ := step lane hl
        rw [ite_eq_right (show ¬ round+1 < min (n-1) 9 by
          change round+1 = min (n-1) 9 at hLast; omega)] at htAt
        rw [← hLast]
        exact ⟨t,ht,htAt⟩)
    exact ⟨⟨c.shuffles,c.votes,c.ends,u,by rw [c.rank,← hLast]; omega⟩⟩

/-- After the V publication of warm round `round`, each lane of the warp has made all
recurring publications up to and including that V use. -/
theorem WarmRoundValuePublished.publicationCount {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (c : WarmRoundValuePublished p l X g batch round) :
    ∀ lane < 32, cacheUseOfRound round ≤
      ((X.tr (warpLane l g lane)).take (c.reached.pos lane)).countP
        recurringPublicationMark := by
  intro lane hl
  obtain ⟨i,hi,he⟩ := c.published lane hl
  have hMark : recurringPublicationMark ⟨reuseArrival 1,
      .asyncArrive (readyObject l (warpLane l g lane) (kvUseStage (cacheUseOfRound round+1)))
        true⟩ = true := by
    apply (recurringPublicationMark_iff _).mpr
    exact ⟨1,_,rfl⟩
  have hRank := recurringPublicationShuffleRank hp hX hFrame hg hw hl hb hLo hHi he hMark
  have hShfl := countP_take_succ_false (p := Execution.isShfl) he rfl
  rw [hi,c.reached.ordinals.shfl lane hl,c.rank] at hShfl
  have hSucc := countP_take_succ he hMark
  rw [hi] at hSucc
  change _ = _ + 32 + 32*(2+((X.tr (warpLane l g lane)).take i).countP recurringPublicationMark)
    at hRank
  unfold cacheUseOfRound
  omega

/-- From the head of a warm round, both loader warps refresh their page slots, pass the K
poll and publish the round's K packet. The release hypothesis is the MMA's return of the
earlier generations of the K slot; for round zero it is trivial. -/
theorem WarmRoundHead.keyPublishedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round < warmRounds p l g batch)
    (hReleased : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)))
    (c : WarmRoundHead p l X g batch round) :
    Nonempty (WarmRoundKeyPublished p l X g batch round) := by
  have hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
    unfold warmRounds at hRound
    omega
  obtain ⟨pages⟩ := c.refreshPagesOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips
  exact pages.keyPublishedOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips hReleased

/-- A count of recurring publications in a recorded prefix bounds the count in the lane's
whole trace. -/
theorem publicationCountOfPrefix {X : Execution} {t pos n : Nat}
    (h : n ≤ ((X.tr t).take pos).countP recurringPublicationMark) :
    n ≤ (X.tr t).countP recurringPublicationMark :=
  h.trans (List.take_sublist pos (X.tr t)).countP_le

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
