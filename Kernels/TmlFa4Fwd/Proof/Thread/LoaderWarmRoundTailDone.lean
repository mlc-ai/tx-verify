-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTail

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The frame at the steady counter gate after the warm tail: the steady counter starts at
the number of warm rounds, and the ring cursor is the first use after the warm rounds. -/
def warmTailFrame (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  [(7181,b32 (warmRounds p l g batch)),
    (1091,b32 (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1))] ++
    drainCarry l (cacheUseOfRound (warmRounds p l g batch)) ++
    warmRoundCarry p l g batch (warmRounds p l g batch) lane

/-- The warp has left the warm tail and reached the steady counter gate at pc 1384. The
shuffle rank is that of the warm exit; the tail adds no shuffle. -/
structure WarmTailDone (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 1384 (warmTailFrame p l g batch) shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+64+64*warmRounds p l g batch

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
