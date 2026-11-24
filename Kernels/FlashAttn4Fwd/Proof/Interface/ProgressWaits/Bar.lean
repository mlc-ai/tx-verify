-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats

@[expose] public section

/-! # What the thread layer exports for the named-barrier waits

A thread whose last event is an arrival on a named barrier that has not returned waits for the
lanes of its warp (a `bar.arrive` returns once its warp's arrival is recorded) and, at a
`bar.sync`, for the participant lanes of its CTA (`BarGroup`: warps 0-12 for barrier 2; the
softmax warp `k + 4 st` and the correction warp `8 + k` for the statistics barrier
`statsId st k`). A lane that has not made its arrival of the thread's ordinal is earlier in the
sequential schedule of `Thread/Roles.lean` than the thread after its arrival:

* barrier 2, ordinal 0 (the `bar0` sites at `bar0T`): a lane before it is at most at `bar0T`,
  the states after it are later (the MMA warp's `ldBase`, the softmax's first statistics poll,
  the correction's first O-free arrival);
* barrier 2, ordinal 1: the MMA warp's `bar.sync` (`bar1`, `mmaTail 10`) follows the softmax and
  correction `bar.arrive` (`barEnd`, tail `+2000`), and a lane of the arriving warp is no later
  than `barEnd` while its thread is at its exit (`+2002`);
* a statistics barrier, ordinal `G`: the softmax's arrival `gen` of ordinal `G` (band S of its
  slot, `+22`) is before the correction's `bar.sync` of ordinal `G` (band C of the same slot);
  every lane of the arriving warp is before the thread's state after its arrival.

A lane that has not made that arrival has not exited: each role exits after all its arrivals
(two on barrier 2; as many on its statistics barrier as its partner warp).

The fields are facts of single threads' runs (the sites and counts of the softmax, correction and
MMA roles, and the site tables), stated for a pair of threads since the time compares a lane's
state with another's. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

/-- The participant warps of named barrier `id`: warps 0-12 for barrier 2, and for statistics
barrier `statsId st k` the softmax warp `k + 4 st` and the correction warp `8 + k`. -/
def BarGroup (id w : Nat) : Prop :=
  (id = 2 ∧ w < 13) ∨
    ∃ st k, st < 2 ∧ k < 4 ∧ id = statsId st k ∧ (w = k + 4 * st ∨ w = 8 + k)

/-- The thread layer's facts for the named-barrier waits. -/
structure BarWaitFacts (L : Launch) (X : Execution) : Prop where
  /-- After a named-barrier event the thread is at a state later than the one before it, or its
  machine has stopped: its run reaches undefined behaviour by local steps (`Frame.end_dead`; the
  softmax after `gen` when the exponent run rejects its inputs). -/
  after : ∀ {g j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : ThreadD}, g < L.threads →
    X.get (g, j) = some ⟨pc, .bar id cnt m⟩ → St L X g j = some (some d) →
      (∃ d', St L X g (j + 1) = some (some d') ∧ stateTime L g d < stateTime L g d') ∨
        St L X g (j + 1) = none
  /-- A lane of a thread's warp that has made no more events on a named barrier than the
  thread before its event there has not exited, and it is no later (`endTime`) than the
  thread's state before the event. -/
  lag_warp : ∀ {g y j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : ThreadD},
    g < L.threads → y < L.threads → SameWarp L g y →
    X.get (g, j) = some ⟨pc, .bar id cnt m⟩ → St L X g j = some (some d) →
    (X.tr y).countP (Execution.isBarId id) ≤ barOrd X g j id →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ endTime L X y ≤ stateTime L g d
  /-- A participant lane of a thread's CTA that has made no more events on a named barrier than
  the thread before its `bar.sync` there has not exited, and it is no later (`endTime`) than
  the thread's state before the `bar.sync`. -/
  lag_sync : ∀ {g y j pc id : Nat} {cnt : Option Nat} {d : ThreadD},
    g < L.threads → y < L.threads → y / L.block = g / L.block → BarGroup id (warpOf L y) →
    X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩ → St L X g j = some (some d) →
    (X.tr y).countP (Execution.isBarId id) ≤ barOrd X g j id →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ endTime L X y ≤ stateTime L g d

end
end PTX.Kernels.FlashAttn4Fwd.Proof
