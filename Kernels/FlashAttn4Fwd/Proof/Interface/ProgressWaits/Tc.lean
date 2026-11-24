-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time

@[expose] public section

/-! # What the thread layer exports for the progress of the warp-collective `tcgen05` events

A lane returns from a warp-collective `tcgen05` instruction (a Tensor Memory load, store, their
waits, an allocation, relinquish or deallocation) only when every lane of its warp has executed
it (`TcBlocking`). The lanes of a warp run one role on one work schedule, so a lane's `k`-th such
event is at the same site, item and trip as every other lane's (`WarpSyncFacts.tc_seq`), and the
times of a role's states follow its program order (`Thread/Roles.lean`). The fields: a lane that
has made at most `k` of these events is no later than a lane of its warp at its `k`-th
(`lag`), and the state after such an event is later than the state before it, or the machine has
stopped (`after`: a correction chunk whose loaded words the products reject stops it at the
load's wait). Both are facts of the threads' run invariants. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

/-- The thread layer's facts for the progress of the warp-collective `tcgen05` events. -/
structure TcWaitFacts (L : Launch) (X : Execution) : Prop where
  /-- A lane of the warp of `g` that has made at most `k` warp-collective `tcgen05` events is no
  later (`endTime`) than `g`'s state before its `k`-th. -/
  lag : ∀ {g h j k : Nat} {d : ThreadD}, g < L.threads → h < L.threads → SameWarp L g h →
    X.TcK (g, j) k → St L X g j = some (some d) → (X.tr h).countP isTcColl ≤ k →
    endTime L X h ≤ stateTime L g d
  /-- After a warp-collective `tcgen05` event the thread is at a state later than the one
  before it, or its machine has stopped. -/
  after : ∀ {g j k : Nat} {d : ThreadD}, g < L.threads → X.TcK (g, j) k →
    St L X g j = some (some d) →
      (∃ d', St L X g (j + 1) = some (some d') ∧ stateTime L g d < stateTime L g d') ∨
        St L X g (j + 1) = none

end
end PTX.Kernels.FlashAttn4Fwd.Proof
