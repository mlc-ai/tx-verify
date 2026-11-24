-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output

@[expose] public section

/-! # What the thread layer exports for the staged polls

A store lane (warp 13) at its `wait st` site of item `i` polls its CTA's staged barrier of stage
`st` (`stagedBar`), with the parity of its successful polls of the barrier, of which it has made
`i` (one per item). Every correction thread of the CTA makes one staged arrival on stage `st` per
item (`staged st`, band C `st` of slot `n`, offset `+176`). A correction thread with no more
staged arrivals on the stage than the store lane's successful polls has not made its arrival of
item `i`, so its state is no later than that arrival's site, which is before the store lane's
poll in the same slot (`Time.staged_lt`). A correction thread exits only after all its arrivals,
so such a thread has not exited.

The fields are facts of single threads' runs (the store and correction sites, their staged
counts, and the site tables). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the staged polls. -/
structure StagedPollFacts (L : Launch) (X : Execution) : Prop where
  /-- A store lane at its `wait st` site polls stage `st`'s staged barrier of its CTA
  (`stagedBar`), with the parity of its successful polls of the barrier. -/
  poll : ∀ {g : Nat} {d : Store.D} {st : Fin 2}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.store d))) → d.site = .wait st →
      PollsOn L X g (stagedBar L (ctaOf L g) st) 0
  /-- A correction thread of the CTA of a store lane at its `wait st` site, with no more staged
  arrivals on stage `st` than the lane's successful polls of the stage's staged barrier, lags the
  store lane. -/
  lag : ∀ {g y : Nat} {d : Store.D} {st : Fin 2}, g < L.threads → y < L.threads →
    ctaOf L y = ctaOf L g → 8 ≤ warpOf L y → warpOf L y < 12 →
    St L X g (X.tr g).length = some (some (.inr (.store d))) → d.site = .wait st →
    arrivals (stagedBar L (ctaOf L g) st) (X.tr y) ≤ okPolls (stagedBar L (ctaOf L g) st) (X.tr g) →
      Lags L X y g (.inr (.store d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
