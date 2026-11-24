-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem

@[expose] public section

/-! # What the thread layer exports for the deallocation handshake poll

A lane of the MMA warp (warp 12) at its `waitDealloc` site polls its CTA's handshake barrier
(`FBar.loc _ _ .dealloc`, offset `+320`) at parity 0, and it has no successful poll of the
barrier yet. Each lane of the other CTA's MMA warp (`pairCta`) arrives on that barrier once, at
its `arrivePeer` site (`+3012` of the tail). A lane of the other CTA's MMA warp that has made no
arrival on the barrier is no later than its `arrivePeer` site, which is before the `waitDealloc`
(`+3020`) of the same tail: both CTAs of a cluster run the cluster's items (`Time.handshake_lt`).
An MMA lane exits only after its arrival, so such a lane has not exited.

The fields are facts of single threads' runs (the MMA sites, the handshake counts, and the site
tables). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the deallocation handshake poll. -/
structure HandshakePollFacts (L : Launch) (X : Execution) : Prop where
  /-- An MMA lane at its `waitDealloc` site polls its CTA's handshake barrier, with the parity of
  its successful polls of the barrier, of which it has made none. -/
  poll : ∀ {g : Nat} {d : Mma.D}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .waitDealloc →
      PollsOn L X g (FBar.loc L (ctaOf L g) .dealloc) 0 ∧
        okPolls (FBar.loc L (ctaOf L g) .dealloc) (X.tr g) = 0
  /-- A lane of the other CTA's MMA warp that has made no arrival on the handshake barrier of the
  CTA of an MMA lane at its `waitDealloc` site lags that lane. -/
  lag : ∀ {g y : Nat} {d : Mma.D}, g < L.threads → y < L.threads →
    ctaOf L y = pairCta (ctaOf L g) → warpOf L y = 12 →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .waitDealloc →
    arrivals (FBar.loc L (ctaOf L g) .dealloc) (X.tr y) = 0 →
      Lags L X y g (.inr (.mma d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
