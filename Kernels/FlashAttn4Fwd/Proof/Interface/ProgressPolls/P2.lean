-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score

@[expose] public section

/-! # What the thread layer exports for the MMA warp's second P-ready polls

An MMA thread at its second P-ready poll `p2Wait k lead` of item `i` at trip `t` (`n` tiles per
item) polls stage `k % 2`'s second P-ready object of its CTA (`pReady2Bar`, offset `160 + 8 st`),
with the parity of its `n i + t` successful polls of it. The poll waits for that object's
arrivals of use `n i + t`: in each tile, each softmax warp of the stage, in both CTAs of the pair,
elects a lane (`el`), and the elected lane arrives (`p2Arr`). A softmax thread every election of
which returned its own lane (`SelfElected`) arrives in every tile it has passed, so its arrival of
use `n i + t` is that of tile `t` of item `i`, in band S of slot `t` (`+42`), before the MMA poll
in slot `t + 1` (`mmaBlock (pvGrp k) + 8` in band M; `Time.pReady_lt`). Such a thread with at
most `n i + t` arrivals is no later than that arrival, so it is earlier than the MMA thread's
state, and it has not exited (it exits after the cluster's items).

The fields are facts of single threads' runs (the MMA warp's role, sites and poll counts, the
softmax elections and arrival counts, and the site tables), stated for a pair of threads since
the time compares a producer's state with the waiter's. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the MMA warp's second P-ready polls. -/
structure P2PollFacts (L : Launch) (X : Execution) : Prop where
  /-- An MMA thread at a second P-ready poll `p2Wait k lead` is of warp 12 of a pair-leader CTA,
  and its next event polls stage `k % 2`'s second P-ready object of its CTA, with the parity of
  its successful polls of it. -/
  poll : ∀ {g : Nat} {d : Mma.D} {k : Fin 4} {lead : Bool}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .p2Wait k lead →
      warpOf L g = 12 ∧ leadCta (ctaOf L g) = ctaOf L g ∧
        PollsOn L X g (pReady2Bar L (ctaOf L g) (k.val % 2)) 0
  /-- A softmax thread of stage `k % 2` of the waiter's pair, every election of which returned
  its own lane, that has made no more arrivals on the polled object than the waiter's successful
  polls of it lags the waiter. -/
  lag_soft : ∀ {g y : Nat} {d : Mma.D} {k : Fin 4} {lead : Bool}, g < L.threads →
    y < L.threads → St L X g (X.tr g).length = some (some (.inr (.mma d))) →
    d.site = .p2Wait k lead → leadCta (ctaOf L y) = ctaOf L g → warpOf L y < 8 →
    warpOf L y / 4 = k.val % 2 → SelfElected L X y →
    arrivals (pReady2Bar L (ctaOf L g) (k.val % 2)) (X.tr y) ≤
      okPolls (pReady2Bar L (ctaOf L g) (k.val % 2)) (X.tr g) →
      Lags L X y g (.inr (.mma d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
