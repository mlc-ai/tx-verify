-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score

@[expose] public section

/-! # What the thread layer exports for the MMA warp's P-ready polls

An MMA thread at its P-ready poll `pWait k` of item `i` at trip `t` (`n` tiles per item) polls
stage `k % 2`'s P-ready object of its CTA (`pReadyBar`, offset `144 + 8 st`), with the parity of
its `n i + t` successful polls of it. The poll waits for that object's arrivals of use `n i + t`:

* the softmax threads of the stage, in both CTAs of the pair, arrive once per tile (`pArr`); the
  arrival of use `n i + t` is that of tile `t` of item `i`, in band S of slot `t`, before the MMA
  poll in slot `t + 1` (`Time.pReady_lt`);
* the correction threads of both CTAs arrive first at their initial O-free arrival (`free st`, at
  `freeT st`, below every slot), then once per trip (`oFree st false`, band C of slot `t + 1`) and
  once at the end of each item (`oFree st true`, band C of slot `n`); the arrival of use `n i + t`
  is the initial one for `i = t = 0`, the end of item `i - 1` for `t = 0 < i` (an earlier item),
  and trip `t - 1`'s in band C of slot `t` otherwise (`Time.oFree_lt`).

A producer state with at most `n i + t` arrivals is no later than its arrival of use `n i + t`,
so it is earlier than the MMA thread's state, and it has not exited (each role exits after all its
arrivals). The fields are facts of single threads' runs (the MMA warp's role, sites and poll
counts, the softmax and correction arrival counts, and the site tables), stated for a pair of
threads since the time compares a producer's state with the waiter's. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the MMA warp's P-ready polls. -/
structure PReadyPollFacts (L : Launch) (X : Execution) : Prop where
  /-- An MMA thread at a P-ready poll `pWait k` is of warp 12 of a pair-leader CTA, and its next
  event polls stage `k % 2`'s P-ready object of its CTA, with the parity of its successful polls
  of it. -/
  poll : ∀ {g : Nat} {d : Mma.D} {k : Fin 4}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .pWait k →
      warpOf L g = 12 ∧ leadCta (ctaOf L g) = ctaOf L g ∧
        PollsOn L X g (pReadyBar L (ctaOf L g) (k.val % 2)) 0
  /-- A softmax thread of stage `k % 2` of the waiter's pair that has made no more arrivals on the
  polled object than the waiter's successful polls of it lags the waiter. -/
  lag_soft : ∀ {g y : Nat} {d : Mma.D} {k : Fin 4}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .pWait k →
    leadCta (ctaOf L y) = ctaOf L g → warpOf L y < 8 → warpOf L y / 4 = k.val % 2 →
    arrivals (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr y) ≤
      okPolls (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr g) →
      Lags L X y g (.inr (.mma d))
  /-- A correction thread of the waiter's pair that has made no more arrivals on the polled
  object than the waiter's successful polls of it lags the waiter. -/
  lag_corr : ∀ {g y : Nat} {d : Mma.D} {k : Fin 4}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .pWait k →
    leadCta (ctaOf L y) = ctaOf L g → 8 ≤ warpOf L y → warpOf L y < 12 →
    arrivals (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr y) ≤
      okPolls (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr g) →
      Lags L X y g (.inr (.mma d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
