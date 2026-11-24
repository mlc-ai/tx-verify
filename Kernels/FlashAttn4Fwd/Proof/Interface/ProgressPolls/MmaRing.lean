-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCounts
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # What the thread layer exports for the MMA warp's Q-full and KV-full polls

On the even CTA of a pair, all 32 lanes of the MMA warp (warp 12) poll the full barrier of the
Q stage or the KV slot that the item's next use reads (`Mma.pollBar`, sites `qWait` and
`kvWait`), with the parity of their successful polls of it. The barrier's phase is filled by the
loader warp (warp 14) of both CTAs of the pair: the leader CTA's elected loader lane arrives once
per use, and the elected loader lane of each CTA issues the use's copies. It is emptied by the
commits of the elected MMA lane to the partner empty barrier.

The fields are facts of single threads' runs:

* `poll`: the waiter is a thread of warp 12 of an even CTA, has made its first `bar.sync 2, 416`,
  and its next event polls the site's full barrier of its CTA with offset 0.
* `commits`: a lane `y` of the waiter's warp whose elections all returned its lane and that has
  made no more elections than the waiter has committed to the partner empty barrier at most as
  often as the waiter has polled the full barrier successfully. Each commit to the empty
  barrier of a use follows, in program order, the poll of that use and the commit's election,
  and every lane makes the same elections in the same order; so a lane with no more elections
  than the waiter has not reached the commit of the use the waiter polls.
* `arrive`: an elected loader lane of the waiter's CTA that has made no more arrivals on the
  barrier than the waiter's successful polls of it has not made the arrival of the waiter's
  use. It is at that use or earlier (band L of the use's load slot, before the waiter's band M
  in the use's slot), and has not exited.
* `copies`: an elected loader lane of either CTA of the pair that has issued fewer copies on
  the barrier than `copies` per use up to the waiter's use has not issued all copies of that
  use. The same times apply. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the MMA warp's Q-full and KV-full polls. -/
structure MmaRingPollFacts (L : Launch) (X : Execution) : Prop where
  /-- An MMA thread at a Q-full or KV-full poll site is a thread of warp 12 of an even CTA,
  has made a `bar.sync 2, 416`, and its next event polls the site's full barrier of its CTA
  with the parity of its successful polls of it. -/
  poll : ∀ {g : Nat} {d : Mma.D}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) →
    ((∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) →
    ctaOf L g % 2 = 0 ∧ warpOf L g = 12 ∧
      (∃ j pc, X.get (g, j) = some ⟨pc, .bar 2 (some 416) .sync⟩) ∧
      ∀ b, Mma.pollBar L d = some b → PollsOn L X g (b.loc L (ctaOf L g)) 0
  /-- A lane of the waiter's warp whose elections all returned its lane, with no more
  elections than the waiter, has committed to the partner empty barrier of the polled barrier
  of the waiter's CTA no more often than the waiter's successful polls of the polled
  barrier. -/
  commits : ∀ {g y : Nat} {d : Mma.D} {b : FBar}, g < L.threads → SameWarp L g y →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) →
    ((∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) → Mma.pollBar L d = some b →
    SelfElected L X y → (X.tr y).countP isElectEv ≤ (X.tr g).countP isElectEv →
    (X.tr y).countP (commitsTo (b.partner.loc L (ctaOf L g))) ≤
      okPolls (b.loc L (ctaOf L g)) (X.tr g)
  /-- An elected loader lane of the waiter's CTA with no more arrivals on the polled barrier
  than the waiter's successful polls of it lags the waiter. -/
  arrive : ∀ {g y : Nat} {d : Mma.D} {b : FBar}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) →
    ((∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) → Mma.pollBar L d = some b →
    ctaOf L y = ctaOf L g → warpOf L y = 14 → SelfElected L X y →
    arrivals (b.loc L (ctaOf L g)) (X.tr y) ≤ okPolls (b.loc L (ctaOf L g)) (X.tr g) →
    Lags L X y g (.inr (.mma d))
  /-- An elected loader lane of the waiter's pair with fewer copies on the polled barrier than
  the barrier's copies per use times one more than the waiter's successful polls of it lags
  the waiter. -/
  copies : ∀ {g y : Nat} {d : Mma.D} {b : FBar}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) →
    ((∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) → Mma.pollBar L d = some b →
    ctaOf L y / 2 = ctaOf L g / 2 → warpOf L y = 14 → SelfElected L X y →
    (X.tr y).countP (issuesTo (b.loc L (ctaOf L g))) <
      b.copies * (okPolls (b.loc L (ctaOf L g)) (X.tr g) + 1) →
    Lags L X y g (.inr (.mma d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
