-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score

@[expose] public section

/-! # What the thread layer exports for the softmax S-full waits

A softmax thread of stage `st` (warps `4 st` to `4 st + 3`) at its S-full wait (`sW`, timed at
`+2` of band S `st` in the slot of its tile) polls its stage's S-full object of its CTA, with the
parity of its successful polls of it. The object is completed by the commits of the committing
lane of warp 12 of the pair leader, one per tile of the stage (at band M of the tile's slot).
A lane of that warp every election of which returned its own lane, with no more commits naming
the stage's S-full object of its own CTA than the waiter's successful polls, has not made the
commit of the waiter's tile: it has not exited, and its state is no later than that commit, so
earlier than the waiter (`Progress.Time.sFull_lt`: band M of a slot is before band S).

The fields are facts of single threads' runs (the softmax and MMA roles' sites and counts and
the site tables), stated for a pair of threads since the time compares a lane's state with the
waiter's. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the softmax S-full waits. -/
structure SFullPollFacts (L : Launch) (X : Execution) : Prop where
  /-- A softmax thread at its S-full wait polls next its stage's S-full object of its CTA, with
  the parity of its successful polls of it. -/
  poll : ∀ {g : Nat} {d : Softmax.D} {lp : Bool}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.softmax d))) → d.site = .sW lp →
      PollsOn L X g (sFullBar L (ctaOf L g) (warpOf L g / 4)) 0
  /-- A lane of warp 12 of the pair leader of a softmax thread at its S-full wait, every
  election of which returned its own lane, that has made no more commits naming the stage's
  S-full object of its own CTA than the thread's successful polls of its stage's S-full object
  lags the thread. -/
  lag : ∀ {g y : Nat} {d : Softmax.D} {lp : Bool}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.softmax d))) → d.site = .sW lp →
    y < L.threads → warpOf L y = 12 → ctaOf L y = leadCta (ctaOf L g) → SelfElected L X y →
    (X.tr y).countP (commitsTo (sFullBar L (ctaOf L y) (warpOf L g / 4))) ≤
      okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) (X.tr g) →
      Lags L X y g (.inr (.softmax d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
