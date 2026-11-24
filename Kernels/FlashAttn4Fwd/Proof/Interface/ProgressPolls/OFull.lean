-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc

@[expose] public section

/-! # What the thread layer exports for the correction O-full waits

A correction thread (warps 8-11) at its O-full wait of stage `st` (`oWait st`, timed at `+8` of
band C `st` in slot `n` of its item) polls stage `st`'s O-full object of its CTA, with the parity
of its successful polls of it. The object is completed by the commits of the committing lane of
warp 12 of the pair leader, one per item and stage (at band M of the item's slot `n`). A lane of
that warp every election of which returned its own lane, with no more commits naming stage
`st`'s O-full object of its own CTA than the waiter's successful polls, has not made the commit
of the waiter's item: it has not exited, and its state is no later than that commit, so earlier
than the waiter (`Progress.Time.oFull_lt`: band M of slot `n` is before band C).

The fields are facts of single threads' runs (the correction and MMA roles' sites and counts and
the site tables), stated for a pair of threads since the time compares a lane's state with the
waiter's. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the correction O-full waits. -/
structure OFullPollFacts (L : Launch) (X : Execution) : Prop where
  /-- A correction thread at its O-full wait of stage `st` polls next stage `st`'s O-full object
  of its CTA, with the parity of its successful polls of it. -/
  poll : ∀ {g : Nat} {d : Correction.D} {st : Fin 2}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.corr d))) → d.site = .oWait st →
      PollsOn L X g (oFullBar L (ctaOf L g) st) 0
  /-- A lane of warp 12 of the pair leader of a correction thread at its O-full wait of stage
  `st`, every election of which returned its own lane, that has made no more commits naming
  stage `st`'s O-full object of its own CTA than the thread's successful polls of stage `st`'s
  O-full object lags the thread. -/
  lag : ∀ {g y : Nat} {d : Correction.D} {st : Fin 2}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.corr d))) → d.site = .oWait st →
    y < L.threads → warpOf L y = 12 → ctaOf L y = leadCta (ctaOf L g) → SelfElected L X y →
    (X.tr y).countP (commitsTo (oFullBar L (ctaOf L y) st)) ≤
      okPolls (oFullBar L (ctaOf L g) st) (X.tr g) →
      Lags L X y g (.inr (.corr d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
