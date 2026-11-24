-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats

@[expose] public section

/-! # What the thread layer exports for the statistics credit polls

A softmax thread of stage `st` (warps `4 st` to `4 st + 3`) polls its CTA's credit barrier of the
stage (`statsBar`) at each `statsW` site, with the parity of its successful polls of the barrier
plus one. In item `i` of an item with `n` KV tiles it has `i (n + 1)` successful polls before
`statsW 0`, one more before `statsW 1`, and `i (n + 1) + t + 2` before `statsW 2` of trip `t`; at
the tail (`statsW 3`) it has `T (n + 1)`, with `T` the cluster's items.

Every correction thread of the CTA makes `n + 1` credit arrivals on each stage per item: on stage
0 `credit 0` (slot 0), `credit 2` of each trip `t` (slot `t + 1`) and `credit 4` (slot `n`); on
stage 1 `credit 1` of each trip (slot `t + 1`, band C 0), `credit 3` (slot `n`, band C 0) and
`credit 5` (slot `n`). A correction thread with fewer arrivals on the stage than the softmax
thread's successful polls has not made the arrival the poll waits for, so its state is no later
than that arrival's site, which is earlier than the poll: an arrival of an earlier global slot
(`Time.credit_prev_lt`) or, for stage 1, the stage-0 band of the same slot (`Time.credit_lt`);
the tail's poll follows every slot of the items (`Time.lt_tail`). A correction thread
exits only after all its arrivals, so such a thread has not exited.

The fields are facts of single threads' runs (the softmax and correction sites, their credit
counts, and the site tables). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the statistics credit polls. -/
structure CreditPollFacts (L : Launch) (X : Execution) : Prop where
  /-- A softmax thread at a credit poll (`statsW k`) polls its stage's credit barrier of its CTA
  (`statsBar`, stage `warpOf / 4`), with the parity of its successful polls of the barrier plus
  one. -/
  poll : ∀ {g : Nat} {d : Softmax.D}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.softmax d))) → (∃ k, d.site = .statsW k) →
      PollsOn L X g (statsBar L (ctaOf L g) (warpOf L g / 4)) 1
  /-- A correction thread of the CTA of a softmax thread at a credit poll, with fewer credit
  arrivals on the thread's stage than the thread's successful polls of that stage's credit
  barrier, lags the softmax thread. -/
  lag : ∀ {g y : Nat} {d : Softmax.D}, g < L.threads → y < L.threads →
    ctaOf L y = ctaOf L g → 8 ≤ warpOf L y → warpOf L y < 12 →
    St L X g (X.tr g).length = some (some (.inr (.softmax d))) → (∃ k, d.site = .statsW k) →
    arrivals (statsBar L (ctaOf L g) (warpOf L g / 4)) (X.tr y) + 1 ≤
      okPolls (statsBar L (ctaOf L g) (warpOf L g / 4)) (X.tr g) →
      Lags L X y g (.inr (.softmax d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
