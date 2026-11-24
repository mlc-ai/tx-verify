-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output

@[expose] public section

/-! # What the thread layer exports for the staging-free polls

A correction thread at its `fWait st` site of item `i` polls its CTA's free barrier of stage `st`
(`freeBar`), with the parity of its successful polls of the barrier plus one, of which it has
made `i` (one per item); at the tail (`tailWait`) it polls stage 1's free barrier, after `T`
successful polls, with `T` the cluster's items. Each of the CTA's 32 store lanes makes one free
arrival on stage `st` per item (`free st`, slot `n`, band ST, offset `+18 + 4 st`). A store lane
with fewer free arrivals on the stage than the correction thread's successful polls has not made
its arrival of item `i - 1` (of item `T - 1` at the tail), so its state is no later than that
arrival's site, which is before the correction thread's poll of the next item
(`Time.stagingFree_lt`) or of the tail (`Time.stagingFree_tail_lt`). A store lane exits only after
all its arrivals, so such a lane has not exited.

The fields are facts of single threads' runs (the correction and store sites, their free counts,
and the site tables). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The staging-free poll sites of a correction thread with the stage they poll: `fWait st`, and
the tail's `tailWait` for stage 1. -/
def FreeSite (s : Correction.Site) (st : Fin 2) : Prop :=
  s = .fWait st ∨ (s = .tailWait ∧ st = 1)

/-- The thread layer's facts for the staging-free polls. -/
structure FreePollFacts (L : Launch) (X : Execution) : Prop where
  /-- A correction thread at a staging-free poll site of stage `st` polls stage `st`'s free
  barrier of its CTA (`freeBar`), with the parity of its successful polls of the barrier plus
  one. -/
  poll : ∀ {g : Nat} {d : Correction.D} {st : Fin 2}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.corr d))) → FreeSite d.site st →
      PollsOn L X g (freeBar L (ctaOf L g) st) 1
  /-- A store lane of the CTA of a correction thread at a staging-free poll site of stage `st`,
  with fewer free arrivals on stage `st` than the correction thread's successful polls of the
  stage's free barrier, lags the correction thread. -/
  lag : ∀ {g y : Nat} {d : Correction.D} {st : Fin 2}, g < L.threads → y < L.threads →
    ctaOf L y = ctaOf L g → warpOf L y = 13 →
    St L X g (X.tr g).length = some (some (.inr (.corr d))) → FreeSite d.site st →
    arrivals (freeBar L (ctaOf L g) st) (X.tr y) + 1 ≤ okPolls (freeBar L (ctaOf L g) st) (X.tr g) →
      Lags L X y g (.inr (.corr d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
