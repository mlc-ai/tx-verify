-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderPollColl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderPoll
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaPollAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreCross

@[expose] public section

/-! # The poll fields of `WarpSyncFacts` with the MMA and loader warps' parts plugged in

The rendezvous collectives are the MMA and loader warps' (`Cross.pollColl`), so `poll_order`
needs only the other positions' order (`PollRest`); the store warp's polls are exempt
(`Cross.PollRest_store`, `Assumptions.pollAgree`), so only the other warps' part remains
(`PollRestRest`: softmax WP5, correction WP6). Lane agreement at the polls holds for warps
12 and 14 (`Cross.PollAgree_mma`, `Cross.PollAgree_loader`); the other warps' part is
`PollAgreeRest` (softmax WP5, correction WP6, store WP1). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- `PollRest` for the warps other than the store warp. -/
def PollRestRest (L : Launch) (X : Execution) : Prop :=
  ∀ g h k k' pc m m' p p' ok ok' acq acq' sc sc', warpOf L g ≠ 13 → g < L.threads →
    h < L.threads → g ≠ h → SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → kernel.pollBranch (pc + 1) = true →
    rdvPos (pc + 1) = false →
    (m ≠ m' ∨ Assumptions.all.any (·.uniPoll (pc + 1)) = false) →
    pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') →
    PollBefore L kernel X (g, k) (h, k')

/-- `PollRest` from the other warps' part: the store warp's polls are exempt. -/
theorem pollRest_of_rest (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) (hrest : PollRestRest L X) : PollRest L X := by
  intro g h k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hb hu hd hlt
  by_cases h13 : warpOf L g = 13
  · exact absurd hd (Cross.PollRest_store hpre hX ht h13 hw he he')
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h13 hg hh hgh hw he he' hb hu hd hlt

/-- `PollAgree` for the warps other than 12 and 14 (softmax, correction, store; the idle warp
has no poll). -/
def PollAgreeRest (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k k' pc p p' : Nat} {m m' : Loc} {ok ok' acq acq' : Bool} {sc sc' : MbarScope}
    {d d' : ThreadD}, warpOf L g ≠ 12 → warpOf L g ≠ 14 → SameWarp L g h →
    St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ →
    pollRound pc ((X.tr g).take k) = pollRound pc ((X.tr h).take k') → m = m' ∧ p % 2 = p' % 2

/-- `PollAgree` from the MMA and loader warps' parts and the others'. -/
theorem pollAgree_of_rest (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) (hrest : PollAgreeRest L X) : PollAgree L X := by
  intro g h k k' pc p p' m m' ok ok' acq acq' sc sc' d d' hw hσ hσ' he he' hr
  by_cases h12 : warpOf L g = 12
  · exact Cross.PollAgree_mma hpre hX ht hw h12 hσ hσ' he he' hr
  by_cases h14 : warpOf L g = 14
  · exact Cross.PollAgree_loader hpre hX ht h14 hw hσ hσ' he he' hr
  exact hrest h12 h14 hw hσ hσ' he he' hr

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
