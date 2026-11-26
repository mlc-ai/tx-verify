-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SldArm

@[expose] public section

/-! # The stage of a lane's score loads

At every state of a lane of warps 0–3 in warpgroup 0's machine, a score-load site's `arm` is the
comparison of the lane's warp word with `1` (`w0_sldArm`, by induction along the trace with
`Wg0.sld_succ`): the lanes of a warp are at one of the two pc orders. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {X : Execution}

/-- **The score loads' arm at a state of warpgroup 0.** -/
theorem w0_sldArm (hFw : Follow P L X) (hnu : ¬ HasUb X) {y : Nat} (hw : warp L y < 4)
    (hy : y < L.threads) :
    ∀ {t : Nat}, t ≤ (X.tr y).length → ∀ {d : Wg0.Control.D} {n : Cls → Nat},
      Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)) →
      Wg0.SldOk (warpW L y) d := by
  intro t
  induction t with
  | zero =>
    intro _ d n hσ
    rcases wg0_pred hFw hnu hw hy (Nat.zero_le _) hσ with ⟨t', ht', -⟩ | hs
    · omega
    · intro a k hk
      rw [hs] at hk
      cases hk
  | succ t ih =>
    intro ht d n hσ
    rcases wg0_pred hFw hnu hw hy ht hσ with ⟨t', ht', d', n', e, -, hs', hS⟩ | hs
    · obtain rfl : t' = t := by omega
      exact Wg0.sld_succ hS (ih (by omega) hs')
    · intro a k hk
      rw [hs] at hk
      cases hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
