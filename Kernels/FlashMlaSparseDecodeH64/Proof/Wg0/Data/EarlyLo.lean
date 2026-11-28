-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules

@[expose] public section

/-! # The low score words of a block are half words

`halfB_lo`: in a valid block (`W0Ok`) each low score word is a `halfB` word (an `f32` or a 32-bit
pattern), so the peer packs (`extE`, `upperE`, `mergeE`) neither fault nor lose the word. A block in
progress agrees with a valid block on the words it read (`W0Early`), so the same holds there. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

theorem halfB_lo {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {c : Nat} (hc : c < 32) :
    halfB (w.lo.getD c (.pred false)) = true :=
  (halfB_iff _).mpr (hw.lo c hc)

/-- A low word a block in progress read is the valid block's. -/
theorem halfB_lo_early {sc : ℝ} {w w' : W0Words} (hw : W0Ok sc w')
    (h : w.lo = [] ∨ w.lo = w'.lo) {c : Nat} (hc : c < 32) (hne : w.lo ≠ []) :
    halfB (w.lo.getD c (.pred false)) = true := by
  rcases h with h | h
  · exact absurd h hne
  · rw [h]; exact halfB_lo hw hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
