-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt

@[expose] public section

/-! # Barrier 9's ordinals among the role's

With `R` blocks, the role's events on barrier 9 below the role ordinal `3 r` are `2 r` (`r ≤ R`),
below `3 R + b` they are `2 R + min b 6`; the exchange sites sit between barrier 9's events
(`w0Cnt9_site`: the sites after block `r`'s first barrier and its pair barrier, and before and
after its last barrier, count `2 r + 1` and `2 r + 2`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

theorem w0Cnt9_loop (R p : Nat) : ∀ r ≤ R, w0IdCnt R p 9 (3 * r) = 2 * r := by
  intro r
  induction r with
  | zero => intro; simp [w0IdCnt]
  | succ r ih =>
    intro hr
    rw [show 3 * (r + 1) = 3 * r + 2 + 1 by omega, w0IdCnt_succ, w0IdCnt_succ, w0IdCnt_succ,
      ih (by omega)]
    simp only [Wg0.idAt]
    split_ifs <;> omega

theorem w0Cnt9_epi (R p : Nat) : ∀ b ≤ 7, w0IdCnt R p 9 (3 * R + b) = 2 * R + min b 6 := by
  intro b
  induction b with
  | zero => intro; simpa using w0Cnt9_loop R p R le_rfl
  | succ b ih =>
    intro hb
    rw [← Nat.add_assoc, w0IdCnt_succ, ih (by omega)]
    simp only [Wg0.idAt]
    split_ifs <;> omega

/-- **The sites of a block between its barriers**: the exchange store (after the block's first
barrier and the pair barrier, before barrier 9) is at count `2 r + 1`, the load after it at
`2 r + 2`. -/
theorem w0Cnt9_site (R p : Nat) {r : Nat} (hr : r < R) :
    w0IdCnt R p 9 (3 * r + 2) = 2 * r + 1 ∧ w0IdCnt R p 9 (3 * r + 3) = 2 * r + 2 := by
  have h0 := w0Cnt9_loop R p r hr.le
  have h2 : w0IdCnt R p 9 (3 * r + 2) = 2 * r + 1 := by
    rw [show 3 * r + 2 = 3 * r + 1 + 1 by omega, w0IdCnt_succ, w0IdCnt_succ, h0]
    simp only [Wg0.idAt]
    split_ifs <;> omega
  refine ⟨h2, ?_⟩
  rw [w0IdCnt_succ, h2]
  simp only [Wg0.idAt]
  split_ifs <;> omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
