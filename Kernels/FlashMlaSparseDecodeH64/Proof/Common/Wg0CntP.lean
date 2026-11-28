-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Cnt9

@[expose] public section

/-! # The warp-pair barrier's ordinals among the role's

With `R` blocks, a lane of warp parity `p` has the role's events on barrier `10 + p` below the role
ordinal `3 r` (`r ≤ R`) exactly `r` (`w0CntP_loop`), below the epilogue's ordinals `3 R + b` also
`R` (`w0CntP_epi`); the exchange sites after block `r`'s first barrier (the stores, ordinal
`3 r + 1`) count `r`, those after the pair barrier (the loads, the P stores) count `r + 1`
(`w0CntP_site`). Barrier 9 is `Common/Wg0Cnt9.lean`'s. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

theorem w0CntP_loop (R p : Nat) : ∀ r ≤ R, w0IdCnt R p (10 + p) (3 * r) = r := by
  intro r
  induction r with
  | zero => intro; simp [w0IdCnt]
  | succ r ih =>
    intro hr
    rw [show 3 * (r + 1) = 3 * r + 2 + 1 by omega, w0IdCnt_succ, w0IdCnt_succ, w0IdCnt_succ,
      ih (by omega)]
    simp only [Wg0.idAt]
    split_ifs <;> omega

theorem w0CntP_epi (R : Nat) {p : Nat} (hp : p < 2) :
    ∀ b ≤ 7, w0IdCnt R p (10 + p) (3 * R + b) = R := by
  intro b
  induction b with
  | zero => intro; simpa using w0CntP_loop R p R le_rfl
  | succ b ih =>
    intro hb
    rw [← Nat.add_assoc, w0IdCnt_succ, ih (by omega)]
    simp only [Wg0.idAt]
    split_ifs <;> omega

/-- **The sites of a block around its pair barrier**: the stores (before it) count `r`, the loads
and the P stores (after it) `r + 1`. -/
theorem w0CntP_site (R p : Nat) {r : Nat} (hr : r < R) :
    w0IdCnt R p (10 + p) (3 * r + 1) = r ∧ w0IdCnt R p (10 + p) (3 * r + 2) = r + 1 ∧
      w0IdCnt R p (10 + p) (3 * r + 3) = r + 1 := by
  have h0 := w0CntP_loop R p r hr.le
  have h1 : w0IdCnt R p (10 + p) (3 * r + 1) = r := by
    rw [w0IdCnt_succ, h0]
    simp only [Wg0.idAt]
    split_ifs <;> omega
  have h2 : w0IdCnt R p (10 + p) (3 * r + 2) = r + 1 := by
    rw [w0IdCnt_succ, h1]
    simp only [Wg0.idAt]
    split_ifs <;> omega
  refine ⟨h1, h2, ?_⟩
  rw [w0IdCnt_succ, h2]
  simp only [Wg0.idAt]
  split_ifs <;> omega

/-- Barrier 9's count at the block's first exchange sites (after its first barrier 9): `2 r + 1`. -/
theorem w0Cnt9_pst (R p : Nat) {r : Nat} (hr : r < R) : w0IdCnt R p 9 (3 * r + 1) = 2 * r + 1 := by
  have h0 := w0Cnt9_loop R p r hr.le
  rw [w0IdCnt_succ, h0]
  simp only [Wg0.idAt]
  split_ifs <;> omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
