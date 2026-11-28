-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

abbrev row (T : Nat) : Nat := T % 16 + T / 32 % 4 * 16
abbrev tokOf (T : Nat) : Nat := row T * 43 / 256
abbrev remOf (T : Nat) : Nat := row T - tokOf T * 6
def rowM (tid : Nat) : Nat := 16 * (tid / 32 % 4) + tid % 16
def tokM (tid : Nat) : Nat := rowM tid / 6

theorem rowM_eq (T : Nat) : row T = rowM T := by
  unfold row rowM
  omega

theorem rowM_lt (T : Nat) : rowM T < 64 := by
  unfold rowM
  omega

theorem tokOf_eq (T : Nat) : tokOf T = tokM T := by
  have key : ∀ x : Nat, x < 64 → x * 43 / 256 = x / 6 := by decide
  unfold tokOf tokM
  rw [rowM_eq]
  exact key _ (rowM_lt T)

theorem remOf_eq (T : Nat) : remOf T = rowM T % 6 := by
  unfold remOf
  rw [tokOf_eq, rowM_eq]
  unfold tokM
  omega

variable {Q : Params}

theorem oLoc_range (s t h d : Nat) (hs : s < Q.splits) (ht : t < Q.nTok) (hh : h < heads)
    (hd : d < headDim) :
    Q.oBase ≤ (oLoc Q s t h d).addr ∧ (oLoc Q s t h d).addr + 4 ≤ Q.oBase + oBytes Q := by
  have h1 : s * Q.nTok + t + 1 ≤ Q.splits * Q.nTok := by
    have := Nat.mul_le_mul_right Q.nTok (show s + 1 ≤ Q.splits by omega)
    rw [Nat.succ_mul] at this
    omega
  have hh' : h < 12 := hh
  have hd' : d < 128 := hd
  have h2 : (s * Q.nTok + t) * 12 + h + 1 ≤ Q.splits * Q.nTok * 12 := by nlinarith
  have h3 : ((s * Q.nTok + t) * 12 + h) * 128 + d + 1 ≤ Q.splits * Q.nTok * 12 * 128 := by
    nlinarith
  simp only [oLoc, oBytes, heads, headDim]
  constructor
  · omega
  · have : 4 * Q.splits * Q.nTok * 12 * 128 = 4 * (Q.splits * Q.nTok * 12 * 128) := by ring
    omega

/-- The `LsePart` element is inside the array. -/
theorem lseLoc_range (s t h : Nat) (hs : s < Q.splits) (ht : t < Q.nTok) (hh : h < heads) :
    Q.lseBase ≤ (lseLoc Q s t h).addr ∧
      (lseLoc Q s t h).addr + 4 ≤ Q.lseBase + lseBytes Q := by
  have h1 : s * Q.nTok + t + 1 ≤ Q.splits * Q.nTok := by
    have := Nat.mul_le_mul_right Q.nTok (show s + 1 ≤ Q.splits by omega)
    rw [Nat.succ_mul] at this
    omega
  have hh' : h < 12 := hh
  have h2 : (s * Q.nTok + t) * 12 + h + 1 ≤ Q.splits * Q.nTok * 12 := by nlinarith
  simp only [lseLoc, lseBytes, heads]
  constructor
  · omega
  · have : 4 * Q.splits * Q.nTok * 12 = 4 * (Q.splits * Q.nTok * 12) := by ring
    omega
theorem blk_lt {Q : Params} {r s i : Nat} (hs : 0 < Q.splits)
    (h : i < Q.numIters r s) : s + i * Q.splits < Q.blocks r := by
  unfold Params.numIters at h
  have h1 := (Nat.le_div_iff_mul_le hs).mp (show i + 1 ≤ _ from h)
  have h2 : (i + 1) * Q.splits = i * Q.splits + Q.splits := by ring
  omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
