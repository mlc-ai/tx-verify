-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax

/-- The mask for the 32-column group, before the decoded per-column predicate tests. -/
def maskWord (group active : Nat) : Nat := (2 ^ 32 - 1) >>> (32 * (group + 1) - active)

theorem maskWord_testBit {group active col : Nat} (hc : col < 32) :
    (maskWord group active).testBit col = decide (32 * group + col < active) := by
  rw [maskWord, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  rw [decide_eq_decide]
  omega

/-- The signed difference at the mask setup counts keys remaining in the last visited block. -/
def firstActive (p : Params) (b row blocks : Nat) : Int :=
  (p.keyCount b row : Int) - 128 * (blocks - 1 : Nat)

theorem firstActive_select (p : Params) (b row blocks group col : Nat) (hc : col < 32) :
    (maskWord group (firstActive p b row blocks).toNat).testBit col =
      decide (visitKey blocks 0 (32 * group + col) < p.keyCount b row) := by
  rw [maskWord_testBit hc]
  unfold firstActive visitKey
  simp only [Nat.sub_zero]
  rw [decide_eq_decide]
  omega

/-- PTX first intersects the nonpadding K extent with the suffix-causal row bound, then
subtracts the keys in earlier blocks. This is the input to its four 32-column masks. -/
theorem firstActive_min (p : Params) (b row blocks : Nat) :
    firstActive p b row blocks =
      min ((p.kLength b - p.qLength b : Nat) + (row : Int) + 1 -
        128 * (blocks - 1 : Nat))
        ((p.kLength b : Int) - 128 * (blocks - 1 : Nat)) := by
  unfold firstActive Params.keyCount
  omega

end PTX.Kernels.TmlFa4Fwd.Softmax
