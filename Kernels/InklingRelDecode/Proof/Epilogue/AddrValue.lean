-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof Arith32

/-- The register of the output word `j` holds the row address plus the column offset. -/
theorem valueOf_word {e : Entry} {L : Launch} {g : Nat} {v : Value} {j : Nat} (hj : j < 64) :
    valueOf e L g v (2380+j) =
      u64 (e.rowAddr (g%L.block) + g%L.block/16%2*256 + 4*j) := by
  have h1 : 2380 + j ≠ 1827 := by omega
  have h2 : 2380 + j ≠ 1828 := by omega
  have h3 : 2380 + j ≠ 1829 := by omega
  have h4 : 2380 + j ≠ 1830 := by omega
  simp only [valueOf, h1, h2, h3, h4, ↓reduceIte]
  unfold scalarValue
  split <;> try (exfalso; omega)
  all_goals (rename_i hne; simp only [show 2380 ≤ 2380 + j ∧ 2380 + j ≤ 2443 by omega, and_self,
    ↓reduceIte, Nat.add_sub_cancel_left])

/-- The register of the LSE store holds the address of the thread's row. -/
theorem valueOf_lse {e : Entry} {L : Launch} {g : Nat} {v : Value} :
    valueOf e L g v 2379 = u64 (e.lseBase + sx (e.tile (g%L.block)) * 4) := rfl

/-- The lane that stores the LSE is in the low half of its row's pair. -/
theorem lead_bit {t : Nat} (h : lead t = true) : t / 16 % 2 = 0 := by
  unfold lead scmpi at h
  simp only [PTX.compare, andi, W, r32, truncBits, BitVec.toNat_ofNat] at h
  have h' := of_decide_eq_true h
  have e0 : (BitVec.ofInt 64 0).toNat = 0 := by decide
  have e16 : (BitVec.ofInt 64 16).toNat = 16 := by decide
  rw [e0, e16] at h'
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.zero_mod, Int.natCast_inj] at h'
  have a1 : t % 2^64 % 2^32 % 2^64 = t % 2^32 := by omega
  have a2 : 16 % 2^32 % 2^64 = 16 := by norm_num
  rw [a1, a2] at h'
  have le : (t % 2^32 &&& 16) ≤ 16 := Nat.and_le_right
  rw [Nat.mod_eq_of_lt (by omega : (t % 2^32 &&& 16) < 2^32),
    Nat.mod_eq_of_lt (by omega : (t % 2^32 &&& 16) < 2^64)] at h'
  have h2 := Nat.testBit_and (t % 2^32) 16 4
  rw [h'] at h2
  have h3 : Nat.testBit (t % 2^32) 4 = false := by
    have : Nat.testBit 16 4 = true := by decide
    rw [this] at h2
    simpa using h2.symm
  rw [Nat.testBit_eq_decide_div_mod_eq] at h3
  simp only [decide_eq_false_iff_not] at h3
  have : t % 2^32 / 2^4 % 2 = t / 16 % 2 := by omega
  omega
end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
