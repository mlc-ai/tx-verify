-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexVal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads
public import Lemmas.Flow.Arith32WordW

@[expose] public section

/-! # The index pair loads' address words as numbers

-- domain: valid-rows

For a thread of the CTA (`ctaidX L g = q`, `ctaidY L g = e`, lane `tidOf L g % 32`) the code's
address words of the two index arrays (`Lib/IndexVal.lean`) are the numbers

* main: `indicesBase + 4 ((e s_q + q) topk) + 8 lane` (`ixAddr0_val`, `ixApB_val`),
* extra: `extraIndicesBase + 4 ((e s_q + q) extra_topk) + 8 lane` (`ixAddr1_val`),
  and the loop word's next-pair address `ixXad_val`;

no step wraps (`Pre.topkRange`, `Pre.indicesRange`, `Pre.extraTopkRange` and
`Pre.extraIndexBatchOffsetLt`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem ixA_pw {x : Nat} (h : x < 2 ^ 32) : pw x = W x := by
  simp only [pw, leNat_eq, pow_zero, Nat.div_one, W]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The lane word: `tid % 32`. -/
theorem ixA_lane (hp : Pre P L m) (g : Nat) : ixLane L g = W (tidOf L g % 32) := by
  have h := tidOf_lt hp g
  exact andi_W_31 h

theorem ixA_lane2 (hp : Pre P L m) (g : Nat) : ixLane2 L g = W (tidOf L g % 32 * 2) := by
  have h := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  rw [ixLane2, ixA_lane hp]
  exact shl1_W (by omega)

/-- The main index row (in words). -/
theorem ixRow0_val (hp : Pre P L m) (g : Nat) :
    ixRow0 P L g = W (ctaidX L g * P.topk + ctaidY L g * (P.s_q * P.topk)) := by
  obtain ⟨hq, he⟩ := ctaid_lt hp g
  have h1 := hp.topkRange
  have h2 := hp.mainIndexBatchOffsetLt he
  have hq' : ctaidX L g * P.topk < 2 ^ 31 := by
    have := Nat.mul_le_mul_right P.topk (Nat.le_of_lt hq)
    omega
  have hc : ixCtaX L g = W (ctaidX L g) := rfl
  have hr : r2W L g = W (ctaidY L g) := rfl
  have hk := hp.topkAdd63Lt
  have hX := hp.sqLt
  have hY := hp.bLt
  have hm : mul32 (pw P.topk) (ixCtaX L g) = W (P.topk * ctaidX L g) := by
    rw [ixA_pw (by omega), hc]
    exact mul32_W (by omega) (by omega) (by rw [Nat.mul_comm]; omega)
  have hm2 : mul32 (pw (P.s_q * P.topk)) (r2W L g) = W (P.s_q * P.topk * ctaidY L g) := by
    rw [ixA_pw (by omega), hr]
    exact mul32_W (by omega) (by omega) (by rw [Nat.mul_comm]; omega)
  simp only [ixRow0, hm, hm2]
  rw [sext_W (by rw [Nat.mul_comm]; omega), sext_W (by rw [Nat.mul_comm]; omega), add64_W]
  congr 1
  rw [Nat.mul_comm P.topk, Nat.mul_comm (P.s_q * P.topk)]

/-- The extra index row's address word (in bytes). -/
theorem ixRow1_val (hp : Pre P L m) (g : Nat) (hx : 0 < P.extra_topk) :
    ixRow1 P L g = W (P.extraIndicesBase +
      4 * (ctaidX L g * P.extra_topk + ctaidY L g * (P.s_q * P.extra_topk))) := by
  obtain ⟨hq, he⟩ := ctaid_lt hp g
  have h1 := hp.extraTopkRange
  have hb := hp.extraIndicesAddressable hx
  have hq' : ctaidX L g * P.extra_topk < 2 ^ 31 := by
    have := Nat.mul_le_mul_right P.extra_topk (Nat.le_of_lt hq)
    omega
  have hk := hp.extraTopkAdd63Lt
  have hX := hp.sqLt
  have hY := hp.bLt
  have hba : P.extraIndicesBase < 2 ^ 64 := by
    have : 0 < 4 * P.b * P.s_q * P.extra_topk := by
      have := hp.bPos; have := hp.sqPos
      positivity
    omega
  have hm : mul32 (pw P.extra_topk) (ixCtaX L g) = W (P.extra_topk * ctaidX L g) := by
    rw [ixA_pw (by omega)]
    exact mul32_W (by omega) (by omega) (by rw [Nat.mul_comm]; omega)
  have hm2 : mulWideR .s (pw (P.s_q * P.extra_topk)) (r2W L g) =
      W (P.s_q * P.extra_topk * ctaidY L g) := by
    rw [ixA_pw (by omega)]
    exact mulWideR_s_W (by omega) (by omega)
  simp only [ixRow1, hm, hm2]
  rw [sext_W (by rw [Nat.mul_comm]; omega), add64_W, shl64_2_W, pw8_eq _ hba, add64_W]
  congr 2
  rw [Nat.mul_comm P.extra_topk, Nat.mul_comm (P.s_q * P.extra_topk)]

private theorem pw8_idx (hp : Pre P L m) : pw8 P.indicesBase = W P.indicesBase := by
  have hb := hp.indicesAddressable
  have : 0 < 4 * P.b * P.s_q * P.topk := by
    have := hp.bPos; have := hp.sqPos; have := hp.topkPos
    positivity
  exact pw8_eq _ (by omega)

/-- **The first main pair's address**: `indicesBase + 4 row + 8 lane`. -/
theorem ixAddr0_val (hp : Pre P L m) (g : Nat) :
    ixAddr0 P L g = W (P.indicesBase + 4 * (ctaidX L g * P.topk +
      ctaidY L g * (P.s_q * P.topk)) + 8 * (tidOf L g % 32)) := by
  have hl := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  simp only [ixAddr0, ixRow0_val hp, pw8_idx hp, ixA_lane2 hp, shl64_2_W]
  rw [mulWide_u_W (by omega) (by norm_num) (by norm_num), add64_W, add64_W]
  congr 1
  simp only [Int.reduceToNat]
  omega

/-- The main loop word's base: the same address. -/
theorem ixApB_val (hp : Pre P L m) (g : Nat) : ixApB P L g = ixAddr0 P L g := by
  have hl := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  rw [ixAddr0_val hp]
  simp only [ixApB, ixRow0_val hp, pw8_idx hp, ixA_lane hp, shl64_2_W]
  rw [mulWide_u_W (by omega) (by norm_num) (by norm_num), add64_W, add64_W]
  congr 1
  simp only [Int.reduceToNat]
  omega

/-- **The first extra pair's address**. -/
theorem ixAddr1_val (hp : Pre P L m) (g : Nat) (hx : 0 < P.extra_topk) :
    ixAddr1 P L g = W (P.extraIndicesBase + 4 * (ctaidX L g * P.extra_topk +
      ctaidY L g * (P.s_q * P.extra_topk)) + 8 * (tidOf L g % 32)) := by
  have hl := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  simp only [ixAddr1, ixRow1_val hp g hx, ixA_lane2 hp]
  rw [mulWide_u_W (by omega) (by norm_num) (by norm_num), add64_W]
  congr 1
  simp only [Int.reduceToNat]
  omega

/-- **A later extra pair's address**: the word `x` (below `2 ^ 32`). -/
theorem ixXad_val (hp : Pre P L m) (g : Nat) (hx : 0 < P.extra_topk) {x : Nat}
    (hxl : x < 2 ^ 32) :
    ixXad P L g (W x) = W (P.extraIndicesBase + 4 * (ctaidX L g * P.extra_topk +
      ctaidY L g * (P.s_q * P.extra_topk)) + 4 * x) := by
  simp only [ixXad, ixRow1_val hp g hx]
  rw [mulWide_u_W (by omega) (by norm_num) (by norm_num), add64_W]
  congr 1
  simp only [Int.reduceToNat]
  omega

/-- **The extra loop word's first value**: the lane's pair word plus one block. -/
theorem ixXa0_val (hp : Pre P L m) (g : Nat) :
    ixXa0 L g = W (tidOf L g % 32 * 2 + 64) := by
  have hl := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  rw [ixXa0, ixA_lane2 hp, show i32 64 = W 64 by decide]
  exact or32_W_64 (by omega)

/-- **No main index address wraps**: the row's word `j` is inside the array. -/
theorem ixA_main_lt (hp : Pre P L m) (g : Nat) {j : Nat} (hj : j < P.topk) :
    P.indicesBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) * P.topk + j) < 2 ^ 64 := by
  obtain ⟨hq, he⟩ := ctaid_lt hp g
  have hb := hp.indicesAddressable
  have h1 : (ctaidY L g * P.s_q + ctaidX L g + 1) * P.topk ≤ P.b * P.s_q * P.topk := by
    apply Nat.mul_le_mul_right
    have : (ctaidY L g + 1) * P.s_q ≤ P.b * P.s_q := Nat.mul_le_mul_right _ he
    nlinarith
  have h2 : 4 * P.b * P.s_q * P.topk = 4 * (P.b * P.s_q * P.topk) := by ring
  have h3 : (ctaidY L g * P.s_q + ctaidX L g + 1) * P.topk =
      (ctaidY L g * P.s_q + ctaidX L g) * P.topk + P.topk := by ring
  omega

/-- The same for the extra array. -/
theorem ixA_extra_lt (hp : Pre P L m) (g : Nat) {j : Nat} (hx : 0 < P.extra_topk)
    (hj : j < P.extra_topk) :
    P.extraIndicesBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) * P.extra_topk + j) <
      2 ^ 64 := by
  obtain ⟨hq, he⟩ := ctaid_lt hp g
  have hb := hp.extraIndicesAddressable hx
  have h1 : (ctaidY L g * P.s_q + ctaidX L g + 1) * P.extra_topk ≤
      P.b * P.s_q * P.extra_topk := by
    apply Nat.mul_le_mul_right
    have : (ctaidY L g + 1) * P.s_q ≤ P.b * P.s_q := Nat.mul_le_mul_right _ he
    nlinarith
  have h2 : 4 * P.b * P.s_q * P.extra_topk = 4 * (P.b * P.s_q * P.extra_topk) := by ring
  have h3 : (ctaidY L g * P.s_q + ctaidX L g + 1) * P.extra_topk =
      (ctaidY L g * P.s_q + ctaidX L g) * P.extra_topk + P.extra_topk := by ring
  omega

/-- A word below `2 ^ 64` is its number as an address. -/
theorem ixA_addr {v : Nat} (h : v < 2 ^ 64) :
    (truncBits 64 (W v) + BitVec.ofInt 64 0).toNat = v := by
  simp only [truncBits, W, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
