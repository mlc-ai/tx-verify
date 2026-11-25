-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Inv
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Arith
public import Lemmas.Cluster.Unit

@[expose] public section

/-! # Store phase: words, bounds and launch facts

The closed forms of the store phase are numbers; the machine computes on 64-bit words. This
file has what the step lemmas need to go from one to the other (`W n` is the word of `n`):

* words of the operations the phase uses that `Lemmas/Flow/Arith32Word.lean` does not cover: a
  left shift by a literal (`shl_W`), the signed maximum (`max32_W`), the low half of a 64-bit
  word (`low32_W`), the exclusive or of two bits (`xor_bit`), adding `-16` (`addi_neg16`), and
  the 64-bit operations of the output address (`r64_W`, `zext_W`, `sext_W`, `add64_W`,
  `mul64_W`, `shl64_8`, `mulWide_256`, `addi64_W`);
* launch facts: the stride word of the tensor-map object 10 is 1 (`scaleOut`), the output
  pointer (`outWord`), the block of a thread is its own cluster, so that `mapa` with rank 0
  returns the address it is given (`mapaPeer_own`);
* bounds from the precondition: the tokens of a sequence are tokens of the batch (`tok_le`),
  the output row of a token ends inside the output array (`out_le`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-! ### Words -/

/-- A left shift by a literal below 32 that does not overflow. -/
theorem shl_W {a : Nat} {n : Int} (h0 : 0 ≤ n) (hn : n < 32) (h : a * 2 ^ n.toNat < 2 ^ 32) :
    shl (W a) n = W (a * 2 ^ n.toNat) := by
  have hi : (i32 n).toNat = n.toNat := i32_toNat_int h0 (by omega)
  have hp : 0 < 2 ^ n.toNat := Nat.pos_of_ne_zero (by positivity)
  have ha : a < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_right a hp) h
  simp only [shl, hi, show ¬ n.toNat ≥ 32 by omega, ↓reduceIte, r32_W ha]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a * 2 ^ n.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (show a * 2 ^ n.toNat < 2 ^ 64 by omega)]

theorem shl3_W {a : Nat} (h : a * 8 < 2 ^ 32) : shl (W a) 3 = W (8 * a) := by
  rw [shl_W (by decide) (by decide) (by simpa using h)]
  apply congrArg W
  simp only [Int.reduceToNat, Nat.reducePow]
  omega

theorem shl4_W {a : Nat} (h : a * 16 < 2 ^ 32) : shl (W a) 4 = W (16 * a) := by
  rw [shl_W (by decide) (by decide) (by simpa using h)]
  apply congrArg W
  simp only [Int.reduceToNat, Nat.reducePow]
  omega

theorem shl12_W {a : Nat} (h : a * 4096 < 2 ^ 32) : shl (W a) 12 = W (4096 * a) := by
  rw [shl_W (by decide) (by decide) (by simpa using h)]
  apply congrArg W
  simp only [Int.reduceToNat, Nat.reducePow]
  omega

/-- The signed maximum of two small words. -/
theorem max32_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    max32 (W a) (W b) = W (max a b) := by
  have hl : PTX.compare .gt .s 32 (W a) (W b) = decide (b < a) := by
    have := scmp_gt_W ha hb
    simpa [scmp, r32_W (show a < 2 ^ 32 by omega), r32_W (show b < 2 ^ 32 by omega)] using this
  simp only [max32, r32_W (show a < 2 ^ 32 by omega), r32_W (show b < 2 ^ 32 by omega), hl]
  by_cases h : b < a
  · simp only [h, decide_true, ↓reduceIte, Nat.max_eq_left (Nat.le_of_lt h)]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte,
      Nat.max_eq_right (Nat.le_of_not_lt h)]

/-- The low 32 bits of a small 64-bit word. -/
theorem low32_W {a : Nat} (h : a < 2 ^ 32) : low32 (W a) = W a := by
  apply BitVec.eq_of_toNat_eq
  simp only [low32, truncBits, W, BitVec.toNat_ofNat]; omega

theorem r64_W (a : Nat) : r64 (W a) = W a := by
  apply BitVec.eq_of_toNat_eq
  simp only [r64, truncBits, W, BitVec.toNat_ofNat]; omega

theorem zext_W {a : Nat} (h : a < 2 ^ 32) : zext (W a) = W a := by
  apply BitVec.eq_of_toNat_eq
  simp only [zext, r32, truncBits, W, BitVec.toNat_ofNat]; omega

theorem add64_W {a b : Nat} (_h : a + b < 2 ^ 64) : add64 (W a) (W b) = W (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [add64, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add]; omega

theorem addi64_W {a : Nat} {n : Int} (h0 : 0 ≤ n) (_h : a + n.toNat < 2 ^ 64) :
    addi64 (W a) n = W (a + n.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi64, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]; omega

theorem mul64_W {a b : Nat} (h : a * b < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    mul64 (W a) (W b) = W (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [mul64, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_mul,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

/-- `shl.b64` by 8 without overflow. -/
theorem shl64_8 {a : Nat} (_h : a * 256 < 2 ^ 64) : shl64 (W a) 8 = W (256 * a) := by
  have hi : (i32 (8 : Int)).toNat = 8 := by decide
  simp only [shl64]
  rw [hi]
  split_ifs with h8
  · exact absurd h8 (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, r64, W, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  rw [Nat.shiftLeft_eq]
  omega

/-- The sign extension of a nonnegative 32-bit word. -/
theorem sext_W {a : Nat} (h : a < 2 ^ 31) : sext (W a) = W a := by
  apply BitVec.eq_of_toNat_eq
  have hs : toSigned 32 (W a) = a := toSigned_W h
  simp only [sext, cvtIntBits, intBits, intSat, intOf, r32_W (show a < 2 ^ 32 by omega), hs,
    Bool.not_false, ↓reduceIte, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

/-- `mul.wide.u32` by 256. -/
theorem mulWide_256 {a : Nat} (h : a < 2 ^ 32) : mulWide .u (W a) 256 = W (256 * a) := by
  have hi : (i32 (256 : Int)).toNat = 256 := by
    rw [i32_toNat_int (by omega) (by omega)]
    rfl
  have hk : ((some IType.u == some IType.s) = true) = False := by simp
  unfold mulWide
  simp only [hk, ↓reduceIte]
  rw [r32_W h, hi, toNat_W (show a < 2 ^ 64 by omega), Nat.mul_comm]

theorem imm_neg16 : i32 (-16 : Int) = W 4294967280 := by decide

/-- Adding `-16` to a word of at least 16. (The proof is cut into small steps on purpose: as
one `omega` call its certificate exceeds the kernel's recursion depth.) -/
theorem addi_neg16 {a : Nat} (h : 16 ≤ a) (ha : a < 2 ^ 32) : addi (W a) (-16) = W (a - 16) := by
  have e3 : (a + 4294967280) % 2 ^ 64 = a + 4294967280 := Nat.mod_eq_of_lt (by omega)
  have e4 : (a + 4294967280) % 2 ^ 32 = a - 16 := by omega
  have e5 : addi (W a) (-16) = truncBits 32 (W a + W 4294967280) := by
    simp only [addi, imm_neg16, r32_W ha]
  rw [e5]
  apply BitVec.eq_of_toNat_eq
  rw [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, toNat_W (show a < 2 ^ 64 by omega),
    toNat_W (show 4294967280 < 2 ^ 64 by omega), e3, e4,
    toNat_W (show a - 16 < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- The exclusive or of two bits. -/
theorem xor_bit {a b : Nat} (ha : a < 2) (hb : b < 2) :
    xor32 (W a) (W b) = W ((a + b) % 2) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> rfl

/-! ### Launch facts -/

/-- The 32-bit word at offset 128 of parameter object 10 (the scale of the first coordinate of
the map of `out`) is 1. -/
theorem scaleOut (hpre : Pre P L mem0) : objField L 10 = W 1 := by
  have h := hpre.scaleOut
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.add_zero] at h0
  have e0 : (leByte 1 0).toNat = 1 := by decide
  have e1 : (leByte 1 1).toNat = 0 := by decide
  have e2 : (leByte 1 2).toNat = 0 := by decide
  have e3 : (leByte 1 3).toNat = 0 := by decide
  simp only [objField, paramName_10, paramNat, Nat.reduceDiv, h0, h1, h2, h3, Option.getD_some,
    e0, e1, e2, e3, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

/-- The word of the output pointer (register `%rd1163`: `cvta.to.global.u64` of parameter 11). -/
theorem outWord (hpre : Pre P L mem0) : r64 (r64 (paramBits L 11)) = W P.outputBase := by
  rw [paramBits, paramName_11, hpre.paramOutput]
  apply BitVec.eq_of_toNat_eq
  simp [r64, truncBits, W]

/-- **`mapa` with rank 0 returns the address it is given**: a block is its own cluster. -/
theorem mapaPeer_own (hpre : Pre P L mem0) (hg : g < L.threads) {a : Nat} (ha : a < 2 ^ 32) :
    mapaPeer L g (W a) (W 0) = some ⟨.shared, g / L.block, a⟩ := by
  have hc : g / L.block < L.grid := by
    rw [block_div hpre, hpre.grid]
    exact cta_lt hpre hg
  have h0 : (truncBits 32 (W 0)).toNat = 0 := by decide
  have h1 : (truncBits 32 (W a)).toNat = a := by
    simp only [truncBits, W, BitVec.toNat_ofNat]; omega
  simp only [mapaPeer, hg, hc, and_self, ↓reduceIte, h0, h1, Launch.mapShared,
    Launch.peerCta_unit (unitClusters hpre) (cta_lt_nclusters hpre hg) hc, Option.map_some]

/-! ### Bounds -/

/-- The tokens of a thread's sequence are tokens of the batch. -/
theorem tok_le (hpre : Pre P L mem0) (g : Nat) :
    firstToken P.length (seqOf P g) + P.length (seqOf P g) ≤ P.total := by
  have h := Startup.cu_succ P (seqOf P g)
  have h2 := Startup.cu_le P (i := seqOf P g + 1) (Startup.seq_lt hpre g)
  simp only [Startup.cu] at h h2
  omega

/-- The 256-byte output row of a token of the batch and a head ends inside the output array. -/
theorem out_le (hpre : Pre P L mem0) {tok h : Nat} (ht : tok < P.total) (hh : h < P.heads) :
    P.outputBase + 256 * (tok * P.heads + h) + 256 ≤ 2 ^ 64 := by
  have h1 : (tok + 1) * P.heads ≤ P.total * P.heads := Nat.mul_le_mul_right _ ht
  have h2 := hpre.outputRange
  simp only [Params.tokenBytes] at h2
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
