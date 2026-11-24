-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvWComp
public import Kernels.InklingRelDecode.Proof.Thread.ProBSpec

@[expose] public section

/-!
# The loader's event shapes in `Spec`'s quantities

`LdShape` (`EvWLoader`) states the origin of a copy and the address of a block-table load as
functions of the loader's words (the inherited parameter words `Loader.Pro`, the counters, the
block-table words), modulo `2 ^ 32` and `2 ^ 64`. With the words the launch fixes (`Words Q P`,
which `after_means` proves of every reachable state) they are the quantities of `Spec`:

* `ldCol_spec`, `ldRow_spec`: the origin column `kvh · head_cols + 128 [V] + 64 hh` and row
  `page · page_rows + kvh · head_rows` modulo `2 ^ 32`, `kvh = ctaid.y`; `ldCopy_origin`: the
  copy's origin as the integers of those expressions, given the row is below `2 ^ 31`
  (`ldRow_lt`: it is, when the block-table word is the page of a block that exists);
* `ldBtAddr_spec`: the address of slab `e`'s block-table word of iteration `i` is `btBase + 4
  (req · stride_bt + 2 (split + i · num_splits) + e)` modulo `2 ^ 64`, `split = ctaid.x`,
  `req = ctaid.z`, for a block below `2 ^ 24` and an index below `2 ^ 31`.

The arithmetic behind the last is `sar_shift` (the signed shift of the block's key row by 6),
`madwide_four` (`mad.wide.s32` by 4) and `sx32_small`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvW
open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000

theorem modmul (a b c m : Nat) : ((a % m) * (b % m) + c) % m = (a * b + c) % m := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem modmul3 (a b c e m : Nat) :
    ((a % m) * (b % m) + c + e) % m = (a * b + c + e) % m := by
  simpa [Nat.add_assoc] using modmul a b (c + e) m

theorem modrow (p a b c m : Nat) :
    (p * (a % m) + (b % m) * (c % m)) % m = (p * a + c * b) % m := by
  have h := Nat.ModEq.add (Nat.ModEq.mul_left p (Nat.mod_modEq a m))
    (Nat.ModEq.mul (Nat.mod_modEq b m) (Nat.mod_modEq c m))
  rw [Nat.mul_comm c b]
  exact h

theorem i32_of_lt {x : Nat} (h : x < 2 ^ 31) : i32 x = (x : Int) := by
  unfold i32
  rw [BitVec.toInt_ofNat', Int.bmod_def]
  have h1 : ((x : Int) % (2 ^ 32 : Nat)) = x := by
    rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
  push_cast at h1 ⊢
  rw [h1]
  split_ifs with h2
  · rfl
  · exfalso; omega

theorem sar_shift (x : Nat) (hx : 128 * x < 2 ^ 31) :
    Loader.sarW (BitVec.ofNat 64 (128 * (x % 2 ^ 32) % 2 ^ 32)) (BitVec.ofInt 64 6) =
      BitVec.ofNat 64 (2 * x) := by
  have hx1 : x % 2 ^ 32 = x := Nat.mod_eq_of_lt (by omega)
  have hA : 128 * x % 2 ^ 32 = 128 * x := Nat.mod_eq_of_lt (by omega)
  rw [hx1, hA]
  unfold Loader.sarW
  nf_simp [toSigned, Loader.pw]
  have hA' : 128 * x % 4294967296 = 128 * x := Nat.mod_eq_of_lt (by omega)
  have h2x : 2 * x % 18446744073709551616 = 2 * x := Nat.mod_eq_of_lt (by omega)
  have h6 : min 6 32 = 6 := rfl
  have hlt : 128 * x < 2147483648 := by omega
  simp only [hA', h2x, h6, hlt, ↓reduceIte]
  omega

theorem madwide_four (a c : Nat) (ha : a < 2 ^ 31) (hc : c < 2 ^ 64) :
    Loader.madWideW (BitVec.ofNat 64 a) (BitVec.ofInt 64 4) (BitVec.ofNat 64 c) =
      BitVec.ofNat 64 (4 * a + c) := by
  unfold Loader.madWideW
  nf_simp [intOf, toSigned]
  have h1 : a % 4294967296 < 2147483648 := by omega
  have hc' : c % 18446744073709551616 = c := Nat.mod_eq_of_lt hc
  simp only [h1, hc', ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  by_cases h2 : c < 9223372036854775808
  · simp only [h2, ↓reduceIte, intBits, truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  · simp only [h2, ↓reduceIte, intBits, truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

theorem sx32_small {x : Nat} (hx : x < 2 ^ 31) : Loader.sx32 x = x := by
  unfold Loader.sx32
  have h1 : x % 2 ^ 32 = x := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h2 : x / 2 ^ 31 = 0 := Nat.div_eq_of_lt hx
  rw [h2]
  simp

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0} {d : Loader.D} {P : Loader.Pro}

/-- The words the loader reads, as `Spec`'s parameters modulo `2 ^ 32`. -/
theorem pro_words (hm : Words Q P) (hpro : Loader.ProEq L g P d) :
    ldStrideBt d = Q.strideBt % 2 ^ 32 ∧
      ldPageRows d = Q.pageRows % 2 ^ 32 ∧
      ldHeadRows d = Q.headRows % 2 ^ 32 ∧
      ldHeadCols d = Q.headCols % 2 ^ 32 ∧
      ldSplits d = Q.splits % 2 ^ 32 ∧
      ldBtBase d = Q.btBase % 2 ^ 64 := by
  unfold ldStrideBt ldPageRows ldHeadRows ldHeadCols ldSplits ldBtBase
  rw [hpro 528 (by decide) (by decide), hpro 529 (by decide) (by decide),
    hpro 530 (by decide) (by decide), hpro 531 (by decide) (by decide),
    hpro 532 (by decide) (by decide), hpro 2020 (by decide) (by decide)]
  simp [Loader.Pro.val, Loader.Pro.table, PTX.Flow.lookupLit, Loader.natOf_b32,
    Loader.natOf64_b64, hm.w67, hm.w68, hm.w69, hm.w70, hm.w71, hm.bt]

/-- The origin column of a box, as `Spec`'s quantity modulo `2 ^ 32`. -/
theorem ldCol_spec (hm : Words Q P) (hpro : Loader.ProEq L g P d) (isV : Bool)
    (hh : Nat) :
    ldCol L g d isV hh =
      (ProA.cta L g .y * Q.headCols + (if isV then 128 else 0) + 64 * hh) % 2 ^ 32 := by
  obtain ⟨-, -, -, h70, -, -⟩ := pro_words hm hpro
  unfold ldCol
  rw [h70]
  have : Loader.ctaY L g = ProA.cta L g .y % 2 ^ 32 := rfl
  rw [this, modmul3, Nat.mul_comm Q.headCols]

/-- The origin row of a slab, as `Spec`'s quantity modulo `2 ^ 32`. -/
theorem ldRow_spec (hm : Words Q P) (hpro : Loader.ProEq L g P d) (slab : Nat) :
    ldRow L g d slab =
      ((if slab = 0 then d.p0 else d.p1) * Q.pageRows + ProA.cta L g .y * Q.headRows) % 2 ^ 32 := by
  obtain ⟨-, h68, h69, -, -, -⟩ := pro_words hm hpro
  unfold ldRow
  rw [h68, h69]
  have : Loader.ctaY L g = ProA.cta L g .y % 2 ^ 32 := rfl
  rw [this, modrow]

/-- Slab 0's block-table address register, from the loop's words. -/
theorem ldBtAddr0_spec
    (hy : 128 * (ldSplits d * d.i + Loader.ctaX L g) < 2 ^ 31)
    (hz : ldStrideBt d * Loader.ctaZ L g < 2 ^ 31) :
    (ldBtAddr0 L g d).toNat =
      (ldBtBase d + 4 * (ldStrideBt d * Loader.ctaZ L g +
        2 * (ldSplits d * d.i + Loader.ctaX L g))) % 2 ^ 64 := by
  unfold ldBtAddr0
  simp only
  rw [sar_shift _ hy, madwide_four _ _ (by omega) (Nat.mod_lt _ (by norm_num)), sx32_small hz]
  simp only [BitVec.toNat_ofNat]
  omega

theorem add64W_four (a : BitVec 64) :
    (Loader.add64W a (BitVec.ofInt 64 4)).toNat = (a.toNat + 4) % 2 ^ 64 := by
  unfold Loader.add64W
  simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_add]
  have : (a.toNat) < 2 ^ 64 := a.isLt
  omega

/-- **The block-table address of a slab, from `Spec`'s quantities**: slab `slab` of the iteration
`d.i` of the CTA with split `ctaid.x`, request `ctaid.z`: `btBase + 4 (req · stride_bt + 2 (split +
i · num_splits) + slab)`, modulo `2 ^ 64`. The two bounds say the index is in the table
(`Pre.btIndexRange` for a block that exists) and the block is below `2 ^ 24` (`blocks ≤ 2 ^ 24`). -/
theorem ldBtAddr_spec (hpre : Pre Q L mem0) (hg : g < L.threads) (hm : Words Q P)
    (hpro : Loader.ProEq L g P d) (slab : Nat) (hs : slab ≤ 1)
    (hblk : ProA.cta L g .x + d.i * Q.splits < 2 ^ 24)
    (hbt : ProA.cta L g .z * Q.strideBt + 2 * (ProA.cta L g .x + d.i * Q.splits) + slab < 2 ^ 31) :
    ldBtAddr L g d slab = (Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
      2 * (ProA.cta L g .x + d.i * Q.splits) + slab)) % 2 ^ 64 := by
  obtain ⟨h67, -, -, -, h71, hbtw⟩ := pro_words hm hpro
  obtain ⟨hx, -, hz⟩ := ProA.cta_lt hpre hg
  have hspl := hpre.splitsRange
  have hb := hpre.bPos
  have hbR := hpre.bRange
  have hX : Loader.ctaX L g = ProA.cta L g .x := by
    show ProA.cta L g .x % 2 ^ 32 = ProA.cta L g .x
    exact Nat.mod_eq_of_lt (by omega)
  have hZ : Loader.ctaZ L g = ProA.cta L g .z := by
    show ProA.cta L g .z % 2 ^ 32 = ProA.cta L g .z
    exact Nat.mod_eq_of_lt (by omega)
  have hS : ldSplits d = Q.splits := by rw [h71]; exact Nat.mod_eq_of_lt (by omega)
  have hW : ldStrideBt d * Loader.ctaZ L g = Q.strideBt * ProA.cta L g .z := by
    rw [h67, hZ]
    by_cases hz0 : ProA.cta L g .z = 0
    · simp [hz0]
    · have hst : Q.strideBt < 2 ^ 31 := by
        have : Q.strideBt ≤ ProA.cta L g .z * Q.strideBt :=
          Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hz0)
        omega
      rw [Nat.mod_eq_of_lt (by omega)]
  have hy : 128 * (ldSplits d * d.i + Loader.ctaX L g) < 2 ^ 31 := by
    rw [hS, hX, Nat.mul_comm Q.splits]
    omega
  have hzz : ldStrideBt d * Loader.ctaZ L g < 2 ^ 31 := by
    rw [hW, Nat.mul_comm]
    omega
  have h0 := ldBtAddr0_spec hy hzz
  rw [hW, hS, hX, hbtw] at h0
  unfold ldBtAddr
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with rfl | rfl
  · simp only [↓reduceIte]
    rw [h0, Nat.mul_comm Q.strideBt, Nat.mul_comm Q.splits]
    omega
  · simp only [Nat.one_ne_zero, ↓reduceIte]
    rw [add64W_four, h0, Nat.mul_comm Q.strideBt, Nat.mul_comm Q.splits]
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.EvW
