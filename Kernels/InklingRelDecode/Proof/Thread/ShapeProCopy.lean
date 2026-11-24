-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDProCopy
public import Kernels.InklingRelDecode.Proof.Thread.ProBOps

@[expose] public section

/-!
# The prologue's copy registers in closed form

The twelve K/V copies of the prologue (`ptcSite i`, block `i / 4`, `i % 4` = K slab 0, V slab 0,
K slab 1, V slab 1) read three registers each: the shared destination, the box column and the box
row. The register table builds them from `%tid.x`, `%ctaid.y`, the shared base, the parameter words
`page_rows`, `head_rows`, `head_cols` (`dt.pro.w68`, `w69`, `w70`) and the loaded block-table words
`dt.b0 … dt.b5`, so each is a closed `Nat` expression, proved one operation at a time over the
register table (`ProBOps` lemmas):

* `copyDst_form`: `sharedBase + 16384 h + 32768 (i / 4) + 98304 (i % 2) + 8192 (i % 4 / 2)`;
* `copyX_form`: `(64 h + 128 (i % 2) + head_cols · ctaid.y) % 2 ^ 32`;

where `h = half dt (i / 4)` is bit 0 of the word the block's broadcast of the warp index received
(`Dat.sh0` …; in a run it is the warp index, so `h = warp % 2`, `Interface.PshOk`);
* `copyY_form`: `(page · page_rows + head_rows · ctaid.y) % 2 ^ 32`, `page` the loaded word of the
  copy's slab `btW dt (2 (i / 4) + i % 4 / 2)`.

The coordinates of a copy are read as signed 32-bit words, so the residues modulo `2 ^ 32` are what
`EvW.kvCopySpec` sees (`Result.Mma.kvCopySpec_mod`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

theorem wShl32_ofNat (a k : Nat) (hk : k < 32) :
    wShl32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 k) =
      BitVec.ofNat 64 ((a % 2 ^ 32) * 2 ^ k % 2 ^ 32) := by
  simp only [wShl32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  have h1 : (BitVec.ofNat 64 (k % 2 ^ 32)).toNat = k := by
    rw [BitVec.toNat_ofNat]; omega
  rw [h1]
  split_ifs with hh
  · omega
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have e1 : a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  rw [e1]
  have hd : 2 ^ 32 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hd]

theorem wMulLo32_ofNat (a b : Nat) :
    wMulLo32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a * b % 2 ^ 32) := by
  simp only [wMulLo32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hd : 2 ^ 32 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_eq_of_lt (a := a % 2 ^ 32) (by omega), Nat.mod_eq_of_lt (a := b % 2 ^ 32) (by omega),
    Nat.mod_mod_of_dvd _ hd, ← Nat.mul_mod]

theorem wMadLo32_ofNat (a b c : Nat) :
    wMadLo32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c) =
      BitVec.ofNat 64 ((a * b + c) % 2 ^ 32) := by
  simp only [wMadLo32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hd : 2 ^ 32 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_eq_of_lt (a := a % 2 ^ 32) (by omega), Nat.mod_eq_of_lt (a := b % 2 ^ 32) (by omega),
    Nat.mod_eq_of_lt (a := c % 2 ^ 32) (by omega)]
  have h1 : (a % 2 ^ 32 * (b % 2 ^ 32) % 2 ^ 64 + c % 2 ^ 32) % 2 ^ 64 % 2 ^ 32 =
      (a * b + c) % 2 ^ 32 := by
    rw [Nat.mod_mod_of_dvd _ hd, Nat.add_mod, Nat.mod_mod_of_dvd _ hd, Nat.mod_mod,
      ← Nat.mul_mod, ← Nat.add_mod]
  rw [h1]

theorem ofInt_ofNat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  rw [BitVec.ofInt_natCast]

theorem v_r234_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r234 L g dt = BitVec.ofNat 64 (half dt 0) := by
  have l : BitVec.ofInt 64 1 = BitVec.ofNat 64 1 := by rw [nf_ofInt]; rfl
  simp only [v_r234, v_r232, l, wAnd32_ofNat]
  exact congrArg _ (shW_bit _)

/-- The shared base leaves room for the K/V rings and the tiles of the prologue. -/
def SbRoom (L : Launch) : Prop := L.sharedBase + 2 ^ 18 < 2 ^ 32

theorem v_r33_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r33 L g dt = BitVec.ofNat 64 (dt.pro.w69 * (cta L g .y % 2 ^ 32) % 2 ^ 32) := by
  simp only [v_r33, v_r69, v_r18, wCta_eq, wMulLo32_ofNat]

theorem v_r34_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r34 L g dt = BitVec.ofNat 64 (dt.pro.w70 * (cta L g .y % 2 ^ 32) % 2 ^ 32) := by
  simp only [v_r34, v_r70, v_r18, wCta_eq, wMulLo32_ofNat]

theorem v_r205_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r205 L g dt = BitVec.ofNat 64 (L.sharedBase % 2 ^ 32) := by
  simp only [v_r205, wSmem, Nat.add_zero, truncBits_ofNat _ _ (by omega : 32 ≤ 64)]

theorem v_r255_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r255 L g dt = BitVec.ofNat 64 (half dt 1) := by
  have l : BitVec.ofInt 64 1 = BitVec.ofNat 64 1 := by rw [nf_ofInt]; rfl
  simp only [v_r255, v_r253, l, wAnd32_ofNat]
  exact congrArg _ (shW_bit _)

theorem v_r277_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r277 L g dt = BitVec.ofNat 64 (half dt 2) := by
  have l : BitVec.ofInt 64 1 = BitVec.ofNat 64 1 := by rw [nf_ofInt]; rfl
  simp only [v_r277, v_r275, l, wAnd32_ofNat]
  exact congrArg _ (shW_bit _)

theorem wordOf_ofNat {x : BitVec 64} {n : Nat} (h : x = BitVec.ofNat 64 n) (hn : n < 2 ^ 32) :
    wordOf (.bits 32 x) = n := by
  subst h
  simp only [wordOf, BitVec.toNat_ofNat]
  omega

theorem c8192 : BitVec.ofInt 64 8192 = BitVec.ofNat 64 8192 := by rw [nf_ofInt]; rfl
theorem c32768 : BitVec.ofInt 64 32768 = BitVec.ofNat 64 32768 := by rw [nf_ofInt]; rfl
theorem c40960 : BitVec.ofInt 64 40960 = BitVec.ofNat 64 40960 := by rw [nf_ofInt]; rfl
theorem c65536 : BitVec.ofInt 64 65536 = BitVec.ofNat 64 65536 := by rw [nf_ofInt]; rfl
theorem c73728 : BitVec.ofInt 64 73728 = BitVec.ofNat 64 73728 := by rw [nf_ofInt]; rfl
theorem c98304 : BitVec.ofInt 64 98304 = BitVec.ofNat 64 98304 := by rw [nf_ofInt]; rfl
theorem c106496 : BitVec.ofInt 64 106496 = BitVec.ofNat 64 106496 := by rw [nf_ofInt]; rfl
theorem c131072 : BitVec.ofInt 64 131072 = BitVec.ofNat 64 131072 := by rw [nf_ofInt]; rfl
theorem c139264 : BitVec.ofInt 64 139264 = BitVec.ofNat 64 139264 := by rw [nf_ofInt]; rfl
theorem c163840 : BitVec.ofInt 64 163840 = BitVec.ofNat 64 163840 := by rw [nf_ofInt]; rfl
theorem c172032 : BitVec.ofInt 64 172032 = BitVec.ofNat 64 172032 := by rw [nf_ofInt]; rfl
theorem c128 : BitVec.ofInt 64 128 = BitVec.ofNat 64 128 := by rw [nf_ofInt]; rfl
theorem c6 : BitVec.ofInt 64 6 = BitVec.ofNat 64 6 := by rw [nf_ofInt]; rfl

theorem v_r235_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r235 L g dt = BitVec.ofNat 64 (16384 * (half dt 0)) := by
  have := half_lt dt 0
  have l : BitVec.ofInt 64 14 = BitVec.ofNat 64 14 := by rw [nf_ofInt]; rfl
  simp only [v_r235, v_r234_eq L g dt, l, wShl32_ofNat _ 14 (by norm_num)]
  congr 1
  omega

theorem v_r256_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r256 L g dt = BitVec.ofNat 64 (16384 * (half dt 1)) := by
  have := half_lt dt 1
  have l : BitVec.ofInt 64 14 = BitVec.ofNat 64 14 := by rw [nf_ofInt]; rfl
  simp only [v_r256, v_r255_eq L g dt, l, wShl32_ofNat _ 14 (by norm_num)]
  congr 1
  omega

theorem v_r278_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r278 L g dt = BitVec.ofNat 64 (16384 * (half dt 2)) := by
  have := half_lt dt 2
  have l : BitVec.ofInt 64 14 = BitVec.ofNat 64 14 := by rw [nf_ofInt]; rfl
  simp only [v_r278, v_r277_eq L g dt, l, wShl32_ofNat _ 14 (by norm_num)]
  congr 1
  omega

/-- Register `%r221 + c` of the first block's destinations. -/
theorem v_r221_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r221 L g dt =
      BitVec.ofNat 64 ((L.sharedBase + 16384 * (half dt 0)) % 2 ^ 32) := by
  have := half_lt dt 0
  simp only [v_r221, v_r205_eq, v_r235_eq L g dt, wAdd32_ofNat]
  congr 1
  omega

theorem v_r257_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r257 L g dt =
      BitVec.ofNat 64 ((L.sharedBase + 16384 * (half dt 1)) % 2 ^ 32) := by
  have := half_lt dt 1
  simp only [v_r257, v_r205_eq, v_r256_eq L g dt, wAdd32_ofNat]
  congr 1
  omega

theorem v_r279_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r279 L g dt =
      BitVec.ofNat 64 ((L.sharedBase + 16384 * (half dt 2)) % 2 ^ 32) := by
  have := half_lt dt 2
  simp only [v_r279, v_r205_eq, v_r278_eq L g dt, wAdd32_ofNat]
  congr 1
  omega

/-- The expected destination of copy `i`. -/
def dstOf (L : Launch) (dt : Dat) (i : Nat) : Nat :=
  (L.sharedBase + 16384 * half dt (i / 4) + 32768 * (i / 4) + 98304 * (i % 2) +
    8192 * (i % 4 / 2)) % 2 ^ 32

theorem dst_regs0 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i < 4, ∃ x : BitVec 64, x = BitVec.ofNat 64 (dstOf L dt i) ∧
      valueOf L g dt (ptcDst (ptcSite i).pc) = .bits 32 x := by
  intro i hi
  have := half_lt dt 0
  have := half_lt dt 1
  have := half_lt dt 2
  interval_cases i
  · refine ⟨v_r221 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r221_eq L g dt]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r224 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r224, v_r221_eq L g dt, c98304, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r227 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r227, v_r221_eq L g dt, c8192, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r229 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r229, v_r221_eq L g dt, c106496, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega

theorem dst_regs1 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i, 4 ≤ i → i < 8 → ∃ x : BitVec 64, x = BitVec.ofNat 64 (dstOf L dt i) ∧
      valueOf L g dt (ptcDst (ptcSite i).pc) = .bits 32 x := by
  intro i h1 h2
  have := half_lt dt 0
  have := half_lt dt 1
  have := half_lt dt 2
  interval_cases i
  · refine ⟨v_r241 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r241, v_r257_eq L g dt, c32768, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r244 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r244, v_r257_eq L g dt, c131072, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r247 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r247, v_r257_eq L g dt, c40960, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r249 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r249, v_r257_eq L g dt, c139264, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega

theorem dst_regs2 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i, 8 ≤ i → i < 12 → ∃ x : BitVec 64, x = BitVec.ofNat 64 (dstOf L dt i) ∧
      valueOf L g dt (ptcDst (ptcSite i).pc) = .bits 32 x := by
  intro i h1 h2
  have := half_lt dt 0
  have := half_lt dt 1
  have := half_lt dt 2
  interval_cases i
  · refine ⟨v_r263 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r263, v_r279_eq L g dt, c65536, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r266 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r266, v_r279_eq L g dt, c163840, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r269 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r269, v_r279_eq L g dt, c73728, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r271 L g dt, ?_, rfl⟩
    simp only [dstOf, Nat.reduceDiv, v_r271, v_r279_eq L g dt, c172032, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega

/-- **The destination of copy `i` in closed form**: the shared base, the half `16384 h` of the slab
(`h = half dt (i / 4)`), the ring slot `32768 (i / 4)`, the V offset `98304 (i % 2)` and the
slab offset `8192 (i % 4 / 2)`. -/
theorem copyDst_form (L : Launch) (g : Nat) (dt : Dat) (hs : SbRoom L)
    {i : Nat} (hi : i < 12) :
    copyDst L g dt i = L.sharedBase + 16384 * half dt (i / 4) + 32768 * (i / 4) +
      98304 * (i % 2) + 8192 * (i % 4 / 2) := by
  obtain ⟨x, hx, hv⟩ : ∃ x : BitVec 64, x = BitVec.ofNat 64 (dstOf L dt i) ∧
      valueOf L g dt (ptcDst (ptcSite i).pc) = .bits 32 x := by
    by_cases h1 : i < 4
    · exact dst_regs0 L g dt i h1
    · by_cases h2 : i < 8
      · exact dst_regs1 L g dt i (by omega) h2
      · exact dst_regs2 L g dt i (by omega) hi
  have hlt : dstOf L dt i < 2 ^ 32 := Nat.mod_lt _ (by omega)
  unfold copyDst
  rw [hv, wordOf_ofNat hx hlt]
  unfold dstOf SbRoom at *
  have := half_lt dt (i / 4)
  have : i / 4 < 3 := by omega
  have : i % 2 < 2 := Nat.mod_lt _ (by omega)
  have : i % 4 / 2 < 2 := by omega
  rw [Nat.mod_eq_of_lt]
  omega

/-! ### The box origin -/

theorem v_r236_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r236 L g dt = BitVec.ofNat 64 (64 * (half dt 0)) := by
  have := half_lt dt 0
  simp only [v_r236, v_r234_eq L g dt, c6, wShl32_ofNat _ 6 (by norm_num)]
  refine congrArg (BitVec.ofNat 64) ?_
  omega

theorem v_r258_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r258 L g dt = BitVec.ofNat 64 (64 * (half dt 1)) := by
  have := half_lt dt 1
  simp only [v_r258, v_r255_eq L g dt, c6, wShl32_ofNat _ 6 (by norm_num)]
  refine congrArg (BitVec.ofNat 64) ?_
  omega

theorem v_r280_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r280 L g dt = BitVec.ofNat 64 (64 * (half dt 2)) := by
  have := half_lt dt 2
  simp only [v_r280, v_r277_eq L g dt, c6, wShl32_ofNat _ 6 (by norm_num)]
  refine congrArg (BitVec.ofNat 64) ?_
  omega

/-- The expected column of the box origin of copy `i`: the half `64 (half dt (i / 4))` of the
head's columns, `head_cols · kvh`, and `128` for V. -/
def colOf (L : Launch) (g : Nat) (dt : Dat) (i : Nat) : Nat :=
  (64 * half dt (i / 4) + 128 * (i % 2) +
    dt.pro.w70 * (cta L g .y % 2 ^ 32) % 2 ^ 32) % 2 ^ 32

theorem x_regs0 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i < 4, ∃ x : BitVec 64, x = BitVec.ofNat 64 (colOf L g dt i) ∧
      valueOf L g dt (ptcCoord (ptcSite i).pc 0) = .bits 32 x := by
  intro i hi
  have := half_lt dt 0
  have := half_lt dt 1
  have := half_lt dt 2
  interval_cases i
  · refine ⟨v_r222 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r222, v_r236_eq L g dt, v_r34_eq, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r225 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r225, v_r222, v_r236_eq L g dt, v_r34_eq, c128, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r222 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r222, v_r236_eq L g dt, v_r34_eq, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r225 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r225, v_r222, v_r236_eq L g dt, v_r34_eq, c128, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega

theorem x_regs1 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i, 4 ≤ i → i < 8 → ∃ x : BitVec 64, x = BitVec.ofNat 64 (colOf L g dt i) ∧
      valueOf L g dt (ptcCoord (ptcSite i).pc 0) = .bits 32 x := by
  intro i h1 h2
  have := half_lt dt 0
  have := half_lt dt 1
  have := half_lt dt 2
  interval_cases i
  · refine ⟨v_r242 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r242, v_r258_eq L g dt, v_r34_eq, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r245 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r245, v_r242, v_r258_eq L g dt, v_r34_eq, c128, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r242 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r242, v_r258_eq L g dt, v_r34_eq, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r245 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r245, v_r242, v_r258_eq L g dt, v_r34_eq, c128, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega

theorem x_regs2 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i, 8 ≤ i → i < 12 → ∃ x : BitVec 64, x = BitVec.ofNat 64 (colOf L g dt i) ∧
      valueOf L g dt (ptcCoord (ptcSite i).pc 0) = .bits 32 x := by
  intro i h1 h2
  have := half_lt dt 0
  have := half_lt dt 1
  have := half_lt dt 2
  interval_cases i
  · refine ⟨v_r264 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r264, v_r280_eq L g dt, v_r34_eq, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r267 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r267, v_r264, v_r280_eq L g dt, v_r34_eq, c128, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r264 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r264, v_r280_eq L g dt, v_r34_eq, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega
  · refine ⟨v_r267 L g dt, ?_, rfl⟩
    simp only [colOf, Nat.reduceDiv, v_r267, v_r264, v_r280_eq L g dt, v_r34_eq, c128, wAdd32_ofNat]
    refine congrArg (BitVec.ofNat 64) ?_
    omega

/-- **The box column of copy `i` in closed form** (modulo `2 ^ 32`, the register's word). -/
theorem copyX_form (L : Launch) (g : Nat) (dt : Dat) {i : Nat}
    (hi : i < 12) : copyX L g dt i = colOf L g dt i := by
  obtain ⟨x, hx, hv⟩ : ∃ x : BitVec 64, x = BitVec.ofNat 64 (colOf L g dt i) ∧
      valueOf L g dt (ptcCoord (ptcSite i).pc 0) = .bits 32 x := by
    by_cases h1 : i < 4
    · exact x_regs0 L g dt i h1
    · by_cases h2 : i < 8
      · exact x_regs1 L g dt i (by omega) h2
      · exact x_regs2 L g dt i (by omega) hi
  have hlt : colOf L g dt i < 2 ^ 32 := Nat.mod_lt _ (by omega)
  unfold copyX
  rw [hv, wordOf_ofNat hx hlt]

/-- The block-table words the prologue loaded: block `k / 2`, slab `k % 2`. -/
def btW (dt : Dat) (k : Nat) : Nat := [dt.b0, dt.b1, dt.b2, dt.b3, dt.b4, dt.b5].getD k 0

/-- The expected row of the box origin of copy `i`: `page · page_rows + head_rows · kvh` of the
loaded word of its slab. -/
def rowOf (L : Launch) (g : Nat) (dt : Dat) (i : Nat) : Nat :=
  (btW dt (2 * (i / 4) + i % 4 / 2) * dt.pro.w68 +
    dt.pro.w69 * (cta L g .y % 2 ^ 32) % 2 ^ 32) % 2 ^ 32

theorem y_regs (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i < 12, ∃ x : BitVec 64, x = BitVec.ofNat 64 (rowOf L g dt i) ∧
      valueOf L g dt (ptcCoord (ptcSite i).pc 1) = .bits 32 x := by
  intro i hi
  interval_cases i
  · refine ⟨v_r223 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r223, v_r220, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r223 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r223, v_r220, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r228 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r228, v_r226, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r228 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r228, v_r226, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r243 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r243, v_r240, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r243 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r243, v_r240, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r248 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r248, v_r246, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r248 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r248, v_r246, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r265 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r265, v_r262, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r265 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r265, v_r262, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r270 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r270, v_r268, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl
  · refine ⟨v_r270 L g dt, ?_, rfl⟩
    simp only [rowOf, btW, v_r270, v_r268, v_r68, v_r33_eq, wMadLo32_ofNat]
    rfl

/-- **The box row of copy `i` in closed form** (modulo `2 ^ 32`, the register's word). -/
theorem copyY_form (L : Launch) (g : Nat) (dt : Dat) {i : Nat} (hi : i < 12) :
    copyY L g dt i = rowOf L g dt i := by
  obtain ⟨x, hx, hv⟩ := y_regs L g dt i hi
  have hlt : rowOf L g dt i < 2 ^ 32 := Nat.mod_lt _ (by omega)
  unfold copyY
  rw [hv, wordOf_ofNat hx hlt]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
