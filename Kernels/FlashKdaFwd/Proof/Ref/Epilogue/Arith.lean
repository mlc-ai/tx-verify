-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Inv
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Arith
public import Kernels.FlashKdaFwd.Proof.Thread.RunPtr

@[expose] public section

/-! # Epilogue phase: the arithmetic, each closed form proved once

* **The swizzle.** `swz_W`: the machine's swizzle of a pointer offset (`Rules.swz`, the code's
  `off xor ((off >> 3) and 16)`) is `swzN` of the number; `xor16`, `and16` are the two bit
  facts behind it. `swzN_block`, `swzN_add`: the swizzle moves an address inside its 32-byte
  block only and commutes with adding a byte index below 4 to a multiple of 4.
* **Pointer moves.** `moved_W`, `movedBy_W`: a move of the pointer with offset `W B` by a
  natural number stays in the window and gives `W (B + k)` (from `Rules.movedOff_nat`);
  `ptr_step`: the condition and the result of the run `add.s64`, swizzle of one store.
* **The base pointer.** `carry_word`: the nine instructions 3115 to 3123 compute
  `carryBase tid` from the thread index (evaluated for the 192 indices); `carryBase_lt`.
* **Registers of the stores.** `stPtr_opaque`, `stSrc_opaque`, `stPtr_ne`: evaluated facts
  about the tables.
* **Addresses of the stores.** `stAddr_bounds`: the address of a store is a multiple of 4
  inside the FP32 buffer (bytes 32768 to 98303 of the block's window).
* **Owners.** `finalOwner_lt`, `finalOwner_store` (a byte that store `j` of compute thread `g`
  writes is owned by `g`) and `store_of_owner` (a byte of the buffer owned by `g` is written by
  one of its 128 stores): the 128 stores of the 128 compute threads tile the buffer. The proof
  reads the bit fields of an offset: bits 0 and 1 the byte, 2 to 4 and 6 to 7 the lane, 10 and
  11 the warp, and 5, 8, 9, 12 to 15 the class of the store (`Tables.lean: spread`).
* **The branch conditions**: `role_ne2` (`%p81`: the thread is outside the store warp),
  `elected_eq0` (`%p78` in the store warp), and the plane `planeWord` of the tensor stores.

`S` abbreviates `P.sharedBase`; `Pre.sharedAlignment` (`S` is a multiple of 128) and
`Pre.sharedRange` are the two launch facts used. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

/-! ### The swizzle -/

theorem xor16_small : ∀ m : Fin 32,
    m.val ^^^ 16 = if m.val / 16 % 2 = 0 then m.val + 16 else m.val - 16 := by
  decide

/-- Flipping bit 4 of a number. -/
theorem xor16 (n : Nat) : n ^^^ 16 = if n / 16 % 2 = 0 then n + 16 else n - 16 := by
  have h1 := Nat.xor_mod_two_pow (a := n) (b := 16) (n := 5)
  have h2 := Nat.xor_div_two_pow (a := n) (b := 16) (n := 5)
  have h3 := xor16_small ⟨n % 32, Nat.mod_lt _ (by decide)⟩
  simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.xor_zero] at h1 h2 h3
  have h4 := Nat.div_add_mod (n ^^^ 16) 32
  split_ifs at h3 ⊢ <;> omega

theorem and16_small : ∀ m : Fin 32, m.val &&& 16 = if m.val / 16 % 2 = 1 then 16 else 0 := by
  decide

/-- Bit 4 of a number, as a mask. -/
theorem and16 (n : Nat) : n &&& 16 = if n / 16 % 2 = 1 then 16 else 0 := by
  have h1 := Nat.and_mod_two_pow (a := n) (b := 16) (n := 5)
  have h2 := Nat.and_div_two_pow (a := n) (b := 16) (n := 5)
  have h3 := and16_small ⟨n % 32, Nat.mod_lt _ (by decide)⟩
  simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.and_zero] at h1 h2 h3
  have h4 := Nat.div_add_mod (n &&& 16) 32
  split_ifs at h3 ⊢ <;> omega

/-- The code's swizzle of a number is `swzN`. -/
theorem swzN_eq (n : Nat) : n ^^^ ((n >>> 3) &&& 16) = swzN n := by
  rw [Nat.shiftRight_eq_div_pow, and16, swzN]
  have e : n / 2 ^ 3 / 16 = n / 128 := by omega
  rw [e]
  by_cases h : n / 128 % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, xor16]
  · rw [ite_eq_right h, ite_eq_right h, Nat.xor_zero]

/-- The swizzle keeps an address in its block of 32 bytes. -/
theorem swzN_block (a : Nat) : a - a % 32 ≤ swzN a ∧ swzN a < a - a % 32 + 32 ∧
    swzN a % 16 = a % 16 ∧ swzN a / 128 = a / 128 := by
  unfold swzN
  split_ifs <;> omega

/-- The swizzle of a multiple of 4 plus a byte index. -/
theorem swzN_add {a b : Nat} (ha : a % 4 = 0) (hb : b < 4) : swzN (a + b) = swzN a + b := by
  unfold swzN
  split_ifs <;> omega

/-- The swizzle is an involution. -/
theorem swzN_swzN (a : Nat) : swzN (swzN a) = a := by
  unfold swzN
  split_ifs <;> omega

/-- **The machine's swizzle of a pointer offset.** -/
theorem swz_W {n : Nat} (h : n < 2 ^ 32) : Rules.swz (W n) = W (swzN n) := by
  have hs := swzN_block n
  apply BitVec.eq_of_toNat_eq
  rw [toNat_W (show swzN n < 2 ^ 64 by omega), Rules.swz, BitVec.toNat_xor, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, toNat_W (show n < 2 ^ 64 by omega)]
  exact swzN_eq n

/-! ### Pointer moves -/

/-- **A move by a natural number** of the pointer with offset `W B`: it stays in the window and
the new offset is `W (B + k)`. `K` is the constant as the generated run writes it. -/
theorem moved_W {B k : Nat} {K : Int} (hK : K = (k : Int)) (h : B + k < 2 ^ 32) :
    Rules.MoveOk (W B) K ∧ Rules.movedOff (W B) K = W (B + k) := by
  subst hK
  have hB : (W B).toNat = B := toNat_W (by omega)
  have h1 := Rules.movedOff_nat (off := W B) (k := k) (by omega) (by rw [hB]; exact h)
  rw [hB] at h1
  exact ⟨h1.2, h1.1⟩

/-- **A move by the word `W c`** (the `add.s64` of two registers at instruction 3127). -/
theorem movedBy_W {B c : Nat} (h : B + c < 2 ^ 32) :
    Rules.MoveOkW (W B) (W c) ∧ Rules.movedBy (W B) (W c) = W (B + c) := by
  have h1 := moved_W (B := B) (k := c) rfl h
  rw [show W c = BitVec.ofInt 64 (c : Int) from (Rules.ofInt_natCast c).symm]
  exact h1

/-- **The pointer run of one store**: from the base pointer with offset `W B`, the move by the
store's constant `K = k` is in the window, and the swizzled result is the pointer with offset
`W (swzN (B + k))`. -/
theorem ptr_step {B k : Nat} {K : Int} (hK : K = (k : Int)) (h : B + k < 2 ^ 32) :
    Rules.MoveOk (W B) K ∧ Rules.swz (Rules.movedOff (W B) K) = W (swzN (B + k)) := by
  obtain ⟨h1, h2⟩ := moved_W hK h
  exact ⟨h1, by rw [h2, swz_W h]⟩

/-! ### The base pointer -/

/-- **The entry index of a thread, times four** (instructions 3115 to 3123): `shl 4`, `and 48`,
`and 31`, `shr 2`, `or`, `shl 3`, `and 7936`, `or`, `mul.wide 4` of the thread index. -/
theorem carry_word : ∀ t : Fin 192,
    mulWide .u (or32 (or32 (andi (shl (W t.val) 4) 48) (shru (andi (W t.val) 31) 2))
      (andi (shl (W t.val) 3) 7936)) 4 = W (carryBase t.val) := by
  decide +kernel

theorem carryBase_lt {t : Nat} (h : t < 128) : carryBase t ≤ 3292 ∧ carryBase t % 4 = 0 := by
  unfold carryBase
  omega

/-- `cvt.u64.u32` of the word of `shared_mem`. -/
theorem zext_W {n : Nat} (h : n < 2 ^ 32) : zext (W n) = W n := by
  apply BitVec.eq_of_toNat_eq
  simp only [zext, r32, truncBits, W, BitVec.toNat_ofNat]
  omega

/-! ### The addresses of the stores -/

/-- The address registers and the carry registers of the 128 stores are opaque slots, and no
address register is the base pointer. -/
theorem stPtr_opaque : ∀ j : Fin 128, isOpaque (stPtr j.val) = true := by decide +kernel
theorem stSrc_opaque : ∀ j : Fin 128, isOpaque (stSrc j.val) = true := by decide +kernel
theorem stPtr_ne : ∀ j : Fin 128, stPtr j.val ≠ 2897 := by decide +kernel

theorem spread_le {c : Nat} (h : c < 128) : spread c ≤ 62240 ∧ spread c % 32 = 0 := by
  unfold spread
  omega

theorem stOff_le (j : Fin 128) : 32768 ≤ stOff j.val ∧ stOff j.val ≤ 95008 ∧
    stOff j.val % 32 = 0 := by
  have h := spread_le (stClass_lt j)
  rw [stOff_eq j]
  omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **The address of a store**: a multiple of 4 in the FP32 buffer of the block's window. -/
theorem stAddr_bounds (hpre : Pre P L mem0) (ht : tid g < 128) (j : Fin 128) :
    stAddr P g j.val % 4 = 0 ∧ P.sharedBase + 32768 ≤ stAddr P g j.val ∧
      stAddr P g j.val + 4 ≤ P.sharedBase + 98304 := by
  have ha := hpre.sharedAlignment
  have hc := carryBase_lt ht
  have ho := stOff_le j
  have hs := spread_le (stClass_lt j)
  have hb := swzN_block (P.sharedBase + carryBase (tid g) + stOff j.val)
  have he := stOff_eq j
  unfold stAddr
  omega

/-- The unswizzled address of a store is in the 32-bit window. -/
theorem stBase_lt (hpre : Pre P L mem0) (ht : tid g < 128) (j : Fin 128) :
    P.sharedBase + carryBase (tid g) + stOff j.val < 2 ^ 32 := by
  have hs := shared_lt hpre
  have hc := carryBase_lt ht
  have ho := stOff_le j
  omega

/-! ### Owners -/

theorem finalOwner_lt (P : Params) (l : Loc) : finalOwner P l < 128 := by
  unfold finalOwner
  omega

/-- The offset of the base pointer of the thread with the bit fields `w` (warp), `l8` (the
lane's three high bits) and `l4` (its two low bits). -/
theorem carryBase_fields {w l8 l4 : Nat} (hl8 : l8 < 8) (hl4 : l4 < 4) :
    carryBase (32 * w + 4 * l8 + l4) = 1024 * w + 64 * l4 + 4 * l8 := by
  unfold carryBase
  omega

/-- The offset of the class with the bit fields `c2`, `c1`, `c0`. -/
theorem spread_fields {c2 c1 c0 : Nat} (hc1 : c1 < 4) (hc0 : c0 < 2) :
    spread (8 * c2 + 2 * c1 + c0) = 32 * c0 + 256 * c1 + 4096 * c2 := by
  unfold spread
  omega

/-- The bit fields of an offset `r` of the buffer give back the thread: with the warp in bits
10 and 11, the lane's low bits in bits 6 and 7 and its high bits in bits 2 to 4. -/
theorem owner_fields {t c b : Nat} (ht : t < 128) (hc : c < 128) (hb : b < 4) :
    32 * ((carryBase t + spread c + b) / 1024 % 4) + 4 * ((carryBase t + spread c + b) / 4 % 8) +
      (carryBase t + spread c + b) / 64 % 4 = t := by
  obtain ⟨w, l8, l4, hw, hl8, hl4, rfl⟩ : ∃ w l8 l4, w < 4 ∧ l8 < 8 ∧ l4 < 4 ∧
      t = 32 * w + 4 * l8 + l4 :=
    ⟨t / 32, t % 32 / 4, t % 4, by omega, by omega, by omega, by omega⟩
  obtain ⟨c2, c1, c0, hc2, hc1, hc0, rfl⟩ : ∃ c2 c1 c0, c2 < 16 ∧ c1 < 4 ∧ c0 < 2 ∧
      c = 8 * c2 + 2 * c1 + c0 := ⟨c / 8, c / 2 % 4, c % 2, by omega, by omega, by omega, by omega⟩
  rw [carryBase_fields hl8 hl4, spread_fields hc1 hc0]
  have d1 : (1024 * w + 64 * l4 + 4 * l8 + (32 * c0 + 256 * c1 + 4096 * c2) + b) / 1024 =
      4 * c2 + w := by omega
  have d2 : (1024 * w + 64 * l4 + 4 * l8 + (32 * c0 + 256 * c1 + 4096 * c2) + b) / 4 =
      8 * (128 * c2 + 32 * w + 8 * c1 + 2 * l4 + c0) + l8 := by omega
  have d3 : (1024 * w + 64 * l4 + 4 * l8 + (32 * c0 + 256 * c1 + 4096 * c2) + b) / 64 =
      4 * (16 * c2 + 4 * w + c1) + l4 := by omega
  have t1 : (4 * c2 + w) % 4 = w := by omega
  have t2 : (8 * (128 * c2 + 32 * w + 8 * c1 + 2 * l4 + c0) + l8) % 8 = l8 := by omega
  have t3 : (4 * (16 * c2 + 4 * w + c1) + l4) % 4 = l4 := by omega
  rw [d1, d2, d3, t1, t2, t3]

/-- **A byte that store `j` of compute thread `g` writes is owned by `g`.** -/
theorem finalOwner_store (hpre : Pre P L mem0) (ht : tid g < 128) (j : Fin 128) {l : Loc}
    (h1 : stAddr P g j.val ≤ l.addr) (h2 : l.addr < stAddr P g j.val + 4) :
    finalOwner P l = tid g := by
  have ha := hpre.sharedAlignment
  have hc := carryBase_lt ht
  have ho := stOff_le j
  have he := stOff_eq j
  obtain ⟨b, hb, hlb⟩ : ∃ b, b < 4 ∧ l.addr = stAddr P g j.val + b :=
    ⟨l.addr - stAddr P g j.val, by omega, by omega⟩
  have hsw : swzN (stAddr P g j.val + b) =
      P.sharedBase + carryBase (tid g) + stOff j.val + b := by
    rw [swzN_add (stAddr_bounds hpre ht j).1 hb, stAddr, swzN_swzN]
  have hr : swzN (stAddr P g j.val + b) - P.sharedBase - 32768 =
      carryBase (tid g) + spread (stClass j.val) + b := by
    rw [hsw, he]
    omega
  unfold finalOwner
  rw [hlb, hr]
  exact owner_fields ht (stClass_lt j) hb

/-- The class of an offset `r` of the buffer: its bits 5, 8, 9 and 12 to 15. -/
def classOf (r : Nat) : Nat := r / 32 % 2 + 2 * (r / 256 % 4) + 8 * (r / 4096)

/-- An offset of the buffer is the sum of its thread part, its class part and its byte. -/
theorem offset_fields {r : Nat} (hr : r < 65536) :
    classOf r < 128 ∧ r = carryBase (32 * (r / 1024 % 4) + 4 * (r / 4 % 8) + r / 64 % 4) +
      spread (classOf r) + r % 4 := by
  -- the seven bit fields of `r`, from the low end
  obtain ⟨a1, b, hb, h1⟩ : ∃ a1 b, b < 4 ∧ r = 4 * a1 + b := ⟨r / 4, r % 4, by omega, by omega⟩
  obtain ⟨a2, l8, hl8, h2⟩ : ∃ a2 l8, l8 < 8 ∧ a1 = 8 * a2 + l8 :=
    ⟨a1 / 8, a1 % 8, by omega, by omega⟩
  obtain ⟨a3, c0, hc0, h3⟩ : ∃ a3 c0, c0 < 2 ∧ a2 = 2 * a3 + c0 :=
    ⟨a2 / 2, a2 % 2, by omega, by omega⟩
  obtain ⟨a4, l4, hl4, h4⟩ : ∃ a4 l4, l4 < 4 ∧ a3 = 4 * a4 + l4 :=
    ⟨a3 / 4, a3 % 4, by omega, by omega⟩
  obtain ⟨a5, c1, hc1, h5⟩ : ∃ a5 c1, c1 < 4 ∧ a4 = 4 * a5 + c1 :=
    ⟨a4 / 4, a4 % 4, by omega, by omega⟩
  obtain ⟨c2, w, hw, h6⟩ : ∃ c2 w, w < 4 ∧ a5 = 4 * c2 + w :=
    ⟨a5 / 4, a5 % 4, by omega, by omega⟩
  have d7 : r % 4 = b := by omega
  have d2 : r / 4 = a1 := by omega
  have d4 : r / 32 = a2 := by omega
  have d3 : r / 64 = a3 := by omega
  have d5 : r / 256 = a4 := by omega
  have d1 : r / 1024 = a5 := by omega
  have d6 : r / 4096 = c2 := by omega
  have t1 : a5 % 4 = w := by omega
  have t2 : a1 % 8 = l8 := by omega
  have t3 : a3 % 4 = l4 := by omega
  have t4 : a2 % 2 = c0 := by omega
  have t5 : a4 % 4 = c1 := by omega
  have hc2 : c2 < 16 := by omega
  have e0 : classOf r = 8 * c2 + 2 * c1 + c0 := by
    unfold classOf
    rw [d4, d5, d6, t4, t5]
    omega
  rw [e0, d1, d2, d3, d7, t1, t2, t3, carryBase_fields hl8 hl4, spread_fields hc1 hc0]
  omega

/-- **A byte of the buffer owned by compute thread `g` is written by one of its stores.** -/
theorem store_of_owner (hpre : Pre P L mem0) (ht : tid g < 128) {l : Loc}
    (h1 : P.sharedBase + 32768 ≤ l.addr) (h2 : l.addr < P.sharedBase + 98304)
    (ho : finalOwner P l = tid g) :
    ∃ j : Fin 128, stAddr P g j.val ≤ l.addr ∧ l.addr < stAddr P g j.val + 4 := by
  have ha := hpre.sharedAlignment
  have hb := swzN_block l.addr
  -- `r`: the offset of the byte in the buffer, before the swizzle
  obtain ⟨r, hr, hsw⟩ : ∃ r, r < 65536 ∧ swzN l.addr = P.sharedBase + 32768 + r :=
    ⟨swzN l.addr - P.sharedBase - 32768, by omega, by omega⟩
  have hf := offset_fields hr
  unfold finalOwner at ho
  rw [show swzN l.addr - P.sharedBase - 32768 = r by omega] at ho
  rw [ho] at hf
  obtain ⟨hlt, hj⟩ := stOfClass_spec ⟨classOf r, hf.1⟩
  refine ⟨⟨stOfClass (classOf r), hlt⟩, ?_⟩
  have he := stOff_eq ⟨stOfClass (classOf r), hlt⟩
  simp only at he hj
  rw [hj] at he
  have hc := carryBase_lt ht
  have hsp := spread_le hf.1
  -- the store's address before the swizzle is the entry of the byte
  have hbase : P.sharedBase + carryBase (tid g) + stOff (stOfClass (classOf r)) =
      swzN l.addr - r % 4 := by omega
  have hl : l.addr = swzN (swzN l.addr - r % 4) + r % 4 := by
    have h4 : (swzN l.addr - r % 4) % 4 = 0 := by omega
    rw [← swzN_add h4 (Nat.mod_lt _ (by decide)), show swzN l.addr - r % 4 + r % 4 = swzN l.addr
      by omega, swzN_swzN]
  simp only [stAddr, hbase]
  omega

/-! ### The branch after the second barrier, and the plane -/

/-- `%p81` (instructions 3769 to 3773): the role number is not 2, i.e. the thread is outside
the store warp. -/
theorem role_ne2 (g : Nat) :
    scmpi .ne .b (sel (scmpi .lt .u (W (tid g)) 128) (i32 0)
      (sel (scmpi .lt .u (W (tid g)) 160) (i32 1) (i32 2))) 2 = decide (tid g < 160) := by
  rw [tid_lt128, tid_lt160]
  by_cases h1 : tid g < 128
  · have h2 : tid g < 160 := by omega
    simp only [h1, h2, decide_true, Arith32.sel, ↓reduceIte]
    decide
  · by_cases h2 : tid g < 160
    · simp only [h1, h2, decide_true, decide_false, Arith32.sel, ↓reduceIte, Bool.false_eq_true]
      decide
    · simp only [h1, h2, decide_false, Arith32.sel, ↓reduceIte, Bool.false_eq_true]
      decide

/-- `%p78` (instruction 3768) in the store warp: the lane was not elected. -/
theorem elected_eq0 (g : Nat) :
    scmpi .eq .b (W (if lane g = 0 then 1 else 0)) 0 = decide (lane g ≠ 0) := by
  by_cases h : lane g = 0
  · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false, decide_false]
    decide
  · simp only [h, ↓reduceIte, ne_eq, not_false_eq_true, decide_true]
    decide

/-- The store leader is lane 0 of the store warp. -/
theorem leader_iff (g : Nat) : tid g = 160 ↔ 160 ≤ tid g ∧ lane g = 0 := by
  have := tid_lt g
  unfold tid lane at *
  omega

/-- **The plane of the final-state stores** (`mad.lo.s32` at instruction 3781): `H * seq +
head`. -/
theorem planeWord (hpre : Pre P L mem0) (hg : g < L.threads) :
    mad32 (r32 (paramBits L 13)) (sreg ((L.ctaidOf (g / L.block)).get .x))
      (sreg ((L.ctaidOf (g / L.block)).get .y)) = W (P.heads * seqOf P g + headOf P g) := by
  have h1 := plane_lt hpre hg
  have h2 := hpre.planesRange
  have h3 := seqOf_lt hpre g
  have h4 := hpre.sequencesLt
  have h5 := hpre.headsLt
  rw [Startup.headsWord hpre, ctaidX hpre hg, ctaidY hpre hg]
  exact mad32_W (by omega) (by omega) (by omega)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
