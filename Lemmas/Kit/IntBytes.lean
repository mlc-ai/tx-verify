-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Core.Thread.Access

@[expose] public section

/-! # Words of integer bytes

The bytes a load of the cache reads are bytes of integers: a byte `c < 256` of the cache
(`(bits 8 c, 0)`) or a byte of the zero fill (`(bits 32 0, k)`, `k < 4`). A list of such bytes
assembles (`littleEndianBits`) to the little-endian word of their values (`leb_ints`), and
Core's `rebuild` of eight or four of them is that word (`rebuild_ints`). -/

namespace PTX.Kit
open PTX

/-- **The value of a byte**: a cache byte `c`, or a zero-fill byte (value `0`). -/
def IntClass (b : Option Byte) (c : Nat) : Prop :=
  b = some (.bits 8 (BitVec.ofNat 64 c), 0) ∨ (c = 0 ∧ ∃ k < 4, b = some (.bits 32 0, k))

theorem byteBits_cache {c : Nat} (hc : c < 256) :
    byteBits (.bits 8 (BitVec.ofNat 64 c), 0) = some c := by
  simp [byteBits, Value.bitPattern, Value.bytes, Nat.mod_eq_of_lt hc]

theorem byteBits_fill {k : Nat} (hk : k < 4) : byteBits (.bits 32 0, k) = some 0 := by
  simp [byteBits, Value.bitPattern, Value.bytes, hk]

theorem IntClass.bits {b : Option Byte} {c : Nat} (h : IntClass b c) (hc : c < 256) :
    ∃ x, b = some x ∧ byteBits x = some c := by
  rcases h with h | ⟨rfl, k, hk, h⟩
  · subst h; exact ⟨_, rfl, byteBits_cache hc⟩
  · subst h; exact ⟨_, rfl, byteBits_fill hk⟩

/-- **The little-endian word of integer bytes.** -/
theorem leb_ints : ∀ (n : Nat) (bs : List (Option Byte)) (c : Nat → Nat), bs.length = n →
    (∀ i < n, ∃ o, bs[i]? = some o ∧ c i < 256 ∧ IntClass o (c i)) →
    ∃ y, littleEndianBits bs = some y ∧ y < 256 ^ n ∧ ∀ i < n, y / 256 ^ i % 256 = c i := by
  intro n
  induction n with
  | zero =>
    intro bs c hl _
    obtain rfl : bs = [] := List.length_eq_zero_iff.mp hl
    exact ⟨0, rfl, by simp, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    intro bs c hl h
    obtain ⟨o, bs', rfl⟩ : ∃ o bs', bs = o :: bs' := by
      cases bs with
      | nil => simp at hl
      | cons o bs' => exact ⟨o, bs', rfl⟩
    have hl' : bs'.length = n := by simpa using hl
    obtain ⟨o0, ho0, hc0, hcl0⟩ := h 0 (by omega)
    obtain rfl : o0 = o := by simpa using ho0.symm
    obtain ⟨x, rfl, hx⟩ := hcl0.bits hc0
    obtain ⟨y, hy, hlt, hdig⟩ := ih bs' (fun i => c (i + 1)) hl' fun i hi => by
      obtain ⟨o1, ho1, hc1, hcl1⟩ := h (i + 1) (by omega)
      exact ⟨o1, by simpa using ho1, hc1, hcl1⟩
    refine ⟨c 0 + 256 * y, ?_, ?_, fun i hi => ?_⟩
    · simp only [littleEndianBits, hx, hy, Option.pure_def]
      rfl
    · rw [Nat.pow_succ]
      omega
    · cases i with
      | zero => simp only [Nat.pow_zero, Nat.div_one]; omega
      | succ i =>
        have h1 : (c 0 + 256 * y) / 256 = y := by omega
        rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, h1]
        exact hdig i (by omega)

private theorem halves_ints {n : Nat} (hn : n = 4 ∨ n = 8) {bs : List (Option Byte)} {y : Nat}
    (hl : bs.length = n) (hall : bs.all intByte = true) (hno : none ∉ bs)
    (hy : littleEndianBits bs = some y) :
    rebuild.halves 2 bs = .ok (.bits (8 * n) (BitVec.ofNat 64 y)) := by
  rw [rebuild.halves]
  simp only [hno, hall, ite_false, true_or, ite_true]
  simp only [rebuildBits, hy, hl]
  rcases hn with rfl | rfl <;> rfl

/-- **Core's `rebuild` of four or eight integer bytes** is the word of their values. -/
theorem rebuild_ints {n : Nat} (hn : n = 4 ∨ n = 8) {bs : List (Option Byte)} {c : Nat → Nat}
    (hl : bs.length = n) (h : ∀ i < n, ∃ o, bs[i]? = some o ∧ c i < 256 ∧ IntClass o (c i)) :
    ∃ y, rebuild 3 bs = .ok (.bits (8 * n) (BitVec.ofNat 64 y)) ∧ y < 256 ^ n ∧
      ∀ i < n, y / 256 ^ i % 256 = c i := by
  obtain ⟨y, hy, hlt, hdig⟩ := leb_ints n bs c hl h
  have hmem : ∀ b ∈ bs, ∃ i < n, bs[i]? = some b := fun b hb => by
    obtain ⟨i, hi, hb'⟩ := List.getElem_of_mem hb
    exact ⟨i, by omega, by rw [List.getElem?_eq_getElem hi, hb']⟩
  have hall : bs.all intByte = true := by
    simp only [List.all_eq_true]
    intro b hb
    obtain ⟨i, hi, hb'⟩ := hmem b hb
    obtain ⟨o, ho, hc, hcl⟩ := h i hi
    obtain rfl : o = b := by rw [hb'] at ho; exact (Option.some.inj ho).symm
    rcases hcl with rfl | ⟨-, k, -, rfl⟩ <;> rfl
  have hno : none ∉ bs := fun hb => by
    obtain ⟨i, hi, hb'⟩ := hmem none hb
    obtain ⟨o, ho, hc, hcl⟩ := h i hi
    rw [hb'] at ho
    obtain rfl := (Option.some.inj ho)
    rcases hcl with h | ⟨-, k, -, h⟩ <;> cases h
  have hh := halves_ints hn hl hall hno hy
  refine ⟨y, ?_, hlt, hdig⟩
  obtain ⟨o0, ho0, hc0, hcl0⟩ := h 0 (by omega)
  have hbs : ∃ rest, bs = o0 :: rest := by
    cases bs with
    | nil => simp at hl; omega
    | cons o r =>
      have : o = o0 := by simpa using ho0
      exact ⟨r, by rw [this]⟩
  obtain ⟨rest, rfl⟩ := hbs
  have hn1 : ¬ (1 = n) := by omega
  rcases hcl0 with rfl | ⟨hc0', k, hk, rfl⟩
  · rw [rebuild]
    simp only [Value.bytes, hl, hn1, false_and, ite_false]
    exact hh
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [rebuild]
      simp only [Value.bytes, hl]
      split_ifs with hg
      · obtain ⟨h4, h2⟩ := hg
        have hn4 : n = 4 := by omega
        subst hn4
        rw [h2] at hy
        have h0 : littleEndianBits (List.map some (Value.bits 32 0).toBytes) = some 0 := by decide
        rw [h0] at hy
        obtain rfl : y = 0 := (Option.some.inj hy).symm
        rfl
      · exact hh
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [rebuild]
      · exact hh
      · intro v tail h
        simp at h

end PTX.Kit
