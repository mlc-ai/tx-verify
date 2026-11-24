-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSBase

@[expose] public section

/-!
# Event shapes of the softmax region: the bias loads

The region's 64 preloads (`pre j`, the first block's bias) and 64 loop loads (`nxt j`, the next
block's bias) are guarded `ld.global.b16` instructions through the 64-bit pointer registers
`%rd(193 + j)` (the current block) and `%rd(263 + j)` (the next block). Each is a read event of
two bytes at the word the pointer register holds; the pointer is a function of the state:

`biasAddr e T n j = ptrAt e T (key n) + 2 j (mod 2 ^ 64)`

is the address of word `j` of the thread's half row of block `n` (`T` is the thread's index in the
block). A preload reads block `D.n` (the state's iteration, `0`), a loop load the block after it,
`D.n + splits`. `biasAddr_nxt` says the next block's pointer register is the same function of the
next block number.

The guard of a load is not part of the shape: an event of the site means the guard held.
Which column of `Rel` the address reads, in the specification's terms, is `EvSBiasSpec`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- The address of word `j` of the thread's half row of block `n`'s bias: the row pointer plus
`2 · (128 n + j)` bytes, as the 64-bit register the code builds. -/
def biasAddr (e : Ent) (T n j : Nat) : Nat := (ptrAt e T (key n) + 2 * j) % 2 ^ 64

/-- The key offset of the block after `n` in the register of the next block's pointers. -/
theorem key_next (e : Ent) (n : Nat) :
    (e.splits * 128 + n * 128) % 4294967296 = key (n + e.splits) := by
  have : e.splits * 128 + n * 128 = (n + e.splits) * 128 := by ring
  rw [this]
  rfl

/-! ### The code of the two groups, decided -/

theorem gload_pre : ∀ j < 64, isGload (680 + 2 * j) 16 = true := by decide +kernel
theorem gload_nxt : ∀ j < 64, isGload (1124 + 2 * j) 16 = true := by decide +kernel
theorem gbase_pre : ∀ j < 64, gloadBase (680 + 2 * j) = 2141 + j := by decide +kernel
theorem gbase_nxt : ∀ j < 64, gloadBase (1124 + 2 * j) = 2211 + j := by decide +kernel
theorem glive_pre : ∀ j < 64, 2141 + j ∈ Flow.live (680 + 2 * j) := by decide +kernel
theorem glive_nxt : ∀ j < 64, 2211 + j ∈ Flow.live (1124 + 2 * j) := by decide +kernel

/-! ### The pointer registers in the table -/

/-- The scalar, 64-bit and pair sections hold no pointer register. -/
theorem keys_off_ptr (d : D) {r : Nat} (hr : (2141 ≤ r ∧ r < 2205) ∨ (2211 ≤ r ∧ r < 2275)) :
    r ∉ (valuesI L g d).map Prod.fst ∧ r ∉ (valuesS L g d).map Prod.fst ∧
      r ∉ (valuesP L g d).map Prod.fst ∧ r ∉ (valuesQ L g d).map Prod.fst := by
  refine ⟨fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · simp only [valuesI, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    omega
  · simp only [valuesS, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    omega
  · simp only [valuesP, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    omega
  · simp only [valuesQ, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range, Function.comp_apply] at hm
    rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> omega

/-- The pointer registers of the current block (`%rd193 …`): word `k` is at `2 k` bytes from the
first word's. -/
theorem valueOf_ptrCur (d : D) {k : Nat} (hk : k < 64) :
    valueOf L g d (2141 + k) = b64 (biasAddr d.e (g % L.block) d.n k) := by
  obtain ⟨hI, hS, hP, hQ⟩ := keys_off_ptr (L := L) (g := g) d (r := 2141 + k) (Or.inl ⟨by omega,
    by omega⟩)
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ hI,
    lookup_none_of_not_mem _ hS, lookup_none_of_not_mem _ hP, lookup_none_of_not_mem _ hQ,
    Option.none_or, valuesR, lookup_range_map]
  have h1 : 2141 ≤ 2141 + k ∧ 2141 + k < 2141 + 64 := by omega
  simp [h1, biasAddr]

/-- The pointer registers of the next block (`%rd263 …`). -/
theorem valueOf_ptrNxt (d : D) {k : Nat} (hk : k < 64) :
    valueOf L g d (2211 + k) = b64 (biasAddr d.e (g % L.block) (d.n + d.e.splits) k) := by
  obtain ⟨hI, hS, hP, hQ⟩ := keys_off_ptr (L := L) (g := g) d (r := 2211 + k) (Or.inr ⟨by omega,
    by omega⟩)
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ hI,
    lookup_none_of_not_mem _ hS, lookup_none_of_not_mem _ hP, lookup_none_of_not_mem _ hQ,
    Option.none_or, valuesR, lookup_range_map]
  have h1 : ¬ (2141 ≤ 2211 + k ∧ 2211 + k < 2141 + 64) := by omega
  have h2 : 2211 ≤ 2211 + k ∧ 2211 + k < 2211 + 64 := by omega
  simp [h1, h2, biasAddr]
  rw [key_next]

/-! ### The shapes -/

/-- **A preload**: two bytes of block `D.n` (the first block of the split) at `biasAddr` of the
word `j`. -/
theorem shape_pre {j : Fin 64} (hF : Fired L g d e (some u)) (hs : d.site = .pre j) :
    ∃ bs : List (Option Byte), bs.length = 2 ∧
      e = ⟨evPc d.site, .rd (globalAcc (biasAddr d.e (g % L.block) d.n j.val) 2) bs⟩ := by
  have hpc : d.site.pc = 680 + 2 * j.val := by rw [hs]; rfl
  obtain ⟨gd, hcode⟩ := isGload_spec (gload_pre j.val j.isLt)
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact hcode) hF
  rw [hpc] at hf
  have hb := gbase_pre j.val j.isLt
  have hr : t.regs (gloadBase (680 + 2 * j.val)) =
      some (b64 (biasAddr d.e (g % L.block) d.n j.val)) := by
    rw [hb, reg_at h (by rw [hpc]; exact glive_pre j.val j.isLt), valueOf_ptrCur d j.isLt]
  have hxl : biasAddr d.e (g % L.block) d.n j.val < 2 ^ 64 := Nat.mod_lt _ (by decide)
  obtain ⟨bs, hl, he⟩ := fires_ld_global rfl h.2.1 hr hxl (Or.inl rfl) hf
  exact ⟨bs, hl, by rw [he, evPc, hpc]⟩

/-- **A loop load**: two bytes of block `D.n + splits` (the block after the state's) at
`biasAddr` of the word `j`. -/
theorem shape_nxt {j : Fin 64} (hF : Fired L g d e (some u)) (hs : d.site = .nxt j) :
    ∃ bs : List (Option Byte), bs.length = 2 ∧
      e = ⟨evPc d.site, .rd (globalAcc
        (biasAddr d.e (g % L.block) (d.n + d.e.splits) j.val) 2) bs⟩ := by
  have hpc : d.site.pc = 1124 + 2 * j.val := by rw [hs]; rfl
  obtain ⟨gd, hcode⟩ := isGload_spec (gload_nxt j.val j.isLt)
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact hcode) hF
  rw [hpc] at hf
  have hb := gbase_nxt j.val j.isLt
  have hr : t.regs (gloadBase (1124 + 2 * j.val)) =
      some (b64 (biasAddr d.e (g % L.block) (d.n + d.e.splits) j.val)) := by
    rw [hb, reg_at h (by rw [hpc]; exact glive_nxt j.val j.isLt), valueOf_ptrNxt d j.isLt]
  have hxl : biasAddr d.e (g % L.block) (d.n + d.e.splits) j.val < 2 ^ 64 :=
    Nat.mod_lt _ (by decide)
  obtain ⟨bs, hl, he⟩ := fires_ld_global rfl h.2.1 hr hxl (Or.inl rfl) hf
  exact ⟨bs, hl, by rw [he, evPc, hpc]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
