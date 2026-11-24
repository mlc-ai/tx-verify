-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! # The global use counter of a ring whose items make several uses

A proof tool for a ring of `S` slots that a producer and a consumer walk through across work
items, item `i` making `m i` uses (FA4's KV ring: `S = 6`, `m i = 2 n` with `n` symbolic). Use `u`
of item `j` is the ring's use number `useIndex m j u = (Σ_{i<j} m i) + u` (`useIndex`); it is in
slot `useIndex % S` and in round `useIndex / S` of that slot, so the slot's objects are in phase
`round` and their parity is `round % 2`.

* The counter runs on across items (`useIndex_succ`, `useIndex_zero`), is `j * c + u` for a fixed
  count `c` (`useIndex_const`), and is injective and order preserving on the uses of the items
  (`useIndex_lt`, `useIndex_inj`).
* The use `S` later is in the same slot and the next round, of the other parity (`slot_add`,
  `round_add`, `parity_add`); the uses of one slot are `k * S + s` (`useIndex_of_slot`).
* With an even ring and even per-item counts, the slot's parity is the use's parity
  (`slot_parity`): FA4's K uses (even `u`) and V uses (odd `u`) keep to even and odd slots.
* After `T` uses, slot `s`'s next use is `nextUse S T s ∈ [T, T + S)` and, when `S ≤ T`, its last
  use is `nextUse S T s - S < T` (`nextUse_slot`, `nextUse_ge`, `nextUse_lt`): a tail that waits for
  the release of every slot waits for the release of each slot's last use. -/

namespace PTX.MbarRing.Index

/-- The ring's use number of use `u` of item `j`, when item `i` makes `m i` uses. -/
def useIndex (m : Nat → Nat) (j u : Nat) : Nat := (∑ i ∈ Finset.range j, m i) + u

/-- The slot of a use number in a ring of `S` slots. -/
def slot (S idx : Nat) : Nat := idx % S

/-- The round of a use number in its slot: the phase of the slot's objects at that use. -/
def round (S idx : Nat) : Nat := idx / S

/-- The next use number of slot `s` from use number `T` on. -/
def nextUse (S T s : Nat) : Nat := T + (s + S - T % S) % S

variable {m : Nat → Nat}

theorem useIndex_zero (u : Nat) : useIndex m 0 u = u := by simp [useIndex]

/-- **The counter runs on across items.** -/
theorem useIndex_succ (j u : Nat) : useIndex m (j + 1) u = useIndex m j (m j + u) := by
  simp only [useIndex, Finset.sum_range_succ]
  omega

/-- The counter with a fixed count `c` of uses per item. -/
theorem useIndex_const (c j u : Nat) : useIndex (fun _ => c) j u = j * c + u := by
  simp [useIndex, Finset.sum_const, Finset.card_range]

/-- The first use of a later item is past every use of an earlier one. -/
theorem useIndex_le_of_lt {j j' : Nat} (h : j < j') (u : Nat) (hu : u < m j) :
    useIndex m j u < useIndex m j' 0 := by
  induction j' with
  | zero => omega
  | succ j' ih =>
    rw [useIndex_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · have := ih h
      simp only [useIndex] at this ⊢
      omega
    · simp only [useIndex]
      omega

/-- **The counter preserves the order of uses**: lexicographic in (item, use). -/
theorem useIndex_lt {j j' u u' : Nat} (hu : u < m j)
    (h : j < j' ∨ (j = j' ∧ u < u')) : useIndex m j u < useIndex m j' u' := by
  rcases h with h | ⟨rfl, h⟩
  · have := useIndex_le_of_lt h u hu
    simp only [useIndex] at this ⊢
    omega
  · simp only [useIndex]
    omega

/-- **Distinct uses have distinct use numbers.** -/
theorem useIndex_inj {j j' u u' : Nat} (hu : u < m j) (hu' : u' < m j')
    (h : useIndex m j u = useIndex m j' u') : j = j' ∧ u = u' := by
  rcases Nat.lt_trichotomy j j' with hj | rfl | hj
  · have := useIndex_lt hu (.inl hj) (u' := u')
    omega
  · simp only [useIndex] at h
    exact ⟨rfl, by omega⟩
  · have := useIndex_lt hu' (.inl hj) (u' := u)
    omega

/-- The use `S` later is in the same slot. -/
theorem slot_add (S idx : Nat) : slot S (idx + S) = slot S idx := by
  simp [slot]

/-- The use `S` later is in the next round. -/
theorem round_add {S : Nat} (hS : 0 < S) (idx : Nat) : round S (idx + S) = round S idx + 1 := by
  simp only [round]
  rw [Nat.add_div_right _ hS]

/-- The use `S` later is in a round of the other parity. -/
theorem parity_add {S : Nat} (hS : 0 < S) (idx : Nat) :
    round S (idx + S) % 2 = (round S idx + 1) % 2 := by
  rw [round_add hS]

/-- The `k`-th use of slot `s < S` is use number `k * S + s`. -/
theorem useIndex_of_slot {S s : Nat} (hs : s < S) (k : Nat) :
    slot S (k * S + s) = s ∧ round S (k * S + s) = k := by
  have hS : 0 < S := by omega
  refine ⟨?_, ?_⟩
  · simp only [slot]
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  · simp only [round]
    rw [Nat.mul_comm, Nat.mul_add_div hS, Nat.div_eq_of_lt hs, Nat.add_zero]

/-- A use number is determined by its slot and round. -/
theorem eq_of_slot_round {S a b : Nat} (hs : slot S a = slot S b) (hr : round S a = round S b) :
    a = b := by
  simp only [slot, round] at hs hr
  rw [← Nat.div_add_mod a S, ← Nat.div_add_mod b S, hs, hr]

/-- **With an even ring and even per-item counts, the slot's parity is the use's parity.** -/
theorem slot_parity {S : Nat} (hS : S % 2 = 0) (hm : ∀ i, m i % 2 = 0) (j u : Nat) :
    slot S (useIndex m j u) % 2 = u % 2 := by
  have hsum : (∑ i ∈ Finset.range j, m i) % 2 = 0 := by
    rw [Finset.sum_nat_mod]
    simp [hm]
  simp only [slot, useIndex]
  rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hS)]
  omega

/-- FA4's KV ring: `2 n` uses per item in `6` slots. -/
theorem kv_slot (n j u : Nat) :
    slot 6 (useIndex (fun _ => 2 * n) j u) = (2 * n * j + u) % 6 ∧
      slot 6 (useIndex (fun _ => 2 * n) j u) % 2 = u % 2 := by
  refine ⟨?_, slot_parity (by decide) (fun _ => by omega) j u⟩
  simp only [slot, useIndex_const]
  rw [Nat.mul_comm j]

/-- **Slot `s`'s next use from `T` on is in slot `s`.** -/
theorem nextUse_slot {S s : Nat} (hs : s < S) (T : Nat) : slot S (nextUse S T s) = s := by
  have hS : 0 < S := by omega
  have hT := Nat.mod_lt T hS
  simp only [slot, nextUse]
  rw [Nat.add_mod, Nat.mod_mod]
  have key : (T % S + (s + S - T % S) % S) % S = s := by
    by_cases h : T % S ≤ s
    · rw [show s + S - T % S = (s - T % S) + S by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : s - T % S < S)]
      rw [show T % S + (s - T % S) = s by omega, Nat.mod_eq_of_lt hs]
    · rw [Nat.mod_eq_of_lt (by omega : s + S - T % S < S),
        show T % S + (s + S - T % S) = s + S by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hs]
  exact key

/-- Slot `s`'s next use is not before `T`. -/
theorem nextUse_ge (S T s : Nat) : T ≤ nextUse S T s := by
  simp only [nextUse]
  omega

/-- Slot `s`'s next use is within the `S` uses from `T` on. -/
theorem nextUse_lt {S : Nat} (hS : 0 < S) (T s : Nat) : nextUse S T s < T + S := by
  simp only [nextUse]
  have := Nat.mod_lt (s + S - T % S) hS
  omega

/-- **Slot `s`'s last use before `T`** is `S` uses before its next one, when `S ≤ T`. -/
theorem lastUse {S s : Nat} (hs : s < S) {T : Nat} (hT : S ≤ T) :
    S ≤ nextUse S T s ∧ nextUse S T s - S < T ∧ slot S (nextUse S T s - S) = s ∧
      round S (nextUse S T s - S) + 1 = round S (nextUse S T s) := by
  have hS : 0 < S := by omega
  have hge := nextUse_ge S T s
  have hlt := nextUse_lt hS T s
  have hsl := nextUse_slot hs T
  have hsub : nextUse S T s - S + S = nextUse S T s := by omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [← slot_add S, hsub, hsl]
  · rw [← round_add hS, hsub]

end PTX.MbarRing.Index
