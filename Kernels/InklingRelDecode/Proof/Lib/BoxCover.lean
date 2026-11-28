-- SPDX-License-Identifier: Apache-2.0
module

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- **Eight disjoint 8192-byte boxes inside the K and V tiles of a slot cover them.** Counting:
the boxes hold 65536 bytes and the two tiles have no more. -/
theorem boxes_cover {kb vb : Nat} (hkv : kb + 32768 ≤ vb) (a : Fin 8 → Nat)
    (hin : ∀ i, ∀ t < 8192, (kb ≤ a i + t ∧ a i + t < kb + 32768) ∨
      (vb ≤ a i + t ∧ a i + t < vb + 32768))
    (hd : ∀ i j, i ≠ j → a i + 8192 ≤ a j ∨ a j + 8192 ≤ a i) {x : Nat}
    (hx : (kb ≤ x ∧ x < kb + 32768) ∨ (vb ≤ x ∧ x < vb + 32768)) :
    ∃ i, a i ≤ x ∧ x < a i + 8192 := by
  by_contra none
  push Not at none
  let T : Finset Nat := (Finset.Ico kb (kb + 32768) ∪ Finset.Ico vb (vb + 32768)).erase x
  have hT : T.card = 65535 := by
    have hx' : x ∈ Finset.Ico kb (kb + 32768) ∪ Finset.Ico vb (vb + 32768) := by
      simp only [Finset.mem_union, Finset.mem_Ico]
      exact hx
    rw [Finset.card_erase_of_mem hx', Finset.card_union_of_disjoint]
    · simp
    · exact Finset.disjoint_left.mpr fun y h1 h2 => by
        simp only [Finset.mem_Ico] at h1 h2
        omega
  have hS : (Finset.univ.biUnion fun i : Fin 8 => Finset.Ico (a i) (a i + 8192)).card = 65536 := by
    rw [Finset.card_biUnion]
    · simp
    · intro i _ j _ ne
      exact Finset.disjoint_left.mpr fun y h1 h2 => by
        simp only [Finset.mem_Ico] at h1 h2
        rcases hd i j ne with h | h <;> omega
  have sub : (Finset.univ.biUnion fun i : Fin 8 => Finset.Ico (a i) (a i + 8192)) ⊆ T := by
    intro y hy
    simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_univ, true_and] at hy
    obtain ⟨i, h1, h2⟩ := hy
    have := hin i (y - a i) (by omega)
    simp only [T, Finset.mem_erase, Finset.mem_union, Finset.mem_Ico]
    refine ⟨fun h => ?_, ?_⟩
    · have := none i
      omega
    · omega
  have := Finset.card_le_card sub
  omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
