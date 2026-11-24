-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The items of a pair TMA ring slot

A proof tool for a ring slot fed by TMA copies from both CTAs of a `cta_group::2` pair onto the
leader CTA's full barrier: per use, the leader's producer arrives once (`expect_tx` of all the
use's bytes) and each CTA's producer issues `n` copies completing on that barrier (GEMM's input
ring: `n = 3`; FA4's Q ring: `n = 2`; FA4's KV ring: `n = 2` on its K slots, `n = 1` on its V
slots). A phase of the full barrier is completed by items of `1 + 2 n` kinds (`Kind n`): the
leader's arrival (kind `0`) and the copies of producer `a` with index `j < n` (kind
`copyKind n a j = 1 + n · a + j`).

* `kOwner n k`: the producer of kind `k` (the leader for the arrival and its copies).
* `kIdx n k u`: the count of earlier events of its kind before the item of kind `k` and use
  `u`: the use for the arrival, `n` per use plus the copy's index for a copy.
* The copy kinds name their producer and index (`kOwner_copyKind`, `kIdx_copyKind`), are not
  the arrival (`copyKind_ne`), and every other kind is one (`eq_copyKind`). -/

namespace PTX.PairTmaRing

/-- The kinds of items of one phase of the full barrier, with `n` copies per CTA. -/
abbrev Kind (n : Nat) : Type := Fin (1 + 2 * n)

/-- The producer of kind `k`: the leader for the arrival and its own copies, else the peer. -/
def kOwner (n : Nat) (k : Kind n) : Fin 2 := if k.val < 1 + n then 0 else 1

/-- The count of earlier events of its kind of the item of kind `k` and use `u`. -/
def kIdx (n : Nat) (k : Kind n) (u : Nat) : Nat := if k.val = 0 then u else n * u + (k.val - 1) % n

/-- The kind of producer `a`'s copy with index `j`. -/
def copyKind (n : Nat) (a : Fin 2) (j : Nat) (hj : j < n) : Kind n :=
  ⟨1 + n * a.val + j, by have := a.isLt; rcases (show a.val = 0 ∨ a.val = 1 by omega) with h | h <;>
    rw [h] <;> omega⟩

variable {n : Nat}

theorem kOwner_zero (hn : 0 < n) : kOwner n ⟨0, by omega⟩ = 0 := by
  simp [kOwner]

theorem kIdx_zero (u : Nat) : kIdx n ⟨0, by omega⟩ u = u := by
  simp [kIdx]

theorem kOwner_copyKind (a : Fin 2) (j : Nat) (hj : j < n) : kOwner n (copyKind n a j hj) = a := by
  unfold kOwner copyKind
  have := a.isLt
  rcases (show a.val = 0 ∨ a.val = 1 by omega) with h | h <;> split <;> apply Fin.ext <;>
    simp_all

theorem kIdx_copyKind (a : Fin 2) (j : Nat) (hj : j < n) (u : Nat) :
    kIdx n (copyKind n a j hj) u = n * u + j := by
  unfold kIdx copyKind
  have := a.isLt
  simp only [Nat.add_eq_zero_iff, one_ne_zero, false_and, ↓reduceIte]
  rcases (show a.val = 0 ∨ a.val = 1 by omega) with h | h <;> rw [h]
  · simp [Nat.mod_eq_of_lt hj]
  · rw [show 1 + n * 1 + j - 1 = j + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj]

theorem copyKind_ne (a : Fin 2) (j : Nat) (hj : j < n) : (copyKind n a j hj).val ≠ 0 := by
  simp [copyKind]

/-- **Every kind other than the arrival is a copy kind.** -/
theorem eq_copyKind (k : Kind n) (hk : k.val ≠ 0) :
    ∃ (a : Fin 2) (j : Nat) (hj : j < n), k = copyKind n a j hj := by
  have hk' := k.isLt
  by_cases h : k.val < 1 + n
  · exact ⟨0, k.val - 1, by omega, Fin.ext (by simp [copyKind]; omega)⟩
  · exact ⟨1, k.val - 1 - n, by omega, Fin.ext (by simp [copyKind]; omega)⟩

end PTX.PairTmaRing
