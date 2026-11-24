-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaResultLayout
public import Core.Tc.TcMmaOperands

@[expose] public section

/-! # The Tensor Memory cells of an A operand

Every kind reads 32 bytes per operand row (`row_bytes`), so the two bytes of a 16-bit element
(`2 n`, `2 n + 1`) are bytes `p` and `p + 1` of one Tensor Memory word, with `p` even
(`aCell_pair`); outside the half datapath an A row lies in lanes `0 … 127` of its CTA
(`aCell_lane`); and an A operand in Tensor Memory has no shared byte (`byteLoc_a_tmem`). -/

namespace PTX.TcMma

/-- Every kind reads 32 bytes per operand row. -/
theorem row_bytes (k : Kind) : k.k * k.width = 32 := by
  cases k <;> rfl

/-- **The two bytes of a 16-bit A element are adjacent bytes of one word.** -/
theorem aCell_pair {s : OperandSpec} {n : Nat} {c : Cell} {p : Nat}
    (h : aCell s (2 * n) = some (c, p)) :
    aCell s (2 * n + 1) = some (c, p + 1) ∧ p % 2 = 0 ∧ p + 1 < 4 := by
  have hb := row_bytes s.descriptor.kind
  unfold aCell at h ⊢
  dsimp only at h ⊢
  rw [hb] at h ⊢
  have h1 : (2 * n + 1) / 32 = 2 * n / 32 := by omega
  have h2 : (2 * n + 1) % 32 / 4 = 2 * n % 32 / 4 := by omega
  have h3 : (2 * n + 1) % 32 % 4 = 2 * n % 32 % 4 + 1 := by omega
  rw [h1, h2, h3]
  cases ha : s.aTmem with
  | none => simp [ha] at h
  | some address =>
    simp only [ha, Option.bind_some] at h ⊢
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by rw [ite_eq_left hc], by omega, by omega⟩
    · cases h

/-- An A operand in Tensor Memory has no shared byte. -/
theorem byteLoc_a_tmem {s : OperandSpec} (h : s.aTmem.isSome = true) (index : Nat) :
    s.byteLoc .a index = none := by
  unfold OperandSpec.byteLoc
  simp [h]

/-- **Outside the half datapath an A row lies in the first 128 lanes.** -/
theorem aCell_lane {s : OperandSpec} {index : Nat} {c : Cell} {p : Nat}
    (hh : halfDatapath s.descriptor = false) (h : aCell s index = some (c, p)) : c.lane < 128 := by
  unfold aCell at h
  dsimp only at h
  cases ha : s.aTmem with
  | none => simp [ha] at h
  | some address =>
    simp only [ha, Option.bind_some, hh, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Nat.mod_lt _ (by decide)
    · cases h

end PTX.TcMma
