-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaACell

@[expose] public section

/-! # The cells of an M = 256 `cta_group::2` MMA

An MMA of `cta_group::2` with M = 256 writes output `(row, col)` at lane `row % 128` of the
group's low CTA (`row < 128`) or high CTA, at column `base % 2^16 + col` (`resultCell_pair`); with
zero lane masks it writes every result cell (`writeCell_zero`). Element `(row, k)` of a 16-bit A
operand in Tensor Memory at `address` is byte `2 (k % 2)` of the word at the same lane and CTA,
column `address % 2^16 + k / 2` (`aCell_pair_elem`). -/

namespace PTX.TcMma

/-- The CTA of output row `row` of a `cta_group::2` MMA. -/
def rowCta (s : OperandSpec) (row : Nat) : Nat := if row < 128 then s.lowCta else s.highCta

/-- **The result cells of an M = 256 `cta_group::2` MMA.** -/
theorem resultCell_pair {s : OperandSpec} {base row col : Nat} {c : Cell}
    (hm : s.descriptor.m = 256) (hg : s.descriptor.group = .two)
    (h : resultCell s base row col = some c) :
    row < 256 ∧ col < s.descriptor.n ∧ c = ⟨rowCta s row, row % 128, base % 2 ^ 16 + col⟩ ∧
      ∀ col', col' < s.descriptor.n →
        resultCell s base row col' = some ⟨rowCta s row, row % 128, base % 2 ^ 16 + col'⟩ := by
  have hsz : s.descriptor.group.size = 2 := by rw [hg]; rfl
  unfold resultCell at h ⊢
  dsimp only at h ⊢
  rw [hsz, hm] at h ⊢
  split at h
  · rename_i hc
    simp only [show (128 * 2 = 256) from rfl, ↓reduceIte, show 256 / 2 = 128 from rfl,
      Option.some.injEq] at h
    have hres : resultColumns s.descriptor = s.descriptor.n := by
      simp [resultColumns, hm, hsz]
    refine ⟨hc.2.2.1, hc.2.2.2.1, h.symm, fun col' hcol' => ?_⟩
    simp only [hc.1, hc.2.1, hc.2.2.1, hcol', hc.2.2.2.2, and_self, ↓reduceIte,
      show (128 * 2 = 256) from rfl, show 256 / 2 = 128 from rfl, rowCta]
  · cases h

/-- **With zero lane masks an MMA writes every result cell.** -/
theorem writeCell_zero {s : OperandSpec} {base row col : Nat} (hm : s.descriptor.m = 256)
    (hg : s.descriptor.group = .two) :
    writeCell s base (List.replicate 8 0) row col = resultCell s base row col := by
  have hsz : s.descriptor.group.size = 2 := by rw [hg]; rfl
  have hv : OutputMaskValid s.descriptor.group (List.replicate 8 0) := by
    rw [hg]
    exact ⟨rfl, by simp⟩
  unfold writeCell
  simp only [hv, not_true_eq_false, ↓reduceIte]
  cases hr : resultCell s base row col with
  | none => rfl
  | some c =>
    obtain ⟨hrow, -, rfl, -⟩ := resultCell_pair hm hg hr
    have hl : (row / (s.descriptor.m / s.descriptor.group.size) * 128 + row % 128) / 32 < 8 := by
      rw [hm, hsz]
      omega
    show (List.replicate 8 0)[(row / (s.descriptor.m / s.descriptor.group.size) * 128 +
        row % 128) / 32]?.bind _ = _
    rw [List.getElem?_replicate_of_lt hl]
    simp

/-- **The A cell of a 16-bit element in Tensor Memory.** -/
theorem aCell_pair_elem {s : OperandSpec} {address row k pos : Nat} {c : Cell}
    (hm : s.descriptor.m = 256) (hg : s.descriptor.group = .two)
    (ha : s.aTmem = some address) (hk : k < 16)
    (h : aCell s (2 * (row * 16 + k)) = some (c, pos)) :
    c = ⟨rowCta s row, row % 128, address % 2 ^ 16 + k / 2⟩ ∧ pos = 2 * (k % 2) := by
  have hsz : s.descriptor.group.size = 2 := by rw [hg]; rfl
  have hhd : halfDatapath s.descriptor = false := by simp [halfDatapath, hg]
  have hb := row_bytes s.descriptor.kind
  unfold aCell at h
  dsimp only at h
  rw [hb, ha] at h
  simp only [Option.bind_some, hhd, Bool.false_eq_true, ↓reduceIte, hsz, hm] at h
  have h1 : 2 * (row * 16 + k) / 32 = row := by omega
  have h2 : 2 * (row * 16 + k) % 32 / 4 = k / 2 := by omega
  have h3 : 2 * (row * 16 + k) % 32 % 4 = 2 * (k % 2) := by omega
  rw [h1, h2, h3] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq, show 256 / 2 = 128 from rfl] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · cases h

end PTX.TcMma
