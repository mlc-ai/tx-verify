-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.TcMma

/-- A single-CTA MMA layout assigns a different cell to each distinct matrix coordinate.
This covers the full, half and blocked datapath forms and is independent of the mask. -/
theorem resultCell_one_injective {s : OperandSpec} (hGroup : s.descriptor.group = .one)
    {base row col row' col' : Nat} {cell : Cell}
    (h : resultCell s base row col = some cell)
    (h' : resultCell s base row' col' = some cell) :
    row = row' ∧ col = col' := by
  let a := base / 2 ^ 16
  let b := base % 2 ^ 16
  have hsize : s.descriptor.group.size = 1 := by simp [hGroup, CtaGroup.size]
  change (if Valid s.descriptor ∧ LaneAligned s.descriptor a ∧ row < s.descriptor.m ∧
    col < s.descriptor.n ∧ b + resultColumns s.descriptor ≤ 512
    then _ else none) = some cell at h
  change (if Valid s.descriptor ∧ LaneAligned s.descriptor a ∧ row' < s.descriptor.m ∧
    col' < s.descriptor.n ∧ b + resultColumns s.descriptor ≤ 512
    then _ else none) = some cell at h'
  split at h
  swap
  · cases h
  split at h'
  swap
  · cases h'
  rename_i hValid hValid'
  obtain ⟨_, _, hr, _, _⟩ := hValid
  obtain ⟨_, _, hr', _, _⟩ := hValid'
  simp only [hsize, Nat.div_one, Nat.mul_one] at h h'
  by_cases hm : s.descriptor.m = 128
  · have hEq : (⟨s.lowCta, row, b + col⟩ : Cell) = ⟨s.lowCta, row', b + col'⟩ := by
      have hR : row < 128 := by omega
      have hR' : row' < 128 := by omega
      have hr0 := Nat.mod_eq_of_lt hR
      have hr1 := Nat.mod_eq_of_lt hR'
      have hA : (⟨s.lowCta, row, b + col⟩ : Cell) = cell := by
        simpa only [hR, ↓reduceIte, hm, hr0, Option.some.injEq] using h
      have hB : (⟨s.lowCta, row', b + col'⟩ : Cell) = cell := by
        simpa only [hR', ↓reduceIte, hm, hr1, Option.some.injEq] using h'
      exact hA.trans hB.symm
    exact ⟨congrArg Cell.lane hEq, Nat.add_left_cancel (congrArg Cell.column hEq)⟩
  · by_cases hf : halfDatapath s.descriptor = true
    · have hA : (⟨s.lowCta, a + row % 16 + 32 * (row / 16), b + col⟩ : Cell) = cell := by
        simpa only [hr, ↓reduceIte, hm, hf, Nat.mod_eq_of_lt hr,
          Option.some.injEq] using h
      have hB : (⟨s.lowCta, a + row' % 16 + 32 * (row' / 16), b + col'⟩ : Cell) = cell := by
        simpa only [hr', ↓reduceIte, hm, hf, Nat.mod_eq_of_lt hr',
          Option.some.injEq] using h'
      have hEq := hA.trans hB.symm
      have hLane := congrArg Cell.lane hEq
      dsimp only at hLane
      exact ⟨by omega, Nat.add_left_cancel (congrArg Cell.column hEq)⟩
    · have hFalse : halfDatapath s.descriptor = false := by simpa using hf
      let width := s.descriptor.n / columnBlocks s.descriptor
      have hA : (⟨s.lowCta, row + s.descriptor.m * (col / width), b + col % width⟩ : Cell)
          = cell := by
        simpa only [hr, ↓reduceIte, hm, hFalse, Bool.false_eq_true, Nat.mod_eq_of_lt hr,
          Option.some.injEq, width] using h
      have hB : (⟨s.lowCta, row' + s.descriptor.m * (col' / width), b + col' % width⟩ : Cell)
          = cell := by
        simpa only [hr', ↓reduceIte, hm, hFalse, Bool.false_eq_true, Nat.mod_eq_of_lt hr',
          Option.some.injEq, width] using h'
      have hEq := hA.trans hB.symm
      have hLane := congrArg Cell.lane hEq
      have hColumn : col % width = col' % width :=
        Nat.add_left_cancel (congrArg Cell.column hEq)
      have hRow : row = row' := by
        have he := congrArg (· % s.descriptor.m) hLane
        change (row + s.descriptor.m * (col / width)) % s.descriptor.m =
          (row' + s.descriptor.m * (col' / width)) % s.descriptor.m at he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] using he
      have hQuot : col / width = col' / width := by
        rw [hRow] at hLane
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < s.descriptor.m)
          (Nat.add_left_cancel hLane)
      have hSum := Nat.div_add_mod col width
      have hSum' := Nat.div_add_mod col' width
      rw [hQuot, hColumn] at hSum
      exact ⟨hRow, hSum.symm.trans hSum'⟩

/-- A mask can omit cells, while the cells that are written retain the layout's injectivity. -/
theorem writeCell_one_injective {s : OperandSpec} (hGroup : s.descriptor.group = .one)
    {base row col row' col' : Nat} {mask : List Nat} {cell : Cell}
    (h : writeCell s base mask row col = some cell)
    (h' : writeCell s base mask row' col' = some cell) :
    row = row' ∧ col = col' :=
  resultCell_one_injective hGroup (writeCell_resultCell h) (writeCell_resultCell h')

end PTX.TcMma
