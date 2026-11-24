-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaResultLayout

@[expose] public section

namespace PTX.TcMma

/-- The 2x2 and 1x4 datapath layouts (B, E, G): 32 or 64 rows per CTA, `128 / r` column
blocks covering the 128 lanes, and N a positive multiple of the block count. -/
theorem blocked_shape {d : Descriptor} (hv : Valid d) (hm : ¬ d.m = 128 * d.group.size)
    (hf : halfDatapath d = false) :
    (d.m / d.group.size = 32 ∧ columnBlocks d = 4 ∨ d.m / d.group.size = 64 ∧ columnBlocks d = 2) ∧
      0 < d.n / columnBlocks d ∧ d.n % columnBlocks d = 0 := by
  obtain ⟨hs, -⟩ := hv
  obtain ⟨g, k, m, n, _, _, _, _, ws⟩ := d
  simp only [columnBlocks, halfDatapath] at hf ⊢
  cases g <;> cases ws <;> cases k <;>
    simp [shapeOk, CtaGroup.size] at hs hm hf ⊢
  all_goals
    obtain ⟨hm', hn'⟩ := hs
    rcases hm' with rfl | rfl | rfl <;> simp at hm hf ⊢ <;> omega

/-- Layout F rows reach at most lane 111 above the alignment. -/
theorem layoutF_lane {row : Nat} (hr : row < 64) : row % 16 + 32 * (row / 16) < 112 := by
  omega

/-- Every represented result cell fits the physical TMEM lane and column bounds. -/
theorem resultCell_bounds {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (h : resultCell s base row col = some cell) : cell.lane < 128 ∧ cell.column < 512 := by
  unfold resultCell at h
  dsimp only at h
  split at h
  next hg =>
    obtain ⟨hv, hl, hr, hc, hb⟩ := hg
    by_cases hm : s.descriptor.m = 128 * s.descriptor.group.size
    · simp only [hm, ↓reduceIte, Option.some.injEq] at h
      subst cell
      simp only [resultColumns, hm, true_or, ↓reduceIte] at hb
      exact ⟨Nat.mod_lt row (by decide), by dsimp only; omega⟩
    · by_cases hf : halfDatapath s.descriptor = true
      · simp only [hm, hf, ↓reduceIte, Option.some.injEq] at h
        subst cell
        simp only [resultColumns, hf, or_true, ↓reduceIte] at hb
        have h64 : s.descriptor.m / s.descriptor.group.size = 64 := by
          simp only [halfDatapath, decide_eq_true_eq] at hf
          obtain ⟨hg, hm', -⟩ := hf
          simp [hg, hm', CtaGroup.size]
        have := layoutF_lane (row := row % (s.descriptor.m / s.descriptor.group.size))
          (by rw [h64]; exact Nat.mod_lt _ (by decide))
        rcases hl with hl | ⟨-, hl⟩ <;> exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · have hf' : halfDatapath s.descriptor = false := by simpa using hf
        simp only [hm, hf', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst cell
        obtain ⟨hrb, hq0, hdiv⟩ := blocked_shape hv hm hf'
        have hnq : s.descriptor.n =
            columnBlocks s.descriptor * (s.descriptor.n / columnBlocks s.descriptor) :=
          (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdiv)).symm
        have hcmod := Nat.mod_lt col hq0
        simp only [resultColumns, hm, hf', Bool.false_eq_true, or_false, ↓reduceIte] at hb
        rcases hrb with ⟨hr', hB⟩ | ⟨hr', hB⟩ <;> rw [hr'] <;> rw [hB] at hnq hcmod hq0 hb ⊢
        · have hq : col / (s.descriptor.n / 4) < 4 :=
            (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
          have hmod := Nat.mod_lt row (by decide : 0 < 32)
          constructor <;> dsimp <;> omega
        · have hq : col / (s.descriptor.n / 2) < 2 :=
            (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
          have hmod := Nat.mod_lt row (by decide : 0 < 64)
          constructor <;> dsimp <;> omega
  next hg => simp at h

/-- Layout D (cta_group::1, M = 128): row `i`, column `j` is lane `i`, column `base + j` of
the issuer's CTA. -/
theorem resultCell_layoutD {s : OperandSpec} {base row col : Nat}
    (hg : s.descriptor.group = .one) (hm : s.descriptor.m = 128) (hv : Valid s.descriptor) :
    resultCell s base row col =
      if row < 128 ∧ col < s.descriptor.n ∧ base + s.descriptor.n ≤ 512 then
        some ⟨s.lowCta, row, base + col⟩ else none := by
  have hf : halfDatapath s.descriptor = false := by simp [halfDatapath, hm, hg]
  unfold resultCell
  simp only [resultColumns, hg, hm, CtaGroup.size, Nat.mul_one, true_or, ↓reduceIte, Nat.div_one]
  by_cases h : row < 128 ∧ col < s.descriptor.n ∧ base + s.descriptor.n ≤ 512
  · have hb : base < 65536 := by omega
    have hl : base / 2 ^ 16 = 0 := by omega
    have hc : base % 2 ^ 16 = base := by omega
    simp only [hl, hc, LaneAligned, true_or, hv, h, and_self, ↓reduceIte, Nat.mod_eq_of_lt h.1]
  · rw [ite_eq_right h, ite_eq_right]
    simp only [hv, true_and, not_and, LaneAligned, hf, Bool.false_eq_true, false_and, or_false]
    intro hl hr hc
    omega

/-- Layout F (cta_group::1, M = 64): row `i`, column `j` is lane
`alignment + i % 16 + 32 (i / 16)`, column `base % 2^16 + j` of the issuer's CTA. -/
theorem resultCell_layoutF {s : OperandSpec} {base row col : Nat}
    (hg : s.descriptor.group = .one) (hm : s.descriptor.m = 64) (hw : s.descriptor.ws = false)
    (hv : Valid s.descriptor)
    (hl : base / 2 ^ 16 = 0 ∨ base / 2 ^ 16 = 16) (hr : row < 64) (hc : col < s.descriptor.n)
    (hb : base % 2 ^ 16 + s.descriptor.n ≤ 512) :
    resultCell s base row col =
      some ⟨s.lowCta, base / 2 ^ 16 + row % 16 + 32 * (row / 16), base % 2 ^ 16 + col⟩ := by
  have hf : halfDatapath s.descriptor = true := by simp [halfDatapath, hg, hm, hw]
  have hla : LaneAligned s.descriptor (base / 2 ^ 16) := by
    rcases hl with hl | hl
    · exact .inl hl
    · exact .inr ⟨hf, hl⟩
  unfold resultCell
  simp only [resultColumns, hg, hm, CtaGroup.size, hf, or_true, ↓reduceIte, Nat.div_one]
  rw [ite_eq_left ⟨hv, hla, hr, hc, hb⟩]
  simp [hr, Nat.mod_eq_of_lt hr]

/-- A result cell is in one of the group's CTAs. -/
theorem resultCell_cta {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (h : resultCell s base row col = some cell) : cell.cta = s.lowCta ∨ cell.cta = s.highCta := by
  unfold resultCell at h
  dsimp only at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst cell; dsimp only; split <;> simp
    · split at h <;>
      · simp only [Option.some.injEq] at h
        subst cell; dsimp only; split <;> simp
  · simp at h

/-- An unmasked write is a result cell. -/
theorem writeCell_resultCell {s : OperandSpec} {base : Nat} {mask : List Nat} {row col : Nat}
    {cell : Cell} (h : writeCell s base mask row col = some cell) :
    resultCell s base row col = some cell := by
  unfold writeCell at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, w, -, h⟩ := h
    split at h
    · cases h; exact hc
    · simp at h

end PTX.TcMma
