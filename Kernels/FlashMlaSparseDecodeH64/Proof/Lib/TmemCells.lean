-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Mma

@[expose] public section

/-! # The Tensor Memory cells of the MMA warp's operations

Pure geometry of the MMA row's operands (`TmemRow.MmaTc`): the descriptor words decode to M 64,
N 128 (QK) and M 64, N 256 (PV), `.ws`, two column blocks, so

* a QK result cell (D at 400) lies in columns `[400, 464)` of the low CTA (`qk_resultCell`);
* a PV result cell (D at `128 (k % 2)`) lies in columns `[b, b + 128)` of the low CTA
  (`pv_resultCell`);
* QK MMA `k`'s A cells (A at `256 + 8 k`, 128 rows of 32 bytes) lie in columns `[256 + 8 k,
  264 + 8 k)` of the low or high CTA (`qk_aCell`);
* copy `k`'s cells (`128x256b` to `256 + 8 k`) lie in columns `[256 + 8 k, 264 + 8 k)`
  (`cp_cell`);
* a written cell is a result cell (`writeCell_result`).

The four column ranges `[0, 256)`, `[256, 384)`, `[400, 464)` are disjoint. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmemRow
open PTX

noncomputable section

/-- The QK descriptor's layout numbers. -/
theorem qk_desc : (TcMma.decode .one true .f16 qkIdesc).map (fun d =>
    (d.m, d.n, d.group.size, TcMma.halfDatapath d, TcMma.columnBlocks d, d.kind.k * d.kind.width,
      TcMma.Operand.rows .a d)) = some (64, 128, 1, false, 2, 32, 128) := by
  rfl

/-- The PV descriptor's layout numbers. -/
theorem pv_desc : (TcMma.decode .one true .f16 pvIdesc).map (fun d =>
    (d.m, d.n, d.group.size, TcMma.halfDatapath d, TcMma.columnBlocks d)) =
      some (64, 256, 1, false, 2) := by
  rfl

/-- A written cell is a result cell. -/
theorem writeCell_result {s : TcMma.OperandSpec} {base : Nat} {mask : List Nat} {row col : Nat}
    {cell : TcMma.Cell} (h : TcMma.writeCell s base mask row col = some cell) :
    TcMma.resultCell s base row col = some cell := by
  simp only [TcMma.writeCell] at h
  split at h
  · cases h
  · cases hr : TcMma.resultCell s base row col with
    | none => simp [hr] at h
    | some c =>
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      cases hw : (mask[((row / (s.descriptor.m / s.descriptor.group.size)) * 128 + c.lane) / 32]?)
        <;> simp only [hw, Option.bind_none, Option.bind_some, reduceCtorEq] at h
      split at h
      · exact (Option.some.inj h) ▸ rfl
      · cases h

/-- The result cells of a `.ws` M-64 descriptor with two column blocks and `n` columns, D at
`base` (lane field 0): columns `[base, base + n / 2)` of the low CTA. -/
theorem resultCell_m64 {s : TcMma.OperandSpec} {base row col n : Nat} {cell : TcMma.Cell}
    (hm : s.descriptor.m = 64) (hn : s.descriptor.n = n) (hg : s.descriptor.group.size = 1)
    (hh : TcMma.halfDatapath s.descriptor = false) (hb : TcMma.columnBlocks s.descriptor = 2)
    (h2 : 2 ≤ n) (hbase : base < 2 ^ 16) (h : TcMma.resultCell s base row col = some cell) :
    cell.cta = s.lowCta ∧ base ≤ cell.column ∧ cell.column < base + n / 2 := by
  simp only [TcMma.resultCell, hm, hn, hg, hh, hb, Nat.div_one] at h
  split at h
  · rename_i hok
    obtain ⟨-, -, hr, hc, -⟩ := hok
    simp only [show ¬ (64 = 128 * 1) by decide, ↓reduceIte, Bool.false_eq_true,
      show row < 64 from hr, Option.some.injEq] at h
    subst h
    have : col % (n / 2) < n / 2 := Nat.mod_lt _ (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · simp only [Nat.mod_eq_of_lt hbase]
      omega
    · simp only [Nat.mod_eq_of_lt hbase]
      omega
  · cases h

/-- **A QK result cell** lies in columns `[400, 464)` of the low CTA. -/
theorem qk_resultCell {L : Launch} {g : Nat} {s : TcMma.OperandSpec} {aT : Option Nat}
    {row col : Nat} {cell : TcMma.Cell} (hs : MmaOps L g s aT qkIdesc)
    (h : TcMma.resultCell s 400 row col = some cell) :
    cell.cta = s.lowCta ∧ 400 ≤ cell.column ∧ cell.column < 464 := by
  obtain ⟨-, hd, -⟩ := hs
  have hq := qk_desc
  rw [hd] at hq
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨hm, hn, hg, hh, hb, -, -⟩ := hq
  exact resultCell_m64 hm hn hg hh hb (by decide) (by decide) h

/-- **A PV result cell** (D at `b`, `b ≤ 128`) lies in columns `[b, b + 128)` of the low CTA. -/
theorem pv_resultCell {L : Launch} {g : Nat} {s : TcMma.OperandSpec} {aT : Option Nat}
    {b row col : Nat} {cell : TcMma.Cell} (hs : MmaOps L g s aT pvIdesc) (hb : b ≤ 128)
    (h : TcMma.resultCell s b row col = some cell) :
    cell.cta = s.lowCta ∧ b ≤ cell.column ∧ cell.column < b + 128 := by
  obtain ⟨-, hd, -⟩ := hs
  have hq := pv_desc
  rw [hd] at hq
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨hm, hn, hg, hh, hbk⟩ := hq
  exact resultCell_m64 hm hn hg hh hbk (by decide) (by omega) h

/-- **QK MMA `k`'s A cell of byte `index`**: lane `index / 32`, column `256 + 8 k + index % 32 / 4`,
in the low CTA for the first 64 rows and the high CTA after. -/
theorem qk_aCell_cell {L : Launch} {g : Nat} {s : TcMma.OperandSpec} {k index b : Nat}
    {cell : TcMma.Cell} (hk : k < 16) (hs : MmaOps L g s (some (256 + 8 * k)) qkIdesc)
    (h : TcMma.aCell s index = some (cell, b)) :
    index < 4096 ∧ cell = ⟨if index / 32 < 64 then s.lowCta else s.highCta, index / 32,
      256 + 8 * k + index % 32 / 4⟩ := by
  obtain ⟨ha, hd, -⟩ := hs
  have hq := qk_desc
  rw [hd] at hq
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨hm, -, hg, hh, -, hw, hrows⟩ := hq
  simp only [TcMma.aCell, ha, Option.bind_some, hw, hm, hg, hh, hrows, Nat.div_one] at h
  split at h
  · rename_i hok
    obtain ⟨-, hr, -⟩ := hok
    simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : (256 + 8 * k) % 2 ^ 16 = 256 + 8 * k := Nat.mod_eq_of_lt (by omega)
    have h3 : index / 32 < 128 := hr
    refine ⟨by omega, ?_⟩
    simp only [h1, Nat.mod_eq_of_lt h3]
  · cases h

/-- **QK MMA `k`'s A cells** lie in columns `[256 + 8 k, 264 + 8 k)` of the low CTA. -/
theorem qk_aCell {L : Launch} {g : Nat} {s : TcMma.OperandSpec} {k index b : Nat}
    {cell : TcMma.Cell} (hk : k < 16) (hs : MmaOps L g s (some (256 + 8 * k)) qkIdesc)
    (h : TcMma.aCell s index = some (cell, b)) :
    (cell.cta = s.lowCta ∨ cell.cta = s.highCta) ∧ 256 + 8 * k ≤ cell.column ∧
      cell.column < 264 + 8 * k := by
  obtain ⟨-, rfl⟩ := qk_aCell_cell hk hs h
  have : index % 32 < 32 := Nat.mod_lt _ (by omega)
  refine ⟨?_, by dsimp only; omega, by dsimp only; omega⟩
  dsimp only
  split
  · exact .inl rfl
  · exact .inr rfl

/-- **Copy `k`'s cells** lie in columns `[256 + 8 k, 264 + 8 k)`. -/
theorem cp_cell {k cta lane index : Nat} (hk : k < 16) :
    256 + 8 * k ≤ (TcCopy.cell .s128x256b (256 + 8 * k) cta lane index).column ∧
      (TcCopy.cell .s128x256b (256 + 8 * k) cta lane index).column < 264 + 8 * k := by
  have h1 : (256 + 8 * k) % 2 ^ 16 = 256 + 8 * k := Nat.mod_eq_of_lt (by omega)
  simp only [TcCopy.cell, h1, TcCpShape.rowBytes]
  have : index % 32 < 32 := Nat.mod_lt _ (by omega)
  omega

/-- **Every cell of the D columns of an `M 64`, two column block MMA is written**: with lane field
0, D at `base`, all output lanes enabled, the cell of CTA `s.lowCta`, lane `l < 128`, column
`base + c` (`c < n / 2`) is the cell of row `l % 64`, column `n / 2 * (l / 64) + c`. -/
theorem writeCell_m64_ex {s : TcMma.OperandSpec} {base n : Nat} {cell : TcMma.Cell}
    (hm : s.descriptor.m = 64) (hn : s.descriptor.n = n) (hg : s.descriptor.group.size = 1)
    (hh : TcMma.halfDatapath s.descriptor = false) (hb : TcMma.columnBlocks s.descriptor = 2)
    (hv : TcMma.Valid s.descriptor) (hla : TcMma.LaneAligned s.descriptor (base / 2 ^ 16))
    (hmk : TcMma.OutputMaskValid s.descriptor.group [0, 0, 0, 0])
    (hbase : base < 2 ^ 16) (hcols : base + n / 2 ≤ 512) (hn2 : n % 2 = 0)
    (hcta : cell.cta = s.lowCta) (hl : cell.lane < 128) (h1 : base ≤ cell.column)
    (h2 : cell.column < base + n / 2) :
    ∃ row col, TcMma.writeCell s base [0, 0, 0, 0] row col = some cell := by
  have hdiv : n / 2 * (cell.lane / 64) + (cell.column - base) < n := by
    have : cell.lane / 64 < 2 := by omega
    have h3 : n / 2 * (cell.lane / 64) ≤ n / 2 * 1 := Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨cell.lane % 64, n / 2 * (cell.lane / 64) + (cell.column - base), ?_⟩
  have hrc : TcMma.resultColumns s.descriptor = n / 2 := by
    simp only [TcMma.resultColumns, hm, hn, hg, hh, hb]
    simp
  have hrc' : TcMma.resultCell s base (cell.lane % 64)
      (n / 2 * (cell.lane / 64) + (cell.column - base)) = some cell := by
    have hlt : cell.lane % 64 < 64 := Nat.mod_lt _ (by omega)
    have hcol : base % 2 ^ 16 + TcMma.resultColumns s.descriptor ≤ 512 := by
      rw [hrc, Nat.mod_eq_of_lt hbase]; omega
    simp only [TcMma.resultCell, hm, hn, hg, hh, hb, Nat.div_one, hv, hla, hlt, hdiv, hcol,
      and_true]
    have hdn : 0 < n / 2 := by omega
    have hq : (n / 2 * (cell.lane / 64) + (cell.column - base)) / (n / 2) = cell.lane / 64 := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hdn, Nat.div_eq_of_lt (by omega)]
      simp
    have hr : (n / 2 * (cell.lane / 64) + (cell.column - base)) % (n / 2) =
        cell.column - base := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    simp only [show ¬ (64 = 128 * 1) by decide, ↓reduceIte,
      Bool.false_eq_true, hq, hr]
    obtain ⟨c0, l0, k0⟩ := cell
    simp only [Nat.mod_eq_of_lt hbase] at *
    simp only [Option.some.injEq, TcMma.Cell.mk.injEq]
    omega
  have hw : [0, 0, 0, 0][cell.lane / 32]? = some 0 := by
    have : cell.lane / 32 < 4 := by omega
    generalize cell.lane / 32 = q at this ⊢
    interval_cases q <;> rfl
  simp only [TcMma.writeCell, hmk, not_true_eq_false, ↓reduceIte, hrc', hm, hg,
    Nat.div_one]
  rw [Nat.div_eq_of_lt (by omega : cell.lane % 64 < 64)]
  simp [hw]

/-- The descriptors are valid, lane field 0 aligned, with the all-enabled mask valid. -/
theorem qk_desc_ok : (TcMma.decode .one true .f16 qkIdesc).map (fun d =>
    decide (TcMma.Valid d ∧ TcMma.LaneAligned d 0 ∧ TcMma.OutputMaskValid d.group [0, 0, 0, 0])) =
      some true := by
  decide +kernel

theorem pv_desc_ok : (TcMma.decode .one true .f16 pvIdesc).map (fun d =>
    decide (TcMma.Valid d ∧ TcMma.LaneAligned d 0 ∧ TcMma.OutputMaskValid d.group [0, 0, 0, 0])) =
      some true := by
  decide +kernel

/-- **A QK MMA writes every cell of columns `[400, 464)`, lanes below 128, of its CTA.** -/
theorem qk_writeCell {L : Launch} {g : Nat} {s : TcMma.OperandSpec} {aT : Option Nat}
    {cell : TcMma.Cell} (hs : MmaOps L g s aT qkIdesc) (hcta : cell.cta = s.lowCta)
    (hl : cell.lane < 128) (h1 : 400 ≤ cell.column) (h2 : cell.column < 464) :
    ∃ row col, TcMma.writeCell s 400 [0, 0, 0, 0] row col = some cell := by
  obtain ⟨-, hd, -⟩ := hs
  have hq := qk_desc
  have ho := qk_desc_ok
  rw [hd] at hq ho
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hq ho
  obtain ⟨hm, hn, hg, hh, hb, -, -⟩ := hq
  obtain ⟨hv, hla, hmk⟩ := ho
  exact writeCell_m64_ex (n := 128) hm hn hg hh hb hv hla hmk (by decide) (by decide) (by decide)
    hcta hl h1 (by omega)

/-- **A PV MMA with D at `128 kk` writes every cell of columns `[128 kk, 128 kk + 128)`, lanes
below 128, of its CTA.** -/
theorem pv_writeCell {L : Launch} {g : Nat} {s : TcMma.OperandSpec} {aT : Option Nat}
    {kk : Nat} {cell : TcMma.Cell} (hs : MmaOps L g s aT pvIdesc) (hkk : kk < 2)
    (hcta : cell.cta = s.lowCta) (hl : cell.lane < 128) (h1 : 128 * kk ≤ cell.column)
    (h2 : cell.column < 128 * kk + 128) :
    ∃ row col, TcMma.writeCell s (128 * kk) [0, 0, 0, 0] row col = some cell := by
  obtain ⟨-, hd, -⟩ := hs
  have hq := pv_desc
  have ho := pv_desc_ok
  rw [hd] at hq ho
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hq ho
  obtain ⟨hm, hn, hg, hh, hb⟩ := hq
  obtain ⟨hv, hla, hmk⟩ := ho
  have hk : 128 * kk < 2 ^ 16 := by omega
  have hla' : TcMma.LaneAligned s.descriptor (128 * kk / 2 ^ 16) := by
    rw [Nat.div_eq_of_lt hk]; exact hla
  exact writeCell_m64_ex (n := 256) hm hn hg hh hb hv hla' hmk hk (by omega) (by decide) hcta hl
    h1 (by omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmemRow
