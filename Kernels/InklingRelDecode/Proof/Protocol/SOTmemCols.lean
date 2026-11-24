-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOSched
public import Kernels.InklingRelDecode.Proof.Interface.ProtocolThreads

@[expose] public section

/-!
# The Tensor Memory columns of the S/P/O handshake

The kernel's 512-column allocation (`tcgen05.alloc` of 512 columns, one per CTA) is split by the
MMA warp's column arithmetic into

* the two **score buffers** `S b`: columns `[tm + 128 b, tm + 128 b + 128)`, `b < 2`;
* the **probabilities** `P b`, aliased on the first half of the score buffer:
  `[tm + 128 b, tm + 128 b + 64)`;
* the **output accumulator** `O`: `[tm + 256, tm + 384)`.

All lie in the allocation `[tm, tm + 512)`; the two buffers and `O` are pairwise disjoint; `P b`
lies in `S b` (the alias), so the two buffers do not alias each other. `tm` is a column of the
32-bit Tensor Memory address (`TmOk`: `tm + 512 ≤ 2 ^ 16`, no lane bits; the allocation returns
column 0: `Consistent.alloc512_result`).

The column footprints of the events of the roles, from the shapes of the MMA events:

* `qk_cells` (QK MMA of block `i`): every result cell of the MMA lies in `S (i % 2)` of the issuing
  CTA (the descriptor is a 64 by 128 `kind::f16` MMA, `cta_group::1`: Layout F, 128 columns from the
  accumulator column);
* `pv_cells` (PV MMA `j` of block `i - 1`): every result cell lies in `O`, and the A operand (read
  from Tensor Memory at `tm + 128 ((i - 1) % 2) + 8 j`, 16 elements of 2 bytes: 8 columns) lies in
  `P ((i - 1) % 2)`; the eight MMAs `j = 0 … 7` cover exactly the 64 columns of `P`.

The Core semantics forbids a cell past column 512 (`resultCell`, `aCell`), so the bound
`< tm + 512` is also an acceptance condition of the events themselves.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.TcMma

noncomputable section

/-! ### The column ranges -/

/-- Score buffer `b`'s columns. -/
def InS (tm b col : Nat) : Prop := tm + 128 * b ≤ col ∧ col < tm + 128 * b + 128

/-- The probabilities of buffer `b`: the first half of its score buffer. -/
def InP (tm b col : Nat) : Prop := tm + 128 * b ≤ col ∧ col < tm + 128 * b + 64

/-- The output accumulator's columns. -/
def InO (tm col : Nat) : Prop := tm + 256 ≤ col ∧ col < tm + 384

/-- A base column of an allocation of 512 columns: a column of the address field, the allocation
fits the 16-bit column field. -/
def TmOk (tm : Nat) : Prop := tm + 512 ≤ 2 ^ 16

theorem inP_inS {tm b col : Nat} (h : InP tm b col) : InS tm b col := by
  unfold InP InS at *; omega

theorem inS_disjoint {tm b b' col : Nat} (hne : b ≠ b')
    (h : InS tm b col) : ¬ InS tm b' col := by
  unfold InS at *; omega

theorem inS_inO_disjoint {tm b col : Nat} (hb : b < 2) (h : InS tm b col) : ¬ InO tm col := by
  unfold InS InO at *; omega

theorem inP_inO_disjoint {tm b col : Nat} (hb : b < 2) (h : InP tm b col) : ¬ InO tm col :=
  inS_inO_disjoint hb (inP_inS h)

/-! ### The cells of the MMA events -/

/-- A write cell is the result cell. -/
theorem writeCell_resultCell {s : OperandSpec} {base row col : Nat} {mask : List Nat}
    {cell : Cell} (h : writeCell s base mask row col = some cell) :
    resultCell s base row col = some cell := by
  unfold writeCell at h
  dsimp only at h
  split at h
  · cases h
  · simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i c hc
      dsimp only at h
      split at h
      · cases h
      · dsimp only at h
        split at h
        · simp only [Option.some.injEq] at h
          rw [hc, h]
        · cases h

/-- **The columns of a result cell of a 64 by 128 MMA of one CTA** (Layout F): from the column of
the accumulator address, 128 columns, within the 512. -/
theorem resultCell_cols {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (hm : s.descriptor.m = 64) (hg : s.descriptor.group = .one) (hw : s.descriptor.ws = false)
    (hn : s.descriptor.n = 128)
    (h : resultCell s base row col = some cell) :
    cell.column = base % 2 ^ 16 + col ∧ col < 128 ∧ base % 2 ^ 16 + 128 ≤ 512 ∧
      (cell.cta = s.lowCta ∨ cell.cta = s.highCta) := by
  unfold resultCell at h
  dsimp only at h
  have hh : halfDatapath s.descriptor = true := by
    simp [halfDatapath, hm, hg, hw]
  have hr : resultColumns s.descriptor = 128 := by
    simp [resultColumns, hh, hn]
  have hne : ¬ s.descriptor.m = 128 * s.descriptor.group.size := by
    simp [hm, hg, CtaGroup.size]
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, -, hcol, hcols⟩ := hc
    rw [hr] at hcols
    refine ⟨rfl, by omega, by omega, ?_⟩
    simp only
    split <;> simp
  · cases h

/-! ### The cells of the QK and PV events -/

variable {X : Execution}

theorem qk_desc {dsc : Descriptor} (h : TcMma.decode .one false .f16 Mma.qkIdesc = some dsc) :
    dsc.m = 64 ∧ dsc.n = 128 ∧ dsc.ws = false ∧ dsc.group = .one := by
  have e : (TcMma.decode .one false .f16 Mma.qkIdesc).map
      (fun d => (d.m, d.n, d.ws, d.group)) = some (64, 128, false, .one) := by decide
  rw [h] at e
  simpa using e

theorem pv_desc {dsc : Descriptor} (h : TcMma.decode .one false .f16 Mma.pvIdesc = some dsc) :
    dsc.m = 64 ∧ dsc.n = 128 ∧ dsc.ws = false ∧ dsc.group = .one ∧
      dsc.kind.k * dsc.kind.width = 32 := by
  have e : (TcMma.decode .one false .f16 Mma.pvIdesc).map
      (fun d => (d.m, d.n, d.ws, d.group, d.kind.k * d.kind.width)) =
      some (64, 128, false, .one, 32) := by decide
  rw [h] at e
  simpa using e

/-- **The result cells of a QK MMA of block `i` lie in the score buffer `i % 2` of the issuing
CTA.** -/
theorem qk_cells {L : Launch} {cta tm i j pc : Nat} {e : Event} (hT : TmOk tm)
    (hq : EvW.QkIssue L cta tm i j pc e) {x : EvId} (hx : X.get x = some e) {cell : Cell}
    (hc : X.MmaCell x cell) : InS tm (i % 2) cell.column ∧ cell.cta = cta := by
  obtain ⟨da, db, dsc, hd, -, -, rfl⟩ := hq
  obtain ⟨d, s, acc, mask, row, col, ⟨pc', hget⟩, hw⟩ := hc
  rw [hx] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hget
  obtain ⟨-, rfl, rfl, -, -⟩ := hget
  obtain ⟨hm, hn, hws, hg⟩ := qk_desc hd
  obtain ⟨hcol, hcl, -, hcta⟩ := resultCell_cols (s := ⟨dsc, da, db, cta, cta, none, {}⟩)
    hm hg hws hn (writeCell_resultCell hw)
  have hb : i % 2 < 2 := Nat.mod_lt _ (by omega)
  have hmod : (tm + 128 * (i % 2)) % 2 ^ 16 = tm + 128 * (i % 2) := by
    apply Nat.mod_eq_of_lt
    unfold TmOk at hT
    omega
  rw [hmod] at hcol
  refine ⟨?_, ?_⟩
  · unfold InS
    omega
  · simpa using hcta

/-- **The result cells of a PV MMA lie in the output accumulator of the issuing CTA.** -/
theorem pv_cells {L : Launch} {cta tm i j pc : Nat} {e : Event} (hT : TmOk tm)
    (hq : EvW.PvIssue L cta tm i j pc e) {x : EvId} (hx : X.get x = some e) {cell : Cell}
    (hc : X.MmaCell x cell) : InO tm cell.column ∧ cell.cta = cta := by
  obtain ⟨db, dsc, hd, -, rfl⟩ := hq
  obtain ⟨d, s, acc, mask, row, col, ⟨pc', hget⟩, hw⟩ := hc
  rw [hx] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hget
  obtain ⟨-, rfl, rfl, -, -⟩ := hget
  obtain ⟨hm, hn, hws, hg, -⟩ := pv_desc hd
  obtain ⟨hcol, hcl, -, hcta⟩ := resultCell_cols
    (s := ⟨dsc, db, db, cta, cta, some (tm + 128 * ((i - 1) % 2) + 8 * j), {}⟩)
    hm hg hws hn (writeCell_resultCell hw)
  have hmod : (tm + 256) % 2 ^ 16 = tm + 256 := by
    apply Nat.mod_eq_of_lt
    unfold TmOk at hT
    omega
  rw [hmod] at hcol
  refine ⟨?_, ?_⟩
  · unfold InO
    omega
  · simpa using hcta

/-- **The columns of an A cell of a 16-element `kind::f16` MMA from Tensor Memory**: 8 columns from
the address's column. -/
theorem aCell_cols {s : OperandSpec} {index : Nat} {cell : Cell} {b : Nat} {a : Nat}
    (hk : s.descriptor.kind.k * s.descriptor.kind.width = 32) (hs : s.aTmem = some a)
    (h : aCell s index = some (cell, b)) :
    a % 2 ^ 16 ≤ cell.column ∧ cell.column < a % 2 ^ 16 + 8 ∧ a % 2 ^ 16 + 8 ≤ 512 ∧
      (cell.cta = s.lowCta ∨ cell.cta = s.highCta) := by
  unfold aCell at h
  dsimp only at h
  rw [hs] at h
  simp only [Option.bind_some, hk] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨-, -, hlt, -⟩ := hc
    refine ⟨?_, ?_, by omega, ?_⟩
    · simp only
      omega
    · simp only
      omega
    · simp only
      split <;> simp
  · cases h

/-- **The A cells of a PV MMA `j` of block `i - 1` lie in `P ((i - 1) % 2)`, in the 8 columns
`tm + 128 b + 8 j`.** -/
theorem pv_aCells {L : Launch} {cta tm i j pc : Nat} {e : Event} (hT : TmOk tm) (hj : j < 8)
    (hq : EvW.PvIssue L cta tm i j pc e) {x : EvId} (hx : X.get x = some e) {cell : Cell}
    (hc : X.MmaACell x cell) :
    InP tm ((i - 1) % 2) cell.column ∧
      tm + 128 * ((i - 1) % 2) + 8 * j ≤ cell.column ∧
      cell.column < tm + 128 * ((i - 1) % 2) + 8 * j + 8 ∧ cell.cta = cta := by
  obtain ⟨db, dsc, hd, -, rfl⟩ := hq
  obtain ⟨d, s, acc, mask, index, b, ⟨pc', hget⟩, hw⟩ := hc
  rw [hx] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hget
  obtain ⟨-, rfl, rfl, -, -⟩ := hget
  obtain ⟨-, -, -, -, hk⟩ := pv_desc hd
  obtain ⟨h1, h2, -, hcta⟩ := aCell_cols
    (s := ⟨dsc, db, db, cta, cta, some (tm + 128 * ((i - 1) % 2) + 8 * j), {}⟩) hk rfl hw
  have hb : (i - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hmod : (tm + 128 * ((i - 1) % 2) + 8 * j) % 2 ^ 16 =
      tm + 128 * ((i - 1) % 2) + 8 * j := by
    apply Nat.mod_eq_of_lt
    unfold TmOk at hT
    omega
  rw [hmod] at h1 h2
  refine ⟨?_, h1, h2, by simpa using hcta⟩
  unfold InP
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.SO
