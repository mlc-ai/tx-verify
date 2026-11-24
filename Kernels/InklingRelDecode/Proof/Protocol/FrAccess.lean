-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Interface.FrTcData
public import Kernels.InklingRelDecode.Proof.Interface.FrEpi
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmIssue
public import Kernels.InklingRelDecode.Proof.Protocol.TmemAccess
public import Kernels.InklingRelDecode.Proof.Result.SwStore

@[expose] public section

/-!
# The footprint of every Tensor Memory access

`Tmem1.AccessInfo`'s first conjunct: every Tensor Memory access (`Tmem.Pair.Access`) is by a
launched thread, in a cell of its own CTA, in the first 512 columns, and the event is an MMA, a
`tcgen05.ld` or a `tcgen05.st`.

* an MMA's cells (written, accumulator and A cells): `resultCell` and `aCell` are `none` past the
  512th column (`resultCell_bounds`, `aCell_bounds`), and the issue's operand specification has
  its own CTA as both CTAs (`Tmem1.mma_cases`);
* a load's or store's cells: `tcDataCell` is in the CTA of the thread, and its column is the base
  column of the access, `128 (i % 2)` (S tile) or `256` (`O`), the half-split offset and the
  register index: at most `128 + 64 + 63` (`FrTcData.lean` gives the address and the shape of each
  site; the base word of the softmax region and of the epilogue is `0`, `Rs.SmBaseZero`);
* no `tcgen05.cp` and no `tcgen05.shift`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem1
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An A cell is in one of the group's CTAs and in the first 512 columns.** -/
theorem aCell_bounds {s : OperandSpec} {index : Nat} {cell : Cell} {b : Nat}
    (h : aCell s index = some (cell, b)) :
    (cell.cta = s.lowCta ∨ cell.cta = s.highCta) ∧ cell.column < 512 := by
  have hk : 0 < s.descriptor.kind.k * s.descriptor.kind.width := by
    cases s.descriptor.kind <;> simp [Kind.k, Kind.width]
  unfold aCell at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨address, -, h⟩ := h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨by dsimp only; split <;> simp, ?_⟩
    dsimp only
    have h2 : address % 2 ^ 16 +
        (s.descriptor.kind.k * s.descriptor.kind.width + 3) / 4 ≤ 512 := hc.2.2.1
    have h3 : index % (s.descriptor.kind.k * s.descriptor.kind.width) <
        s.descriptor.kind.k * s.descriptor.kind.width := Nat.mod_lt _ hk
    omega
  · cases h

/-- **The cells of an MMA event** are in its thread's CTA and the first 512 columns: the CTA
fields of the operand specification are the thread's CTA. -/
theorem mma_cell_info (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {e : EvId} {pc d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hget : X.get e = some ⟨pc, .tc (.mma d s acc mask)⟩) :
    e.1 < L.threads ∧ s.lowCta = e.1 / L.block ∧ s.highCta = e.1 / L.block := by
  obtain ⟨hg, d', P, -, -, hcases⟩ := mma_cases hpre hX hf hget
  refine ⟨hg, ?_⟩
  rcases hcases with ⟨j, -, da, db, dsc, -, -, -, -, hsp⟩ | ⟨j, -, db, dsc, -, -, -, hsp⟩
  · subst hsp
    exact ⟨rfl, rfl⟩
  · subst hsp
    exact ⟨rfl, rfl⟩

/-- A `.16x32bx2` access whose base column and offset leave the registers inside the first
512 columns. -/
theorem s16_col {L : Launch} {g a off j : Nat} (h1 : a % 2 ^ 16 + off + j < 512)
    (h2 : (a + off) % 2 ^ 16 = a % 2 ^ 16 + off) :
    (tcDataCell L g (.s16x32bx2 off) a j).column < 512 := by
  simp only [tcDataCell, TcShape.base, TcShape.columnIn]
  split <;> omega

/-- **Every Tensor Memory access has its footprint** (`Tmem1.AccessInfo`'s first conjunct): a
launched thread's MMA, load or store, of a cell of its own CTA in the first 512 columns. The
premises: the Tensor Memory base word of the softmax region is `0` (`Rs.SmBaseZero`) and the
kernel issues no `tcgen05.shift`. -/
theorem access_shape_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X)
    (hnosh : ∀ e s, ¬ X.ShiftIssue e s) (hnocp : ∀ i c, ¬ X.CpIssue i c) :
    ∀ {e : EvId} {cell : Cell}, Tmem.Pair.Access L X e cell →
      e.1 < L.threads ∧ cell.cta = e.1 / L.block ∧ cell.column < 512 ∧
        (SO.IsMma X e ∨ (∃ a vals sh, X.TLd e a vals sh) ∨ ∃ a vals sh, X.TSt e a vals sh) := by
  intro e cell hacc
  have key : ∀ {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue e d s acc mask → e.1 < L.threads ∧ s.lowCta = e.1 / L.block ∧
        s.highCta = e.1 / L.block ∧ SO.IsMma X e := by
    intro d s acc mask hi
    obtain ⟨pc, hget⟩ := hi
    obtain ⟨hg, h1, h2⟩ := mma_cell_info hpre hX hf hget
    exact ⟨hg, h1, h2, ⟨d, s, acc, mask, pc, hget⟩⟩
  rcases hacc with hm | ⟨j, a, vals, sh, hld, hj, hcell⟩ | ⟨a, vals, sh, j, hst, hj, hcell⟩ |
    ⟨c, cta, index, lane, hcp, -⟩ | ⟨sf, hsh, -⟩ | ⟨sf, hsh, -⟩
  · rcases hm with ⟨d, s, acc, mask, row, col, hi, hw⟩ | ⟨d, s, mask, row, col, hi, hw⟩ |
      ⟨d, s, acc, mask, index, b, hi, hw⟩
    · obtain ⟨hg, hlo, hhi, hism⟩ := key hi
      have hr := writeCell_resultCell hw
      refine ⟨hg, ?_, (resultCell_bounds hr).2, Or.inl hism⟩
      rcases resultCell_cta hr with h | h <;> simp [h, hlo, hhi]
    · obtain ⟨hg, hlo, hhi, hism⟩ := key hi
      refine ⟨hg, ?_, (resultCell_bounds hw).2, Or.inl hism⟩
      rcases resultCell_cta hw with h | h <;> simp [h, hlo, hhi]
    · obtain ⟨hg, hlo, hhi, hism⟩ := key hi
      obtain ⟨hc, hcol⟩ := aCell_bounds hw
      refine ⟨hg, ?_, hcol, Or.inl hism⟩
      rcases hc with h | h <;> simp [h, hlo, hhi]
  · obtain ⟨pc, hget⟩ := hld
    have hg : e.1 < L.threads := Frame.lt_of_get hX hget
    have hk : e.2 ≤ (X.tr e.1).length := Interface.Lk.event_le hget
    subst hcell
    obtain ⟨rfl, hlen, hcases⟩ := Interface.Lk.tcld_event hpre hX hf hg hget
    refine ⟨hg, rfl, ?_, Or.inr (Or.inl ⟨a, vals, _, ⟨pc, hget⟩⟩)⟩
    rcases hcases with ⟨d, hσ, h | h⟩ | ⟨d, hσ, hs, rfl⟩
    · obtain ⟨hs, rfl⟩ := h
      have hT := Interface.Lk.sm_def hk hσ
      have htm := hz hg hσ
      have := Sm.tileAddr_eq (L := L) (g := e.1) (d := d) hT (by omega)
        (Interface.sm_bw' hpre hX hf hg hσ (by rw [hs]; trivial))
      refine s16_col ?_ ?_ <;> rw [this, htm] <;> omega
    · obtain ⟨hs, rfl⟩ := h
      have hT := Interface.Lk.sm_def hk hσ
      have htm := hz hg hσ
      have := Sm.oAddr_eq (L := L) (g := e.1) (d := d) hT (by omega)
        (Interface.sm_bw' hpre hX hf hg hσ (by rw [hs]; trivial))
      refine s16_col ?_ ?_ <;> rw [this, htm] <;> omega
    · obtain ⟨k0, dsm, hk0, h0, hpr⟩ := Interface.epi_pr hk hσ
      have hT : e.1 % L.block < 128 := (Interface.cls_inv e.2 _ hk hσ).mp trivial
      have htm := hz hg h0
      rw [hpr]
      simp only [Epi.Prm.taddr, Epi.M32, Br.prm, DComp.exitIn, htm, Nat.zero_add]
      refine s16_col ?_ ?_ <;> omega
  · obtain ⟨pc, hget⟩ := hst
    have hg : e.1 < L.threads := Frame.lt_of_get hX hget
    have hk : e.2 ≤ (X.tr e.1).length := Interface.Lk.event_le hget
    subst hcell
    obtain ⟨d, hσ, h | h⟩ := Interface.Lk.tcst_event hX hf hg hget
    · obtain ⟨hs, rfl, rfl, hlen⟩ := h
      refine ⟨hg, rfl, ?_, Or.inr (Or.inr ⟨_, vals, _, ⟨pc, hget⟩⟩)⟩
      have hT := Interface.Lk.sm_def hk hσ
      have htm := hz hg hσ
      have := Sm.tileAddr_eq (L := L) (g := e.1) (d := d) hT (by omega)
        (Interface.sm_bw' hpre hX hf hg hσ (by rw [hs]; trivial))
      refine s16_col ?_ ?_ <;> rw [this, htm] <;> omega
    · obtain ⟨hs, rfl, rfl, hlen⟩ := h
      refine ⟨hg, rfl, ?_, Or.inr (Or.inr ⟨_, vals, _, ⟨pc, hget⟩⟩)⟩
      have hT := Interface.Lk.sm_def hk hσ
      have htm := hz hg hσ
      have := Sm.oAddr_eq (L := L) (g := e.1) (d := d) hT (by omega)
        (Interface.sm_bw' hpre hX hf hg hσ (by rw [hs]; trivial))
      refine s16_col ?_ ?_ <;> rw [this, htm] <;> omega
  · exact absurd hcp (hnocp _ _)
  · exact absurd hsh (hnosh _ _)
  · exact absurd hsh (hnosh _ _)

end
end PTX.Kernels.InklingRelDecode.Proof.Tmem1
