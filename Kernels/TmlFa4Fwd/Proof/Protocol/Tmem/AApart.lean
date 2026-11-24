-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
public import Lemmas.Tcgen05.MmaFinishTmemA
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMAs' Tensor Memory operands are apart from their accumulators

An MMA with its A operand in Tensor Memory is a PV MMA: it reads the probability columns (below 256)
and accumulates in the output columns (from 256), so no MMA of its accumulator writes a cell it
reads (`aTmemApart`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A PV MMA's A cell is in the probability columns. -/
theorem pv_aCell {s : OperandSpec} {index : Nat} {cell : Cell} {pos st j : Nat}
    (hD : s.descriptor = Tm.pvDsc) (ha : s.aTmem = some (128 * st + 64 + 8 * j)) (hst : st < 2)
    (hj : j < 8) (h : aCell s index = some (cell, pos)) : cell.column < 256 := by
  unfold aCell at h
  rw [ha] at h
  simp only [Option.bind_some] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hb : s.descriptor.kind.k * s.descriptor.kind.width = 32 := by rw [hD]; rfl
    simp only [hb]
    have := Nat.mod_lt index (show 0 < 32 by decide)
    omega
  · cases h

/-- A full-datapath MMA's result cells are from its base column. -/
theorem result_column {s : OperandSpec} {base row col : Nat} {mask : List Nat} {cell : Cell}
    (hD : s.descriptor.m = 128 * s.descriptor.group.size)
    (h : writeCell s base mask row col = some cell) : base % 2 ^ 16 ≤ cell.column := by
  unfold writeCell at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i c hc
  simp only at h
  have hcell : c = cell := by
    split at h
    · cases h
    · simp only at h
      split at h
      · exact Option.some.inj h
      · cases h
  subst hcell
  unfold resultCell at hc
  simp only [hD, ↓reduceIte] at hc
  split at hc
  · simp only [Option.some.injEq] at hc
    subst hc
    exact Nat.le_add_right _ _
  · cases hc

/-- **No MMA reads a Tensor Memory A cell its accumulator's MMAs write.** -/
theorem aTmemApart (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : ATmemApart X := by
  intro j d s acc mask hj index cell pos ha w d' s' acc' mask' row col hw hsame hcell
  obtain ⟨-, st, u, i, hst, h⟩ := Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hj⟩
  obtain ⟨-, st', u', i', hst', h'⟩ := Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hw⟩
  have hD' : s'.descriptor.m = 128 * s'.descriptor.group.size := by
    rcases h' with h' | h'
    · obtain ⟨-, -, -, rfl⟩ := h'.spec_eq hw; rfl
    · obtain ⟨-, -, -, rfl⟩ := h'.spec_eq hw; rfl
  have hle := result_column hD' hcell
  rcases h with h | h
  · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hj
    simp [aCell] at ha
  · obtain ⟨hd, -, -, rfl⟩ := h.spec_eq hj
    have hlt := pv_aCell (st := st) (j := i.val) rfl rfl hst i.isLt ha
    have hdd := hsame.1
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
