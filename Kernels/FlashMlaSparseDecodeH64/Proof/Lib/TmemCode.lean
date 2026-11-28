-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCells
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.Flow.TcStLen
public import Lemmas.Cluster.Unit
public import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

/-! # The kernel's Tensor Memory stores and groups

* `code_noShift`, `code_stLen` (static): the code has no `tcgen05.shift`, and every
  `tcgen05.st` has 64 source registers (`.32x32b.x64`);
* `ctaGroup_self`: a CTA's group of qualifier `one` is the CTA itself (single-CTA clusters);
* `stCell`: register `j` of warpgroup 0's `32x32b` store at column `64 c` of thread `g`
  is in `g`'s CTA, in lane `32 w + l` for its warp `w < 4` and lane `l`, at column `64 c + j`;
* `writeCell_zeroMask`, `resultCell_indices` (moved from the old tree): with zero output masks
  every result cell of an M 64 group-one MMA is written. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **Static check**: no instruction of the kernel is a `tcgen05.shift`. -/
theorem code_noShift : kernel.code.all (fun ins => !Flow.tcShiftOp ins.op) = true := by
  decide +kernel

/-- **Static check**: every `tcgen05.st` of the kernel has 64 source operands. -/
theorem code_stLen : kernel.code.all (fun ins => match ins.op with
    | .tcSt _ ss _ => ss.length == 64
    | _ => true) = true := by
  decide +kernel

/-- The instruction at a store's pc has 64 source operands. -/
theorem stLen_of_code {pc : Nat} {ins : Instr} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hc : kernel.code[pc]? = some ins) (hop : ins.op = .tcSt ta ss sh) : ss.length = 64 := by
  have h := List.all_eq_true.mp code_stLen ins (List.mem_of_getElem? hc)
  rw [hop] at h
  simpa using h

/-- **A CTA's group of qualifier `one` is the CTA.** -/
theorem ctaGroup_self (hpre : Pre P L mem0) {c : Nat} (hc : c < L.grid) :
    L.ctaGroup c .one = some [c] := by
  have hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩ := fun k => by
    rw [hpre.clusterPlaces]
    rfl
  have hn : c < L.nclusters := by rw [hpre.nclusters]; exact hc
  rw [Launch.ctaGroup_one, Launch.rankOfCta_unit hs hn, Launch.peerCta_unit hs hn hc]
  rfl

/-- **The cell of register `j` of a `32x32b` store of warpgroup 0 at column `64 c`.** -/
theorem stCell (hpre : Pre P L mem0) {g c j : Nat} (hw : MbarRow.warp L g < 4) (hc : c < 4) :
    (tcDataCell L g .s32x32b (64 * c) j).cta = g / L.block ∧
      (tcDataCell L g .s32x32b (64 * c) j).lane = g % 384 ∧
      (tcDataCell L g .s32x32b (64 * c) j).column = 64 * c + j := by
  have hx := tidOf_x_eq hpre g
  unfold MbarRow.warp at hw
  rw [hx] at hw
  have hb := hpre.block
  simp only [tcDataCell, TcShape.base, TcShape.laneIn, TcShape.columnIn, TcShape.lanes,
    laneBase, PTX.laneOf, chunkOffset, hb]
  exact ⟨trivial, by omega, by omega⟩

/-- A represented result cell lies inside the logical matrix dimensions. -/
theorem resultCell_indices {s : TcMma.OperandSpec} {base row col : Nat} {cell : TcMma.Cell}
    (h : TcMma.resultCell s base row col = some cell) :
    row < s.descriptor.m ∧ col < s.descriptor.n := by
  unfold TcMma.resultCell at h
  dsimp only at h
  split at h
  · rename_i hguard
    obtain ⟨-, -, hr, hc, -⟩ := hguard
    exact ⟨hr, hc⟩
  · cases h

/-- **Zero output masks write every result cell** of an M 64 group-one MMA. -/
theorem writeCell_zeroMask {s : TcMma.OperandSpec} {base row col : Nat}
    {cell : TcMma.Cell} (hg : s.descriptor.group = .one) (hm : s.descriptor.m = 64)
    (hc : TcMma.resultCell s base row col = some cell) :
    TcMma.writeCell s base [0, 0, 0, 0] row col = some cell := by
  have hr : row < 64 := hm ▸ (resultCell_indices hc).1
  have hl : cell.lane < 128 := (TcMma.resultCell_bounds hc).1
  have hv : TcMma.OutputMaskValid s.descriptor.group [0, 0, 0, 0] := by
    rw [hg]
    decide
  have hrow : row / (s.descriptor.m / s.descriptor.group.size) = 0 := by
    rw [hm, hg]
    exact Nat.div_eq_of_lt hr
  have hword : ([0, 0, 0, 0] : List Nat)[cell.lane / 32]? = some 0 := by
    have he : cell.lane / 32 < 4 := by omega
    interval_cases cell.lane / 32 <;> rfl
  simp only [TcMma.writeCell, hv, not_true_eq_false, ite_false, hc, hrow, Nat.zero_mul,
    Nat.zero_add, bind, Option.bind, hword, Nat.zero_div, Nat.zero_mod, ite_true]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
