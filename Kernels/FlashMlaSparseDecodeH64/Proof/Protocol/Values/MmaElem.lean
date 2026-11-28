-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.QkAElem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.DqBElem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvAElem
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Foot
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Dq
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaBytePair
import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

/-! # The operand elements of the completed MMAs are numbers, but the P tile's

`mma_elements`: every completed MMA's operand elements decode (`MmaElements`) given that the PV
MMAs' A elements do (`PvAElements`). The B elements of QK and PV MMAs are elements of the
dequantized tile the MMA reads (`mma_b_elem`, from `dq_b_elem`: valid data, no undefined
behaviour); the A elements of the QK MMAs are the query values (`qk_a_elem`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An MMA of the MMA warp is a QK or a PV MMA.** -/
theorem mma_kind (hT : TmemRows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {g i pc d : Nat} {s : TcMma.OperandSpec} {a : Bool} {mask : List Nat}
    (he : X.get (g, i) = some ⟨pc, .tc (.mma d s a mask)⟩) :
    (d = 400 ∧ ∃ k, k < 16 ∧ pc = TmemRow.qkPc k ∧ a = (k != 0) ∧ mask = [0, 0, 0, 0] ∧
      MmaOn L g pc ∧ TmemRow.MmaOps L g s (some (256 + 8 * k)) TmemRow.qkIdesc) ∨
    (d < 256 ∧ ∃ k, k < 8 ∧ pc = TmemRow.pvPc k ∧ MmaOn L g pc ∧
      TmemRow.MmaOps L g s none TmemRow.pvIdesc) := by
  have hg := Frame.lt_of_get hX he
  rcases tc_role hT hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, hops⟩ |
      ⟨_, _, k, hk, hpc, h, -, hops⟩ <;> simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
    · cases h
    · cases h
    · cases h
    · obtain ⟨hd, rfl, rfl, rfl⟩ := h
      refine .inl ⟨hd, k, hk, hpc, rfl, rfl, ⟨hat, ?_⟩, hops⟩
      simp only [TmemRow.qkPc] at hpc
      split at hpc <;> omega
    · obtain ⟨hd, rfl, rfl, rfl⟩ := h
      refine .inr ⟨by omega, k, hk, hpc, ⟨hat, ?_⟩, hops⟩
      simp only [TmemRow.pvPc] at hpc
      split at hpc <;> omega
  · cases hc'

/-- **The column and row of a written cell are within the MMA's shape.** -/
theorem writeCell_col {s : TcMma.OperandSpec} {base row col : Nat} {mask : List Nat}
    {cell : TcMma.Cell} (h : TcMma.writeCell s base mask row col = some cell) :
    col < s.descriptor.n ∧ row < s.descriptor.m := by
  cases hr : TcMma.resultCell s base row col with
  | none => simp [TcMma.writeCell, hr] at h
  | some c =>
    unfold TcMma.resultCell at hr
    by_cases hh : TcMma.Valid s.descriptor ∧ TcMma.LaneAligned s.descriptor (base / 2 ^ 16) ∧
      row < s.descriptor.m ∧ col < s.descriptor.n ∧
      base % 2 ^ 16 + TcMma.resultColumns s.descriptor ≤ 512
    · obtain ⟨-, -, hrow', hcol', -⟩ := hh
      exact ⟨hcol', hrow'⟩
    · exact absurd hr (by simp only [hh]; simp)

/-- The A row of a QK MMA's cell is below 128. -/
theorem qk_operandRow_lt : ∀ row < 64, ∀ col < 128, TcMma.operandRow MmaFoot.qkD row col < 128 := by
  decide +kernel

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
  (hv : ∀ h k, NoUbBefore X h k → DqValid X h k)
  (hS : ∀ i d s acc mask, X.MmaIssue i d s acc mask → TcMma.IssueShape L i d s mask)
include hp hX hFw hR hI hB hN hv hS

/-- **The B elements of an MMA are numbers**: the B operand of a QK or PV MMA is a dequantized
tile (valid data). -/
theorem mma_b_elem {g j pc d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} (he : X.get (g, j) = some ⟨pc, .tc (.mma d s acc mask)⟩)
    (hat : MbarRow.MmaAt L g pc) (hops : X.async.mmaOperands (g, j) = some ops)
    (hk : s.descriptor.kind = .f16 .bf16 .f32) {col k : Nat} (hc : col < s.descriptor.n)
    (hk16 : k < 16) :
    ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k = .ok y := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hvalid, -, -, -, ⟨-, -, -, hs1, hs2, hs3⟩, -, -, -, hex⟩ :=
    hS _ _ _ _ _ (show X.MmaIssue (g, j) d s acc mask from ⟨pc, he⟩)
  have hidx : 2 * (col * 16 + k) < TcMma.Operand.b.bytes s.descriptor := by
    simp only [TcMma.Operand.bytes, TcMma.Operand.rows, TcMma.Operand.extent, hk,
      TcMma.Kind.k, TcMma.Kind.width, reduceCtorEq, false_and, ↓reduceIte]
    omega
  obtain ⟨l, hl⟩ : ∃ l, s.byteLoc .b (2 * (col * 16 + k)) = some l := by
    rcases hex .b _ hidx with h | ⟨h, -⟩
    · exact h
    · cases h
  have hf : X.MmaFootprint (g, j) true (2 * (col * 16 + k)) l :=
    Or.inl ⟨d, s, acc, mask, ⟨pc, he⟩, by simpa using hl⟩
  obtain ⟨b0, hlg⟩ : ∃ b0, MemRow.LocIn L (g / L.block) (.dequant b0) l := by
    rcases mmaFoot_pv hp hX hFw hg he hat hf with h | ⟨-, -, hh⟩
    · exact h
    · obtain ⟨-, -, -, -, -, -, -, hfalse⟩ := hh
      cases hfalse
  obtain ⟨-, u, hmu, -⟩ := mma_dqUse hp hX hFw he hat hf hlg
  obtain ⟨x, hx, -⟩ := dq_b_elem hp hX hFw hR hI hB hN hv he hat hops hk
    ⟨by omega, by omega, by omega⟩ hl hlg hmu
  exact ⟨x, Result.bf16MmaElement_of_bytes hx⟩

variable (hT : TmemRows P L X) (hO : MmaOne L X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
include hT hO ht hmd

/-- **The operand elements of every completed MMA are numbers**, given the PV MMAs' A elements:
the QK MMAs' A elements are the query values and every B element is a dequantized value. -/
theorem mma_elem_at (i : EvId)
    (hPA : ∀ d s acc mask ops row col cell, X.MmaIssue i d s acc mask →
      X.async.mmaDone i = true → X.async.mmaOperands i = some ops →
      TcMma.writeCell s d mask row col = some cell → d < 256 →
      ∀ k < 16, ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
        (TcMma.operandRow s.descriptor row col) k = .ok x) : MmaElemAt X i := by
  intro d s acc mask ops row col cell hi hdone hops hcell
  obtain ⟨g, j⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨hcol, hrow⟩ := writeCell_col hcell
  rcases mma_kind hT hX he with ⟨rfl, k, hk, rfl, rfl, rfl, hon, hmo⟩ |
    ⟨hd256, k, hk, rfl, hon, hmo⟩
  · have hD := MmaFoot.qkD_eq hmo.2.1
    have hkd := (desc_bf16 (Or.inl rfl) hmo.2.1).1
    refine ⟨fun t htt => ?_, fun t htt => ?_⟩
    · have hr : TcMma.operandRow s.descriptor row col < 128 := by
        rw [hD] at hrow hcol ⊢
        exact qk_operandRow_lt row (by simpa [MmaFoot.qkD] using hrow) col
          (by simpa [MmaFoot.qkD] using hcol)
      exact ⟨_, qk_a_elem hp hX hFw hT hO hR hI hB ht hmd (noUbInner hX) he hk hops
        hr htt⟩
    · exact mma_b_elem hp hX hFw hR hI hB hN hv hS he hon.1 hops hkd hcol htt
  · have hkd := (desc_bf16 (Or.inr rfl) hmo.2.1).1
    refine ⟨fun t htt => ?_, fun t htt => ?_⟩
    · exact hPA d s acc mask ops row col cell ⟨_, he⟩ hdone hops hcell hd256 t htt
    · exact mma_b_elem hp hX hFw hR hI hB hN hv hS he hon.1 hops hkd hcol htt

/-- **The operand elements of every completed MMA are numbers**, given the PV MMAs' A elements. -/
theorem mma_elements (hPA : PvAElements X) : MmaElements X :=
  fun i => mma_elem_at hp hX hFw hR hI hB hN hv hS hT hO ht hmd i (hPA i)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
