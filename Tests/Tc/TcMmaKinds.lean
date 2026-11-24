-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaOperands
public import Lemmas.Tcgen05.TcMmaResultLayout
public import Lemmas.Tcgen05.TcMmaValue

/-! One MMA rule family for both CTA groups and both kinds: operand placement, result
cells, exact integer results and the issue checks, across the four combinations. -/
namespace PTX.Tests.TcMmaKinds
open TcMma
noncomputable section

private def launch : Launch :=
  { grid := 8, block := 128, params := fun _ => none, clusterSize := ⟨4, by decide⟩ }
private def k8 : TcShared.Descriptor := ⟨0, 128, 256, 0, false, false, .none⟩

/-! ### cta_group::2, kind::i8 -/

private def i8x2 : Descriptor := ⟨.two, .i8 false true false, 256, 32, false, false, false, false,
    false⟩
private def at2 (issuer : Nat) (op : Operand) (index : Nat) : Option Loc := do
  let s ← makeOperands launch issuer i8x2 k8 k8
  s.byteLoc op index

-- Either CTA of the pair resolves the same two CTAs.
example : (makeOperands launch 5 i8x2 k8 k8).map (fun s => (s.lowCta, s.highCta)) = some (4, 5) :=
  rfl
example : (makeOperands launch 4 i8x2 k8 k8).map (fun s => (s.lowCta, s.highCta)) = some (4, 5) :=
  rfl
-- A rows 0..127 are in the even CTA and 128..255 in the odd one, one byte per element.
example : at2 5 .a 0 = some ⟨.shared, 4, 0⟩ := rfl
example : at2 5 .a (127 * 32 + 31) = some ⟨.shared, 4, 16 * 7 + 256 * 15 + 15 + 128⟩ := rfl
example : at2 5 .a (128 * 32) = some ⟨.shared, 5, 0⟩ := rfl
-- B columns 0..15 are in the even CTA and 16..31 in the odd one.
example : at2 4 .b (15 * 32) = some ⟨.shared, 4, 16 * 7 + 256⟩ := rfl
example : at2 4 .b (16 * 32) = some ⟨.shared, 5, 0⟩ := rfl
example : at2 4 .b (32 * 32) = none := rfl

-- Layout A: M = 256 over the pair, one row per lane, N columns.
private def specA : OperandSpec := ⟨i8x2, k8, k8, 4, 5, none, {}⟩
example : resultCell specA 32 0 0 = some ⟨4, 0, 32⟩ := rfl
example : resultCell specA 32 200 31 = some ⟨5, 72, 63⟩ := rfl
-- Layout B: M = 128 splits N over the lower and upper 64 lanes of each CTA.
private def specB : OperandSpec := ⟨{ i8x2 with m := 128 }, k8, k8, 4, 5, none, {}⟩
example : resultCell specB 0 0 15 = some ⟨4, 0, 15⟩ := rfl
example : resultCell specB 0 0 16 = some ⟨4, 64, 0⟩ := rfl
example : resultCell specB 0 64 16 = some ⟨5, 64, 0⟩ := rfl
example : resultColumns specB.descriptor = 16 := rfl
-- Eight mask words for a pair; four would be malformed.
example : writeCell specA 0 [0, 0, 0, 0] 0 0 = none := rfl
example : writeCell specA 0 [0, 0, 0, 0, 1, 0, 0, 0] 128 0 = none := rfl
example : writeCell specA 0 [0, 0, 0, 0, 1, 0, 0, 0] 129 0 = some ⟨5, 1, 0⟩ := rfl

/-! ### cta_group::1, kind::f16 -/

private def f16x1 : Descriptor := ⟨.one, .f16 .bf16 .f32, 128, 8, false, false, false, false, false⟩
private def at1 (op : Operand) (index : Nat) : Option Loc := do
  let s ← makeOperands launch 6 f16x1 k8 k8
  s.byteLoc op index

-- Both operands stay in the issuer's CTA, two bytes per element, 16 elements per row.
example : at1 .a 0 = some ⟨.shared, 6, 0⟩ := rfl
example : at1 .a 1 = some ⟨.shared, 6, 1⟩ := rfl
example : at1 .a 2 = some ⟨.shared, 6, 2⟩ := rfl
example : at1 .a 16 = some ⟨.shared, 6, 128⟩ := rfl
example : at1 .a (127 * 32) = some ⟨.shared, 6, 16 * 7 + 256 * 15⟩ := rfl
example : at1 .b (8 * 32) = none := rfl
-- Layout D: lane = row, column = base + j.
private def specD : OperandSpec := ⟨f16x1, k8, k8, 6, 6, none, {}⟩
example : resultCell specD 100 127 7 = some ⟨6, 127, 107⟩ := rfl
example : resultCell specD 505 0 0 = none := rfl

/-! ### cta_group::1, M = 64 (Layout F) -/

private def m64 : Descriptor := ⟨.one, .i8 true false false, 64, 48, false, false, false, false,
    false⟩
private def specF : OperandSpec := ⟨m64, k8, k8, 6, 6, none, {}⟩

-- Table 48 admits M = 64 for cta_group::1 (and not for cta_group::2).
example : decode .one false .i8 (4 * 2 ^ 24 + 6 * 2 ^ 17 + 0x4a0 - 1024) = some m64 := rfl
example : decode .two false .i8 (4 * 2 ^ 24 + 6 * 2 ^ 17 + 0x4a0 - 1024) = none := rfl
example : decode .one false .f16 (4 * 2 ^ 24 + 1 * 2 ^ 17 + 16) =
    some ⟨.one, .f16 .f16 .f32, 64, 8, false, false, false, false, false⟩ := rfl
-- Sixteen rows per 32-lane subpartition: rows 0..15 → lanes 0..15, 16 → 32, 63 → 111.
example : resultCell specF 0 0 0 = some ⟨6, 0, 0⟩ := rfl
example : resultCell specF 0 15 47 = some ⟨6, 15, 47⟩ := rfl
example : resultCell specF 0 16 0 = some ⟨6, 32, 0⟩ := rfl
example : resultCell specF 0 63 0 = some ⟨6, 111, 0⟩ := rfl
example : resultColumns m64 = 48 := rfl
-- Lane alignment 16 uses the other half of each subpartition.
example : resultCell specF (16 * 2 ^ 16 + 100) 0 0 = some ⟨6, 16, 100⟩ := rfl
example : resultCell specF (16 * 2 ^ 16 + 100) 63 1 = some ⟨6, 127, 101⟩ := rfl
-- Other lane fields are not datapath alignments; M = 128 has only alignment 0.
example : resultCell specF (8 * 2 ^ 16) 0 0 = none := rfl
example : resultCell specF (32 * 2 ^ 16) 0 0 = none := rfl
example : resultCell specD (16 * 2 ^ 16) 0 0 = none := rfl
example : resultCell specF 0 64 0 = none := rfl
example : resultCell specF 465 0 0 = none := rfl
-- The general statement, for every row and column.
example (row col : Nat) (hr : row < 64) (hc : col < 48) :
    resultCell specF (16 * 2 ^ 16) row col = some ⟨6, 16 + row % 16 + 32 * (row / 16), col⟩ := by
  have := resultCell_layoutF (s := specF) (base := 16 * 2 ^ 16) rfl rfl rfl (by decide)
    (.inr rfl) hr hc (by decide)
  simpa [show specF.lowCta = 6 from rfl] using this
-- Masks address physical lanes: word 3 bit 15 is lane 111, i.e. row 63.
example : writeCell specF 0 [0, 0, 0, 2 ^ 15] 63 0 = none := rfl
example : writeCell specF 0 [0, 0, 0, 2 ^ 15] 62 0 = some ⟨6, 110, 0⟩ := rfl

/-! ### Exact integer results -/

private def int8 (v : Int) : Option Byte := some (.bits 8 (BitVec.ofInt 64 v), 0)
private def i8x1 : Descriptor := ⟨.one, .i8 true true false, 128, 8, false, false, false, false,
    false⟩
private def spec1 : OperandSpec := ⟨i8x1, k8, k8, 0, 0, none, {}⟩
private def masks : List Nat := [0, 0, 0, 0]
-- A row of 3s and a column of -1s: every product sums to -96.
private def ops : AsyncCopy.MmaOperands :=
  ⟨List.replicate 4096 (int8 3), List.replicate 256 (int8 (-1))⟩
private def X : Execution where
  tr := fun g => if g = 0 then [⟨0, .tc (.mma 0 spec1 false masks)⟩] else []
  rf := fun _ _ => none
  async := { mmaOperands := fun i => if i = (0, 0) then some ops else none }

private theorem issue : X.MmaIssue (0, 0) 0 spec1 false masks := ⟨0, rfl⟩

-- With no numerical profile the integer result is derived exactly.
example (L : Launch) : Result L [] X (0, 0) ⟨0, 5, 3⟩ (s32 (-96)) :=
  .overwrite issue (row := 5) (col := 3) rfl rfl rfl

/-- Layout D for this test MMA. -/
private theorem cell_inv {row col lane column : Nat}
    (h : writeCell spec1 0 masks row col = some ⟨0, lane, column⟩) :
    row = lane ∧ col = column ∧ row < 128 ∧ col < 8 := by
  have hcell := writeCell_resultCell h
  rw [resultCell_layoutD rfl rfl (by decide)] at hcell
  split_ifs at hcell with hg
  simp only [Option.some.injEq, Cell.mk.injEq] at hcell
  obtain ⟨-, rfl, hc⟩ := hcell
  exact ⟨rfl, by simpa using hc, hg.1, hg.2.1⟩

-- No other value can be derived for that cell.
example (L : Launch) (v : Value) (h : Result L [] X (0, 0) ⟨0, 5, 3⟩ v) : v = s32 (-96) := by
  cases h with
  | @overwrite i d s mask row col cell operands value hi hp hr ha =>
    obtain ⟨pc, hi⟩ := hi
    simp [Execution.get, X] at hi
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hi
    simp only [X, ite_true, Option.some.injEq] at hr
    subst hr
    obtain ⟨rfl, rfl, -, -⟩ := cell_inv hp
    have : eval [] i8x1 false ops.a ops.b none 5 3 = .ok (s32 (-96)) := rfl
    rw [show spec1.descriptor = i8x1 from rfl, this] at ha
    cases ha
    rfl
  | accumulate hi _ _ _ _ _ =>
    obtain ⟨pc, hi⟩ := hi
    simp [Execution.get, X] at hi
  | accumulateStored hi _ _ _ _ _ =>
    obtain ⟨pc, hi⟩ := hi
    simp [Execution.get, X] at hi

-- A completed integer MMA with an unknown operand byte has no result: it is unsafe.
private def badOps : AsyncCopy.MmaOperands :=
  ⟨none :: List.replicate 4095 (int8 3), List.replicate 256 (int8 (-1))⟩
private def Xu : Execution :=
  { X with async := { mmaOperands := fun i => if i = (0, 0) then some badOps else none
                      mmaDone := fun i => i = (0, 0) } }
example (L : Launch) : ¬ CompletedValues L [] Xu (0, 0) := by
  intro h
  obtain ⟨v, hv⟩ := h (by simp [Xu]) ⟨0, 0, 0⟩ ⟨0, spec1, false, masks, 0, 0, ⟨0, rfl⟩, rfl⟩
  cases hv with
  | @overwrite i d s mask row col cell operands value hi hp hr ha =>
    obtain ⟨pc, hi⟩ := hi
    simp [Execution.get, Xu, X] at hi
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hi
    simp only [Xu, ite_true, Option.some.injEq] at hr
    subst hr
    obtain ⟨rfl, rfl, -, -⟩ := cell_inv hp
    have : eval [] i8x1 false badOps.a badOps.b none 0 0 = .error .uninitialized := rfl
    rw [show spec1.descriptor = i8x1 from rfl, this] at ha
    cases ha
  | accumulate hi _ _ _ _ _ =>
    obtain ⟨pc, hi⟩ := hi
    simp [Execution.get, Xu, X] at hi
  | accumulateStored hi _ _ _ _ _ =>
    obtain ⟨pc, hi⟩ := hi
    simp [Execution.get, Xu, X] at hi

/-! ### Issue checks -/

-- A cta_group::1 D that runs past column 511 is rejected at issue.
example (L : Launch) (i : EvId) : ¬ IssueShape L i 505 spec1 masks := by
  intro h
  have hb := h.2.2.2.2.2.2.2.2.1
  simp [resultColumns, spec1, i8x1, CtaGroup.size] at hb
-- A group-1 issue with a pair's eight mask words is malformed.
example (L : Launch) (i : EvId) : ¬ IssueShape L i 0 spec1 (List.replicate 8 0) := by
  intro h
  have hm := h.2.2.1.1
  simp [spec1, i8x1, CtaGroup.size] at hm

end
end PTX.Tests.TcMmaKinds
