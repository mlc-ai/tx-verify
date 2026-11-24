-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaValue
public import Core.Assumption.IdealReal
public import Mathlib.Tactic

namespace PTX.Tests.TcMmaValue
open TcMma
noncomputable section

/-- Exact real arithmetic for `kind::f16` with `f16` inputs and `f32` output only. -/
private def idealMmaF16 : Assumption :=
  Assumption.idealReal "test-ideal-mma" { mma := [.f16 .f16 .f32] } "test"

private def smem : TcShared.Descriptor := ⟨0, 0, 1024, 0, false, false, .b128⟩
private def operands : OperandSpec :=
  ⟨⟨.two, .f16 .f16 .f32, 256, 256, false, false, false, false, false⟩, smem, smem, 0, 1, none,
    {}⟩
private def L : Launch :=
  { grid := 2, block := 32, clusterSize := 2, params := fun _ => none }
private def X : Execution := {
  tr := fun _ => [⟨0, .tc (.mma 0 operands false (List.replicate 8 0))⟩,
                 ⟨1, .tc (.mma 0 operands true (List.replicate 8 0))⟩],
  rf := fun _ _ => none }

-- Initial overwrite followed by accumulation pipelines without an intervening wait.
example : Pipelined L X .dWrite (0, 0) .dWrite (0, 1) := by
  refine ⟨?_, ?_, 0, operands, false, List.replicate 8 0,
    0, operands, true, List.replicate 8 0, ⟨0, rfl⟩, ⟨1, rfl⟩, ?_⟩
  · unfold SameWarp SameCta
    decide
  · exact .inl (Relation.TransGen.single (Or.inl ⟨rfl, by decide, by decide⟩))
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Different D bases and shapes do not silently inherit a pipeline.
example : ¬ SameAccumulator 0 operands 32 operands := by
  intro h; cases h.1
example : ¬ SameAccumulator 0 operands 0
    { operands with descriptor := { operands.descriptor with m := 128 } } := by
  intro h; cases h.2.1
-- Negation and shared operand addresses may change without changing the accumulator.
example : SameAccumulator 0 operands 0
    { operands with descriptor := { operands.descriptor with negateA := true }, a :=
                    { smem with start := 1024 } } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example (Y : Execution) (i : EvId) (cell : Cell) : ¬ ReadSource L Y .acc i i cell := by
  intro h; exact h.1 rfl

-- If every MMA requires an old accumulator, the model cannot synthesize one.
example (Y : Execution) (A : List Assumption)
    (noInit : ∀ i d s mask, ¬ Y.MmaIssue i d s false mask)
    (noStore : ∀ e a vals sh, ¬ Y.TSt e a vals sh)
    (i : EvId) (cell : Cell) (v : Value) : ¬ Result L A Y i cell v := by
  intro h
  obtain ⟨first, (⟨d, s, mask, hi, _⟩ | ⟨v, a, vals, sh, j, ht, -⟩)⟩ := h.has_initializer
  · exact noInit first d s mask hi
  · exact noStore _ _ _ _ ht

example (d : Descriptor) (hk : d.kind = .f16 .f16 .f32)
    (a b : List (Option Byte)) (old : Option Value) (row col : Nat) :
    eval [idealMmaF16] d true a b old row col =
      Assumption.execIdealMma d true a b old row col := by
  simp [eval, hk, List.findSome?, idealMmaF16, Assumption.idealReal]

-- A kind outside the assumption's scope gets no rule from it.
example (d : Descriptor) (hk : d.kind = .f16 .bf16 .f32)
    (a b : List (Option Byte)) (old : Option Value) (row col : Nat) :
    eval [idealMmaF16] d true a b old row col = .error .noRule := by
  simp [eval, hk, List.findSome?, idealMmaF16, Assumption.idealReal]

-- kind::i8 is exact Core arithmetic: no profile is consulted, and an unknown byte or a
-- missing old accumulator has no value.
private def int8 (v : Int) : Option Byte := some (.bits 8 (BitVec.ofInt 64 v), 0)
private def ones : List (Option Byte) := List.replicate 32 (int8 1)
private def twos : List (Option Byte) := List.replicate 32 (int8 (-2))

example : intEval true true false false ones twos none 0 0 = .ok (s32 (-64)) := rfl
example : intEval false true false false ones twos none 0 0 = .ok (s32 (-64)) := rfl
-- 0xfe read unsigned is 254.
example : intEval true false false false ones twos none 0 0 = .ok (s32 (32 * 254)) := rfl
example : intEval true true false true ones twos (some (s32 100)) 0 0 = .ok (s32 36) := rfl
example : intEval true true false true ones twos none 0 0 = .error .uninitialized := rfl
example : intEval true true false false (none :: ones.tail) twos none 0 0 = .error .uninitialized :=
  rfl
example (d : Descriptor) (hk : d.kind = .i8 true true false) :
    eval [] d false ones twos none 0 0 = .ok (s32 (-64)) := by
  simp only [eval, hk, operandRow, Nat.zero_add,
    Nat.zero_div, Nat.mul_zero, ite_self]
  rfl

end
end PTX.Tests.TcMmaValue
