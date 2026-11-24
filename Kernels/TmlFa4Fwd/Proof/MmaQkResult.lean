-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFragmentResult
public import Kernels.TmlFa4Fwd.Proof.MmaKeyValues

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX
open scoped BigOperators

noncomputable section

/-- Q is zero-filled beyond the packed descriptor and otherwise holds its input row. -/
def qkQuery (p : Params) (row head d : Nat) : ℝ :=
  if row < p.totalQ then p.q row head d else 0

/-- An invalid key row is supplied by the ordinary copy's explicit zero fill. -/
def qkKey (p : Params) (batch head key d : Nat) : ℝ :=
  if key < p.kLength batch then p.k (p.page batch (key / 16)) (head / 6) (key % 16) d
  else 0

private theorem qkDim (step : Fin 8) (k : Nat) :
    64 * qkPlane step + qkPlaneColumn step k = 16 * step.val + k := by
  unfold qkPlane qkPlaneColumn
  omega

/-- Each observed QK fragment reads the actual launch values of these operands. Its two input
sources may use different async engines, but share the same logical contraction dimension. -/
structure QkCellInputs (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (block : Fin 4) (use batch head firstQ firstK : Nat) (row col : Fin 128)
    (issues : Fin 8 → EvId) : Prop where
  query : ∀ (step : Fin 8) (k byte : Nat), k < 16 → byte < 2 → ∃ loc,
    (qkOperands l g block step use).byteLoc .a (qkByteIndex row.val k byte) = some loc ∧
    OperandByteSource l X (issues step) false (qkByteIndex row.val k byte) loc
      ((Value.float .bf16 (qkQuery p (firstQ + row.val) head (16 * step.val + k))).byteAt byte)
  key : ∀ (step : Fin 8) (k byte : Nat), k < 16 → byte < 2 → ∃ loc,
    (qkOperands l g block step use).byteLoc .b (qkByteIndex col.val k byte) = some loc ∧
    OperandByteSource l X (issues step) true (qkByteIndex col.val k byte) loc
      (if firstK + col.val < p.kLength batch then
        (Value.float .bf16 (qkKey p batch head (firstK + col.val) (16 * step.val + k))).byteAt byte
        else AsyncCopy.zeroByte)

/-- Rebuild the observed Q and K elements directly from the two byte snapshots. -/
theorem QkCellInputs.elements {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g use batch head firstQ firstK : Nat} {block : Fin 4} {row col : Fin 128}
    {issues : Fin 8 → EvId}
    (hIn : QkCellInputs p l X g block use batch head firstQ firstK row col issues)
    (hX : Consistent l kernel Assumptions.all m X) (step : Fin 8)
    {operands : AsyncCopy.MmaOperands} {acc : Bool}
    (hi : X.MmaIssue (issues step) (scoreColumn (qkStage block)) (qkOperands l g block step use)
      acc (List.replicate 4 0))
    (ho : X.async.mmaOperands (issues step) = some operands) :
    (∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a operands.a row.val k =
      .ok (qkQuery p (firstQ + row.val) head (16 * step.val + k))) ∧
    (∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b operands.b col.val k =
      .ok (qkKey p batch head (firstK + col.val) (16 * step.val + k))) := by
  constructor
  · intro k hk
    have hb (byte : Nat) (hj : byte < 2) :
        operands.a[qkByteIndex row.val k byte]? = some (some ((Value.float .bf16
          (qkQuery p (firstQ + row.val) head (16 * step.val + k))).byteAt byte)) := by
      obtain ⟨loc, hl, hByte⟩ := hIn.query step k byte hk hj
      exact operandByte_observed hX hi ho (isB := false) hl hByte
    exact idealBf16Element_of_bytes (hb 0 (by decide)) (hb 1 (by decide))
  · intro k hk
    have hb (byte : Nat) (hj : byte < 2) :
        operands.b[qkByteIndex col.val k byte]? = some (some
          (if firstK + col.val < p.kLength batch then (Value.float .bf16
            (qkKey p batch head (firstK + col.val) (16 * step.val + k))).byteAt byte
          else AsyncCopy.zeroByte)) := by
      obtain ⟨loc, hl, hByte⟩ := hIn.key step k byte hk hj
      exact operandByte_observed hX hi ho (isB := true) hl hByte
    by_cases hKey : firstK + col.val < p.kLength batch
    · exact idealBf16Element_of_bytes
        (by simpa only [hKey, ↓reduceIte] using hb 0 (by decide))
        (by simpa only [hKey, ↓reduceIte] using hb 1 (by decide))
    · rw [qkKey, ite_eq_right hKey]
      exact idealBf16Element_of_zeroBytes
        (by simpa only [hKey, ↓reduceIte] using hb 0 (by decide))
        (by simpa only [hKey, ↓reduceIte] using hb 1 (by decide))

/-- The last actual QK issue supplies the full dot product in the stage's score cell. -/
theorem qkCellResult {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g use batch head firstQ firstK : Nat} (block : Fin 4) (row col : Fin 128)
    (issues : Fin 8 → EvId)
    (hIn : QkCellInputs p l X g block use batch head firstQ firstK row col issues)
    (hi : ∀ step : Fin 8, X.MmaIssue (issues step) (scoreColumn (qkStage block))
      (qkOperands l g block step use) (decide (0 < step.val)) (List.replicate 4 0))
    (ho : ∀ step : Fin 8, ∃ ops, X.async.mmaOperands (issues step) = some ops)
    (hPrior : ∀ step : Fin 8, step.val ≠ 0 →
      TcMma.ReadSource l X .acc (issues ⟨step.val - 1, by have := step.isLt; omega⟩) (issues step)
        ⟨g / l.block, row.val, scoreColumn (qkStage block) + col.val⟩) :
    TcMma.Result l Assumptions.all X (issues 7)
      ⟨g / l.block, row.val, scoreColumn (qkStage block) + col.val⟩
      (.float .f32 (∑ d ∈ Finset.range 128,
        qkQuery p (firstQ + row.val) head d * qkKey p batch head (firstK + col.val) d)) := by
  let x := qkQuery p (firstQ + row.val) head
  let y := qkKey p batch head (firstK + col.val)
  have hFrag : CellFragments l X issues (fun step => qkOperands l g block step use)
      (scoreColumn (qkStage block)) row.val col.val
      ⟨g / l.block, row.val, scoreColumn (qkStage block) + col.val⟩ false x y := by
    refine ⟨hi, ?_, ?_, hPrior⟩
    · intro step
      exact writeCell_no_mask_128 rfl rfl row.isLt row.isLt (qkResultCell rfl _ row col)
    · intro step
      obtain ⟨ops, hObs⟩ := ho step
      obtain ⟨hA, hB⟩ := hIn.elements hX step (hi step) hObs
      obtain ⟨hValid, hLenA, hLenB⟩ := hX.mma_observation_shape (hi step) hObs
      refine ⟨ops, hObs, fun old prev hPrev => ?_⟩
      exact evalBf16Cell rfl hValid rfl rfl rfl
        (by exact hLenA) (by exact hLenB) row.isLt col.isLt hA hB hPrev
  have h := fullFragmentResult hFrag 0 (fun _ => rfl) (fun h => by cases h)
  simpa only [x, y, zero_add] using h

/-- The two address conventions index the same Q dimension. -/
theorem qkQSlotLogicalColumn (step : Fin 8) (k : Nat) :
    64 * qkPlane step + qkPlaneColumn step k = 16 * step.val + k :=
  qkDim step k

end
end PTX.Kernels.TmlFa4Fwd.Mma
