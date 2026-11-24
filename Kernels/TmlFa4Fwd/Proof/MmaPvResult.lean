-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFragmentResult
public import Kernels.TmlFa4Fwd.Proof.MmaValueBytes
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmemCells
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstPublication

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX
open scoped BigOperators

noncomputable section

/-- Masked value rows are represented by the ordinary loader's zero fill. -/
def pvValue (p : Params) (batch head key col : Nat) : ℝ :=
  if key < p.kLength batch then p.v (p.page batch (key / 16)) (head / 6) (key % 16) col
  else 0

/-- The two physically distinct PV operands hold the probabilities and the paged V bytes. -/
structure PvCellInputs (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (block : Fin 4) (use batch head firstK : Nat) (row col : Fin 128)
    (issues : Fin 8 → EvId) (weights : Nat → ℝ) : Prop where
  probability : ∀ (step : Fin 8) (k byte : Nat), k < 16 → byte < 2 →
    ∀ ops, X.async.mmaOperands (issues step) = some ops →
      ops.a[qkByteIndex row.val k byte]? =
        some (some ((Value.float .bf16 (weights (16 * step.val + k))).byteAt byte))
  value : ∀ (step : Fin 8) (k byte : Nat), k < 16 → byte < 2 → ∃ loc,
    (pvOperands l g block step use).byteLoc .b (qkByteIndex col.val k byte) = some loc ∧
    OperandByteSource l X (issues step) true (qkByteIndex col.val k byte) loc
      (if firstK + 16 * step.val + k < p.kLength batch then
        (Value.float .bf16 (pvValue p batch head (firstK + 16 * step.val + k) col.val)).byteAt byte
        else AsyncCopy.zeroByte)

theorem PvCellInputs.elements {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g use batch head firstK : Nat} {block : Fin 4} {row col : Fin 128}
    {issues : Fin 8 → EvId} {weights : Nat → ℝ}
    (hIn : PvCellInputs p l X g block use batch head firstK row col issues weights)
    (hX : Consistent l kernel Assumptions.all m X) (step : Fin 8)
    {ops : AsyncCopy.MmaOperands} {acc : Bool}
    (hi : X.MmaIssue (issues step) (outputColumn (pvSite block).stage)
      (pvOperands l g block step use) acc (List.replicate 4 0))
    (ho : X.async.mmaOperands (issues step) = some ops) :
    (∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row.val k =
      .ok (weights (16 * step.val + k))) ∧
    (∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col.val k =
      .ok (pvValue p batch head (firstK + 16 * step.val + k) col.val)) := by
  constructor
  · intro k hk
    exact idealBf16Element_of_bytes (hIn.probability step k 0 hk (by decide) ops ho)
      (hIn.probability step k 1 hk (by decide) ops ho)
  · intro k hk
    have hByte (byte : Nat) (hb : byte < 2) :
        ops.b[qkByteIndex col.val k byte]? = some (some
          (if firstK + 16 * step.val + k < p.kLength batch then
            (Value.float .bf16
              (pvValue p batch head (firstK + 16 * step.val + k) col.val)).byteAt byte
          else AsyncCopy.zeroByte)) := by
      obtain ⟨loc, hLoc, hSource⟩ := hIn.value step k byte hk hb
      exact operandByte_observed hX hi ho (isB := true) hLoc hSource
    by_cases hKey : firstK + 16 * step.val + k < p.kLength batch
    · exact idealBf16Element_of_bytes
        (by simpa only [hKey, ↓reduceIte] using hByte 0 (by decide))
        (by simpa only [hKey, ↓reduceIte] using hByte 1 (by decide))
    · rw [pvValue, ite_eq_right hKey]
      exact idealBf16Element_of_zeroBytes
        (by simpa only [hKey, ↓reduceIte] using hByte 0 (by decide))
        (by simpa only [hKey, ↓reduceIte] using hByte 1 (by decide))

/-- The decoded PV tile adds the full 128-element weighted value sum to the corrected carry. -/
theorem pvCellResult {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g use batch head firstK : Nat} (block : Fin 4) (row col : Fin 128)
    (issues : Fin 8 → EvId) (weights : Nat → ℝ) (keep : Bool) (carry : ℝ)
    (hIn : PvCellInputs p l X g block use batch head firstK row col issues weights)
    (hi : ∀ step : Fin 8, X.MmaIssue (issues step) (outputColumn (pvSite block).stage)
      (pvOperands l g block step use) (keep || decide (0 < step.val)) (List.replicate 4 0))
    (ho : ∀ step : Fin 8, ∃ ops, X.async.mmaOperands (issues step) = some ops) :
    let dst := outputColumn (pvSite block).stage
    let cell : TcMma.Cell := ⟨g / l.block, row.val, dst + col.val⟩
    (∀ step : Fin 8, step.val ≠ 0 → TcMma.ReadSource l X .acc
      (issues ⟨step.val - 1, by have := step.isLt; omega⟩) (issues step) cell) →
    (keep = false → carry = 0) →
    (keep = true → ∃ source, TcMma.ReadSource l X .acc source (issues 0) cell ∧
      (TcMma.Result l Assumptions.all X source cell (.float .f32 carry) ∨
        TcMma.StoreValue l X source cell (.float .f32 carry))) →
    TcMma.Result l Assumptions.all X (issues 7) cell
      (.float .f32 (carry + ∑ k ∈ Finset.range 128,
        weights k * pvValue p batch head (firstK + k) col.val)) := by
  dsimp only
  intro hPrevious hStart hCarry
  let dst := outputColumn (pvSite block).stage
  let cell : TcMma.Cell := ⟨g / l.block, row.val, dst + col.val⟩
  let vals := fun k => pvValue p batch head (firstK + k) col.val
  have hFrag : CellFragments l X issues (fun step => pvOperands l g block step use)
      dst row.val col.val cell keep weights vals := by
    refine ⟨hi, ?_, ?_, hPrevious⟩
    · intro step
      exact writeCell_no_mask_128 rfl rfl row.isLt row.isLt (pvResultCell rfl _ row col)
    · intro step
      obtain ⟨ops, hObs⟩ := ho step
      obtain ⟨hA, hB⟩ := hIn.elements hX step (hi step) hObs
      obtain ⟨hValid, hLenA, hLenB⟩ := hX.mma_observation_shape (hi step) hObs
      refine ⟨ops, hObs, fun old prev hPrev => ?_⟩
      exact evalBf16Cell rfl hValid rfl rfl rfl hLenA hLenB row.isLt col.isLt hA
        (by simpa only [vals, Nat.add_assoc] using hB) hPrev
  exact fullFragmentResult hFrag carry hStart hCarry

end
end PTX.Kernels.TmlFa4Fwd.Mma
