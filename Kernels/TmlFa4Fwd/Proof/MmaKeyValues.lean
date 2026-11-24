-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaOperandValues
public import Kernels.TmlFa4Fwd.Proof.LoaderCopies
public import Lemmas.Protocol.CpAsyncPhase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX Loader

noncomputable section

/-- The ordinary packet's row and byte of a K element agree with the logical contraction. -/
theorem qkLoaderCoordinates (step : Fin 8) (tile : Nat) {row k byte : Nat}
    (hk : k < 16) (hb : byte < 2) :
    let lane := qkLoaderLane step row k
    let off := qkLoaderByte step k byte
    let up := decide (4 ≤ step.val)
    kvCopyRow tile lane (row / 8) = 128 * tile + row ∧
    kvCopyColumn lane up + off / 2 = 16 * step.val + k ∧ off % 2 = byte ∧ off < 16 := by
  dsimp only [qkLoaderLane, qkLoaderByte, kvCopyRow, kvCopyColumn]
  have hCol := qkPlaneColumn_lt step hk
  have hs := step.isLt
  simp only [qkPlaneColumn, decide_eq_true_eq] at *
  split <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
