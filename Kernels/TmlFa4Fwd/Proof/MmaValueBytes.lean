-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvInputLayout
public import Kernels.TmlFa4Fwd.Proof.MmaOperandValues
public import Kernels.TmlFa4Fwd.Proof.LoaderVCopies
public import Lemmas.Protocol.CpAsyncPhase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX Loader

noncomputable section

def pvLoaderLane (step : Fin 8) (col k : Nat) : Nat :=
  8 * (pvKeyRow step k % 8) + (col % 64) / 8

def pvLoaderByte (col byte : Nat) : Nat := 2 * (col % 8) + byte

/-- The priming V packet and the PV operand use the same BF16 row, column and byte. -/
theorem pvLoaderCoordinates (step : Fin 8) (tile : Nat) {col k byte : Nat}
    (hc : col < 128) (hb : byte < 2) :
    let key := pvKeyRow step k
    let lane := pvLoaderLane step col k
    let off := pvLoaderByte col byte
    kvCopyRow tile lane (key / 8) = 128 * tile + key ∧
    kvCopyColumn lane (decide (64 ≤ col)) + off / 2 = col ∧
    off % 2 = byte ∧ off < 16 := by
  dsimp only [pvLoaderLane, pvLoaderByte, kvCopyRow, kvCopyColumn]
  simp only [decide_eq_true_eq]
  split <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
