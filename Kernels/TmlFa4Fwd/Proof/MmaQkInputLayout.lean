-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.InputCopies
public import Kernels.TmlFa4Fwd.Proof.MmaQkIssue
public import Kernels.TmlFa4Fwd.Proof.PagedKvGeometry
public import Lemmas.Tcgen05.TcSharedAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The compact operand-byte ordinal used by the MMA snapshot. -/
def qkByteIndex (row k byte : Nat) : Nat := 32 * row + 2 * k + byte

def qkInputStart (l : Launch) (block : Fin 4) (use : Nat) : TcMma.Operand → Nat
  | .a => qStart l (qkStage block)
  | .b => kvStart l use

private theorem qkAddressCalculation (start row k byte : Nat) (hb : byte < 2) :
    TcShared.byteAddress 2 .k (sharedDescriptor start 16) row k byte =
      some (TensorSwizzle.offset .b128 0 (start + 128 * row + 2 * k + byte)) := by
  unfold TcShared.byteAddress
  have hN : start + TcShared.linear 2 .k .b128 (sharedDescriptor start 16) row k + byte =
      start + 128 * row + 2 * k + byte := by
    rw [TcShared.linear_k128 2 _ row k rfl]
    omega
  simpa [hb, sharedDescriptor, TcShared.Swizzle.offset] using
    congrArg (TensorSwizzle.offset .b128 0) hN

/-- Both frozen QK operands read the same K-major swizzle, from their respective physical planes. -/
theorem qkInputByteLoc (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat)
    (op : TcMma.Operand) {row k byte : Nat} (hr : row < 128) (hk : k < 16) (hb : byte < 2) :
    (qkOperands l g block step use).byteLoc op (qkByteIndex row k byte) =
      some ⟨.shared, g / l.block, TensorSwizzle.offset .b128 0
        (qkInputStart l block use op + qkFragment step + 128 * row + 2 * k + byte)⟩ := by
  have hR : qkByteIndex row k byte / 32 = row := by unfold qkByteIndex; omega
  have hK : qkByteIndex row k byte / 2 % 16 = k := by unfold qkByteIndex; omega
  have hB : qkByteIndex row k byte % 2 = byte := by unfold qkByteIndex; omega
  have hD : TcMma.Valid ⟨.one, .f16 .bf16 .f32, 128, 128, false, false,
      false, false, false⟩ := by decide
  cases op <;>
    simp only [qkOperands, TcMma.OperandSpec.byteLoc, qkDescriptor, qkInputStart,
      TcMma.Kind.width, TcMma.Kind.k, TcMma.Operand.extent, TcMma.Operand.major,
      Nat.reduceMul, CtaGroup.size, Nat.div_one, Bool.false_eq_true, and_false, reduceCtorEq,
      false_and, ↓reduceIte, hR, hK, hB, hD, hr, Nat.mod_eq_of_lt hr,
      Option.isSome_none, and_true, not_true] <;>
    rw [qkAddressCalculation _ row k byte hb] <;> rfl

/-- The plane containing the contraction dimension of a QK step. -/
def qkPlane (step : Fin 8) : Nat := step.val / 4

/-- The element within the plane produced by the Q box or the ordinary K packet. -/
def qkPlaneColumn (step : Fin 8) (k : Nat) : Nat := 16 * (step.val % 4) + k

theorem qkPlaneColumn_lt (step : Fin 8) {k : Nat} (hk : k < 16) :
    qkPlaneColumn step k < 64 := by
  have h := Nat.mod_lt step.val (show 0 < 4 by decide)
  unfold qkPlaneColumn
  omega

/-- The exact slot of the Q input tensor that feeds one byte of the selected MMA operand. -/
def qkQSlot (p : Params) (step : Fin 8) {row k byte : Nat}
    (hr : row < 128) (hk : k < 16) (hb : byte < 2) : TensorTransfer.Slot p.qMap :=
  ⟨⟨qkPlaneColumn step k, by
    simpa [Params.qMap, TensorTile.count, TensorTile.step] using qkPlaneColumn_lt step hk⟩,
    ⟨row, by
      simpa [Params.qMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
        using hr⟩,
    ⟨byte, hb⟩⟩

/-- Each Q operand byte is written by the corresponding box, using the actual two-plane offset
of its K step. This equates the read and transfer addresses before any ordering argument. -/
theorem qkQInputSlot {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (block : Fin 4) (step : Fin 8) (use absoluteRow head : Nat)
    (barrier : Loc) (clusterAddress : Bool)
    {row k byte : Nat} (hr : row < 128) (hk : k < 16) (hb : byte < 2) :
    let base := qStart l (qkStage block) + 16384 * qkPlane step
    let spec := qInputSpec p (64 * qkPlane step) absoluteRow head
      ⟨.shared, g / l.block, base⟩ barrier clusterAddress
    (qkOperands l g block step use).byteLoc .a (qkByteIndex row k byte) =
      some (spec.sharedLoc (qkQSlot p step hr hk hb)) := by
  dsimp only
  rw [qkInputByteLoc l g block step use .a hr hk hb]
  let base := qStart l (qkStage block) + 16384 * qkPlane step
  have hBase : base % 128 = 0 := by
    dsimp [base, qStart]
    have := hp.shared.1
    omega
  have hEq : qkInputStart l block use .a + qkFragment step + 128 * row + 2 * k + byte =
      base + (128 * row + 2 * qkPlaneColumn step k + byte) := by
    simp only [qkInputStart, qkFragment, qkPlaneColumn, base, qkPlane]
    omega
  rw [hEq, TensorSwizzle.offset_add_base _ _ _ hBase]
  simp [qInputSpec, TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, TensorTile.swizzleWidth, TensorTile.count, TensorTile.step, Params.qMap,
    qkQSlot, TensorDescriptor.Format.bytes, base, Nat.mul_comm]

end
end PTX.Kernels.TmlFa4Fwd.Mma
