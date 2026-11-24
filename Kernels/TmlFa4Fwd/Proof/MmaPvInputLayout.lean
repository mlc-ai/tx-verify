-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvIssue
public import Kernels.TmlFa4Fwd.Proof.MmaQkKeyLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX

noncomputable section

/-- The V element's key row within the tile. -/
def pvKeyRow (step : Fin 8) (k : Nat) : Nat := 16 * step.val + k

/-- The V byte, in the same packet coordinates used by the ordinary loader copies. -/
theorem pvValueByteLoc (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat)
    (hBase : l.sharedBase % 1024 = 0) {col k byte : Nat}
    (hc : col < 128) (hk : k < 16) (hb : byte < 2) :
    let key := pvKeyRow step k
    let lane := 8 * (key % 8) + (col % 64) / 8
    (pvOperands l g block step use).byteLoc .b (qkByteIndex col k byte) =
      some ⟨.shared, g / l.block, kvCopyAddress l.sharedBase (kvSlot use) lane (key / 8)
        (decide (64 ≤ col)) + 2 * (col % 8) + byte⟩ := by
  dsimp only
  have hR : qkByteIndex col k byte / 32 = col := by unfold qkByteIndex; omega
  have hK : qkByteIndex col k byte / 2 % 16 = k := by unfold qkByteIndex; omega
  have hB : qkByteIndex col k byte % 2 = byte := by unfold qkByteIndex; omega
  simp only [pvOperands, TcMma.OperandSpec.byteLoc, pvDescriptor,
    TcMma.Kind.width, TcMma.Kind.k, TcMma.Operand.extent, TcMma.Operand.major,
    Nat.reduceMul, CtaGroup.size, Nat.div_one, Bool.false_eq_true, and_false, reduceCtorEq,
    false_and, ↓reduceIte, hR, hK, hB, hc, Nat.mod_eq_of_lt hc, and_true]
  have hAddr : TcShared.byteAddress 2 .mn (sharedDescriptor
      (kvStart l use + pvFragment step) 16384) col k byte =
      some (kvSwizzle (kvStart l use + pvFragment step +
        16384 * (col / 64) + 128 * k + 2 * (col % 64) + byte)) := by
    have hOffset : kvStart l use + pvFragment step + TcShared.linear 2 .mn .b128
        (sharedDescriptor (kvStart l use + pvFragment step) 16384) col k + byte =
      kvStart l use + pvFragment step + 16384 * (col / 64) + 128 * k + 2 * (col % 64) + byte := by
      simp only [TcShared.linear, sharedDescriptor, TcShared.Swizzle.sectors, reduceCtorEq,
        ↓reduceIte, Nat.reduceDiv, Nat.reduceMul]
      omega
    simpa [TcShared.byteAddress, sharedDescriptor, TcShared.Swizzle.offset, hb, kvSwizzle_eq_offset]
      using congrArg (TensorSwizzle.offset .b128 0) hOffset
  rw [hAddr]
  change some (⟨.shared, g / l.block, kvSwizzle (kvStart l use + pvFragment step +
    16384 * (col / 64) + 128 * k + 2 * (col % 64) + byte)⟩ : Loc) = _
  have hKey : pvKeyRow step k < 128 := by unfold pvKeyRow; have := step.isLt; omega
  let lane := 8 * (pvKeyRow step k % 8) + (col % 64) / 8
  let group := pvKeyRow step k / 8
  let low := l.sharedBase + 68608 + 1024 * (group % 2) + 16 * (lane % 64)
  let n := 32 * kvSlot use + 2 * (group / 2) + if 64 ≤ col then 16 else 0
  let off := 2 * (col % 8) + byte
  have hLane : 8 * (pvKeyRow step k % 8) + (col % 64) / 8 < 64 := by omega
  have hRaw : kvStart l use + pvFragment step + 16384 * (col / 64) +
      128 * k + 2 * (col % 64) + byte = low + 1024 * n + off := by
    dsimp only [kvStart, pvFragment, low, n, group, lane, off]
    rw [Nat.mod_eq_of_lt hLane]
    unfold pvKeyRow
    split <;> omega
  have hA : (low + 1024 * n) % 16 = 0 := by dsimp only [low]; omega
  have hOff : off < 16 := by dsimp only [off]; omega
  rw [hRaw, kvSwizzle_byte _ _ hA hOff, kvSwizzle_add_period]
  congr 2
  simp only [kvCopyAddress, low, n, group, lane, off, decide_eq_true_eq]
  split <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
