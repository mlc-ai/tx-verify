-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPointerBroadcast
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingStart

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX

noncomputable section

/-- The pointer's sender belongs to the same eight-lane subgroup. The selected
scratch slot provides the high part of the pair's row coordinate. -/
theorem kvCopyRow_of_pointerLane (tile warp lane group : Nat) :
    primingLaneRow tile (32 * warp + pointerBroadcastLane lane + group % 8) +
      64 * (group / 8) = kvCopyRow tile (32 * warp + lane) group := by
  have hLane : (32 * warp + pointerBroadcastLane lane + group % 8) / 8 =
      (32 * warp + lane) / 8 := by unfold pointerBroadcastLane; omega
  have hLow : (32 * warp + pointerBroadcastLane lane + group % 8) % 8 = group % 8 := by
    unfold pointerBroadcastLane
    omega
  simp only [primingLaneRow, kvCopyColumn, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    kvCopyRow, hLane, hLow]
  omega

/-- The first pair uses the first scratch slot and the base lane of the subgroup. -/
theorem recurringFirstPointerRow (tile warp lane : Nat) :
    primingLaneRow tile (32 * warp + pointerBroadcastLane lane) =
      kvCopyRow tile (32 * warp + lane) 0 := by
  simpa using kvCopyRow_of_pointerLane tile warp lane 0

end
end PTX.Kernels.TmlFa4Fwd.Loader
