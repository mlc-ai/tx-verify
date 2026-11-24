-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.OutputMap

@[expose] public section

/-! # The output stores' sites, staging slots and boxes -/

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX

noncomputable section

/-- Each output tile stage is issued as four 32-column subboxes. -/
def storePc (stage : Fin 2) (subbox : Fin 4) : Nat :=
  if stage = 0 then 2963 + 2 * subbox.val else 2976 + subbox.val

def sharedSlot (l : Launch) (g : Nat) (stage : Fin 2) (subbox : Fin 4) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + (3072 + 65536 * stage.val + 16384 * subbox.val)⟩

def stageRow (tile : Nat) (stage : Fin 2) : Nat := 256 * tile + 128 * stage.val

/-- The specification of an output store: a subbox of a stage of a tile, through the O map. -/
def writebackStoreSpec (p : Params) (l : Launch) (g batch head tile : Nat)
    (stage : Fin 2) (subbox : Fin 4) : TensorStore.Spec :=
  ⟨⟨3, p.oMap, oCoordinate p batch head (stageRow tile stage) (32 * subbox.val),
    sharedSlot l g stage subbox, none⟩, none⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
