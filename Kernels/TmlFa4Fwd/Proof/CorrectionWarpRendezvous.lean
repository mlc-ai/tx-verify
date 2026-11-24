-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTileIngress
public import Kernels.TmlFa4Fwd.Proof.CorrectionStartSync
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def tileSetupFrame (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  correctionTileGeometryFacts l (warpLane l g lane) true ++
    correctionActiveTileFacts p l g batch lane

/-- The post-rendezvous frame includes the selected request's input offsets and live KV count. -/
def correctionBeforeRescale (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  let tile := (assignedCoordinates p batch (g / l.block)).1
  (1636, b32 (Mma.trips p batch tile)) :: (5967, b32 (256 * tile)) ::
    (1634, b32 (p.qOffset batch)) :: (1635, b32 (p.qLength batch)) ::
    tileSetupFrame p l g batch lane

end
end PTX.Kernels.TmlFa4Fwd.Correction
