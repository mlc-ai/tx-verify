-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleCounter
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleStage
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Flow.Code.Part125

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The two stage bases are computed once per tile. This straight-line entry expands them
into every rescale address and initializes the negative iteration counter. -/
theorem rescaleInitialize (l : Launch) (g : Nat) {blocks : Nat}
    (hPositive : 2 ≤ blocks) (hCount : blocks < 2 ^ 31) :
    Seg kernel [] l g 15 7991
      [(1629, b32 (outputAddress l g 0 0)), (1633, b32 (outputAddress l g 1 0)),
        (1636, b32 blocks)] 8006
      ((7278, remainingRescaleWord blocks) ::
        (rescaleStageAddresses l g 0 ++ rescaleStageAddresses l g 1)) := by
  intro t ht
  have hC : blocks < 2 ^ 32 := by omega
  have h0 : outputColumn (0 : Fin 2) = 256 := rfl
  have h1 : outputColumn (1 : Fin 2) = 384 := rfl
  have hEncoded := tmem_warp_encoding_lt l g (col := 496) (by decide)
  have hEncoded' : 65536 * laneBase l g + 496 < 2 ^ 32 := hEncoded
  change ∃ u, run kernel [] l g 15 t = some u ∧ At u 8006
      [(7278, remainingRescaleWord blocks),
       (1629, b32 (outputAddress l g 0 0)),
       (1637, b32 (outputAddress l g 0 16)),
       (1638, b32 (outputAddress l g 0 32)),
       (1639, b32 (outputAddress l g 0 48)),
       (1640, b32 (outputAddress l g 0 64)),
       (1641, b32 (outputAddress l g 0 80)),
       (1642, b32 (outputAddress l g 0 96)),
       (1643, b32 (outputAddress l g 0 112)),
       (1633, b32 (outputAddress l g 1 0)),
       (1644, b32 (outputAddress l g 1 16)),
       (1645, b32 (outputAddress l g 1 32)),
       (1646, b32 (outputAddress l g 1 48)),
       (1647, b32 (outputAddress l g 1 64)),
       (1648, b32 (outputAddress l g 1 80)),
       (1649, b32 (outputAddress l g 1 96)),
       (1650, b32 (outputAddress l g 1 112))]
  seg_fp ht using
    norm_bits [remainingRescaleWord, outputAddress, h0, h1]

end
end PTX.Kernels.TmlFa4Fwd.Correction
