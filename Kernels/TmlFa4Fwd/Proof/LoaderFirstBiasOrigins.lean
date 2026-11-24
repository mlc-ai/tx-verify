-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasFirstVisit
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVAdmission

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy Epilogue Protocol.Bias Softmax Thread.Scores

noncomputable section

/-- The lower causal stage is at most one block shorter than the full tile. In the
loader's subtraction order the encoded residue is therefore either zero or minus one. -/
theorem firstBiasResidual (p : Params) (batch tile : Nat) :
    vPrimingResidual p batch tile = 0 ∨ vPrimingResidual p batch tile = 2 ^ 32 - 1 := by
  let extent := p.kLength batch - p.qLength batch + 256 * tile
  let keyBlocks := (p.kLength batch + 127) / 128
  let lower := min keyBlocks ((extent + 128 + 127) / 128)
  let upper := min keyBlocks ((extent + 256 + 127) / 128)
  have hResidual : vPrimingResidual p batch tile = (lower + 2 ^ 32 - upper) % 2 ^ 32 := by
    unfold vPrimingResidual Mma.trips
    have hExtent : p.kLength batch - p.qLength batch + 256 * (tile + 1) = extent + 256 := by
      dsimp [extent]
      omega
    rw [hExtent]
  have hGap : upper ≤ lower + 1 := by dsimp [lower, upper]; omega
  have hLe : lower ≤ upper := by dsimp [lower, upper]; omega
  rw [hResidual]
  omega

/-- The priming packet's two Bias issues for each query stage. -/
def firstBiasIssueSite : Fin 2 → Fin 2 → Fin 14
  | 0, 0 => 2
  | 0, 1 => 3
  | 1, 0 => 6
  | 1, 1 => 7

def firstBiasPrepSteps (stage : Fin 2) : Nat :=
  if stage.val = 0 then 4 else 3

/-- The first instruction after the selected loader lane's Bias election branch. -/
def firstBiasPrepPc (stage half : Fin 2) : Nat :=
  (inputSite (firstBiasIssueSite stage half)).pc - firstBiasPrepSteps stage

end
end PTX.Kernels.TmlFa4Fwd.Loader
