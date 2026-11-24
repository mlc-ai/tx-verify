-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmBlock
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreBytes
import Lemmas.Tcgen05.TcDataCell

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX.Proof MmaDataTrace Wg1Mma

noncomputable section

/-- The score register selects the given token in the lane's datapath half. -/
theorem scoreLoad_cell {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hg : tidOf L g < 128) (part : Fin 2) (reg : Fin 32) :
    tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val =
      ⟨Wg1Mma.ctaOf L g, tidOf L g, tmemP + (32 * part.val + reg.val)⟩ := by
  rw [tcDataCell_s32x32b, tidOf_eq hpre]
  have ht : g % 384 < 128 := by simpa only [tidOf_eq hpre] using hg
  simp only [tcDataCell32, laneBase, PTX.laneOf, Wg1Mma.ctaOf, hpre.block,
    Wg0.scoreLoadColumn, tmemP]
  congr 1 <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
