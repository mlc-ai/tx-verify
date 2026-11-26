-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqMma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Cover
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region

@[expose] public section

/-! # Every tile byte a dequant store writes is read by an MMA of its use

A dequant lane's chunk store `W` of use `u` into tile `b` of its CTA (block `2 u + b`) writes
bytes of the tile; every byte is read by a QK MMA of the same block (`mma_qkCover`), which has
`u + 1` polls of `dequantReady b`, so `W` is ordered before that read (`dq_before`).
The MMA exists once a PV commit to `svDone` of a block at or after `2 u + b` does (the lane's
block count bounds the block of `W`, `dequant_wrUse`): `dq_mmaCover`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **A dequant store is ordered before the QK MMA that reads its byte**: for a PV commit to
`svDone s0` of the MMA lane of CTA `c` with `n` earlier commits to it, at the CTA's last block
(`blocksOf ≤ 2 n + s0 + 1`), a chunk store of a lane of the CTA covering `l` is before a QK MMA of
the lane that reads `l`, which is before the commit. -/
theorem dq_mmaCover {c h k ic pcw pc0 : Nat} {s0 : Fin 2} {ac : Acc} {bs : List Byte}
    {sp : TcCommit.Spec} {l : Loc}
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : MbarRow.DequantAt L h pcw)
    (hcov : ac.Covers l) (hhc : h / L.block = c) (hmc : mmaLane L X c / L.block = c)
    (hi : X.get (mmaLane L X c, ic) = some ⟨pc0, .tc (.commit sp)⟩)
    (hm : sp.mbar = mbarLoc L c (.svDone s0))
    (hlast : blocksOf P L c ≤ 2 * ((X.tr (mmaLane L X c)).take ic).countP
      (PTX.Flow.commitsTo (mbarLoc L c (.svDone s0))) + s0.val + 1) :
    ∃ j < ic, ∃ pc bb idx sp' acc mask,
      X.get (mmaLane L X c, j) = some ⟨pc, .tc (.mma bb sp' acc mask)⟩ ∧
      MbarRow.MmaAt L (mmaLane L X c) pc ∧ 1853 < pc ∧
      X.MmaFootprint (mmaLane L X c, j) true idx l ∧
      modelCausality L X l (.thread (h, k)) (.async (mmaLane L X c, j) (.mmaRead true idx)) := by
  obtain ⟨bw, r, s', u, hws, hpol, harr, hub⟩ := dequant_wrUse hp hX hFw hW hat
  have hlt := MemRow.dqChunk_lt (i := h % 128) (Nat.mod_lt _ (by decide)) r.isLt s'.isLt
  have hsi : MemRow.SharedIn L (h / L.block) (.dequant bw) ac :=
    MemRow.wsAcc_in hws (Nat.le_add_right _ _) (by simp only [Region.size]; omega)
  have hlw : MemRow.LocIn L c (.dequant bw) l := by
    rw [← hhc]
    exact hsi.locIn hcov
  obtain ⟨a, ha⟩ := deq_lane hp hat
  rw [hhc] at ha hpol harr hub
  subst ha
  obtain ⟨hls, hlcm, -, -⟩ := id hlw
  have hmc' : (mmaLane L X c) / L.block = c := hmc
  have hb' : bw.val = (2 * u + bw.val) % 2 := by have := bw.isLt; omega
  have hcm : 2 * u + bw.val ≤ 2 * ((X.tr (mmaLane L X c)).take ic).countP
      (PTX.Flow.commitsTo (mbarLoc L c (.svDone s0))) + s0.val := by
    simp only [ringUses] at hub
    omega
  obtain ⟨j, hj, pc', bb, idx, sp', acc, mask, hx, hatm, h1853, hfp, hpoll, -⟩ :=
    mma_qkCover hp hX hFw (y := mmaLane L X c) (c := c) hi hm hcm hb' (by rw [hmc']; exact hlw)
  rw [hmc'] at hpoll
  refine ⟨j, hj, pc', bb, idx, sp', acc, mask, hx, hatm, h1853, hfp, ?_⟩
  refine dq_before hp hX hFw hR hI hB hN hW harr hx ?_ hfp hls ?_ hmc'
  · rw [hpoll]
    simp only [ringUses]
    omega
  · rw [hlcm]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
