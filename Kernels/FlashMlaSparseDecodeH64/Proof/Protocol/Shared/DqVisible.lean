-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqMma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Chunks
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Lag
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Dq
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # A dequantized-tile byte an MMA reads has a covering write before the read

The QK and PV MMAs read the dequantized tile `b` of their CTA as B. A byte of the tile lies in the
chunk `(r, q)` of one dequant lane `a` (`dqCol` is a bijection of the 128 lanes onto the 16-byte
columns of 2048 bytes, `dqChunk_cover`). The MMA's poll of `dequantReady b` observes the arrival
of lane `a` of the use (`dequantReady_observes`), which follows the lane's chunk store `(r, q)` of
the use (`dequant_chunks`), so the store is before the MMA's read (`dq_before`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The 128 lanes' columns are the 128 sixteen-byte columns of 2048 bytes. -/
private theorem dqCol_onto : ∀ c < 128, ∃ i < 128, MemRow.dqCol i = 16 * c := by
  decide +kernel

/-- **Every byte of a dequantized tile is in a chunk of a lane's.** -/
theorem dqChunk_cover {t : Nat} (ht : t < 65536) :
    ∃ i r s, i < 128 ∧ r < 4 ∧ s < 8 ∧ MemRow.dqChunk i r s ≤ t ∧
      t < MemRow.dqChunk i r s + 16 := by
  obtain ⟨i, hi, hc⟩ := dqCol_onto (t % 2048 / 16) (by omega)
  refine ⟨i, t % 8192 / 2048, t / 8192, hi, by omega, by omega, ?_, ?_⟩ <;>
    simp only [MemRow.dqChunk, hc] <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **A byte of the dequantized tile an MMA reads has a covering write before the read**: a chunk
store of a dequant lane of the CTA. -/
theorem dq_visible {g i pc bb idx : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {isB : Bool} {l : Loc} {b0 : Fin 2}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩) (hatm : MbarRow.MmaAt L g pc)
    (hf : X.MmaFootprint (g, i) isB idx l) (hl : MemRow.LocIn L (g / L.block) (.dequant b0) l) :
    ∃ w a bs, X.MemWrites w a bs ∧ a.Covers l ∧
      ByteCausality L X l w (.async (g, i) (.mmaRead isB idx)) := by
  obtain ⟨hpcm, u, hpm, -⟩ := mma_dqUse hp hX hFw hx hatm hf hl
  have hon : MmaOn L g pc := ⟨hatm, hpcm⟩
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  obtain ⟨hls, hlcm, hlo, hhi⟩ := id hl
  obtain ⟨i0, r0, q0, hi0, hr0, hq0, hc1, hc2⟩ := dqChunk_cover
    (t := l.addr - L.sharedBase - (Region.dequant b0).lo) (by
      simp only [Region.lo, Region.size] at hlo hhi ⊢
      omega)
  generalize hcd : g / L.block = c at *
  subst hg
  obtain ⟨jw, pcp, p, acq, sc, hjw, hget, hq⟩ := UnitHandoff.exists_poll
    (m := mbarLoc L c (.dequantReady b0)) (h := mmaLane L X c) (f := i) (c := u) hpm.ge
  obtain ⟨-, hall⟩ := dequantReady_observes hp hX hFw hR hI hB hN hget
  obtain ⟨ia, pca, sca, hga, hca, -⟩ := hall ⟨i0, hi0⟩
  obtain ⟨j, hj, pcw, ac, bs, hW, hat, hws, hcnt⟩ := dequant_chunks hp hX hFw
    (deqLane_warp hp c ⟨i0, hi0⟩) hga ⟨r0, hr0⟩ ⟨q0, hq0⟩
  have hlane : deqLane L c ⟨i0, hi0⟩ % 128 = i0 := by
    simp only [deqLane, hp.block]
    omega
  rw [deqLane_cta hp c ⟨i0, hi0⟩, hlane] at hws
  have hcov : ac.Covers l := by
    obtain ⟨hw1, hw2⟩ := hws
    rw [Acc.Covers, hw1, hw2]
    simp only [Loc.InRange, wsLoc, Region.lo, Region.size, MemRow.dqChunk] at hc1 hc2 hlo hhi ⊢
    refine ⟨hls, hlcm, ?_, ?_⟩ <;> omega
  refine ⟨.thread (deqLane L c ⟨i0, hi0⟩, j), ac, bs, Or.inl ⟨pcw, hW⟩, hcov, .direct ?_⟩
  refine dq_before hp hX hFw hR hI hB hN (s := b0) (u := u) hW ?_ hx ?_ hf hls hlcm hcd
  · rw [hcnt, hca, hq]
  · omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
