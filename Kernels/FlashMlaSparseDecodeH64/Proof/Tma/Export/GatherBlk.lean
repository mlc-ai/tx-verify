-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaMain
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.GatherDst
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ClsRd
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep

@[expose] public section

/-! # The block and the map of a TMA gather

A gather `q` of the TMA lane is in a block `r`: it is made after `64 r + 8 + 4 q` (`64 r + 64` for
gather 15) coordinate reads of the lane, and its descriptor is the main cache's four-row map when
`r` is below the main cache's blocks `numOrigBlocks (topkLen)` and the extra cache's from then on
(`tma_gatherBlk`). With `tma_rdBlock` (`Tma/Export/Use.lean`) it ties the gather to the block of
the coordinate reads it takes its rows from. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- The four-row transfer of a cache map is the gather's map. -/
private theorem gather_map_main {o : Nat} {d0 : TensorDescriptor.Descriptor o}
    {desc : TensorDescriptor.Descriptor o} (hd : desc = TensorMode.fourRows.transfer d0)
    (h : (⟨o, d0⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, mapKv P.kvBase P.numBlocks P.blockStride P.kvClass⟩) :
    (⟨o, desc⟩ : Σ n, TensorDescriptor.Descriptor n) = gatherMap P false := by
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  subst h1
  obtain rfl := eq_of_heq h2
  simp [hd, gatherMap, mapKv]

private theorem gather_map_extra {o : Nat} {d0 : TensorDescriptor.Descriptor o}
    {desc : TensorDescriptor.Descriptor o} (hd : desc = TensorMode.fourRows.transfer d0)
    (h : (⟨o, d0⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, mapExtraKv P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass⟩) :
    (⟨o, desc⟩ : Σ n, TensorDescriptor.Descriptor n) = gatherMap P true := by
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  subst h1
  obtain rfl := eq_of_heq h2
  simp [hd, gatherMap, mapExtraKv]

/-- **The block and the map of a TMA gather.** -/
theorem tma_gatherBlk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hat : MbarRow.TmaAt L g e.pc) {a : Nat}
    {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    ∃ q < 16, ∃ r, e.pc = gatherPc q ∧
      ((X.tr g).take k).countP tmaRd = 64 * r + (if q = 15 then 64 else 4 * q + 8) ∧
      (r < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) →
        (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) = gatherMap P false) ∧
      (FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) ≤ r →
        (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) = gatherMap P true) := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [hk] at h; cases h
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d0, -, -, ⟨hpc, hE⟩, hl', -⟩ := tma_at hp hX hFw he hub hr
  obtain ⟨i, hs⟩ := Tma.ev_gather hl' ⟨hpc, hE⟩ hk
  have hpcq : e.pc = gatherPc i.val := by
    rw [hpc, hs]; unfold Tma.Site.pc gatherPc; rfl
  have hpcR : 2165 < e.pc ∧ e.pc < 2332 := by
    rw [hpc, hs]
    exact (by decide : ∀ i : Fin 16, 2165 < (Tma.Site.gather i).pc ∧
      (Tma.Site.gather i).pc < 2332) i
  obtain ⟨d, n, t, ins, o, q, hσ, hat', hs', hc, hf, hmain, hL, hev, hn⟩ :=
    tma_gather_at_n hp hX hFw he hpcR hk
  have hpcq : e.pc = gatherPc q.val := by
    have h1 : e.pc = d.site.pc := hev.1
    rw [h1, hs']; unfold Tma.Site.pc gatherPc; rfl
  obtain ⟨j, hjk, inst, hj⟩ := tma_won hp hX hFw he hub hpcR
  obtain ⟨d2, n2, heq, -, hok⟩ := tma_words hp hX hFw hj hjk hσ
  have h2d : d2 = d := by
    simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at heq
    exact heq.1.symm
  rw [h2d] at hok
  obtain ⟨h0, -⟩ := tma_words_of_ok (by rw [hs']; simp) (by rw [hs']; simp) hok
  have hL' := hL
  obtain ⟨-, -, -, -, -, hbuf, -⟩ := hL'
  have hb2 := Nat.mod_lt d.cnt.toNat (by decide : 0 < 2)
  obtain ⟨-, -, -, d1, hd1, hmap⟩ := Tma.gather_dst hp hat' hs' hc hf hmain hb2 hbuf hk
  have hM := tma_isMain hp h0 hL
  refine ⟨q.val, q.isLt, d.cnt.toNat, hpcq, ?_, fun hlt => ?_, fun hge => ?_⟩
  · have := hn .rd (by simp)
    rw [show Tma.cls .rd = tmaRd from funext Tma.cls_rd] at this
    rw [this]
    simp only [Tma.cntAt, Tma.proCnt, Tma.loopCnt, Bool.false_eq_true, ↓reduceIte, hs',
      Tma.Site.rdN]
    omega
  · rw [hM] at hmap
    simp only [hlt, decide_true] at hmap
    rcases hmap with ⟨-, h⟩ | ⟨h, -⟩
    · exact gather_map_main hd1 h
    · exact absurd h (by decide)
  · rw [hM] at hmap
    have hn' : ¬ d.cnt.toNat < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) := by
      omega
    simp only [hn', decide_false] at hmap
    rcases hmap with ⟨h, -⟩ | ⟨-, -, h⟩
    · exact absurd h (by decide)
    · exact gather_map_extra hd1 h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
