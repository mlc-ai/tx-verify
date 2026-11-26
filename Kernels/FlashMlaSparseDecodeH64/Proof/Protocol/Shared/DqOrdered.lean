-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ordered
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqClass
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Bar9
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqCover
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqWw
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.QueryTile
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.StageEpi
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.StageStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.CpOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Dq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce

@[expose] public section

/-! # The dequantized tiles are ordered

Two conflicting accesses of a byte of a dequantized tile are of two of the six kinds of
`dq_classify`, one of them a write (a dequant lane's chunk store, a staging store, a query load's
write). Each pair of kinds is ordered by the lemma of its protocol:

* chunk store with chunk store: one lane's program order (`dq_ww`); with an MMA read: the poll
  of `dequantReady`, or of `svDone` (`dq_mma`); with the copy or the query load: the query tile's
  (`q_cp_dq`, `q_tload_dq`);
* staging store with an MMA read, a chunk store, the tensor store: the poll of `svDone` at pc 1184
  (`mma_stage`, `dq_stage`, `dq_store`), the publication of barrier 9 (`stage_store_order`);
  two staging stores of a byte are one (`wg0_stage_once`);
* query load with the copy and the MMA reads: its `qTma` poll (`q_tload_after`); two loads of a
  byte are one (`q_tload_ww`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The asynchronous read footprint of an MMA or copy covers its byte. -/
private theorem fp_cov {i : EvId} {isB : Bool} {idx : Nat} {l : Loc}
    (hf : X.MmaFootprint i isB idx l) : AsyncCovers X i (.mmaRead isB idx) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, hf⟩, Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **A query load is before an MMA read or a copy read of the lane's CTA after the lane's `qTma`
poll** (the MMA or copy `g2`, `i2`, at a pc after the election). -/
private theorem tload_after {g iT pcT al x yy j g2 i2 : Nat} {s : TensorCopy.Spec} {aT : Acc}
    {q : AsyncCopy.Part} {l : Loc} {e2 : Event}
    (hT : X.get (g, iT) = some ⟨pcT, .tensorIssue al s⟩) (hatT : MmaAt L g pcT)
    (hiT : X.Intent (.async (g, iT) (.write (.load x yy j))) aT true) (hcvT : aT.Covers l)
    (he2 : X.get (g2, i2) = some e2) (hon : MmaOn L g2 e2.pc)
    (hq : okPolls (mbarLoc L (g2 / L.block) .qTma) ((X.tr g2).take i2) = 1)
    (hc2 : AsyncCovers X (g2, i2) q l) (hcg : g / L.block = g2 / L.block)
    (hu2 : ∀ f, e2.kind ≠ .ub f) :
    ByteCausality L X l (.async (g, iT) (.write (.load x yy j))) (.async (g2, i2) q) := by
  obtain ⟨hpc, -⟩ := mma_qLoad_range hp hX hFw hatT.1 hT
  have e1 : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hT (fun _ h => by cases h) ⟨hatT, hpc⟩
  have e2 : g2 = mmaLane L X (g2 / L.block) := laneOn_eq (mmaOne hp hX hFw) he2 hu2 hon
  obtain rfl : g = g2 := by rw [e1, e2, hcg]
  exact .direct (q_tload_after hp hX hFw hR hI hB hT hatT he2 hq ⟨aT, true, hiT, hcvT⟩ hc2)

variable (hN : DequantInputs L X) (hBar : BarRows P L X) (hO : OutRows P L X)
include hN hBar hO

/-- **A write of a dequantized tile's byte and another access of it are ordered.** -/
private theorem writer_pair {e f : AsyncCopy.Ref} {a b : Acc} {wf : Bool} {c : Nat} {r : Fin 2}
    {l : Loc} (hne : e ≠ f) (hIe : X.Intent e a true) (ha : a.Covers l)
    (hIf : X.Intent f b wf) (hb : b.Covers l) (hl : MemRow.LocIn L c (.dequant r) l)
    (ce : DqRef L X c r l e true) (cf : DqRef L X c r l f wf) :
    ByteCausality L X l e f ∨ ByteCausality L X l f e := by
  have hls := hl.1
  cases ce with
  | dq hW1 hat1 hcov1 hc1 =>
    cases cf with
    | dq hW2 hat2 hcov2 hc2 =>
      exact dq_ww hp hX hFw hW1 hat1 hW2 hat2 hcov1 hcov2 (fun hh => hne (by rw [hh]))
    | stage hS hatS hr hst hcovS hc2 =>
      exact .inl (dq_stage hp hX hFw hR hI hB hN hW1 hat1 hcov1 hls (hc1.trans hc2.symm)
        hS hatS hst hcovS)
    | mma hx hatm hf hc2 =>
      exact dq_mma hp hX hFw hR hI hB hN hW1 hat1 hcov1 hx hatm hf (by rw [hc2]; exact hl)
    | cp hr hC hatC hf hc2 =>
      exact .inr (.direct (q_cp_dq hp hX hFw hR hI hB hC hatC hf hls hW1 hat1 hcov1
        (hc1.trans hc2.symm)))
    | tload hr hT hatT hrl hc2 =>
      subst hr
      exact .inr (q_tload_dq hp hX hFw hR hI hB hT hatT hIf hb (by rw [hc2]; exact hl) hW1 hat1
        hcov1 (hc1.trans hc2.symm))
    | tstore hr hT hatT hrl hc2 =>
      exact .inl (dq_store hp hX hFw hR hI hB hN hW1 hat1 hcov1 hls (hc1.trans hc2.symm) hT
        hatT hrl ⟨b, .inl ⟨false, hIf⟩, hb⟩)
  | stage hS1 hatS1 hr1 hst1 hcov1 hc1 =>
    cases cf with
    | dq hW2 hat2 hcov2 hc2 =>
      exact .inr (dq_stage hp hX hFw hR hI hB hN hW2 hat2 hcov2 hls (hc2.trans hc1.symm)
        hS1 hatS1 hst1 hcov1)
    | stage hS2 hatS2 hr2 hst2 hcov2 hc2 =>
      obtain ⟨rfl, rfl⟩ := wg0_stage_once hp hX hFw hatS1.1 hatS2.1 hS1 hS2 hst1 hst2 hcov1
        hcov2
      exact absurd rfl hne
    | mma hx hatm hf hc2 =>
      exact .inr (mma_stage hp hX hFw hR hI hB hN hx hatm hf (by rw [hc2]; exact hl)
        (hc1.trans hc2.symm) hS1 hatS1 hst1 hcov1)
    | cp hr2 hC hatC hf hc2 => exact absurd (hr1.symm.trans hr2) (by decide)
    | tload hr2 hT hatT hrl hc2 => exact absurd (hr1.symm.trans hr2) (by decide)
    | tstore hr2 hT hatT hrl hc2 =>
      subst hr2
      exact .inl (stage_store_order hp hX hFw hBar hO hT hrl hS1 hatS1 hst1 hcov1
        (by rw [hc2]; exact hl))
  | tload hr1 hT1 hatT1 hrl1 hc1 =>
    cases cf with
    | dq hW2 hat2 hcov2 hc2 =>
      subst hr1
      exact .inl (q_tload_dq hp hX hFw hR hI hB hT1 hatT1 hIe ha (by rw [hc1]; exact hl) hW2 hat2
        hcov2 (hc2.trans hc1.symm))
    | stage hS2 hatS2 hr2 hst2 hcov2 hc2 => exact absurd (hr1.symm.trans hr2) (by decide)
    | mma hx hatm hf hc2 =>
      have h1853 := (mma_dqUse hp hX hFw hx hatm hf (h0 := r) (by rw [hc2]; exact hl)).1
      exact .inl (tload_after hp hX hFw hR hI hB hT1 hatT1 hIe ha hx ⟨hatm, h1853⟩
        (mma_mma_qWait hp hX hFw hx hatm) (fp_cov hf) (hc1.trans hc2.symm)
        (fun _ hh => by cases hh))
    | cp hr2 hC hatC hf hc2 =>
      exact .inl (tload_after hp hX hFw hR hI hB hT1 hatT1 hIe ha hC
        ⟨hatC, mma_cp_on hp hX hFw hC hatC⟩ (mma_cp_qWait hp hX hFw hC hatC) (fp_cov hf)
        (hc1.trans hc2.symm) (fun _ hh => by cases hh))
    | tload hr2 hT2 hatT2 hrl2 hc2 =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := q_tload_ww hp hX hFw hT1 hatT1 hrl1 hT2 hatT2 hrl2
        (hc1.trans hc2.symm)
      exact absurd rfl hne
    | tstore hr2 hT hatT hrl hc2 => exact absurd (hr1.symm.trans hr2) (by decide)

/-- **The dequantized tiles are ordered**: conflicting accesses of a byte of a dequantized tile of
any CTA are ordered (the dequant lanes' chunk stores, warpgroup 0's staging stores, the MMA lane's
operand reads, the query load and the output tensor stores). -/
theorem dequant_ordered (r : Fin 2) : RegionOrdered L X (.dequant r) := by
  rintro e f a b l ⟨hne, we, wf, hIe, hIf, hw, -⟩ ha hb ⟨c, hl⟩ -
  have ce := dq_classify hp hX hFw hIe ha hl
  have cf := dq_classify hp hX hFw hIf hb hl
  rcases hw with rfl | rfl
  · exact writer_pair hp hX hFw hR hI hB hN hBar hO hne hIe ha hIf hb hl ce cf
  · exact (writer_pair hp hX hFw hR hI hB hN hBar hO hne.symm hIf hb hIe ha hl cf ce).symm

end

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
