-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.CpOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.QPoll
import Lemmas.Protocol.UnitGate
import Lemmas.Tensor.BoxInj
import Lemmas.Tcgen05.MmaObservedReads
import Lemmas.Flow.NthEv
import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # The query tile: the tensor loads of the MMA lane are finished at its `qTma` poll

The MMA lane's eight tensor loads of the query write the dequantized tile 0 of its CTA. Its one
successful poll of `qTma` (pc 1931) observes each of them (`qTma_observes`), so each load is
finished at that poll (`q_tload_finished`): the load is found by its count of earlier loads to
`qTma`, which names its 8192 bytes (`mma_qLoad_range`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **A query tensor load is finished at the lane's successful poll of `qTma`.** -/
theorem q_tload_finished {g iT jw pc pcw al p x yy j : Nat} {s : TensorCopy.Spec} {acq : Bool}
    {sc : MbarScope}
    (hT : X.get (g, iT) = some ⟨pc, .tensorIssue al s⟩) (hat : MmaAt L g pc)
    (hpoll : X.get (g, jw) = some ⟨pcw, .wait (mbarLoc L (g / L.block) .qTma) p true acq sc⟩) :
    AsyncFinished L X (g, iT) (.write (.load x yy j)) (g, jw) := by
  obtain ⟨hacq, rfl⟩ := mbarWait_cta hX hR hpoll
  subst hacq
  have hg : g < L.threads := Frame.lt_of_get hX hT
  obtain ⟨hpc, hmb, a, ha, hcnt, -⟩ := mma_qLoad_range hp hX hFw hat.1 hT
  have hlane : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hT (fun _ h => by cases h) ⟨hat, hpc⟩
  generalize hc : g / L.block = c at *
  subst hlane
  have hw4 : warp L (mmaLane L X c) = 4 := hat.1
  simp only [loc, hc] at hmb hcnt
  obtain ⟨-, -, -, hall⟩ := qTma_observes hp hX hFw hR hI hB (mmaOne hp hX hFw) (c := c)
    (by simpa only [loc, hc] using mma_issues_le hp hX hFw hw4)
    (by simpa only [loc, hc] using mma_arrivals_le hp hX hFw hw4 (mbarLoc L c .qTma)) hpoll
  obtain ⟨i, pc2, al2, sp2, hget2, hm2, hc2, hobs⟩ := hall ⟨a, ha⟩
  have hik : i = iT := nthEv_unique (p := issuesTo (mbarLoc L c .qTma)) hget2
    (by rw [issuesTo_tensorIssue]; simpa using hm2) hT
    (by rw [issuesTo_tensorIssue]; simpa using hmb) (by rw [hc2, hcnt])
  subst hik
  rw [hT] at hget2
  obtain ⟨-, hsp⟩ := Event.mk.inj (Option.some.inj hget2)
  obtain ⟨-, rfl⟩ := Kind.tensorIssue.inj hsp
  obtain ⟨i1, j1, r, w1, ph, hr1, hid1, -⟩ := hobs.2
  have hrec : r ∈ X.objects (mbarLoc L c .qTma) := List.mem_of_getElem? hr1
  have hpres := object_record_present hX.tma hrec
  rw [hid1] at hpres
  obtain ⟨o, ho, hn⟩ := hpres
  obtain ⟨⟨a', pc3, hget3⟩, -, -⟩ := hX.tensor _ o ho
  have hg3 := hget3
  rw [hT] at hg3
  obtain ⟨-, hsp3⟩ := Event.mk.inj (Option.some.inj hg3)
  obtain ⟨-, hs3⟩ := Kind.tensorIssue.inj hsp3
  refine .inr ⟨.cta, ⟨.async _ (.notify .load), mbarLoc L c .qTma,
    ⟨rfl, o, a', ho, ⟨pc3, ?_⟩, ?_, hn⟩, hobs.1, hobs.2⟩, ?_⟩
  · exact hget3
  · rw [← hs3]
    exact hmb
  · exact Unit.Gate.scopesMeet ⟨hg, hg, rfl⟩ _ _

/-- **A tensor load is before everything the lane does after its `qTma` poll**: an asynchronous
access of the MMA lane after the lane's one successful poll of `qTma` follows each query load
(`modelCausality`, the chain `AsyncBefore`). -/
theorem q_tload_after {g iT i2 pc al : Nat} {s : TensorCopy.Spec} {x yy j : Nat}
    {q : Part} {l : Loc} {e2 : Event}
    (hT : X.get (g, iT) = some ⟨pc, .tensorIssue al s⟩) (hat : MmaAt L g pc)
    (he2 : X.get (g, i2) = some e2)
    (hq : okPolls (mbarLoc L (g / L.block) .qTma) ((X.tr g).take i2) = 1)
    (hcT : AsyncCovers X (g, iT) (.write (.load x yy j)) l) (hc2 : AsyncCovers X (g, i2) q l) :
    modelCausality L X l (.async (g, iT) (.write (.load x yy j))) (.async (g, i2) q) := by
  have h1 : 0 + 1 ≤ okPolls (mbarLoc L (g / L.block) .qTma) ((X.tr g).take i2) := by omega
  obtain ⟨jw, pcp, p, acq, sc, hjw, hpoll, -⟩ := UnitHandoff.exists_poll h1
  have hg : g < L.threads := Frame.lt_of_get hX hT
  have hil : i2 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he2).1
  refine ⟨.inl ⟨hg, hg, rfl⟩, .direct ⟨hcT, hc2, .inl ⟨(g, jw),
    q_tload_finished hp hX hFw hR hI hB hT hat hpoll, ?_⟩⟩⟩
  exact .single (.inl (po_of_source_not_access rfl hjw hil (by rw [hpoll]; rfl)))

/-- **A dequant lane's poll of `qUtccp` observes the completion of every copy**: the poll at
pc 2644 observes the notification of the MMA lane's commit at pc 1982, which tracks every copy
before it (`AsyncObserved` of the copy's completion), and the copy has completed. -/
theorem q_utccp_done {h jq c : Nat}
    (hpoll : X.get (h, jq) = some ⟨2644, .wait (mbarLoc L c .qUtccp) 0 true true .cta⟩)
    (hmc : mmaLane L X c / L.block = c) (hw4 : warp L (mmaLane L X c) = 4) :
    ∃ ic sp, X.get (mmaLane L X c, ic) = some ⟨1982, .tc (.commit sp)⟩ ∧ h / L.block = c ∧
      ∀ {jc pc : Nat} {cs : TcCopy.Spec},
        X.get (mmaLane L X c, jc) = some ⟨pc, .tc (.cp cs)⟩ → jc < ic →
          AsyncObserved X (mmaLane L X c, jc) .mmaDone (h, jq) true .cta ∧
            X.AsyncPresent (mmaLane L X c, jc) .mmaDone := by
  have hC1 : (X.tr (mmaLane L X c)).countP (PTX.Flow.commitsTo (mbarLoc L c .qUtccp)) ≤ 1 := by
    have := mma_commits_le hp hX hFw hw4
    simpa only [loc, hmc] using this
  obtain ⟨-, hc, ic, sp, rank, hget, hm, ht, hrank, hobs⟩ :=
    qUtccp_observes hp hX hFw hR hI hB (mmaOne hp hX hFw) (c := c) hC1 hpoll
  refine ⟨ic, sp, hget, hc, fun {jc pc cs} hcp hjc => ?_⟩
  have htr : TracksMma X (mmaLane L X c, jc) (mmaLane L X c, ic) :=
    ⟨rfl, hjc, .inr (.inl ⟨cs, pc, hcp⟩), sp, 1982, hget⟩
  exact ⟨⟨_, _, ⟨(mmaLane L X c, ic), sp, rank, rfl, htr, ⟨1982, hget⟩, ht, hrank⟩, hobs⟩,
    (hX.tcCommit _ rank hrank).2 _ htr⟩

omit hp hX hFw hR hI hB in
/-- The asynchronous read footprint of a copy covers its byte. -/
private theorem cp_covers {i : EvId} {idx : Nat} {l : Loc} (hf : X.MmaFootprint i false idx l) :
    AsyncCovers X i (.mmaRead false idx) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, hf⟩, Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩

/-- **A copy's read of a query byte is before a dequant lane's store of it**: the copy is done at
the lane's poll of `qUtccp` (pc 2644), which precedes the store. -/
theorem q_cp_dq {g iC pcC h k pcw idx : Nat} {c : TcCopy.Spec} {ac : Acc} {bs : List Byte}
    {l : Loc}
    (hC : X.get (g, iC) = some ⟨pcC, .tc (.cp c)⟩) (hatC : MmaAt L g pcC)
    (hf : X.MmaFootprint (g, iC) false idx l) (hls : l.space = .shared)
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : DequantAt L h pcw) (hcov : ac.Covers l)
    (hcg : h / L.block = g / L.block) :
    modelCausality L X l (.async (g, iC) (.mmaRead false idx)) (.thread (h, k)) := by
  have hlane : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hC (fun _ h => by cases h) ⟨hatC, mma_cp_on hp hX hFw hC hatC⟩
  obtain ⟨jq, hjq, hpoll⟩ := dequant_qPoll hp hX hFw hW hat
  have hg : g < L.threads := Frame.lt_of_get hX hC
  have hh : h < L.threads := Frame.lt_of_get hX hW
  have hkl : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp hW).1
  rw [hcg] at hpoll
  generalize hc : g / L.block = c' at *
  subst hlane
  obtain ⟨ic, sp, hcm, -, hall⟩ := q_utccp_done hp hX hFw hR hI hB hpoll hc hatC.1
  have hjc := mma_cp_before_commit hp hX hFw hC ⟨hatC.2.1, hatC.2.2⟩ hcm (by decide)
  obtain ⟨hobs, -⟩ := hall hC hjc
  refine ⟨cp_covers hf, (h, jq), .inr ⟨.cta, hobs, ?_⟩, .inr ⟨hls, .inl ⟨rfl, c, pcC, hC⟩, ?_,
    ac, bs, ⟨pcw, hW⟩, hcov⟩⟩
  · exact ⟨⟨hg, hh, by simp only [hc, hcg]⟩, hh, hg, hcg.trans hc.symm⟩
  · exact .single (.inl (po_of_source_not_access rfl hjq hkl (by rw [hpoll]; rfl)))

/-- **A query tensor load's write is before a dequant lane's store of the byte** (byte
causality): the load is before a copy covering the byte (`q_tload_after`, the copy covers every
byte of the tile: `mma_cp_cover`), the copy is done at the lane's poll of `qUtccp`, and the
observed copy handoff carries the order to the store (`ByteCausality.commitOperand`). -/
theorem q_tload_dq {g iT pcT al x yy j h k pcw : Nat} {s : TensorCopy.Spec} {aT ac : Acc}
    {bs : List Byte} {l : Loc}
    (hT : X.get (g, iT) = some ⟨pcT, .tensorIssue al s⟩) (hatT : MmaAt L g pcT)
    (hiT : X.Intent (.async (g, iT) (.write (.load x yy j))) aT true) (hcvT : aT.Covers l)
    (hl : MemRow.LocIn L (g / L.block) (.dequant 0) l)
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : DequantAt L h pcw) (hcov : ac.Covers l)
    (hcg : h / L.block = g / L.block) :
    ByteCausality L X l (.async (g, iT) (.write (.load x yy j))) (.thread (h, k)) := by
  obtain ⟨hpc, -⟩ := mma_qLoad_range hp hX hFw hatT.1 hT
  have hlane : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hT (fun _ h => by cases h) ⟨hatT, hpc⟩
  obtain ⟨jq, hjq, hpoll⟩ := dequant_qPoll hp hX hFw hW hat
  have hg : g < L.threads := Frame.lt_of_get hX hT
  have hh : h < L.threads := Frame.lt_of_get hX hW
  have hkl : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp hW).1
  rw [hcg] at hpoll
  have hl1 := hl.1
  generalize hc : g / L.block = c' at *
  subst hlane
  obtain ⟨ic, sp, hcm, -, hall⟩ := q_utccp_done hp hX hFw hR hI hB hpoll hc hatT.1
  obtain ⟨jc, hjc, pc', cs, idx', hcp, hatC, hf⟩ := mma_cp_cover hp hX hFw hcm
    (by decide) (by rw [hc]; exact hl)
  obtain ⟨hobs, hdone⟩ := hall hcp hjc
  have hprior := q_tload_after hp hX hFw hR hI hB hT hatT hcp
    (mma_cp_qWait hp hX hFw hcp hatC) ⟨aT, true, hiT, hcvT⟩ (cp_covers hf)
  have hwr : X.MemWrites (.thread (h, k)) ac bs := .inl ⟨pcw, hW⟩
  exact .commitOperand hl1 ⟨aT, hiT, hcvT⟩
    (.inr ⟨rfl, rfl, ⟨cs, pc', hcp⟩, ac, bs, ⟨pcw, hW⟩, hcov⟩)
    (hX.tma.2.1.cp_read_of_complete ⟨pc', hcp⟩ hdone hf) (.direct hprior)
    ⟨.cta, hobs, ⟨hg, hh, by simp only [hc, hcg]⟩, hh, hg, hcg.trans hc.symm⟩
    (po_of_source_not_access rfl hjq hkl (by rw [hpoll]; rfl))
    ⟨ac, .inl ⟨true, hwr.intent⟩, hcov⟩

omit hR hI hB in
/-- **Two query tensor-load write parts covering one byte are one part**: the byte names the
load (its 8192 bytes, `mma_qLoad_range`) and the slot (`writeLoc_inj`). -/
theorem q_tload_ww {g iT pc al x yy j g' iT' pc' al' x' y' j' : Nat} {s s' : TensorCopy.Spec}
    {l : Loc}
    (hT : X.get (g, iT) = some ⟨pc, .tensorIssue al s⟩) (hat : MmaAt L g pc)
    (hl : TensorCopy.writeLoc s x yy j = some l)
    (hT' : X.get (g', iT') = some ⟨pc', .tensorIssue al' s'⟩) (hat' : MmaAt L g' pc')
    (hl' : TensorCopy.writeLoc s' x' y' j' = some l) (hcg : g / L.block = g' / L.block) :
    g = g' ∧ iT = iT' ∧ x = x' ∧ yy = y' ∧ j = j' := by
  obtain ⟨hpc, hmb, a, ha, hcnt, hrng⟩ := mma_qLoad_range hp hX hFw hat.1 hT
  obtain ⟨hpc', hmb', a', ha', hcnt', hrng'⟩ := mma_qLoad_range hp hX hFw hat'.1 hT'
  have e1 : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hT (fun _ h => by cases h) ⟨hat, hpc⟩
  have e2 : g' = mmaLane L X (g' / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hT' (fun _ h => by cases h) ⟨hat', hpc'⟩
  obtain rfl : g = g' := by rw [e1, e2, hcg]
  obtain ⟨-, -, h1, h2⟩ := hrng hl
  obtain ⟨-, -, h3, h4⟩ := hrng' hl'
  obtain rfl : a = a' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h <;> omega
  have hik : iT = iT' := nthEv_unique (p := issuesTo (loc L g .qTma)) hT
    (by rw [issuesTo_tensorIssue]; simpa using hmb) hT'
    (by rw [issuesTo_tensorIssue]; simpa using hmb') (by rw [hcnt, hcnt'])
  subst hik
  rw [hT] at hT'
  obtain ⟨-, hsp⟩ := Event.mk.inj (Option.some.inj hT')
  obtain ⟨-, rfl⟩ := Kind.tensorIssue.inj hsp
  obtain ⟨rfl, rfl, rfl⟩ := TensorCopy.writeLoc_inj hl hl'
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
