-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqCover
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Final
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.Obj
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SvPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Dq
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
import Lemmas.Tcgen05.MmaObservedReads
import Lemmas.Order.OrderWaits

@[expose] public section

/-! # The epilogue's stores follow the MMAs and the dequant stores of their tile

A staging store, and the tensor store reading the staging tiles, of a lane of warpgroup 0 follow
that lane's successful poll of `svDone` at pc 1184 (`wg0_stage_poll`, `wg0_store_poll`), which
observes the completion of every MMA and copy of the CTA (`svDone_done`) and carries the order of
the writes before an MMA's operand read to the later accesses of the polling lane
(`ByteCausality.commitOperand`, the observed operand handoff). So:

* an MMA operand read of a byte is before a staging store of it (`mma_stage`);
* a dequant lane's chunk store of a byte is before a staging store (`dq_stage`) and the tensor
  store (`dq_store`) of it: the store is before a QK MMA reading the byte (`dq_mmaCover`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR

/-- **A commit to `svDone` of CTA `c` is the CTA's MMA lane's.** -/
theorem svCommit_lane {y i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.svDone s)) :
    y / L.block = c ∧ y = mmaLane L X c := by
  have hub : ∀ f, (⟨pc, .tc (.commit sp)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  rcases score_use hR ⟨s, .inr (.inr rfl)⟩ (Frame.lt_of_get hX he) he
      (mma_commitHit hp hX he hm) with ⟨n, hk⟩ | ⟨hc, ⟨hat, ⟨-, hk⟩ | ⟨⟨_, hf⟩, -⟩⟩ |
      ⟨hw, ⟨⟨_, hf⟩, -⟩ | ⟨⟨_, hf⟩, -⟩ | ⟨-, q, ok, hk⟩⟩ | ⟨-, -, ok, hk⟩⟩
  · cases hk
  · have hy := laneOn_eq (mmaOne hp hX hFw) he hub hat
    rw [hc] at hy
    exact ⟨hc, hy⟩
  all_goals first | cases hf | cases hk

end

/-- **The polling lane meets the MMA lane**: a lane of the CTA and the MMA lane of the CTA meet at
cluster scope. -/
private theorem meets {c y : Nat} (hyc : y / L.block = c) (hmc : mmaLane L X c / L.block = c)
    (hy : y < L.threads) (hg : mmaLane L X c < L.threads) :
    ScopesMeet L .cluster (mmaLane L X c) .cta y :=
  ⟨⟨hg, hy, by rw [hmc, hyc]⟩, hy, hg, by rw [hmc, hyc]⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **The poll at pc 1184 gives the MMA lane of its CTA** and its last commit, after which the
earlier writes to an MMA's operand byte are before the later accesses of the polling lane. -/
private theorem dq_epi {h k c y jw p pcw : Nat} {ac : Acc} {bs : List Byte} {l : Loc}
    {dst : AsyncCopy.Ref} (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩)
    (hat : DequantAt L h pcw) (hcov : ac.Covers l) (hls : l.space = .shared)
    (hhc : h / L.block = c) (hy : warp L y < 4)
    (hpoll : X.get (y, jw) = some ⟨1184, .wait (mbarLoc L c
      (.svDone (slot2 (blocksOf P L c - 1)))) p true true .cta⟩)
    (hpo : po X (y, jw) dst.issuer) (hd : ∃ a, X.MemTouches dst a ∧ a.Covers l) :
    ByteCausality L X l (.thread (h, k)) dst := by
  obtain ⟨-, ic, pci, spi, rank, hgc, hmi, -, hci, -⟩ :=
    svDone_last hp hX hFw hR hI hB hN hy hpoll
  obtain ⟨hmc, -⟩ := svCommit_lane hp hX hFw hR hgc hmi
  have hpos := blocksOf_pos hp c
  have hlast : blocksOf P L c ≤ 2 * ((X.tr (mmaLane L X c)).take ic).countP
      (PTX.Flow.commitsTo (mbarLoc L c (.svDone (slot2 (blocksOf P L c - 1))))) +
      (slot2 (blocksOf P L c - 1)).val + 1 := by
    rw [hci]
    simp only [slot2]
    omega
  obtain ⟨j, -, pc, bb, idx, sp', acc, mask, hx, hatm, h1853, hfp, hmodel⟩ :=
    dq_mmaCover hp hX hFw hR hI hB hN hW hat hcov hhc hmc hgc hmi hlast
  obtain ⟨hobs, -⟩ := svDone_done hp hX hFw hR hI hB hN hy hmc hpoll hx hatm h1853
    (.inl ⟨bb, sp', acc, mask, rfl⟩)
  have hyc := (wg0_svPoll hp hX hFw hpoll).1
  have hfp0 := hfp
  rcases hfp with ⟨d, s, accum, mk, hiss, hbl⟩ | ⟨cc, kk, cta, ⟨pcc, hcp⟩, -⟩
  · obtain ⟨l', b, hr⟩ := observed_mmaRead hX hiss hbl hobs
    exact .commitOperand hls ⟨ac, (show X.MemWrites (.thread (h, k)) ac bs from
      .inl ⟨pcw, hW⟩).intent, hcov⟩ (.inl ⟨d, s, accum, mk, hiss⟩)
      ⟨b, hfp0, hr.2⟩ (.direct hmodel)
      ⟨.cta, hobs, meets hyc hmc (Frame.lt_of_get hX hpoll)
        (Frame.lt_of_get hX hx)⟩ hpo hd
  · rw [hx] at hcp
    cases hcp

/-- **A dequant lane's chunk store is before a staging store of its byte** (of the CTA). -/
theorem dq_stage {h k y i pcw pcS : Nat} {ac aS : Acc} {bs bsS : List Byte} {l : Loc}
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : DequantAt L h pcw)
    (hcov : ac.Covers l) (hls : l.space = .shared) (hhc : h / L.block = y / L.block)
    (hS : X.get (y, i) = some ⟨pcS, .wr aS bsS⟩) (hatS : Wg0At L y pcS)
    (hst : MemRow.Wg0Stage L y pcS aS) (hcovS : aS.Covers l) :
    ByteCausality L X l (.thread (h, k)) (.thread (y, i)) := by
  obtain ⟨jw, p, hj, hpoll⟩ := wg0_stage_poll hp hX hFw hatS.1 hS hst
  have hkl : i < (X.tr y).length := (List.getElem?_eq_some_iff.mp hS).1
  exact dq_epi hp hX hFw hR hI hB hN hW hat hcov hls hhc hatS.1 hpoll
    (po_of_source_not_access rfl hj hkl (by rw [hpoll]; rfl))
    ⟨aS, .inl ⟨true, (show X.MemWrites (.thread (y, i)) aS bsS from .inl ⟨pcS, hS⟩).intent⟩,
      hcovS⟩

/-- **A dequant lane's chunk store is before the tensor store reading its byte** (of the CTA);
`hd` says the tensor store's read covers the byte. -/
theorem dq_store {h k g i pcw pcT addr : Nat} {ac : Acc} {bs : List Byte} {l : Loc}
    {s : TensorStore.Spec} {x y j : Nat} (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩)
    (hat : DequantAt L h pcw) (hcov : ac.Covers l) (hls : l.space = .shared)
    (hhc : h / L.block = g / L.block) (hT : X.get (g, i) = some ⟨pcT, .tensorStore addr s⟩)
    (hatT : Wg0At L g pcT) (hrl : TensorStore.readLoc s x y j = some l)
    (hd : ∃ a, X.MemTouches (.async (g, i) (.read (.store x y j))) a ∧ a.Covers l) :
    ByteCausality L X l (.thread (h, k)) (.async (g, i) (.read (.store x y j))) := by
  obtain ⟨c0, hc4, hpc0, -⟩ := wg0_store_read hp hX hFw hT hatT rfl hrl
  obtain ⟨jw, p, hj, hpoll⟩ := wg0_store_poll hp hX hFw hatT.1 hT ⟨c0, hc4, hpc0⟩
  have hkl : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hT).1
  exact dq_epi hp hX hFw hR hI hB hN hW hat hcov hls hhc hatT.1 hpoll
    (po_of_source_not_access rfl hj hkl (by rw [hpoll]; rfl)) hd

/-- **An MMA's operand read of a byte is before a staging store of it** (of the CTA): the MMA is
done at the storing lane's poll of `svDone`. -/
theorem mma_stage {g j y i pcm pcS bb : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {isB : Bool} {idx : Nat} {aS : Acc} {bsS : List Byte} {l : Loc}
    {b0 : Fin 2} (hx : X.get (g, j) = some ⟨pcm, .tc (.mma bb sp acc mask)⟩)
    (hatm : MmaAt L g pcm) (hf : X.MmaFootprint (g, j) isB idx l)
    (hlg : MemRow.LocIn L (g / L.block) (.dequant b0) l) (hyc : y / L.block = g / L.block)
    (hS : X.get (y, i) = some ⟨pcS, .wr aS bsS⟩) (hatS : Wg0At L y pcS)
    (hst : MemRow.Wg0Stage L y pcS aS) (hcovS : aS.Covers l) :
    ByteCausality L X l (.async (g, j) (.mmaRead isB idx)) (.thread (y, i)) := by
  obtain ⟨jw, p, hj, hpoll⟩ := wg0_stage_poll hp hX hFw hatS.1 hS hst
  obtain ⟨h1853, -⟩ := mma_dqUse hp hX hFw hx hatm hf hlg
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) ⟨hatm, h1853⟩
  obtain ⟨-, ic, pci, spi, rank, hgc, hmi, -⟩ := svDone_last hp hX hFw hR hI hB hN hatS.1 hpoll
  obtain ⟨hmc, -⟩ := svCommit_lane hp hX hFw hR hgc hmi
  rw [← hyc] at hg
  subst hg
  obtain ⟨hobs, -⟩ := svDone_done hp hX hFw hR hI hB hN hatS.1 hmc hpoll hx hatm h1853
    (.inl ⟨bb, sp, acc, mask, rfl⟩)
  have hkl : i < (X.tr y).length := (List.getElem?_eq_some_iff.mp hS).1
  have hls := hlg.1
  have hf0 := hf
  rcases hf with ⟨d, s, accum, mk, hiss, hbl⟩ | ⟨cc, kk, cta, ⟨pcc, hcp⟩, -⟩
  · exact completed_mma_source_before_store (f := (y, i)) hiss hf0
      (.inr ⟨.cta, hobs, meets rfl hmc (Frame.lt_of_get hX hpoll) (Frame.lt_of_get hX hx)⟩)
      rfl hj (.single (.inl (po_of_source_not_access rfl hj hkl (by rw [hpoll]; rfl)))) hls
      ⟨pcS, hS⟩ hcovS
  · rw [hx] at hcp
    cases hcp

end

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
