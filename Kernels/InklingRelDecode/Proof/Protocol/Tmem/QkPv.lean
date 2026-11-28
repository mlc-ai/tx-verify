-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PHandoff
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaDone
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BlockCounts
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarArrivals
import Kernels.InklingRelDecode.Proof.Softmax.Export.ArrivalCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits

@[expose] public section

/-! # A QK MMA of a buffer is done before the PV MMA that reads the probabilities of its block

The PV MMA of block `m` (state `b = m + 1`) follows `m / 2 + 1` polls of the probability slot of
its parity; the poll with `m / 2` earlier ones observes lane zero's publication of round `n ≥ m` of
that parity, which follows lane zero's score poll with `m / 2` earlier polls. A QK MMA of the
slot's parity and a block at most `m` has at most `m / 2` earlier commits to the slot, so lane
zero's poll observes a commit after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A QK MMA with at most `m / 2` earlier commits to the score slot is done before the PV MMA
whose probability slot of parity `m % 2` has `m / 2 + 1` polls before it.** -/
public theorem qk_before_pv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (words : RoleBytes L X) {g kq kp pcq dq sq aq mq pcp dp sp ap mp b}
    (hq : X.get (g,kq) = some ⟨pcq,.tc (.mma dq sq aq mq)⟩)
    (hv : X.get (g,kp) = some ⟨pcp,.tc (.mma dp sp ap mp)⟩)
    (pb : pollRound 2510 ((X.tr g).take kp) = b) (one : 1 ≤ b)
    (few : ((X.tr g).take kq).countP
      (commitsTo ((Object.score (MbarRow.slot2 (b-1))).loc L (g/L.block))) ≤ (b-1)/2) :
    DoneBefore L X (g,kq) (g,kp) := by
  obtain ⟨lead,warp⟩ := mma_leader hp hX hf hv
  simp only at lead warp
  have hg := Frame.lt_of_get hX hv
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : g/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 hg
  have hz : g/L.block*L.block < L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cz : g/L.block*L.block/L.block = g/L.block := by simp [hp.block]
  have hk : kp < (X.tr g).length := (List.getElem?_eq_some_iff.mp hv).1
  have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 (b-1))) kp
  change okPolls ((Object.prob (MbarRow.slot2 (b-1))).loc L (g/L.block)) ((X.tr g).take kp) =
    (Object.prob (MbarRow.slot2 (b-1))).visits (pollRound 2510 ((X.tr g).take kp)) at cnt
  rw [pb] at cnt
  have vis : (Object.prob (MbarRow.slot2 (b-1))).visits b = (b+2-1-(b-1)%2)/2 := rfl
  have hU := prob_handoff hp hX hf rows init words hc (MbarRow.slot2 (b-1))
  obtain ⟨j,pc,p,acq,sc,hjk,hw,hqq⟩ := UnitHandoff.exists_poll (m := (Object.prob
    (MbarRow.slot2 (b-1))).loc L (g/L.block)) (h := g) (f := kp) (c := (b-1)/2)
    (by rw [cnt,vis]; omega)
  obtain ⟨ia,harr,hsync⟩ := hU _ j pc p acq sc ((b-1)/2) lead.symm hw (by simpa using hqq)
    (g/L.block*L.block) ⟨0,rfl⟩
  obtain ⟨ev,hev,hit⟩ := hsync.arrives
  obtain ⟨tx,n,rel,sc',rfl,-⟩ := arrival_event rows hz hev hit
  obtain ⟨-,slot,bound⟩ := arrival_ordinal rows hz hev
  have hn : b-1 ≤ ((X.tr (g/L.block*L.block)).take ia).countP (fun e : Event => e.pc == 1013) := by
    have : (MbarRow.slot2 (b-1)).val = (b-1)%2 := rfl
    omega
  obtain ⟨-,pn⟩ := Softmax.Export.arrival_polls hp hX hf hev
  have cnt2 := Protocol.Scalar.count rows hz (Object.score (MbarRow.slot2 (b-1))) ia
  change okPolls ((Object.score (MbarRow.slot2 (b-1))).loc L (g/L.block*L.block/L.block))
    ((X.tr (g/L.block*L.block)).take ia) = (Object.score (MbarRow.slot2 (b-1))).visits
    (pollRound 1257 ((X.tr (g/L.block*L.block)).take ia)) at cnt2
  rw [cz,pn] at cnt2
  have vis2 : ∀ n, (Object.score (MbarRow.slot2 (b-1))).visits n = (n+2-1-(b-1)%2)/2 :=
    fun _ => rfl
  obtain ⟨j2,pc2,p2,acq2,sc2,hj2,hw2,hq2⟩ := UnitHandoff.exists_poll
    (m := (Object.score (MbarRow.slot2 (b-1))).loc L (g/L.block)) (h := g/L.block*L.block)
    (f := ia) (c := (b-1)/2) (by rw [cnt2,vis2]; omega)
  have len : ia < (X.tr (g/L.block*L.block)).length := (List.getElem?_eq_some_iff.mp hev).1
  have bc1 : baseCausality L X (g/L.block*L.block,j2) (g/L.block*L.block,ia) :=
    .single (.inl (po_of_source_not_access rfl hj2 len (by rw [hw2]; rfl)))
  have bc2 := hU.hb (h := g) (g := g/L.block*L.block) (e := ia) lead.symm hw
    (by simpa using hqq) ⟨0,rfl⟩ (by omega) hjk hk
  exact mma_done_before hp hX hf rows init words hc (o := Object.score (MbarRow.slot2 (b-1)))
    (Or.inl ⟨_,rfl⟩) hw2 hq2 hq lead.symm (by dsimp only; omega) (bc1.trans bc2)

end PTX.Kernels.InklingRelDecode.Proof.Tmem
