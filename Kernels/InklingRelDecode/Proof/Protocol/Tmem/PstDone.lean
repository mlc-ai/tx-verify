-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaDone
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RoundBar
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LastBar
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PeerBar
import Lemmas.Kernel.Frame
import Lemmas.Kernel.Safety.TableU

@[expose] public section

/-! # An MMA of the lane is done before a probability store of the round whose score it precedes

An MMA with at most `r / 2` earlier commits to the score slot of parity `r % 2` is before the
commit lane zero's poll of round `r` observes. The store of round `r` follows the round's last
mandatory rendezvous (pc 999) directly, and lane zero's poll precedes its own rendezvous of the
round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An MMA with at most `r / 2` earlier commits to the score slot is done before the round-`r`
probability store.** -/
public theorem mma_before_pst (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (rows : MbarRows Q L X)
    (init : Protocol.Mbar.InitRows L X) (words : RoleBytes L X)
    {g k pc dst s acc mask t sk a vals sh r}
    (hx : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (hy : X.get (t,sk) = some ⟨1009,.tc (.st a vals sh)⟩) (lt : t%L.block < 128)
    (cta : g/L.block = t/L.block) (rd : pollRound 1257 ((X.tr t).take sk) = r+1)
    (s3 : Softmax.Export.mandatory ((X.tr t).take sk) + 2 = 4*r+3)
    (few : ((X.tr g).take k).countP
      (commitsTo ((Object.score (MbarRow.slot2 r)).loc L (g/L.block))) ≤ r/2) :
    DoneBefore L X (g,k) (t,sk) := by
  obtain ⟨lead,-⟩ := mma_leader hp hX hf hx
  have hg := Frame.lt_of_get hX hx
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : g/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 hg
  have hz : g/L.block*L.block < L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cz : g/L.block*L.block/L.block = g/L.block := by simp [hp.block]
  have lp : g/L.block*L.block%L.block < 128 := by rw [Nat.mul_mod_left]; omega
  have lent : sk < (X.tr t).length := (List.getElem?_eq_some_iff.mp hy).1
  have nu : ∀ i ev, i < sk → X.get (t,i) = some ev → ∀ f, ev.kind ≠ .ub f :=
    fun i ev hi get => Frame.noUbBefore_of_get hX hy i hi ev get
  obtain ⟨jb,pcb,cb,hjb,hbar,hpcb,hmand⟩ := last_bar hX hp.block (t := t) nu (by omega)
  obtain ⟨ir,r1,r2,r3⟩ := bar_round_facts hp hX hf hbar hpcb
  have bp : barPos pcb ≤ 3 := by unfold barPos; split_ifs <;> omega
  have ir_r : ir = r := by omega
  subst ir_r
  obtain ⟨ib,cb',hb2,ord,p1,p2⟩ := peer_bar hp hX hf safe (t := t) (h := g/L.block*L.block)
    hpcb hbar (by omega) lt lp (by rw [cz,cta])
  have cnt := Protocol.Scalar.count rows hz (Object.score (MbarRow.slot2 ir)) ib
  change okPolls ((Object.score (MbarRow.slot2 ir)).loc L (g/L.block*L.block/L.block))
    ((X.tr (g/L.block*L.block)).take ib) = (Object.score (MbarRow.slot2 ir)).visits
    (pollRound 1257 ((X.tr (g/L.block*L.block)).take ib)) at cnt
  rw [cz,p1,r1] at cnt
  have vis : (Object.score (MbarRow.slot2 ir)).visits (ir+1) = (ir+1+2-1-ir%2)/2 := rfl
  obtain ⟨j,pcj,pj,acq,scj,hjib,hw,hq⟩ := MbarRing.UnitHandoff.exists_poll
    (m := (Object.score (MbarRow.slot2 ir)).loc L (g/L.block)) (h := g/L.block*L.block)
    (f := ib) (c := ir/2) (by rw [cnt,vis]; omega)
  have po : baseCausality L X (g/L.block*L.block,j) (t,sk) :=
    Protocol.Shared.scratch_handoff hp hX hb2 hbar (by rw [cz,cta]) lp lt ord hjib hjb lent
  exact mma_done_before hp hX hf rows init words hc (o := Object.score (MbarRow.slot2 ir))
    (Or.inl ⟨_,rfl⟩) hw hq hx lead.symm few po

end PTX.Kernels.InklingRelDecode.Proof.Tmem
