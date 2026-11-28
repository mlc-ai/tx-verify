-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarReach
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PeerBar
import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Kernels.InklingRelDecode.Proof.Softmax.Export.ArrivalCredit
import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive
import Lemmas.Protocol.NamedBarPhaseKeys

@[expose] public section

/-! # Every data lane's polls of a commit slot reach lane zero's later publication

A data lane's poll of a score slot or of the output slot precedes its rendezvous at pc 1012 of the
round, which is counted by lane zero's rendezvous of the round directly before its publication. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.Frame PTX.MbarRing MbarRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {c : Nat}

/-- **A data lane's poll of a score or done slot reaches the publication that follows lane
zero's rendezvous of the poll's round.** -/
theorem ToArrival.lane (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (rows : MbarRows Q L X) (hc : c<L.grid) {o : Object}
    (cm : (∃ s, o = Object.score s) ∨ o = Object.done) {t : Nat} (lt : t%L.block<128)
    (cta : t/L.block=c) : ToArrival L X c (o.loc L c) t := by
  intro j ka l tx cnt rel sc arr enough
  have hz : c*L.block<L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cz : c*L.block/L.block=c := by simp [hp.block]
  have lp : c*L.block%L.block<128 := by simp [hp.block]
  have ct : t/L.block=c*L.block/L.block := by rw [cz,cta]
  have ht : t<L.threads := by
    simp only [Launch.threads,hp.block] at *
    omega
  obtain ⟨u,c0,hu,bar⟩ := Softmax.Export.arrive_source hp hX arr
  have len : ka<(X.tr (c*L.block)).length := (List.getElem?_eq_some_iff.mp arr).1
  obtain ⟨ib,c',hb,ord,pr1,pr2⟩ := Tmem.peer_bar hp hX hf safe (t := c*L.block) (h := t)
    (Or.inr (Or.inr (Or.inr rfl))) bar (by omega) lp lt ct
  obtain ⟨pn,ps⟩ := Softmax.Export.arrival_polls hp hX hf arr
  subst hu
  have k1 := Tmem.poll_keeps 1257 bar
  have k2 := Tmem.poll_keeps 2239 bar
  have same : roundAt X t ib o.pc = roundAt X (c*L.block) (u+1) o.pc := by
    rcases cm with ⟨s,rfl⟩|rfl <;> simp only [roundAt,Object.pc] <;> omega
  have n1 := Scalar.count rows ht o ib
  have n2 := Scalar.count rows hz o (u+1)
  rw [cta] at n1
  rw [cz] at n2
  rw [n2,← same,← n1] at enough
  have hl : ib<(X.tr t).length := (List.getElem?_eq_some_iff.mp hb).1
  have wt : t%L.block/32 ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have w0 : c*L.block%L.block/32 ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have witness : Witness L X (.thread (t,ib)) (c*L.block,u) :=
    NamedBar.D_same_ordinal_witness hX (Export.barZeroSources hp hX)
      (by simp [CtaBarrier.warps,hp.block]) (Finset.card_range _)
      (by simp [CtaBarrier.warps,hp.block]) (by simp [CtaBarrier.target])
      ⟨lt_of_get hX hb,lt_of_get hX bar,ct⟩ hb bar (by omega)
      wt w0 ord
  exact (Relation.TransGen.single (Reach.poll_guard (spin hX) hl enough)).tail
    (DepStep.of_witness L witness) |>.tail (DepStep.of_resumes L
      (Resumes.of_blocking (f := (c*L.block,u+1)) bar rfl ⟨rfl,Nat.lt_succ_self _,len⟩))

/-- **Every data lane's polls of the score slots and of the done slot reach the notifications of
the elected lane's later commits.** -/
theorem lane_reach (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hc : c<L.grid) {t : Nat} (lt : t%L.block<128) (cta : t/L.block=c)
    {o : Object} (cm : (∃ s, o = Object.score s) ∨ o = Object.done) :
    Notify.Reach L kernel Assumptions.all X (o.loc L c) (KV.leader L X c 7) (o.loc L c) 0 t := by
  have ih := goals_all hp hX hf rows init words
  refine Reach.notify_reach hX (notification hp hX hf rows init (c := c) cm) fun n hn => ?_
  rcases cm with ⟨s,rfl⟩|rfl
  · intro x hx hn' j hj
    obtain ⟨⟨k,r,hk,hid,-,-⟩,pc,sp,getc,hm,ht,hcnt⟩ := Notify.Obj.S_rec
      (notification hp hX hf rows init (c := c) (.inl ⟨s,rfl⟩)) hx
    obtain ⟨_,_,_,_,mem⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
    subst hn'
    exact score_path hp hX hf rows init words hc
      (ToArrival.lane hp hX hf safe rows hc (.inl ⟨s,rfl⟩) lt cta) getc hm mem (by omega)
      fun n' hn'' _ => ih c hc n' hn''
  · intro x hx hn' j hj
    obtain ⟨⟨k,r,hk,hid,-,-⟩,pc,sp,getc,hm,ht,hcnt⟩ := Notify.Obj.S_rec
      (notification hp hX hf rows init (c := c) (.inr rfl)) hx
    obtain ⟨_,_,_,_,mem⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
    subst hn'
    exact done_path hp hX hf rows init words hc
      (ToArrival.lane hp hX hf safe rows hc (.inr rfl) lt cta) getc hm mem (by omega)
      fun n' hn'' _ => ih c hc n' hn''

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
