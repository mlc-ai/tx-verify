-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarLane
public import Lemmas.Tcgen05.TmemRace
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Lemmas.Protocol.ReachJoint
import Lemmas.Protocol.UnitNotify
import Lemmas.Protocol.ObservedSync
import Lemmas.Protocol.CountNth
import Lemmas.Flow.NthEv
import Lemmas.Kernel.Frame

@[expose] public section

/-! # An MMA is done before what follows lane zero's poll of a commit slot

The elected MMA lane's commit to a score slot or to the output slot is observed by lane zero's poll
with as many earlier polls as the commit has earlier commits (`Notify.Obj.observes`). An MMA with at
most that many earlier commits to the slot is before the commit, so it is done before every event
that follows the poll. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem poll_scope {c g k pc p ok acq sc o}
    (rows : MbarRows Q L X) (hg : g < L.threads) (cm : (∃ s, o = Object.score s) ∨ o = Object.done)
    (get : X.get (g,k) = some ⟨pc,.wait (o.loc L c) p ok acq sc⟩) : acq = true ∧ sc = .cta := by
  obtain ⟨-,use⟩ := uses rows hg get rfl
  cases use with
  | init kd => cases kd
  | scoreWait _ _ w | doneWait _ _ w | probWait _ _ w =>
    obtain ⟨ok',kd⟩ := w
    obtain ⟨-,-,-,h1,h2⟩ := Kind.wait.inj kd
    exact ⟨h1,h2⟩
  | scoreCommit _ _ bad | doneCommit _ _ bad =>
    obtain ⟨_,kd,_⟩ := bad
    cases kd
  | probArrive _ _ bad => cases bad

/-- **An MMA with at most `u` earlier commits to the slot is done before every event that follows
lane zero's poll with `u` earlier polls of the slot.** -/
public theorem mma_done_reach (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    {c : Nat} (hc : c < L.grid) {o : Object} (cm : (∃ s, o = Object.score s) ∨ o = Object.done)
    {h : Nat} (hh : h < L.threads) (cta : h/L.block = c)
    (R : Notify.Reach L kernel Assumptions.all X (o.loc L c) (KV.leader L X c 7) (o.loc L c) 0 h)
    {j u pc p acq sc}
    (get : X.get (h,j) = some ⟨pc,.wait (o.loc L c) p true acq sc⟩)
    (hq : okPolls (o.loc L c) ((X.tr h).take j) = u) {x : EvId} {pc0 dd s acc mask}
    (hx : X.get x = some ⟨pc0,.tc (.mma dd s acc mask)⟩) (hxc : x.1 = KV.leader L X c 7)
    (few : ((X.tr x.1).take x.2).countP (commitsTo (o.loc L c)) ≤ u) {e : EvId}
    (po : baseCausality L X (h,j) e) : DoneBefore L X x e := by
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  obtain ⟨hacq,hsc⟩ := poll_scope (c := c) rows hh cm get
  subst hacq hsc
  have O := notification hp hX hf rows init (c := c) cm
  obtain ⟨ic,pc',sp,rank,hget,hm,ht,hcnt,hrk,hobs⟩ := O.observes hX R get (by simpa using hq)
  obtain ⟨g,k⟩ := x
  simp only at hxc
  subst hxc
  have hk : k < ic := by
    by_contra! le
    have step := countP_take_succ (p := commitsTo (o.loc L c)) hget (by simp [commitsTo,hm])
    have ne : ic ≠ k := by
      rintro rfl
      rw [hget] at hx
      cases hx
    have mono := countP_take_mono (commitsTo (o.loc L c)) (X.tr (KV.leader L X c 7))
      (show ic+1 ≤ k by omega)
    simp only at few
    omega
  refine .inl ⟨(h,j),.cta,⟨_,_,⟨(KV.leader L X c 7,ic),sp,rank,rfl,
    ⟨rfl,hk,.inl ⟨dd,s,acc,mask,pc0,hx⟩,sp,pc',hget⟩,⟨pc',hget⟩,ht,hrk⟩,hobs⟩,?_,po⟩
  show ScopesMeet L .cluster (KV.leader L X c 7) .cta h
  exact ⟨⟨hy,hh,by rw [cy,cta]⟩,hh,hy,by rw [cy,cta]⟩

/-- **The same for lane zero's own poll.** -/
public theorem mma_done_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) {c : Nat} (hc : c < L.grid) {o : Object}
    (cm : (∃ s, o = Object.score s) ∨ o = Object.done) {j u pc p acq sc}
    (get : X.get (c*L.block,j) = some ⟨pc,.wait (o.loc L c) p true acq sc⟩)
    (hq : okPolls (o.loc L c) ((X.tr (c*L.block)).take j) = u) {x : EvId} {pc0 dd s acc mask}
    (hx : X.get x = some ⟨pc0,.tc (.mma dd s acc mask)⟩) (hxc : x.1 = KV.leader L X c 7)
    (few : ((X.tr x.1).take x.2).countP (commitsTo (o.loc L c)) ≤ u) {e : EvId}
    (po : baseCausality L X (c*L.block,j) e) : DoneBefore L X x e := by
  have hz : c*L.block < L.threads := by simp only [Launch.threads,hp.block] at *; omega
  refine mma_done_reach hp hX hf rows init hc cm hz (by simp [hp.block])
    (Reach.notify_reach hX (notification hp hX hf rows init (c := c) cm) fun n hn => ?_)
    get hq hx hxc few po
  rcases cm with ⟨s,rfl⟩|rfl
  · exact (goals_all hp hX hf rows init words c hc n hn).2.1 s
  · exact (goals_all hp hX hf rows init words c hc n hn).2.2

/-- **The same for a data lane's poll.** -/
public theorem mma_done_lane (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) {c : Nat} (hc : c < L.grid) {o : Object}
    (cm : (∃ s, o = Object.score s) ∨ o = Object.done) {t : Nat} (lt : t%L.block < 128)
    (cta : t/L.block = c) {j u pc p acq sc}
    (get : X.get (t,j) = some ⟨pc,.wait (o.loc L c) p true acq sc⟩)
    (hq : okPolls (o.loc L c) ((X.tr t).take j) = u) {x : EvId} {pc0 dd s acc mask}
    (hx : X.get x = some ⟨pc0,.tc (.mma dd s acc mask)⟩) (hxc : x.1 = KV.leader L X c 7)
    (few : ((X.tr x.1).take x.2).countP (commitsTo (o.loc L c)) ≤ u) {e : EvId}
    (po : baseCausality L X (t,j) e) : DoneBefore L X x e :=
  mma_done_reach hp hX hf rows init hc cm (Frame.lt_of_get hX get) cta
    (lane_reach hp hX hf safe rows init words hc lt cta cm) get hq hx hxc few po

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
