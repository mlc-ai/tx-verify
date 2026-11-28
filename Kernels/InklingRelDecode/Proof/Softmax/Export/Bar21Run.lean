-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.RescaleSkip
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RoundBar
import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
import Kernels.InklingRelDecode.Proof.Softmax.Export.PredBar
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Kernels.InklingRelDecode.Proof.Softmax.PollStep
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Kernels.InklingRelDecode.Proof.Lib.BarOne

/-! # What precedes the last rendezvous of a round after the first

The rendezvous of pc 1012 of a round after the first follows the P store and its wait, the P store
the mandatory rendezvous of pc 999, and that one a skipped decision or the rescale store of the
round, all within the round's polls. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Control

set_option maxRecDepth 10000 in
private theorem pred_bar21 {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.bar21) :
    d.site=.tmemWait := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | rfl

set_option maxRecDepth 10000 in
private theorem pred_tmemWait {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.tmemWait) :
    d.site=.tmemSt := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | rfl

private theorem site_1012 (s : Site) (h : s.pc=1012) : s=.bar21 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem back {Q L m X g i e k w ent d cnt} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,i)=some e) (hk : k ≤ i)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (softState w ent d cnt))) (later : d≠{}) :
    ∃ u old cnt' ev, u+1=k ∧
      Frame.stateAt (thread Q L) X g u=some (some (softState w ent old cnt')) ∧
      X.get (g,u)=some ev ∧ Control.next ent L g old ev=some (some d) ∧ ev.pc=old.site.pc ∧
      (∀ f, ev.kind≠.ub f) := by
  have len : k≤(X.tr g).length := hk.trans (List.getElem?_eq_some_iff.mp get).1.le
  obtain ⟨u,old,cnt',ev,eq,st,got,step⟩ := soft_prev len later hs
  have clean := Frame.noUbBefore_of_get hX get u (by omega) ev got
  exact ⟨u,old,cnt',ev,eq,st,got,step,Frame.event_pcU (fun g hg => thread_sound hp hg) hX got st
    clean,clean⟩

/-- **A late round's last rendezvous follows a skipped decision or the rescale store.** -/
public theorem bar21_run {Q L m X g i c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (bar : X.get (g,i)=some ⟨1012,.bar 0 c .sync⟩)
    (late : 2 ≤ pollRound 1257 ((X.tr g).take i)) :
    (∃ k a b' c' recv ok, X.get (g,k)=some ⟨2255,.shfl .bfly a b' c' recv ok⟩ ∧
      pollRound 1257 ((X.tr g).take k)=pollRound 1257 ((X.tr g).take i) ∧
      Lib.rescaleSkip L a recv=true) ∨
    ∃ k e, X.get (g,k)=some e ∧ e.pc=2328 ∧ (∀ f, e.kind≠.ub f) ∧
      pollRound 1257 ((X.tr g).take k)=pollRound 1257 ((X.tr g).take i) := by
  have clean : ∀ f, (Event.mk 1012 (.bar 0 c .sync)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX bar clean (by show 574<1012; decide)
    (by show 1012<2331; decide)
  have site : d.site=.bar21 := site_1012 _ pc.symm
  obtain ⟨u1,o1,c1,e1,eq1,s1,g1,n1,p1,k1⟩ := back hp hX bar le_rfl hs
    (by rintro rfl; exact absurd site (by decide))
  have t1 := pred_bar21 n1 site
  obtain ⟨u2,o2,c2,e2,eq2,s2,g2,n2,p2,k2⟩ := back hp hX bar (by omega) s1
    (by rintro rfl; exact absurd t1 (by decide))
  have t2 := pred_tmemWait n2 t1
  obtain ⟨u3,o3,c3,e3,eq3,s3,g3,n3,p3,k3⟩ := back hp hX bar (by omega) s2
    (by rintro rfl; exact absurd t2 (by decide))
  have t3 := (pred_tmemSt n3 t2).1
  have pc3 : e3.pc=999 := by rw [p3,t3]; rfl
  have b3 := Lib.zero_event hX hp.block g3 k3
  rw [pc3,show Lib.zeroSite 999=true by decide +kernel] at b3
  obtain ⟨p3',kd⟩ := e3
  change p3'=999 at pc3
  subst pc3
  cases kd <;> simp [Execution.isBarId] at b3
  rename_i id c3' md
  subst b3
  obtain ⟨rfl,_⟩ := Lib.recorded_bar hX hp.block g3
  have r2 : pollRound 1257 ((X.tr g).take (u3+1))=pollRound 1257 ((X.tr g).take u3) :=
    poll_same g3 (by show (999:Nat) ≠ 1257; omega)
  have r1 : pollRound 1257 ((X.tr g).take (u2+1))=pollRound 1257 ((X.tr g).take u2) :=
    poll_same g2 (by rw [p2,t2]; decide)
  have r0 : pollRound 1257 ((X.tr g).take (u1+1))=pollRound 1257 ((X.tr g).take u1) :=
    poll_same g1 (by rw [p1,t1]; decide)
  have rr : pollRound 1257 ((X.tr g).take i)=pollRound 1257 ((X.tr g).take u3) := by
    have a : u3+1=u2 := eq3
    have b : u2+1=u1 := eq2
    have c' : u1+1=i := eq1
    rw [← c', r0, ← b, r1, ← a, r2]
  rcases bar20_source hp hX g3 with ⟨k,a,b',c',recv,ok,hk,g4,sk,-⟩ |
      ⟨u,e,hu,ge,-,pce,-,e2',e1',h2,pc2,cl2,h1,pc1,cl1⟩ | zero
  · left
    refine ⟨k,a,b',c',recv,ok,g4,?_,sk⟩
    have : pollRound 1257 ((X.tr g).take (k+1))=pollRound 1257 ((X.tr g).take k) :=
      poll_same g4 (by show (2255:Nat) ≠ 1257; omega)
    rw [rr, ← this, hk]
  · right
    subst hu
    refine ⟨u+1,e2',h2,pc2,cl2,?_⟩
    have s2' := poll_same h2 (by rw [pc2]; omega)
    have s1' := poll_same h1 (by rw [pc1]; omega)
    have e3 : pollRound 1257 ((X.tr g).take (u+3))=pollRound 1257 ((X.tr g).take (u+1)) :=
      s1'.trans s2'
    rw [rr, e3]
  · exfalso
    have key := round_barriers hp hX hf g3 (fun _ => nofun) (by show 574<999; omega)
      (by show 999<2331; omega) (n := 4*(pollRound 1257 ((X.tr g).take u3)-1)+2) (by
        simp [mandatoryAt])
    omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
