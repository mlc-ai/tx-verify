-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
import Kernels.InklingRelDecode.Proof.Softmax.Export.PredBar
public import Kernels.InklingRelDecode.Proof.Lib.RescaleSkip
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RoundBar
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Softmax.RescaleChoice
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Kernels.InklingRelDecode.Proof.Common.SoftFixed
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Control

set_option maxRecDepth 10000 in
private theorem pred_ldO {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.ldO) :
    d.site=.shfl12 ∧ ∃ m sent b c recv ok, ev.kind=.shfl m sent b c recv ok ∧
      skipRescale L g sent recv=false := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) |
    exact ⟨rfl,_,_,_,_,_,_,by assumption,by simpa using ‹¬skipRescale _ _ _ _ = true›⟩

set_option maxRecDepth 10000 in
private theorem pred_bar24 {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.bar24) :
    d.site=.waitLdO := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | rfl

set_option maxRecDepth 10000 in
private theorem pred_waitLdO {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.waitLdO) :
    d.site=.ldO := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | rfl

private theorem site_2326 (s : Site) (h : s.pc=2326) : s=.bar24 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_999 (s : Site) (h : s.pc=999) : s=.bar20 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- The preceding event of an event of the Softmax interior, with its state. -/
private theorem step_back {Q L m X g i e k w ent d cnt} (hp : Pre Q L m)
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

private theorem flat {Q L m X g u ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,u)=some ev)
    (clean : ∀ f, ev.kind≠.ub f) (zero : Lib.zeroSite ev.pc=false) :
    ((X.tr g).take (u+1)).countP (Execution.isBarId 0)=
      ((X.tr g).take u).countP (Execution.isBarId 0) := by
  have e := Lib.zero_event hX hp.block get clean
  have : (X.tr g)[u]?=some ev := get
  rw [List.take_add_one,this,List.countP_append]
  simp [e,zero]

private theorem not_empty {s : Site} (h : s≠.setMaxReg) (d : D) (e : d.site=s) : d≠{} := by
  rintro rfl
  exact h e.symm

/-- The optional rendezvous is reached only from a rescale decision that did not skip: its
second shuffle is three events earlier, with no barrier zero in between. -/
public theorem rescale_source {Q L m X g i c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (bar : X.get (g,i)=some ⟨2326,.bar 0 c .sync⟩) :
    ∃ k a b' c' recv ok, k+3=i ∧ X.get (g,k)=some ⟨2255,.shfl .bfly a b' c' recv ok⟩ ∧
      Lib.rescaleSkip L a recv=false ∧
      ((X.tr g).take i).countP (Execution.isBarId 0)=
        ((X.tr g).take k).countP (Execution.isBarId 0) := by
  have clean : ∀ f, (Event.mk 2326 (.bar 0 c .sync)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX bar clean (by show 574<2326; decide)
    (by show 2326<2331; decide)
  have site : d.site=.bar24 := site_2326 _ pc.symm
  obtain ⟨u1,o1,c1,e1,eq1,s1,g1,n1,p1,k1⟩ := step_back hp hX bar le_rfl hs
    (not_empty (by decide) d site)
  have t1 := pred_bar24 n1 site
  obtain ⟨u2,o2,c2,e2,eq2,s2,g2,n2,p2,k2⟩ := step_back hp hX bar (by omega) s1
    (not_empty (by decide) o1 t1)
  have t2 := pred_waitLdO n2 t1
  obtain ⟨u3,o3,c3,e3,eq3,s3,g3,n3,p3,k3⟩ := step_back hp hX bar (by omega) s2
    (not_empty (by decide) o2 t2)
  obtain ⟨t3,m3,a3,b3,c3',r3,ok3,kind3,skip3⟩ := pred_ldO n3 t2
  have pc3 : e3.pc=2255 := by rw [p3,t3]; rfl
  obtain ⟨p,kd⟩ := e3
  change p=2255 at pc3
  subst pc3
  cases kind3
  obtain ⟨rfl,-,-⟩ := shuffle_2255_shape hp hX g3
  refine ⟨u3,a3,b3,c3',r3,ok3,by omega,g3,(Control.skip_free L g a3 r3).symm.trans skip3,?_⟩
  have z1 : Lib.zeroSite e2.pc=false := by rw [p2,t2]; decide +kernel
  have z0 : Lib.zeroSite e1.pc=false := by rw [p1,t1]; decide +kernel
  have f2 := flat hp hX g2 k2 z1
  have f1 := flat hp hX g1 k1 z0
  have f3 : ((X.tr g).take (u3+1)).countP (Execution.isBarId 0)=
      ((X.tr g).take u3).countP (Execution.isBarId 0) := by
    have : (X.tr g)[u3]?=some ⟨2255,.shfl .bfly a3 b3 c3' r3 ok3⟩ := g3
    rw [List.take_add_one,this,List.countP_append]
    simp [Execution.isBarId]
  rw [eq1] at f1
  rw [eq2] at f2
  rw [eq3] at f3
  exact f1.trans (f2.trans f3)

/-- The mandatory rendezvous that follows a round's decision is preceded either by a skipped
decision, by the optional rendezvous, or by the first round's setup. -/
public theorem bar20_source {Q L m X g i c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (bar : X.get (g,i)=some ⟨999,.bar 0 c .sync⟩) :
    (∃ k a b' c' recv ok, k+1=i ∧ X.get (g,k)=some ⟨2255,.shfl .bfly a b' c' recv ok⟩ ∧
      Lib.rescaleSkip L a recv=true ∧
      ((X.tr g).take i).countP (Execution.isBarId 0)=
        ((X.tr g).take k).countP (Execution.isBarId 0)) ∨
    (∃ u e, u+3=i ∧ X.get (g,u)=some e ∧ Execution.isBarId 0 e=true ∧ e.pc=2326 ∧
      ((X.tr g).take i).countP (Execution.isBarId 0)=
        ((X.tr g).take u).countP (Execution.isBarId 0)+1 ∧
      ∃ e2 e1, X.get (g,u+1)=some e2 ∧ e2.pc=2328 ∧ (∀ f, e2.kind≠.ub f) ∧
        X.get (g,u+2)=some e1 ∧ e1.pc=2329 ∧ (∀ f, e1.kind≠.ub f)) ∨
    mandatory ((X.tr g).take i)=0 := by
  have clean : ∀ f, (Event.mk 999 (.bar 0 c .sync)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX bar clean (by show 574<999; decide)
    (by show 999<2331; decide)
  have site : d.site=.bar20 := site_999 _ pc.symm
  obtain ⟨u1,o1,c1,e1,eq1,s1,g1,n1,p1,k1⟩ := step_back hp hX bar le_rfl hs
    (not_empty (by decide) d site)
  rcases pred_bar20 n1 site with ⟨t1,m1,a1,b1,cc1,r1,ok1,kind1,skip1⟩|t1|⟨t1,zero⟩
  · left
    have pc1 : e1.pc=2255 := by rw [p1,t1]; rfl
    obtain ⟨p,kd⟩ := e1
    change p=2255 at pc1
    subst pc1
    cases kind1
    obtain ⟨rfl,-,-⟩ := shuffle_2255_shape hp hX g1
    refine ⟨u1,a1,b1,cc1,r1,ok1,eq1,g1,(Control.skip_free L g a1 r1).symm.trans skip1,?_⟩
    rw [←eq1]
    have : (X.tr g)[u1]?=some ⟨2255,.shfl .bfly a1 b1 cc1 r1 ok1⟩ := g1
    rw [List.take_add_one,this,List.countP_append]
    simp [Execution.isBarId]
  · right; left
    obtain ⟨u2,o2,c2,e2,eq2,s2,g2,n2,p2,k2⟩ := step_back hp hX bar (by omega) s1
      (not_empty (by decide) o1 t1)
    have t2 := pred_waitStO n2 t1
    obtain ⟨u3,o3,c3,e3,eq3,s3,g3,n3,p3,k3⟩ := step_back hp hX bar (by omega) s2
      (not_empty (by decide) o2 t2)
    have t3 := pred_stO n3 t2
    have z1 : Lib.zeroSite e1.pc=false := by rw [p1,t1]; decide +kernel
    have z2 : Lib.zeroSite e2.pc=false := by rw [p2,t2]; decide +kernel
    have pc3 : e3.pc=2326 := by rw [p3,t3]; rfl
    have bar3 : Execution.isBarId 0 e3=true := by
      rw [Lib.zero_event hX hp.block g3 k3,pc3]; decide +kernel
    refine ⟨u3,e3,by omega,g3,bar3,pc3,?_,e2,e1,by rw [eq3]; exact g2,by rw [p2,t2]; rfl,k2,
      by rw [show u3+2=u1 by omega]; exact g1,by rw [p1,t1]; rfl,k1⟩
    have f1 := flat hp hX g1 k1 z1
    have f2 := flat hp hX g2 k2 z2
    have : (X.tr g)[u3]?=some e3 := g3
    have f3 : ((X.tr g).take (u3+1)).countP (Execution.isBarId 0)=
        ((X.tr g).take u3).countP (Execution.isBarId 0)+1 := by
      rw [List.take_add_one,this,List.countP_append]
      simp [bar3]
    rw [eq1] at f1
    rw [eq2] at f2
    rw [eq3] at f3
    omega
  · right; right
    have len := (List.getElem?_eq_some_iff.mp bar).1.le
    have fixed := soft_fixed_total hp hX len hs (Frame.noUbBefore_of_get hX bar)
    have count (key : Cls) : n key=((X.tr g).take i).countP (cls key) := fcount hs key
    simp only [count,fixedCount,site] at fixed
    change mandatory ((X.tr g).take i)+2=4*d.i+2 at fixed
    have : d.i=0 := zero
    omega

private theorem site_2260 (s : Site) (h : s.pc=2260) : s=.ldO := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_1009 (s : Site) (h : s.pc=1009) : s=.tmemSt := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- The O load of a rescale is reached only from a rescale decision that did not skip: its second
shuffle is the event before, with no barrier zero in between. -/
public theorem ldO_source {Q L m X g i k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,i)=some ⟨2260,k⟩)
    (clean : ∀ f, k≠.ub f) :
    ∃ u a b' c' recv ok, u+1=i ∧ X.get (g,u)=some ⟨2255,.shfl .bfly a b' c' recv ok⟩ ∧
      Lib.rescaleSkip L a recv=false ∧
      ((X.tr g).take i).countP (Execution.isBarId 0)=
        ((X.tr g).take u).countP (Execution.isBarId 0) := by
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<2260; decide)
    (by show 2260<2331; decide)
  have site : d.site=.ldO := site_2260 _ pc.symm
  obtain ⟨u1,o1,c1,e1,eq1,s1,g1,n1,p1,k1⟩ := step_back hp hX get le_rfl hs
    (not_empty (by decide) d site)
  obtain ⟨t3,m3,a3,b3,c3',r3,ok3,kind3,skip3⟩ := pred_ldO n1 site
  have pc3 : e1.pc=2255 := by rw [p1,t3]; rfl
  obtain ⟨p,kd⟩ := e1
  change p=2255 at pc3
  subst pc3
  cases kind3
  obtain ⟨rfl,-,-⟩ := shuffle_2255_shape hp hX g1
  refine ⟨u1,a3,b3,c3',r3,ok3,eq1,g1,(Control.skip_free L g a3 r3).symm.trans skip3,?_⟩
  have f3 : ((X.tr g).take (u1+1)).countP (Execution.isBarId 0)=
      ((X.tr g).take u1).countP (Execution.isBarId 0) := by
    have : (X.tr g)[u1]?=some ⟨2255,.shfl .bfly a3 b3 c3' r3 ok3⟩ := g1
    rw [List.take_add_one,this,List.countP_append]
    simp [Execution.isBarId]
  rw [eq1] at f3
  exact f3

/-- The P store is reached only from the mandatory rendezvous before it. -/
public theorem tmemSt_source {Q L m X g i k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,i)=some ⟨1009,k⟩)
    (clean : ∀ f, k≠.ub f) :
    ∃ u e, u+1=i ∧ X.get (g,u)=some e ∧ e.pc=999 ∧ Execution.isBarId 0 e=true := by
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<1009; decide)
    (by show 1009<2331; decide)
  have site : d.site=.tmemSt := site_1009 _ pc.symm
  obtain ⟨u1,o1,c1,e1,eq1,s1,g1,n1,p1,k1⟩ := step_back hp hX get le_rfl hs
    (not_empty (by decide) d site)
  have t1 := (pred_tmemSt n1 site).1
  have pc1 : e1.pc=999 := by rw [p1,t1]; rfl
  refine ⟨u1,e1,eq1,g1,pc1,?_⟩
  rw [Lib.zero_event hX hp.block g1 k1,pc1]
  decide +kernel

set_option maxRecDepth 10000 in
private theorem pred_arrive {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.arrive) :
    d.site=.bar21 := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | rfl

private theorem site_1013 (s : Site) (h : s.pc=1013) : s=.arrive := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- A probability publication follows the last mandatory rendezvous of its round directly. -/
public theorem arrive_source {Q L m X g i l tx cnt rel sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,i)=some ⟨1013,.arrive l tx cnt rel sc⟩) :
    ∃ u c, u+1=i ∧ X.get (g,u)=some ⟨1012,.bar 0 c .sync⟩ := by
  have clean : ∀ f, (Event.mk 1013 (.arrive l tx cnt rel sc)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<1013; decide)
    (by show 1013<2331; decide)
  have site : d.site=.arrive := site_1013 _ pc.symm
  obtain ⟨u,o,c1,e,eq,s1,g1,n1,p1,k1⟩ := step_back hp hX get le_rfl hs
    (not_empty (by decide) d site)
  have t1 := pred_arrive n1 site
  have pc1 : e.pc=1012 := by rw [p1,t1]; rfl
  have bar := Lib.zero_event hX hp.block g1 k1
  rw [pc1,show Lib.zeroSite 1012=true by decide +kernel] at bar
  obtain ⟨p,kd⟩ := e
  change p=1012 at pc1
  subst pc1
  cases kd <;> simp [Execution.isBarId] at bar
  rename_i id c md
  subst bar
  obtain ⟨rfl,_⟩ := Lib.recorded_bar hX hp.block g1
  exact ⟨u,c,eq,g1⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
