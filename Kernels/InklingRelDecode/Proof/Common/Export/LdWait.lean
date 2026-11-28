-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import all Kernels.InklingRelDecode.Proof.Common.Export.TcForward
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.EpilogueEvent
import Kernels.InklingRelDecode.Proof.Common.Table
import Kernels.InklingRelDecode.Proof.Common.Where
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Lemmas.Flow.NotTcData
import Lemmas.Flow.TcStAddr
import Lemmas.Flow.GlueStep

@[expose] public section

/-! # A load or a store is followed by its wait

The kernel's Tensor Memory loads (pc 1265, 2260, 2607) and stores (pc 1009, 2328) are each followed
in the control flow by the wait for them (pc 1298, 2261, 2608; 1010, 2329); the next event of the
thread, when there is one, is that wait. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem epi_forward {i w ent d n ev e1} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hs : stateAt (thread Q L) X g i=some (some (epiState w ent d n)))
    (get : X.get (g,i)=some ev) (get1 : X.get (g,i+1)=some e1) (clean1 : ∀ f, e1.kind≠.ub f) :
    ∃ dn n', stateAt (thread Q L) X g (i+1)=some (some (epiState w ent dn n')) ∧
      Epilogue.Control.next (epiEntry ent (g%L.block)) L g d ev=some (some dn) := by
  have hg := lt_of_get hX get1
  obtain ⟨⟨s1,n1⟩,hs1,_⟩ := good_stateU (fun g h => thread_sound hp h) hX get1
    (fun _ f h => clean1 f (congrArg Event.kind h)) (hf g hg (i+1))
  have get' : (X.tr g)[i]?=some ev := get
  have hs0 := hs1
  rw [stateAt_succ get',hs] at hs1
  have move : (thread Q L g).next (epiState w ent d n) ev=some (some (s1,n1)) := hs1
  obtain ⟨step,rfl⟩ := Code.counted_next_some move
  obtain ⟨_,sub,rfl⟩ := Code.glue_inr_some step
  obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
  obtain ⟨_,localStep,rfl⟩ := Code.glue_inr_some go
  refine ⟨_,Code.bump cls n ev,?_,localStep⟩
  rw [hs0]

private theorem no_ub {X : Execution} {i : Nat} (nu : Frame.NoUbBefore X g (i+2)) {e : Event}
    (he : X.get (g,i+1)=some e) : ∀ f, e.kind≠.ub f := fun f => nu (i+1) (by omega) e he f

private theorem site_ld (s : Softmax.Site) (h : s.pc = 1265 ∨ s.pc = 2260 ∨ s.pc = 1009 ∨
    s.pc = 2328) : (s.pc = 1265 → s = .ldS) ∧ (s.pc = 2260 → s = .ldO) ∧
      (s.pc = 1009 → s = .tmemSt) ∧ (s.pc = 2328 → s = .stO) := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem wait_kind {e1 : Event} {j : Nat} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (g1 : X.get (g,j)=some e1)
    (clean : ∀ f, e1.kind≠.ub f) (w : e1.pc=1298 ∨ e1.pc=2261 ∨ e1.pc=2608 ∨ e1.pc=2329 ∨
      e1.pc=1010) :
    (e1.pc=1298 ∨ e1.pc=2261 ∨ e1.pc=2608) ∧ e1=⟨e1.pc,.tc .waitLd⟩ ∨
      (e1.pc=2329 ∨ e1.pc=1010) ∧ e1=⟨e1.pc,.tc .waitSt⟩ := by
  have hb : L.block % 32 = 0 := by simp [hp.block]
  obtain ⟨f,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX g1
  · exact (clean f bad).elim
  rcases w with w|w|w|w|w <;> rw [w] at code fire
  · obtain rfl := Option.some.inj (code.symm.trans Flow.code_1298)
    exact .inl ⟨.inl w,(fires_tcWaitLd hb fire).trans (by rw [w])⟩
  · obtain rfl := Option.some.inj (code.symm.trans Flow.code_2261)
    exact .inl ⟨.inr (.inl w),(fires_tcWaitLd hb fire).trans (by rw [w])⟩
  · obtain rfl := Option.some.inj (code.symm.trans Flow.code_2608)
    exact .inl ⟨.inr (.inr w),(fires_tcWaitLd hb fire).trans (by rw [w])⟩
  · obtain rfl := Option.some.inj (code.symm.trans Flow.code_2329)
    exact .inr ⟨.inl w,(fires_tcWaitSt_kind hb fire).trans (by rw [w])⟩
  · obtain rfl := Option.some.inj (code.symm.trans Flow.code_1010)
    exact .inr ⟨.inr w,(fires_tcWaitSt_kind hb fire).trans (by rw [w])⟩

private theorem det_go {ent L g d ev dn} {a b : Softmax.Site} (site : d.site=a)
    (rule : a = .ldS ∧ b = .waitLd ∨ a = .ldO ∧ b = .waitLdO ∨ a = .tmemSt ∧ b = .tmemWait ∨
      a = .stO ∧ b = .waitStO)
    (step : Softmax.Control.next ent L g d ev=some (some dn)) : dn.site=b := by
  obtain ⟨s,i,v⟩ := d
  change s=a at site
  subst site
  rcases rule with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    (simp only [Softmax.Control.next] at step; cases step; rfl)

/-- **After a Softmax load or store comes its wait.** -/
private theorem soft_next {i k pc e1} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,i)=some ⟨pc,k⟩) (hk : ∀ f, k≠.ub f) (g1 : X.get (g,i+1)=some e1)
    (n1 : ∀ f, e1.kind≠.ub f) (hpc : pc = 1265 ∨ pc = 2260 ∨ pc = 1009 ∨ pc = 2328) :
    (pc = 1265 → e1.pc = 1298) ∧ (pc = 2260 → e1.pc = 2261) ∧ (pc = 1009 → e1.pc = 1010) ∧
      (pc = 2328 → e1.pc = 2329) := by
  have rng : 574 < pc ∧ pc < 2331 := by omega
  obtain ⟨w,ent,d,n,hs,pcd⟩ := at_site hp hX he hk rng.1 rng.2
  have sites := site_ld d.site (by rw [← pcd]; exact hpc)
  have key (a s2 : Softmax.Site) (site : d.site = a) (ne : s2 ≠ .epilogue)
      (rule : a = .ldS ∧ s2 = .waitLd ∨ a = .ldO ∧ s2 = .waitLdO ∨ a = .tmemSt ∧ s2 = .tmemWait ∨
        a = .stO ∧ s2 = .waitStO) : e1.pc = s2.pc := by
    obtain ⟨d1,n',hs1,s1⟩ := soft_forward hp hX hf he hs g1 n1 (fun dn st => det_go site rule st) ne
    have p1 := event_pcU (fun g h => thread_sound hp h) hX g1 hs1 n1
    change e1.pc = d1.site.pc at p1
    rw [p1, s1]
  obtain ⟨s1,s2,s3,s4⟩ := sites
  refine ⟨fun h => ?_,fun h => ?_,fun h => ?_,fun h => ?_⟩
  · exact key _ _ (s1 (by rw [← pcd]; exact h)) (by decide) (.inl ⟨rfl,rfl⟩)
  · exact key _ _ (s2 (by rw [← pcd]; exact h)) (by decide) (.inr (.inl ⟨rfl,rfl⟩))
  · exact key _ _ (s3 (by rw [← pcd]; exact h)) (by decide) (.inr (.inr (.inl ⟨rfl,rfl⟩)))
  · exact key _ _ (s4 (by rw [← pcd]; exact h)) (by decide) (.inr (.inr (.inr ⟨rfl,rfl⟩)))


private theorem epi_load (s : Epilogue.Site) (h : s.pc = 2607) : s = .load := by
  cases s <;> first | rfl | (exfalso; revert h; decide) |
    (simp only [Epilogue.Site.pc, Epilogue.storePc] at h; omega)

/-- **After the epilogue's load comes its wait.** -/
private theorem epi_next {i k e1} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,i)=some ⟨2607,k⟩) (hk : ∀ f, k≠.ub f) (g1 : X.get (g,i+1)=some e1)
    (n1 : ∀ f, e1.kind≠.ub f) : e1.pc = 2608 := by
  obtain ⟨w,ent,d,n,t,ins,u,hs,-,-,pcd,-⟩ := epilogue_event_entry hp hX hf he hk
    (by show 2565 ≤ 2607; decide)
    (by show 2607 < 2853; decide)
  have site : d.site = .load := epi_load _ pcd.symm
  obtain ⟨dn,n',hs1,step⟩ := epi_forward hp hX hf hs he g1 n1
  have p1 := event_pcU (fun g h => thread_sound hp h) hX g1 hs1 n1
  change e1.pc = dn.site.pc at p1
  obtain ⟨s,r⟩ := d
  change s = .load at site
  subst site
  simp only [Epilogue.Control.next] at step
  cases step
  exact p1

/-- **A Tensor Memory load is followed by its `wait::ld`.** -/
public theorem ld_wait {i pc a v sh e1} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (nu : Frame.NoUbBefore X g (i+2))
    (hpc : pc = 1265 ∨ pc = 2260 ∨ pc = 2607) (he : X.get (g,i)=some ⟨pc,.tc (.ld a v sh)⟩)
    (g1 : X.get (g,i+1)=some e1) : ∃ pcw, e1 = ⟨pcw,.tc .waitLd⟩ := by
  have n1 := no_ub nu g1
  have hk : ∀ f, (Kind.tc (.ld a v sh)) ≠ .ub f := fun f => nofun
  have w : e1.pc = 1298 ∨ e1.pc = 2261 ∨ e1.pc = 2608 := by
    rcases hpc with h|h|h
    · obtain ⟨a1,-,-,-⟩ := soft_next hp hX hf he hk g1 n1 (by omega)
      exact .inl (a1 h)
    · obtain ⟨-,a2,-,-⟩ := soft_next hp hX hf he hk g1 n1 (by omega)
      exact .inr (.inl (a2 h))
    · subst h
      exact .inr (.inr (epi_next hp hX hf he hk g1 n1))
  rcases wait_kind hp hX g1 n1 (by omega) with ⟨-,eq⟩|⟨h,-⟩
  · exact ⟨_,eq⟩
  · omega

/-- **A Tensor Memory store is followed by its `wait::st`.** -/
public theorem st_wait {i pc a v sh e1} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (nu : Frame.NoUbBefore X g (i+2))
    (hpc : pc = 1009 ∨ pc = 2328) (he : X.get (g,i)=some ⟨pc,.tc (.st a v sh)⟩)
    (g1 : X.get (g,i+1)=some e1) : ∃ pcw, e1 = ⟨pcw,.tc .waitSt⟩ := by
  have n1 := no_ub nu g1
  have hk : ∀ f, (Kind.tc (.st a v sh)) ≠ .ub f := fun f => nofun
  have w : e1.pc = 1010 ∨ e1.pc = 2329 := by
    obtain ⟨-,-,a3,a4⟩ := soft_next hp hX hf he hk g1 n1 (by omega)
    rcases hpc with h|h
    · exact .inl (a3 h)
    · exact .inr (a4 h)
  rcases wait_kind hp hX g1 n1 (by omega) with ⟨h,-⟩|⟨-,eq⟩
  · omega
  · exact ⟨_,eq⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
