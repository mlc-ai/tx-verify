-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.Table
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.Where
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Lemmas.Flow.GlueStep

@[expose] public section

/-! # What follows the P store's wait in the Softmax loop

After the wait for the rescale's store (pc 2329) a lane makes the mandatory rendezvous (pc 999)
and then the P store (pc 1009): the rescale's path is straight-line. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem soft_forward {i w ent d n ev e1 s2} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,i)=some ev) (hs : stateAt (thread Q L) X g i=some (some (softState w ent d n)))
    (get1 : X.get (g,i+1)=some e1) (clean1 : ∀ f, e1.kind≠.ub f)
    (det : ∀ dn, Softmax.Control.next ent L g d ev=some (some dn) → dn.site=s2)
    (ne : s2≠.epilogue) :
    ∃ dn n', stateAt (thread Q L) X g (i+1)=some (some (softState w ent dn n')) ∧ dn.site=s2 := by
  have hg := lt_of_get hX get1
  obtain ⟨⟨s1,n1⟩,hs1,_⟩ := good_stateU (fun g h => thread_sound hp h) hX get1
    (fun _ f h => clean1 f (congrArg Event.kind h)) (hf g hg (i+1))
  have get' : (X.tr g)[i]?=some ev := get
  have hs0 := hs1
  rw [stateAt_succ get',hs] at hs1
  have move : (thread Q L g).next (softState w ent d n) ev=some (some (s1,n1)) := hs1
  obtain ⟨step,rfl⟩ := Code.counted_next_some move
  obtain ⟨_,sub,rfl⟩ := Code.glue_inr_some step
  obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
  obtain ⟨dn,localStep,rfl⟩ := Code.glue_inl_some go
  have site := det dn localStep
  have off : dn.site≠.epilogue := by rw [site]; exact ne
  have none : epiExit dn=none := by simp [epiExit,off]
  refine ⟨dn,Code.bump cls n ev,?_,site⟩
  rw [hs0]
  simp only [Code.enter,none]

private theorem det_waitStO {ent L g d ev dn} (site : d.site=.waitStO)
    (step : Softmax.Control.next ent L g d ev=some (some dn)) : dn.site=.bar20 := by
  obtain ⟨s,i,v⟩ := d
  change s=.waitStO at site
  subst site
  simp only [Softmax.Control.next] at step
  cases step
  rfl

private theorem det_bar20 {ent L g d ev dn} (site : d.site=.bar20)
    (step : Softmax.Control.next ent L g d ev=some (some dn)) : dn.site=.tmemSt := by
  obtain ⟨s,i,v⟩ := d
  change s=.bar20 at site
  subst site
  simp only [Softmax.Control.next] at step
  cases step
  rfl

/-- **After the wait of the rescale's store come the mandatory rendezvous and the P store.** -/
public theorem after_waitStO (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {i k e1} (get : X.get (g,i)=some ⟨2329,k⟩) (clean : ∀ f, k≠.ub f)
    (g1 : X.get (g,i+1)=some e1) (n1 : ∀ f, e1.kind≠.ub f) :
    e1.pc=999 ∧ ∀ e2, X.get (g,i+2)=some e2 → (∀ f, e2.kind≠.ub f) → e2.pc=1009 := by
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<2329; decide)
    (by show 2329<2331; decide)
  have site : d.site=.waitStO := by
    have : (2329:Nat)=d.site.pc := pc
    revert this
    generalize d.site=s
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain ⟨d1,n',hs1,s1⟩ := soft_forward hp hX hf get hs g1 n1 (fun dn st => det_waitStO site st)
    (by decide)
  have p1 := event_pcU (fun g h => thread_sound hp h) hX g1 hs1 n1
  refine ⟨?_,fun e2 g2 n2 => ?_⟩
  · change e1.pc=d1.site.pc at p1
    rw [p1,s1]; rfl
  · obtain ⟨d2,n'',hs2,s2⟩ := soft_forward hp hX hf g1 hs1 g2 n2
      (fun dn st => det_bar20 s1 st) (by decide)
    have p2 := event_pcU (fun g h => thread_sound hp h) hX g2 hs2 n2
    change e2.pc=d2.site.pc at p2
    rw [p2,s2]; rfl

private theorem det_bar24 {ent L g d ev dn} (site : d.site=.bar24)
    (step : Softmax.Control.next ent L g d ev=some (some dn)) : dn.site=.stO := by
  obtain ⟨s,i,v⟩ := d
  change s=.bar24 at site
  subst site
  simp only [Softmax.Control.next] at step
  cases step
  rfl

private theorem det_stO {ent L g d ev dn} (site : d.site=.stO)
    (step : Softmax.Control.next ent L g d ev=some (some dn)) : dn.site=.waitStO := by
  obtain ⟨s,i,v⟩ := d
  change s=.stO at site
  subst site
  simp only [Softmax.Control.next] at step
  cases step
  rfl

/-- **After the optional rendezvous of a rescale come the store, its wait and the mandatory
rendezvous**: the next barrier-0 event of the lane is at pc 999. -/
public theorem after_visit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {i k} (get : X.get (g,i)=some ⟨2326,k⟩) (clean : ∀ f, k≠.ub f)
    (n1 : ∀ e1, X.get (g,i+1)=some e1 → ∀ f, e1.kind≠.ub f)
    (n2 : ∀ e2, X.get (g,i+2)=some e2 → ∀ f, e2.kind≠.ub f)
    (n3 : ∀ e3, X.get (g,i+3)=some e3 → ∀ f, e3.kind≠.ub f) :
    (∀ e1, X.get (g,i+1)=some e1 → e1.pc=2328) ∧ (∀ e2, X.get (g,i+2)=some e2 → e2.pc=2329) ∧
      ∀ e3, X.get (g,i+3)=some e3 → e3.pc=999 := by
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<2326; decide)
    (by show 2326<2331; decide)
  have site : d.site=.bar24 := by
    have : (2326:Nat)=d.site.pc := pc
    revert this
    generalize d.site=s
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  have step1 (e1) (g1 : X.get (g,i+1)=some e1) : ∃ d1 n1', stateAt (thread Q L) X g (i+1)=
      some (some (softState w ent d1 n1')) ∧ d1.site=.stO ∧ e1.pc=2328 := by
    obtain ⟨d1,n',hs1,s1⟩ := soft_forward hp hX hf get hs g1 (n1 e1 g1)
      (fun dn st => det_bar24 site st) (by decide)
    have p1 := event_pcU (fun g h => thread_sound hp h) hX g1 hs1 (n1 e1 g1)
    change e1.pc=d1.site.pc at p1
    exact ⟨d1,n',hs1,s1,by rw [p1,s1]; rfl⟩
  have step2 (e1 e2) (g1 : X.get (g,i+1)=some e1) (g2 : X.get (g,i+2)=some e2) :
      ∃ d2 n2', stateAt (thread Q L) X g (i+2)=some (some (softState w ent d2 n2')) ∧
        d2.site=.waitStO ∧ e2.pc=2329 := by
    obtain ⟨d1,n1',hs1,s1,-⟩ := step1 e1 g1
    obtain ⟨d2,n',hs2,s2⟩ := soft_forward hp hX hf g1 hs1 g2 (n2 e2 g2)
      (fun dn st => det_stO s1 st) (by decide)
    have p2 := event_pcU (fun g h => thread_sound hp h) hX g2 hs2 (n2 e2 g2)
    change e2.pc=d2.site.pc at p2
    exact ⟨d2,n',hs2,s2,by rw [p2,s2]; rfl⟩
  have back (a b : Nat) (hab : a ≤ b) (e) (h : X.get (g,b)=some e) : ∃ e', X.get (g,a)=some e' := by
    have h' : (X.tr g)[b]?=some e := h
    obtain ⟨hl,-⟩ := List.getElem?_eq_some_iff.mp h'
    exact ⟨_,List.getElem?_eq_getElem (show a<(X.tr g).length by omega)⟩
  refine ⟨fun e1 g1 => (step1 e1 g1).choose_spec.choose_spec.2.2, fun e2 g2 => ?_,
    fun e3 g3 => ?_⟩
  · obtain ⟨e1,g1⟩ := back (i+1) (i+2) (by omega) e2 g2
    exact (step2 e1 e2 g1 g2).choose_spec.choose_spec.2.2
  · obtain ⟨e2,g2⟩ := back (i+2) (i+3) (by omega) e3 g3
    obtain ⟨e1,g1⟩ := back (i+1) (i+3) (by omega) e3 g3
    obtain ⟨d2,n2',hs2,s2,-⟩ := step2 e1 e2 g1 g2
    obtain ⟨d3,n',hs3,s3⟩ := soft_forward hp hX hf g2 hs2 g3 (n3 e3 g3)
      (fun dn st => det_waitStO s2 st) (by decide)
    have p3 := event_pcU (fun g h => thread_sound hp h) hX g3 hs3 (n3 e3 g3)
    change e3.pc=d3.site.pc at p3
    rw [p3,s3]; rfl

end PTX.Kernels.InklingRelDecode.Proof.Export
