-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.InklingRelDecode.Proof.Common.Staged.Alloc
import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.FollowControl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

/-- The startup's barrier-0 count at the event of a state, and that state's site. -/
private theorem startup_count {Q L m X g k pc ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,ev⟩)
    (low : pc<27) (nu : ∀ f, ev≠.ub f) :
    ∃ s : Startup.D, pc=s.site.pc ∧
      ((X.tr g).take k).countP (Execution.isBarId 0)=Startup.barriers s.site := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => nu f (congrArg Event.kind eq))
      ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs
    (fun f => nu f)
  obtain ⟨⟨site,tm,x,w⟩,n,rfl⟩ := (pos ▸ state_role s).startup low
  have lc := startup_counts hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
    (Frame.noUbBefore_of_get hX he)
  have eq := fcount hs (.bar 0)
  rw [cls_bar0] at eq
  exact ⟨⟨site,tm,x,w⟩,pos,eq.symm.trans lc.first⟩

/-- **The allocation's store is thread zero's second event, before its first barrier 0.** -/
public theorem base_store {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨11,.wr a bs⟩) :
    k=1 ∧ g%L.block=0 ∧
      ((X.tr g).take (k+1)).countP (Execution.isBarId 0)=0 := by
  obtain ⟨⟨site,tm,x,w⟩,pc,count⟩ := startup_count hp hX he (by decide) (by simp)
  have zero : ((X.tr g).take k).countP (Execution.isBarId 0)=0 := by
    rw [count]
    change 11=site.pc at pc
    cases site <;> first | rfl | contradiction | (rename_i r; cases r <;> contradiction)
  have z0 : c0 X g k = 0 := zero
  obtain ⟨hk,h0,-,-⟩ := early_write hp hX he (by omega)
  refine ⟨hk,h0,?_⟩
  have := c0_succ (X := X) (g := g) (k := k) he
  simp only [Execution.isBarId] at this
  exact this.trans zero

/-- **The base word's load follows exactly one barrier-0 event of its thread.** -/
public theorem base_load {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨13,.rd a bs⟩) :
    ((X.tr g).take k).countP (Execution.isBarId 0)=1 ∧
      ((X.tr g).take (k+1)).countP (Execution.isBarId 0)=1 := by
  obtain ⟨⟨site,tm,x,w⟩,pc,count⟩ := startup_count hp hX he (by decide) (by simp)
  have one : ((X.tr g).take k).countP (Execution.isBarId 0)=1 := by
    rw [count]
    change 13=site.pc at pc
    cases site <;> first | rfl | contradiction | (rename_i r; cases r <;> contradiction)
  have := c0_succ (X := X) (g := g) (k := k) he
  simp only [Execution.isBarId] at this
  exact ⟨one,this.trans one⟩

/-- **A proxy fence is after two barrier-0 events of its thread.** -/
public theorem fence_late {Q L m X f jf pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (f,jf)=some ⟨pc,.fenceProxy (.async (some (.shared .cta))) none⟩) :
    2≤((X.tr f).take jf).countP (Execution.isBarId 0) := by
  by_contra lt
  have lt' : c0 X f jf ≤ 1 := by unfold c0; omega
  obtain ⟨s,n,-,hs,-,hev⟩ := early_at hp hX he (by simp) lt'
  obtain ⟨site,tm,x,bw⟩ := s
  simp only at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl <;> simp only [Startup.Ev] at hev
  · cases hev
  · obtain ⟨_,_,h⟩ := hev; cases h
  · cases hev
  · obtain ⟨_,_,h,_⟩ := hev; cases h
  · cases hev

/-- **Barrier 0's first two instances order the CTA**: an event of `g` with at most one
barrier-0 event up to and including it happens before an event of `h` of the same CTA that
follows more of them. -/
public theorem startup_before {Q L m X g h e f} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hsame : SameCta L g h)
    (hf : f<(X.tr h).length)
    (hlt : ((X.tr g).take (e+1)).countP (Execution.isBarId 0) <
      ((X.tr h).take f).countP (Execution.isBarId 0))
    (hle : ((X.tr g).take (e+1)).countP (Execution.isBarId 0)≤1) :
    baseCausality L X (g,e) (h,f) :=
  bar0_before hp hX hsame hf hlt hle

end PTX.Kernels.InklingRelDecode.Proof.Export
