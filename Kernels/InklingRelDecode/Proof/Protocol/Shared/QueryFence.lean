-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Reuse
import Kernels.InklingRelDecode.Proof.Common.Export.FirstBar
import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Prologue.Export.Published
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Flow.NthEv
import Lemmas.Kernel.Frame
import Lemmas.CtaBarrier.CtaBarrierRoundHistory
import Lemmas.Order.OrderBaseCausality

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

private abbrev phase (X : Execution) (g k : Nat) := ((X.tr g).take k).countP (Execution.isBarId 1)

private theorem phase_mono {X g i j} (h : i ≤ j) : phase X g i ≤ phase X g j :=
  (List.take_sublist_take_left h).countP_le

/-- A lane that passed a barrier-one rendezvous finds every lane of its CTA at the first
barrier-one rendezvous with the barrier-one count zero before it. -/
theorem first_arrival {Q L m X g h f} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (len : f<(X.tr h).length)
    (late : 1 ≤ ((X.tr h).take f).countP (Execution.isBarId 1))
    (cta : g/L.block=h/L.block) :
    ∃ u p, X.get (g,u)=some ⟨p,.bar 1 none .sync⟩ ∧
      ((X.tr g).take u).countP (Execution.isBarId 1)=0 := by
  obtain ⟨j,ev,get,hit,zero⟩ := CtaBarrier.countP_index (xs := (X.tr h).take f)
    (p := Execution.isBarId 1) (n := 0) late
  have jf : j<f := by
    by_contra bad
    have : ((X.tr h).take f).length ≤ j := by simp [List.length_take]; omega
    have := (List.getElem?_eq_some_iff.mp get).1
    omega
  have get' : X.get (h,j)=some ev := by
    change (X.tr h)[j]?=some ev
    rw [List.getElem?_take_of_lt jf] at get
    exact get
  obtain ⟨pc',kind⟩ := ev
  cases kind with
  | bar id cnt mode =>
    simp only [Execution.isBarId,beq_iff_eq] at hit
    subst hit
    obtain ⟨rfl,rfl⟩ := Lib.publication_kind hX hp.block get'
    have zero' : phase X h j=0 := by
      change ((X.tr h).take j).countP _=0
      rw [List.take_take,min_eq_left jf.le] at zero
      exact zero
    obtain ⟨u,p,get_g,order⟩ := member_sync hp hX get' (by omega) cta
    exact ⟨u,p,get_g,order.trans zero'⟩
  | _ => simp [Execution.isBarId] at hit

/-- **A query store precedes the issue of every MMA of its CTA** at every shared byte of the
CTA: its lane's proxy fence follows it before the releasing barrier, and the MMA lane has
crossed that barrier. -/
theorem query_proxy {Q L m X g k h f pc dst s acc mask a bs l} {i : Fin 8} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (store : X.get (g,k)=some ⟨526+6*i.val,.wr a bs⟩) (lane : g%L.block<128)
    (mma : X.get (h,f)=some ⟨pc,.tc (.mma dst s acc mask)⟩) (range : 2462≤pc ∧ pc≤2553)
    (cta : g/L.block=h/L.block) (space : l.space=.shared) (own : l.cta=g/L.block) :
    ProxyBefore L X (g,k) (h,f) l := by
  have hg := Frame.lt_of_get hX store
  have hh := Frame.lt_of_get hX mma
  have flen : f<(X.tr h).length := (List.getElem?_eq_some_iff.mp mma).1
  have late : 2 ≤ phase X h f :=
    Export.after_initialization hp hX mma (fun _ => nofun)
      (by simp only [Export.afterInit]; simp; omega)
  have zero : phase X g k=0 := Export.publication_store hp hX store (by
    obtain ⟨i,hi⟩ := i
    interval_cases i <;> rfl)
  obtain ⟨u,p,sync,pu⟩ := first_arrival (g := g) hp hX flen (by change 1 ≤ phase X h f; omega) cta
  have pu' : phase X g u=0 := pu
  have lo : p=573 := Export.first_barrier_pc hp hX sync pu lane
  subst lo
  obtain ⟨uf,four,fence,between⟩ := Prologue.Export.published_fence hp hX sync
  have ulen : u<(X.tr g).length := (List.getElem?_eq_some_iff.mp sync).1
  have ordered : k<u := by
    by_contra after
    have diff : k≠u := by
      rintro rfl
      have same := congrArg Event.pc (Option.some.inj (store.symm.trans sync))
      simp only at same
      have := i.isLt
      omega
    have mono : phase X g (u+1) ≤ phase X g k := phase_mono (by omega)
    have step : phase X g (u+1)=phase X g u+1 := by
      unfold phase
      rw [List.take_add_one,show (X.tr g)[u]?=_ from sync,List.countP_append]
      simp [Execution.isBarId]
    omega
  have before : k<uf := by
    by_contra inside
    have ne : k≠uf := by
      rintro rfl
      have same := congrArg Event.pc (Option.some.inj (store.symm.trans fence))
      simp only at same
      have := i.isLt
      omega
    obtain ⟨ev,gev,pcs⟩ := between k (by omega) ordered
    have same := congrArg Event.pc (Option.some.inj (store.symm.trans gev))
    simp only at same pcs
    have := i.isLt
    omega
  have flen' : uf<(X.tr g).length := (List.getElem?_eq_some_iff.mp fence).1
  have quiet : phase X g (uf+1)=0 := by
    have : phase X g (uf+1) ≤ phase X g u := phase_mono (by omega)
    omega
  refine ⟨(g,uf),_,_,⟨_,fence⟩,hg,⟨space,own⟩,⟨hg,hh,by simp only; rw [cta]⟩,?_,?_⟩
  · exact .single (.inl (po_of_not_access rfl before flen' (by rw [fence]; rfl)))
  · refine publication_handoff hp hX g h uf f ⟨hg,hh,cta⟩ flen ?_
    change phase X g (uf+1) < phase X h f
    omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
