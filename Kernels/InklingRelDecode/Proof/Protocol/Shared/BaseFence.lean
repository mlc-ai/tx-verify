-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.QueryFence
import Kernels.InklingRelDecode.Proof.Common.Export.BaseWord
import Kernels.InklingRelDecode.Proof.Common.Export.FirstBar
import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Prologue.Export.Published
import Lemmas.Kernel.Frame
import Kernels.InklingRelDecode.Proof.Prologue.Export.PreloadSync
import Kernels.InklingRelDecode.Proof.Lib.TensorSites
import Lemmas.Order.OrderWaits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

/-- **A lane past the first release has a fence of its CTA before it**: the proxy fence of the
CTA's first thread (`pc 569`, after two barrier-zero events) reaches every event after a
barrier-one rendezvous through barrier one's first instance. -/
theorem fence_after_release {Q L m X h f} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hh : h<L.threads)
    (flen : f<(X.tr h).length)
    (late : 1 ≤ ((X.tr h).take f).countP (Execution.isBarId 1)) :
    ∃ g0 uf, g0/L.block=h/L.block ∧ g0<L.threads ∧
      X.get (g0,uf)=some ⟨569,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      2 ≤ ((X.tr g0).take uf).countP (Execution.isBarId 0) ∧
      baseCausality L X (g0,uf) (h,f) := by
  have hb : 0<L.block := by have := hp.block; omega
  obtain ⟨g0,hg0⟩ : ∃ g0, g0=h/L.block*L.block := ⟨_,rfl⟩
  have cta : g0/L.block=h/L.block := by rw [hg0]; exact Nat.mul_div_cancel _ hb
  have hg : g0<L.threads := hg0 ▸ lt_of_le_of_lt (Nat.div_mul_le_self h L.block) hh
  obtain ⟨u,p,sync,pu⟩ := first_arrival (g := g0) hp hX flen late cta
  have lo : p=573 := Export.first_barrier_pc hp hX sync pu (by
    rw [hg0,Nat.mul_mod_left]; omega)
  subst lo
  obtain ⟨uf,four,fence,between⟩ := Prologue.Export.published_fence hp hX sync
  have quiet : ((X.tr g0).take (uf+1)).countP (Execution.isBarId 1)=0 := by
    have : ((X.tr g0).take (uf+1)).countP (Execution.isBarId 1) ≤
        ((X.tr g0).take u).countP (Execution.isBarId 1) :=
      (List.take_sublist_take_left (by omega)).countP_le
    omega
  refine ⟨g0,uf,cta,hg,fence,Export.fence_late hp hX fence,?_⟩
  exact publication_handoff hp hX g0 h uf f ⟨hg,hh,cta⟩ flen (by
    change ((X.tr g0).take (uf+1)).countP (Execution.isBarId 1) <
      ((X.tr h).take f).countP (Execution.isBarId 1)
    omega)

/-- **Every tensor-copy issue has a proxy fence of its CTA before it**, after two barrier-zero
events of the fence's thread: the preload's own fence, or the first thread's fence the loader
reaches through barrier one. -/
theorem copy_fence {Q L m X h j pc a sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (h,j)=some ⟨pc,.tensorIssue a sp⟩) :
    ∃ f jf, f/L.block=h/L.block ∧ f<L.threads ∧
      (∃ pcf, X.get (f,jf)=some ⟨pcf,.fenceProxy (.async (some (.shared .cta))) none⟩) ∧
      2 ≤ ((X.tr f).take jf).countP (Execution.isBarId 0) ∧ baseCausality L X (f,jf) (h,j) := by
  have hh := Frame.lt_of_get hX he
  have jlen : j<(X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  rcases Lib.tensor_issue_site hX he with pre|wk
  · obtain ⟨uf,lt,fence⟩ := Prologue.Export.preload_fence hp hX he (by simp) (by
      change 180<pc
      simp only [Lib.preloadPcs,List.mem_cons,List.not_mem_nil,or_false] at pre
      omega) (by
      change pc<574
      simp only [Lib.preloadPcs,List.mem_cons,List.not_mem_nil,or_false] at pre
      omega)
    refine ⟨h,uf,rfl,hh,⟨_,fence⟩,Export.fence_late hp hX fence,?_⟩
    exact .single (.inl (po_of_source_not_access rfl lt jlen (by rw [fence]; rfl)))
  · have range : 2374 ≤ pc ∧ pc ≤ 2412 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at wk
      omega
    have late : 2 ≤ ((X.tr h).take j).countP (Execution.isBarId 1) :=
      Export.after_initialization hp hX he (by simp) (by
        simp only [Export.afterInit]
        simp
        omega)
    obtain ⟨g0,uf,cta,hg,fence,two,order⟩ := fence_after_release hp hX hh jlen (by omega)
    exact ⟨g0,uf,cta,hg,⟨_,fence⟩,two,order⟩

/-- **An early thread access precedes an event the CTA's fence reaches**: an access of a thread
with at most one barrier-zero event up to it, before the issue of a copy, at a shared byte of
its CTA. -/
theorem early_proxy {Q L m X g k h j l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g<L.threads) (hh : h<L.threads)
    (cta : g/L.block=h/L.block) (early : ((X.tr g).take (k+1)).countP (Execution.isBarId 0) ≤ 1)
    {f jf} (fcta : f/L.block=h/L.block) (flt : f<L.threads)
    (fence : ∃ pcf, X.get (f,jf)=some ⟨pcf,.fenceProxy (.async (some (.shared .cta))) none⟩)
    (two : 2 ≤ ((X.tr f).take jf).countP (Execution.isBarId 0))
    (order : baseCausality L X (f,jf) (h,j))
    (space : l.space=.shared) (own : l.cta=g/L.block) (flen : jf<(X.tr f).length) :
    ProxyBefore L X (g,k) (h,j) l := by
  obtain ⟨pcf,get⟩ := fence
  refine ⟨(f,jf),_,_,⟨pcf,get⟩,flt,⟨space,?_⟩,⟨flt,hh,by simp only; rw [fcta]⟩,?_,order⟩
  · simp only
    rw [own,cta,fcta]
  · exact Export.startup_before hp hX ⟨hg,flt,cta.trans fcta.symm⟩ flen (by omega) early

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
