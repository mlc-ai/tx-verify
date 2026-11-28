-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Prologue
public import Kernels.InklingRelDecode.Proof.Common.Export.Publication
public import Lemmas.Kernel.Progress.NextEv
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.Export.Publisher
import Kernels.InklingRelDecode.Proof.Prologue.Export.Init
import Kernels.InklingRelDecode.Proof.Protocol.Warp.Leader
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Reuse
import Lemmas.Kernel.Safety.HandoffPhased
import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
open PTX PTX.Flow PTX.Frame PTX.Sched

/-- A lane that passed publication has a first publication event from every
data warp in its CTA, even if a worker wait is still pending. -/
theorem data_published {Q L m X g y} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (phase : 2≤(X.tr g).countP (Execution.isBarId 1)) (cta : y/L.block=g/L.block)
    (low : y%L.block<128) : ∃ v, X.get (y,v)=some ⟨573,.bar 1 none .sync⟩ ∧
      ((X.tr y).take v).countP (Execution.isBarId 1)=0 := by
  have allBar : 2≤((X.tr g).take (X.tr g).length).countP (Execution.isBarId 1) := by simpa
  obtain ⟨a,pc,cnt,md,_,bar,zero⟩ := nth_bar (q := 0) (by omega : 0+1≤_ )
    (X := X) (g := g) (id := 1) (f := (X.tr g).length)
  obtain ⟨b,_,_,_,bl,_,one⟩ := nth_bar (q := 1) allBar
  have ab : a<b := by
    by_contra! rev
    have mono := countP_take_mono (Execution.isBarId 1) (X.tr g) rev
    omega
  obtain ⟨rfl,rfl⟩ := Lib.publication_kind hX hp.block bar
  obtain ⟨v,p,sync,ord⟩ := Shared.member_sync hp hX bar (by omega) cta
  obtain rfl := Export.first_data_sync hp hX sync low (ord.trans zero)
  exact ⟨v,sync,ord.trans zero⟩

/-- Passing the first CTA publication barrier exposes all twelve initializer events
in the elected prologue lane, even if the observer's next event has not fired. -/
theorem init_present {Q L m X g} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g<L.threads) (phase : 2≤(X.tr g).countP (Execution.isBarId 1)) (j : Fin 12) :
    ∃ y u, X.get (y,u)=some ⟨134+4*j.val,.mbInit (MbarRow.loc L g (MbarRow.initOffset j)) 1⟩ ∧
      y/L.block=g/L.block ∧ ((X.tr y).take (u+1)).countP (Execution.isBarId 1)=0 := by
  let c := g/L.block
  have hc : c<L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  have w := KV.leader_warp (X := X) hp hc (by decide : 0<8)
  have w0 := w.2.2
  obtain ⟨v,sync,zero⟩ := data_published hp hX phase w.2.1 (by omega)
  obtain ⟨u,uv,init⟩ := Prologue.Export.initialized hp hX sync (by simp) (by decide) (by decide)
    (by omega) (Warp.leader_wins hp hX hc (by decide : 0<8)) j
  refine ⟨_,u,by simpa only [MbarRow.loc,w.2.1] using init,w.2.1,?_⟩
  have bound := countP_take_mono (Execution.isBarId 1) (X.tr (KV.leader L X c 0)) uv
  rw [zero] at bound
  exact Nat.le_zero.mp bound

/-- Every post-publication user sees the initializer through barrier 1 in base causality. -/
theorem published_at {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some e)
    (nu : ∀ f, e.kind≠.ub f) (site : Export.afterInit e.pc) (j : Fin 12) :
    ∃ v, X.MbInit v (MbarRow.loc L g (MbarRow.initOffset j)) 1 ∧
      baseCausality L X v (g,k) := by
  have hg := lt_of_get hX he
  have phase := Export.after_initialization hp hX he nu site
  have full := (List.take_sublist k (X.tr g)).countP_le (p := Execution.isBarId 1)
  obtain ⟨y,u,get,cta,zero⟩ := init_present hp hX hg (phase.trans full) j
  refine ⟨(y,u),⟨_,get⟩,Shared.publication_handoff hp hX y g u k
    ⟨lt_of_get hX get,hg,cta⟩ (List.getElem?_eq_some_iff.mp he).1 ?_⟩
  dsimp only
  omega

theorem next_published {Q L m X g pc l q ok ac sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨pc,.wait l q ok ac sc⟩)
    (site : Export.afterInit pc) (j : Fin 12) :
    X.objects (MbarRow.loc L g (MbarRow.initOffset j)) ≠ [] := by
  have hg := hn.lt
  obtain ⟨Y,hY,pref,get⟩ := hn
  have phase := Export.after_initialization hp hY get (by simp) site
  rw [pref] at phase
  obtain ⟨y,u,get,_,_⟩ := init_present hp hX hg phase j
  obtain ⟨i,r,rec,_⟩ := init_record_of_objectsOk hX.tma.2.2.1 (e := (y,u)) ⟨_,get⟩
  intro nil
  simp [nil] at rec

/-- An event after initialization exposes every initializer record of its CTA. -/
theorem event_published {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some e)
    (nu : ∀ f, e.kind≠.ub f) (site : Export.afterInit e.pc) (j : Fin 12) :
    X.objects (MbarRow.loc L g (MbarRow.initOffset j)) ≠ [] := by
  have phase := Export.after_initialization hp hX he nu site
  have full := (List.take_sublist k (X.tr g)).countP_le (p := Execution.isBarId 1)
  obtain ⟨y,u,get,_,_⟩ := init_present hp hX (lt_of_get hX he) (phase.trans full) j
  obtain ⟨i,r,rec,_⟩ := init_record_of_objectsOk hX.tma.2.2.1 (e := (y,u)) ⟨_,get⟩
  intro nil
  simp [nil] at rec

/-- An event that occurs (in the trace, or the lane's next) after initialization exposes every
initializer record of its CTA. -/
theorem occ_published {Q L m X g k} {e : Event} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k e)
    (nu : ∀ f, e.kind≠.ub f) (site : Export.afterInit e.pc) (j : Fin 12) :
    X.objects (MbarRow.loc L g (MbarRow.initOffset j)) ≠ [] := by
  have phase := Export.after_initialization_occ hp hX hf he nu site
  have full := (List.take_sublist k (X.tr g)).countP_le (p := Execution.isBarId 1)
  obtain ⟨y,u,get,_,_⟩ := init_present hp hX (he.lt hX) (phase.trans full) j
  obtain ⟨i,r,rec,_⟩ := init_record_of_objectsOk hX.tma.2.2.1 (e := (y,u)) ⟨_,get⟩
  intro nil
  simp [nil] at rec

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
