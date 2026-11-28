-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Softmax
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEvent
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Softmax.Shape
import Lemmas.Protocol.MbarRowSource

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Control MbarRow PTX.MbarRow

private theorem sites (s : Softmax.Site) :
    (s.pc = 1013 → s = .arrive) ∧ (s.pc = 1257 → s = .waitS) ∧ (s.pc = 2239 → s = .waitO) := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

private theorem source {L m X g k ev l} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k) = some ev) (atPc : SoftmaxAt L g ev.pc) (hm : Frame.MbarOf ev l) :
    ev.pc = 1013 ∨ ev.pc = 1257 ∨ ev.pc = 2239 := by
  rcases atPc.2 with ⟨lo,hi⟩ | ⟨lo,hi⟩
  · obtain ⟨s,hs,hpc,_⟩ := region_source softmax_sites hX he hm lo hi
    have h : ∀ x ∈ softmaxSites, x.pc = 1013 ∨ x.pc = 1257 ∨ x.pc = 2239 := by decide
    exact hpc ▸ h s hs
  · obtain ⟨_,h,_⟩ := region_source softmax_sites_1 hX he hm lo hi
    cases h

/-- **A Softmax poll that occurs** (in the trace, or the lane's next event) polls the object
its round selects, at the parity its round selects. -/
public theorem wait_occ {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k ev)
    (nu : ∀ f, ev.kind ≠ .ub f) (pcs : ev.pc = 1257 ∨ ev.pc = 2239) :
    (ev.pc = 1257 ∧ ∃ ok, ev.kind = .wait (loc L g (Iface.sReady (slot2 (roundAt X g k 1257))))
        (roundAt X g k 1257 / 2 % 2) ok true .cta) ∨
    (ev.pc = 2239 ∧ ∃ ok, ev.kind = .wait (loc L g Iface.oDone) (roundAt X g k 2239 % 2) ok true
        .cta) := by
  obtain ⟨ent,⟨s,i,v⟩,t,ins,u,ht,inv,eq,hc,fire,ref⟩ :=
    softmax_occ hp hX hf he nu (by omega) (by omega)
  have shape := object_shape hp ht hc fire
  change ev.pc = s.pc at eq
  obtain ⟨ledger,ow⟩ := ref
  rcases pcs with h|h
  · obtain rfl := (sites s).2.1 (eq ▸ h)
    have ct := congrArg Cnt.s ledger
    change roundAt X g k 1257 = i at ct
    obtain ⟨ok,hk⟩ := shape
    exact .inl ⟨h,ok,ct ▸ hk⟩
  · obtain rfl := (sites s).2.2 (eq ▸ h)
    have ct := congrArg Cnt.o ledger
    change roundAt X g k 2239 = i-1 at ct
    have pos : 0 < i := ow rfl
    have par : roundAt X g k 2239 % 2 = (i+1)%2 := by omega
    obtain ⟨ok,hk⟩ := shape
    exact .inr ⟨h,ok,par ▸ hk⟩

public theorem mbarRow {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : MbarRow.Softmax Q L X := by
  intro g k ev l _ he hat hm
  have pcs := source hX he hat hm
  have nu : ∀ f, ev.kind ≠ .ub f := by
    have obj := objectKind hm
    intro f h; rw [h] at obj; exact obj.elim
  rcases pcs with h|h|h
  · obtain ⟨ent,⟨s,i,v⟩,t,ins,u,ht,inv,eq,hc,fire,ref⟩ :=
      softmax_event hp hX hf he nu (by omega) (by omega)
    have shape := object_shape hp ht hc fire
    change ev.pc = s.pc at eq
    obtain ⟨ledger,ow⟩ := ref
    obtain rfl := (sites s).1 (eq ▸ h)
    have lead := inv.lead rfl
    have short := hat.1
    have zero : g%L.block = 0 := by omega
    have ct := congrArg Cnt.p ledger
    change _ = (if g%L.block%128=0 then i else 0) at ct
    simp only [lead,↓reduceIte] at ct
    have arr : PTX.MbarRow.Arrive ev _ 0 := shape
    have hl : l = loc L g (Iface.pReady (slot2 i)) := by
      obtain ⟨pc,kd⟩ := ev
      change kd = _ at arr
      cases arr
      exact hm
    subst l
    exact .pArrive h zero (ct ▸ rfl) arr
  · rcases wait_occ hp hX hf (.inl he) nu (.inl h) with ⟨_,ok,hk⟩ | ⟨h',_⟩
    · obtain ⟨pc,kd⟩ := ev
      change kd = _ at hk
      cases hk
      subst hm
      exact .sWait h rfl ⟨ok,rfl⟩
    · omega
  · rcases wait_occ hp hX hf (.inl he) nu (.inr h) with ⟨h',_⟩ | ⟨_,ok,hk⟩
    · omega
    · obtain ⟨pc,kd⟩ := ev
      change kd = _ at hk
      cases hk
      subst hm
      exact .oWait h rfl ⟨ok,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
