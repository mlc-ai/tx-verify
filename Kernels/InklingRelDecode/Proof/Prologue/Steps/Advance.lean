-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Machine
public import Lemmas.Flow.LandsU
public import Lemmas.Flow.Next

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

theorem straight {Q L g w d z op gd} (fetch : kernel.code[d.site.pc]? = some ⟨gd,op⟩)
    (nonloc : op.isLocal = false)
    (guardAt : Inv (g%L.block) d → Code.GuardTrue (facts Q L g w d d.site.pc) gd)
    (fire : ∀ {t ev u}, Fires d.site.pc (eventTmpl Assumptions.all L g t op) ev (some u) →
      u = PTX.next t)
    (go : ∀ ev, next Q L g d ev = some (some {d with site := z}))
    (sub : d.site.sub = 0) (sub' : z.sub = 0) (inv : Inv (g%L.block) {d with site := z})
    (seg : SegU kernel Assumptions.all L g (d.site.pc+1) (facts Q L g w d d.site.pc)
      z.pc (facts Q L g w d z.pc)) : (code Q L g w).StepAtU d where
  site := fun hi => ⟨_,fetch,nonloc,guardAt hi⟩
  step := by
    intro t ev u ins hat _ hc hf
    obtain rfl := Option.some.inj (hc.symm.trans fetch)
    obtain rfl := fire hf
    let dn := {d with site := z}
    obtain ⟨u,hr,hgood⟩ := Code.landsU (C := code Q L g w) (d := dn)
      (At.next (Code.at_of_atD hat sub rfl)) seg inv sub' rfl
    exact .inl (.inr ⟨dn,u,go ev,hr,hgood⟩)

theorem samePc {Q L g w d p q} (eq : p+1 = q) (live : (ctlLive q).isSublist (ctlLive p)) :
    SegU kernel Assumptions.all L g (p+1) (facts Q L g w d p) q (facts Q L g w d q) := by
  subst q
  intro t ht
  obtain ⟨hpc,hs,ha,hf,regs⟩ := ht
  exact .inl ⟨t,.refl,⟨hpc,hs,ha,hf,holds_factsFrom_mono regs
    (List.isSublist_iff_sublist.mp live).subset⟩⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
