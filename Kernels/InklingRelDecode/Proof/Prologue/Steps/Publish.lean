-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Flow.Code.Part008
import Lemmas.Flow.Vector

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

private def publish (off : Int) (srcs : List Opnd) : MemAccess :=
  {kind := .store,space := some (.shared .cta),sem := .weak,elem := .int .b 32,
   vec := srcs.length,addr := ⟨.sharedSym 0,off⟩,srcs := srcs}

private theorem stored {L g t u ev p off srcs}
    (hr : (publish off srcs).rule = some .threadAccess)
    (hf : Fires p (eventTmpl Assumptions.all L g t (.mem (publish off srcs))) ev (some u)) :
    u = PTX.afterStore t srcs := by
  simp only [eventTmpl,memTmpl,hr] at hf
  change Fires p (accessTmpl Assumptions.all L g t (publish off srcs))
    ev (some u) at hf
  simp only [accessTmpl,publish] at hf
  repeat' split at hf
  all_goals first | exact Option.some.inj hf.2 | cases hf.2

private theorem fetch570 : kernel.code[570]? =
    some ⟨none,.mem (publish 213336 [.imm 16777730])⟩ :=
  Flow.code_570
private theorem fetch571 : kernel.code[571]? =
    some ⟨none,.mem (publish 212992 [.reg 493,.reg 487])⟩ :=
  Flow.code_571

theorem step_role_word {Q L g w} (d : D) (hs : d.site = .st8) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  refine ⟨fun _ => ⟨_,fetch570,rfl,trivial⟩,?_⟩
  intro t ev u ins hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans fetch570)
  change Fires 570 (eventTmpl Assumptions.all L g t (.mem (publish 213336 [.imm 16777730])))
    ev (some u) at hf
  have hu : u = PTX.afterStore t [.imm 16777730] := by
    apply @stored L g t u ev 570 213336 [.imm 16777730] (by decide)
    assumption
  rw [PTX.Flow.afterStore_last (by simp)] at hu
  rw [hu]
  obtain ⟨pc,sub,acc,fault,regs⟩ := hat
  have live : (ctlLive 571).isSublist (ctlLive 570) := by decide +kernel
  exact .inl (.inr ⟨⟨.st9 0,a,x,c,won,bcast⟩,_,rfl,.refl,.inl ⟨⟨congrArg (·+1) pc,rfl,acc,fault,
    holds_factsFrom_mono regs (List.isSublist_iff_sublist.mp live).subset⟩,trivial⟩⟩)

theorem step_pair_first {Q L g w} (d : D) (hs : d.site = .st9 0) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  refine ⟨fun _ => ⟨_,fetch571,rfl,trivial⟩,?_⟩
  intro t ev u ins hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans fetch571)
  obtain ⟨pc,sub,acc,fault,regs⟩ := hat
  change t.sub = 0 at sub
  change Fires 571 (eventTmpl Assumptions.all L g t (.mem (publish 212992 [.reg 493,.reg 487])))
    ev (some u) at hf
  have hu : u = PTX.afterStore t [.reg 493,.reg 487] := by
    apply @stored L g t u ev 571 212992 [.reg 493,.reg 487] (by decide)
    assumption
  rw [PTX.Flow.afterStore_mid (by simp [sub])] at hu
  rw [hu]
  exact .inl (.inr ⟨⟨.st9 1,a,x,c,won,bcast⟩,_,rfl,.refl,.inl ⟨⟨pc,congrArg (·+1) sub,
    acc,fault,regs⟩,trivial⟩⟩)

private theorem pair_segment {Q L g w d} :
    SegU kernel Assumptions.all L g 572 (facts Q L g w d 571) 573 (facts Q L g w d 573) := by
  apply Lib.sum_span (V := valueOf Q L g w d) (rs := ctlLive 571) (rs' := ctlLive 573)
    (r := 666) (dst := 792) (δ := 212992) false (by decide) Flow.code_572 (by decide +kernel)
    (by decide +kernel) _ (fun _ _ => ⟨rfl,rfl⟩) _
  · exact (Lib.addBase_bits L.sharedBase 212992).symm
  · intro r hr
    have chk : (ctlLive 573).all (fun r => decide (r = 792 ∨ r ∈ ctlLive 571)) := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp chk r hr)

/-- The second vector element advances past the store and sets the shared address for Softmax. -/
theorem step_pair_last {Q L g w} (d : D) (hs : d.site = .st9 1) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.st9 1,a,x,c,won,bcast⟩
  let dn : D := {d with site := .bar18}
  refine ⟨fun _ => ⟨_,fetch571,rfl,trivial⟩,?_⟩
  intro t ev u ins hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans fetch571)
  obtain ⟨pc,sub,acc,fault,regs⟩ := hat
  change t.sub = 1 at sub
  change Fires 571 (eventTmpl Assumptions.all L g t (.mem (publish 212992 [.reg 493,.reg 487])))
    ev (some u) at hf
  have hu : u = PTX.afterStore t [.reg 493,.reg 487] := by
    apply @stored L g t u ev 571 212992 [.reg 493,.reg 487] (by decide)
    assumption
  rw [PTX.Flow.afterStore_last (by simp [sub])] at hu
  rw [hu]
  obtain ⟨u',steps,good⟩ := Code.landsU (C := code Q L g w) (d := dn)
    (u := {t with pc := t.pc+1, sub := 0}) ⟨congrArg (·+1) pc,rfl,acc,fault,regs⟩
    (pair_segment (d := d)) trivial rfl rfl
  exact .inl (.inr ⟨dn,u',rfl,steps,good⟩)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
