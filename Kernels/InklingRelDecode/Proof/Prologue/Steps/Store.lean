-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Machine
import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryAddr
import Kernels.InklingRelDecode.Flow.Code.Part008
import Lemmas.Flow.EventCont
import Lemmas.Flow.CtlStepsU
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

def srcs (i : Fin 8) : List Opnd :=
  [.reg (747+5*i.val),.reg (748+5*i.val),.reg (749+5*i.val),.reg (750+5*i.val)]
def storeOp (i : Fin 8) : Op := .mem
  {kind := .store,space := some (.shared .cta),sem := .weak,elem := .int .b 32,vec := 4,
   addr := ⟨.reg (746+5*i.val) 32,0⟩,srcs := srcs i}

theorem fetchQueryStore : ∀ i, kernel.code[(Site.stq i 0).pc]? = some ⟨none,storeOp i⟩ := by
  intro i
  fin_cases i <;> first | exact Flow.code_526 | exact Flow.code_532 | exact Flow.code_538 |
    exact Flow.code_544 | exact Flow.code_550 | exact Flow.code_556 | exact Flow.code_562 |
    exact Flow.code_568

private theorem write {L g t u ev p} (i : Fin 8)
    (hf : Fires p (eventTmpl Assumptions.all L g t (storeOp i)) ev (some u)) :
    u = PTX.afterStore t (srcs i) :=
  (fires_stv_after (sp := .shared .cta) (ty := .int .b 32) (bw := 32) (base := 746+5*i.val)
    (off := 0) (srcs := srcs i) (lsp := .shared) (by rfl) (by rfl) hf).1

theorem step_store_mid {Q L g w} (d : D) (i : Fin 8) (j : Fin 4)
    (hs : d.site = .stq i j) (mid : j.val+1 < 4) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let z : Fin 4 := ⟨j.val+1,mid⟩
  let dn : D := ⟨.stq i z,a,b,c,won,bcast⟩
  constructor
  · exact fun _ => ⟨_,fetchQueryStore i,rfl,trivial⟩
  · intro t ev u ins hat _ hi fire
    obtain rfl := Option.some.inj (hi.symm.trans (fetchQueryStore i))
    have hu := write i fire
    obtain ⟨hp,hsub,ha,hf,hr⟩ := hat
    change t.sub = j.val at hsub
    have more : t.sub+1 < (srcs i).length := hsub ▸ mid
    rw [PTX.Flow.afterStore_mid more] at hu
    subst u
    refine .inl (.inr ⟨dn,{t with sub := t.sub+1},?_,.refl,.inl ⟨⟨hp,?_,ha,hf,hr⟩,trivial⟩⟩)
    · change some (some (D.mk (afterStore i j) a b c won bcast)) = _
      simp only [afterStore,dite_eq_left mid]
      rfl
    · exact congrArg (·+1) hsub

private def afterPc (i : Fin 8) : Nat := if i.val < 7 then 526+6*(i.val+1) else 569

theorem step_store_last {Q L g w} (d : D) (i : Fin 8) (hs : d.site = .stq i 3) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.stq i 3,a,b,c,won,bcast⟩
  let dn : D := {d with site := afterStore i 3}
  have subAll : ∀ i, (afterStore i 3).sub = 0 := by decide +kernel
  have pc : dn.site.pc = afterPc i := by
    change (afterStore i 3).pc = afterPc i
    revert i; decide +kernel
  have sub : dn.site.sub = 0 := subAll i
  have inv : Inv (g%L.block) dn := by
    dsimp only [dn,afterStore]
    split_ifs <;> trivial
  constructor
  · exact fun _ => ⟨_,fetchQueryStore i,rfl,trivial⟩
  · intro t ev u ins hat _ hi fire
    obtain rfl := Option.some.inj (hi.symm.trans (fetchQueryStore i))
    have hu := write i fire
    obtain ⟨hp,hsub,ha,hf,hr⟩ := hat
    change t.sub = 3 at hsub
    have last : ¬ t.sub+1 < (srcs i).length := hsub ▸ Nat.lt_irrefl 4
    rw [PTX.Flow.afterStore_last last] at hu
    subst u
    suffices reach : ∃ u', Relation.ReflTransGen (Tau kernel Assumptions.all L g)
        {t with pc := t.pc+1, sub := 0} u' ∧ (code Q L g w).GoodU (some dn) u' by
      obtain ⟨u',hrun,hgood⟩ := reach
      exact .inl (.inr ⟨dn,u',rfl,hrun,hgood⟩)
    apply Code.landsU (C := code Q L g w) (d := dn) (u := {t with pc := t.pc+1, sub := 0})
      (a := d.site.pc+1) (F := facts Q L g w d d.site.pc)
      ⟨congrArg (·+1) hp,rfl,ha,hf,hr⟩ _ inv sub rfl
    change SegU _ _ _ _ (d.site.pc+1) _ dn.site.pc (facts Q L g w dn dn.site.pc)
    rw [pc]
    by_cases h : i.val < 7
    · change SegU _ _ _ _ (526+6*i.val+1) (facts Q L g w d (526+6*i.val))
        (afterPc i) (facts Q L g w d (afterPc i))
      rw [show afterPc i = 532+6*i.val by simp [afterPc,h]; omega,
        show 526+6*i.val+1 = 527+6*i.val by omega]
      exact next_store_addr ⟨i.val,h⟩
    · have eq : i = 7 := Fin.ext (by change i.val=7; omega)
      subst i
      exact cross (by decide +kernel : crossCheck 568 569 569)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
