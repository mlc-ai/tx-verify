-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Machine
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Init
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.Ledger
import Lemmas.Flow.CtlStepsU
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow PTX.Proof Control

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {w : Value} {d : D}
  {t : TState} {e : Event} {o : Option TState} {ins : Instr}

theorem object_reg (hp : Pre Q L m) (ht : (code Q L g w).AtD d t) (i : Fin 12)
    (key : 613+i.val ∈ ctlLive d.site.pc) :
    let addr := L.sharedBase+MbarRow.initOffset i
    t.regs (613+i.val) = some (b32 addr) ∧ addr < 2^32 ∧ addr%8=0 := by
  obtain ⟨_,_,_,_,regs⟩ := ht
  have val : valueOf Q L g w d (613+i.val) = u32 (L.sharedBase+MbarRow.initOffset i) := by
    fin_cases i <;> rfl
  have table : ∀ i : Fin 12, MbarRow.initOffset i < sharedBytes ∧ MbarRow.initOffset i%8=0 := by
    decide +kernel
  have range := hp.sharedRange
  have align := hp.sharedAlignment
  obtain ⟨h,ha⟩ := table i
  have bound : L.sharedBase+MbarRow.initOffset i < 2^32 := by omega
  rw [u32,Nat.mod_eq_of_lt bound] at val
  exact ⟨holds_mem regs (mem_factsFrom_eq key val),bound,by omega⟩

theorem init_shape (hp : Pre Q L m) (ht : (code Q L g w).AtD d t) (i : Fin 12)
    (hs : d.site = .init i) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    e.kind = .mbInit (MbarRow.loc L g (MbarRow.initOffset i)) 1 := by
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (init_fetch i))
  have keys : ∀ i : Fin 12, 613+i.val ∈ ctlLive (Site.init i).pc := by decide +kernel
  obtain ⟨reg,bound,aligned⟩ := object_reg hp ht i (hs ▸ keys i)
  exact shape_mbInit (P := fun ev => ev.kind = _) hf reg bound (by decide) (by decide) aligned rfl

def readyIndex (b : Fin 3) : Fin 12 := ⟨2*b.val,by omega⟩

theorem ready_addr (b : Fin 3) : MbarRow.initOffset (readyIndex b) = Iface.kvReady b := by
  fin_cases b <;> rfl

theorem arrive_shape (hp : Pre Q L m) (ht : (code Q L g w).AtD d t) (b : Fin 3)
    (hs : d.site = .arr b) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    PTX.MbarRow.Arrive e (MbarRow.loc L g (Iface.kvReady b)) 65536 := by
  have fetch : kernel.code[(Site.arr b).pc]? = some ⟨some (177,false),
      .mbarArrive (613+2*b.val) 0 (.imm 65536) (.imm 1) false true .cta none⟩ := by
    fin_cases b
    · exact Flow.code_193
    · exact Flow.code_237
    · exact Flow.code_279
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans fetch)
  have keys : ∀ b : Fin 3, 613+2*b.val ∈ ctlLive (Site.arr b).pc := by decide +kernel
  obtain ⟨reg,bound,aligned⟩ := object_reg hp ht (readyIndex b) (hs ▸ keys b)
  rw [← ready_addr b]
  exact fires_arrive_exact (by rfl) (mbarLoc_b32 reg bound aligned) (by rfl) (by rfl) hf

end PTX.Kernels.InklingRelDecode.Proof.Prologue
