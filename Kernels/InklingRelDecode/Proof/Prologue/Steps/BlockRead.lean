-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
def lbDst (b : Fin 3) (h : Fin 2) : Nat :=
  [681,701,723][b.val]! + 6*h.val
def lbAddr (b : Fin 3) (h : Fin 2) : Nat := 2071+2*b.val+h.val
def lbBar (b : Fin 3) (h : Fin 2) : Site := .pb b (if h.val = 0 then 1 else 3)

def lbOp (b : Fin 3) (h : Fin 2) : MemAccess :=
  {kind := .load,space := some .global,sem := .weak,elem := .int .b 32,
   addr := ⟨.reg (lbAddr b h) 64,0⟩,dsts := [some (lbDst b h)]}

theorem lb_fetch (b : Fin 3) (h : Fin 2) : kernel.code[(Site.lb b h).pc]? =
    some ⟨none,.mem (lbOp b h)⟩ := by
  fin_cases b <;> fin_cases h
  · exact Flow.code_197
  · exact Flow.code_220
  · exact Flow.code_241
  · exact Flow.code_262
  · exact Flow.code_283
  · exact Flow.code_304

theorem lb_checked : ∀ b h, lbDst b h ∉ ctlLive (Site.lb b h).pc ∧
    crossCheck (Site.lb b h).pc ((Site.lb b h).pc+1) (lbBar b h).pc := by decide +kernel

/-- The two block-table loads of each preload. Their payload selects the global
source row of a tensor copy; it never changes a control successor. -/
theorem step_block_read {Q L g w} (d : D) (b : Fin 3) (h : Fin 2) (hs : d.site = .lb b h) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.lb b h,a,x,c,won,bcast⟩
  let dn : D := {d with site := lbBar b h}
  obtain ⟨data,frame⟩ := lb_checked b h
  apply Code.step_loadU (C := code Q L g w) (d := d) (d' := dn) (r := lbDst b h)
    (lb_fetch b h) rfl rfl rfl rfl rfl rfl rfl rfl rfl _ trivial _ (cross frame)
  · intro l bs; fin_cases h <;> rfl
  · change lbDst b h ∉ (facts Q L g w d d.site.pc).map Prod.fst
    rw [facts,factsFrom_keys]
    exact data

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
