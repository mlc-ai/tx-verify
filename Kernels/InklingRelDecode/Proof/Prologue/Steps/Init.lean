-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Advance
import Kernels.InklingRelDecode.Flow.Code.Part002
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
theorem init_fetch (i : Fin 12) : kernel.code[(Site.init i).pc]? =
    some ⟨some (26+i.val,false),.mbarInit (613+i.val) 0 (.imm 1)⟩ := by
  fin_cases i
  · exact Flow.code_134
  · exact Flow.code_138
  · exact Flow.code_142
  · exact Flow.code_146
  · exact Flow.code_150
  · exact Flow.code_154
  · exact Flow.code_158
  · exact Flow.code_162
  · exact Flow.code_166
  · exact Flow.code_170
  · exact Flow.code_174
  · exact Flow.code_178

theorem init_checked : ∀ i, (26+i.val ∈ ctlLive (Site.init i).pc) ∧
    (afterInit i).sub = 0 ∧ (Site.init i).pc+1 = (afterInit i).pc ∧
    (ctlLive (afterInit i).pc).isSublist (ctlLive (Site.init i).pc) := by decide +kernel

theorem step_init {Q L g w} (d : D) (i : Fin 12) (hs : d.site = .init i) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.init i,a,b,c,won,bcast⟩
  obtain ⟨predLive,sub,pc,live⟩ := init_checked i
  apply straight (d := d) (z := afterInit i) (init_fetch i) rfl _
    (fun h => fires_next (by trivial) h) (fun _ => rfl) rfl sub _
    (samePc pc live)
  · intro hi
    obtain ⟨warp,elect⟩ := hi
    apply Code.guardTrue_factsFrom predLive
    have val : valueOf Q L g w d (26+i.val) = .pred (decide (g%L.block<32) && won) := by
      fin_cases i <;> rfl
    rw [val]
    simp [warp,show won = true from elect]
  · unfold afterInit
    split <;> trivial

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
