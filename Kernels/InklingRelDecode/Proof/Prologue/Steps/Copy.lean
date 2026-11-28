-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockPointer
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
def ptcGuardReg (b : Fin 3) (j : Fin 3) := [54,64,73][b.val]! + j.val
def ptcOp (b : Fin 3) (j : Fin 3) : Op :=
  let base := [682,702,724][b.val]!
  .cpTensor false false (base+3*j.val) 0 (.reg 1949)
    [.reg (base + (if j.val=1 then 4 else 1)),.reg (base + (if j.val=2 then 7 else 2))]
    (613+2*b.val) 0 none .tile none
def ptcFrom (b j : Fin 3) : Site := .ptc b ⟨j.val,by omega⟩
def ptcDst (b : Fin 3) : Fin 3 → Site
  | 0 => .pb b 2
  | 1 => .lb b 1
  | 2 => .pb b 4

theorem ptcI_fetch (b j : Fin 3) : kernel.code[(ptcFrom b j).pc]? =
    some ⟨some (ptcGuardReg b j,false),ptcOp b j⟩ := by
  fin_cases b <;> fin_cases j
  · exact Flow.code_211
  · exact Flow.code_217
  · exact Flow.code_226
  · exact Flow.code_253
  · exact Flow.code_259
  · exact Flow.code_268
  · exact Flow.code_295
  · exact Flow.code_301
  · exact Flow.code_310

theorem ptcI_guard : ∀ b j, ptcGuardReg b j ∈ ctlLive (ptcFrom b j).pc := by decide +kernel

theorem ptcI_frame {Q L g w} (d : D) (b j : Fin 3) :
    SegU kernel Assumptions.all L g ((ptcFrom b j).pc+1) (facts Q L g w d (ptcFrom b j).pc)
      (ptcDst b j).pc (facts Q L g w d (ptcDst b j).pc) := by
  fin_cases b <;> fin_cases j
  · exact cross (by decide +kernel)
  · exact block_half_0
  · exact cross (by decide +kernel)
  · exact cross (by decide +kernel)
  · exact block_half_1
  · exact cross (by decide +kernel)
  · exact cross (by decide +kernel)
  · exact block_half_2
  · exact cross (by decide +kernel)

/-- The first three issues stay in the same preload block. -/
theorem step_copy_inner {Q L g w} (d : D) (b j : Fin 3) (hs : d.site = .ptc b ⟨j.val,by omega⟩) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨ptcFrom b j,a,x,c,won,bcast⟩
  have key := ptcI_guard b j
  apply straight (d := d) (z := ptcDst b j) (ptcI_fetch b j) rfl _
    (fun h => fires_next (by trivial) h) _ rfl _ _ (ptcI_frame d b j)
  · intro hi
    obtain ⟨eligible,elected⟩ := hi
    apply Code.guardTrue_factsFrom key
    have val : valueOf Q L g w d (ptcGuardReg b j) = .pred (decide (g%L.block%128<64) && won) := by
      fin_cases b <;> fin_cases j <;> rfl
    rw [val]
    simp [eligible,show won = true from elected]
  · intro e; fin_cases j <;> rfl
  · fin_cases j <;> rfl
  · fin_cases j <;> trivial

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
