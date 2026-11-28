-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Gen.StepPrologue
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d
local notation "V" => valueOf Q L g w d

def copyMathPc (b : Fin 3) (j : Fin 4) :=
  pelPc b j + (if b=0 ∧ j=0 then 3 else 2)

private def maskPc (b : Fin 3) := copyMathPc b 0
private def src (b : Fin 3) := [693,714,736][b.val]!
private def dst (b : Fin 3) := [695,716,738][b.val]!

private theorem mask_fetch (b : Fin 3) : kernel.code[maskPc b]?=some ⟨none,.int ⟨.and,
    .int .b 32,false,[some (dst b)],[.reg (src b),.imm 1]⟩⟩ := by
  fin_cases b
  · exact Flow.code_206
  · exact Flow.code_247
  · exact Flow.code_289

private theorem mask (b : Fin 3) :
    SegU kernel Assumptions.all L g (maskPc b) (F (maskPc b)) (maskPc b+1) (F (maskPc b+1)) := by
  have keys : ∀ b, src b ∈ ctlLive (maskPc b) ∧
      (ctlLive (maskPc b+1)).all (fun r => decide (r=dst b ∨ r ∈ ctlLive (maskPc b))) := by
    decide +kernel
  apply Lib.scalarStepU (r := dst b) (v := V (dst b)) (mask_fetch b) rfl rfl
    (by fin_cases b <;> decide)
  · intro t u regs ev
    have val := holds_mem regs (mem_factsFrom (val := V) (keys b).1)
    have imm : readBits L g t 32 (.imm 1)=.ok (i32 1) := rfl
    simp only [execInt,DType.width,imm,bind,Except.bind,pure,Except.pure] at ev
    cases rd : readBits L g t 32 (.reg (src b)) <;> rw [rd] at ev <;> try contradiction
    rw [Lib.readBits_eq_pattern val rd] at ev
    have eq : V (dst b) = .bits 32 (Lib.word (V (src b)) &&& i32 1) := by
      have red : r32 (Lib.word d.broadcast)=Lib.word d.broadcast := by
        unfold Lib.word r32
        generalize d.broadcast.regBits.getD 0=z
        rw [show z=BitVec.ofNat 64 z.toNat by simp]
        nf_simp
      fin_cases b <;> change Value.bits 32 (r32 (Lib.word d.broadcast) &&& i32 1)=_ <;> rw [red]
      all_goals rfl
    rw [eq]
    exact (Except.ok.inj ev).symm
  · intro R regs
    exact Lib.writeLive (fun r hr => of_decide_eq_true (List.all_eq_true.mp (keys b).2 r hr)) regs

private def endAddr (b : Fin 3) := if b=0 then maskPc b+3 else maskPc b+4

private theorem base_span (b : Fin 3) :
    SegU kernel Assumptions.all L g (maskPc b+1) (F (maskPc b+1)) (endAddr b) (F (endAddr b)) := by
  fin_cases b
  · apply SegU.of_seg (n := 2); intro t ht; seg_fp ht using rfl
  all_goals apply SegU.of_seg (n := 3); intro t ht; seg_fp ht using rfl

theorem copy_math (b : Fin 3) (j : Fin 4) :
    SegU kernel Assumptions.all L g (copyMathPc b j) (F (copyMathPc b j))
      (ptcPc b j) (F (ptcPc b j)) := by
  by_cases first : j=0
  · subst j
    exact (mask b).comp ((base_span b).comp
      (cross ((by decide +kernel : ∀ b, crossCheck (endAddr b) (endAddr b) (ptcPc b 0)) b)))
  · apply SegU.comp (b := copyMathPc b j+1) (G := F (copyMathPc b j+1))
    · apply SegU.of_seg (n := 1)
      fin_cases b <;> fin_cases j <;> first | contradiction | (intro t ht; seg_fp ht using rfl)
    · exact cross ((by decide +kernel : ∀ b j, j≠0 →
        crossCheck (copyMathPc b j+1) (copyMathPc b j+1) (ptcPc b j)) b j first)

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
