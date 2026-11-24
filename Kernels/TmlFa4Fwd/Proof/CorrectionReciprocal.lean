-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStats
public import Lemmas.Flow.Recip
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

def reciprocalPc (stage : Fin 2) : Nat := 8469 + 296 * stage.val

def reciprocalPred (stage : Fin 2) : Nat := 739 + stage.val

def reciprocalInput (stage : Fin 2) : Nat := 6514 + 280 * stage.val

def reciprocalReg (stage : Fin 2) : Nat := reciprocalInput stage + 1

private theorem compareCode (stage : Fin 2) :
    kernel.code[reciprocalPc stage]? = some ⟨none, .float
      { op := .setp (.ord .ne) none, ty := ⟨.f32, 1⟩, dsts := [some (reciprocalPred stage)],
        srcs := [.reg (statsReg stage .sum), .f32imm 0] }⟩ := by
  fin_cases stage
  · exact Flow.code_8469
  · exact Flow.code_8765

private theorem selectCode (stage : Fin 2) :
    kernel.code[reciprocalPc stage + 1]? = some ⟨none, .int
      ⟨.selp, .float .f32, false, [some (reciprocalInput stage)],
        [.reg (statsReg stage .sum), .f32imm 1065353216, .reg (reciprocalPred stage)]⟩⟩ := by
  fin_cases stage
  · exact Flow.code_8470
  · exact Flow.code_8766

private def reciprocalOp (stage : Fin 2) : Op :=
  .float { op := .rcp, ty := ⟨.f32, 1⟩, mode := .approx, ftz := true,
           dsts := [some (reciprocalReg stage)], srcs := [.reg (reciprocalInput stage)] }

private theorem recipCode (stage : Fin 2) :
    kernel.code[reciprocalPc stage + 2]? = some ⟨none, reciprocalOp stage⟩ := by
  fin_cases stage
  · exact Flow.code_8471
  · exact Flow.code_8767

private theorem noSelp : NoSelp Assumptions.numeric := by
  intro d a p L g t asm hm
  simp only [Assumptions.numeric, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem execRecip {l : Launch} {g : Nat} {t : TState} (stage : Fin 2)
    (hPc : t.pc = reciprocalPc stage + 2) {e : Exec TState}
    (hExec : execApproxExact t (reciprocalOp stage) = some e) :
    execLocalA Assumptions.numeric l g t (reciprocalOp stage) = e := by
  have hSeg : t.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; fin_cases stage <;> decide
  rw [(Assumptions.numeric_segSites.pc hSeg).at rfl |>.exec]
  have hIdeal : Assumptions.idealArith.localRule l g t (reciprocalOp stage) = none :=
    idealReal_localRule_none (by simp [FloatForm.ofOp, reciprocalOp])
  have hApprox : Assumptions.approx.localRule l g t (reciprocalOp stage) = some e :=
    (approxExact_localRule_of (by rfl) (by
      change (.rcp .f32 : ApproxForm) ∈ Assumptions.approxForms
      decide)).trans hExec
  simp only [execLocalRule, Assumptions.numeric, List.findSome?, hIdeal, hApprox]

/-- At either final normalization, only a zero sum substitutes one before taking its reciprocal.
The decoded instructions preserve the caller frame. -/
theorem finalReciprocalWithPredicateLocal {l : Launch} {g : Nat} {t : TState}
    (stage : Fin 2) {value : Value} {sum : ℝ} {F : List (Nat × Value)}
    (ht : At t (reciprocalPc stage) F)
    (hReg : t.regs (statsReg stage .sum) = some value)
    (hVal : valFloat .f32 value = .ok sum)
    (hFrame : ∀ pair ∈ F, pair.1 ∉
      [reciprocalPred stage, reciprocalInput stage, reciprocalReg stage]) :
    ∃ u, At u (reciprocalPc stage + 3)
        ((reciprocalReg stage, fl (1 / (if sum = 0 then 1 else sum))) ::
          (reciprocalPred stage, .pred (decide (sum ≠ 0))) :: F) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  let u := recipState t (reciprocalPred stage) (reciprocalInput stage) (reciprocalReg stage)
    value sum
  have hs : t.pc ∉ Assumptions.swExp2Sites := by rw [ht.1]; fin_cases stage <;> decide
  have hs1 : t.pc + 1 ∉ Assumptions.swExp2Sites := by rw [ht.1]; fin_cases stage <;> decide
  have hIdeal : IdealAt Assumptions.numeric (.setp .f32) l g t :=
    idealAt_head (by decide) (Assumptions.numeric_segSites.pc hs).tail
  have hRun : run kernel Assumptions.numeric l g 3 t = some u := by
    apply recip_run (ht.1.symm ▸ compareCode stage)
    · rw [ht.1]
      exact selectCode stage
    · rw [ht.1]
      exact recipCode stage
    · fin_cases stage <;> decide
    · exact ht.2.2.2.1
    · exact hReg
    · exact hVal
    · exact hIdeal
    · exact noSelp
    · exact Assumptions.numeric_segSites.pc hs1
    · intro s hPc e he
      exact execRecip stage (by rw [hPc, ht.1]) he
  have hRunAll : run kernel Assumptions.all l g 3 t = some u := by
    rw [Assumptions.run_all_eq_numeric]
    exact hRun
  have h1 : ∀ pair ∈ F, pair.1 ≠ reciprocalPred stage := fun pair hm he =>
    hFrame pair hm (by simp [he])
  have h2 : ∀ pair ∈ F, pair.1 ≠ reciprocalInput stage := fun pair hm he =>
    hFrame pair hm (by simp [he])
  have h3 : ∀ pair ∈ F, pair.1 ≠ reciprocalReg stage := fun pair hm he =>
    hFrame pair hm (by simp [he])
  refine ⟨u, ⟨?_, ht.2.1, ht.2.2.1, ht.2.2.2.1, Function.update_self .., ?_⟩,
    run_rtg hRunAll⟩
  · change t.pc + 1 + 1 + 1 = reciprocalPc stage + 3
    rw [ht.1]
  · have h12 : reciprocalPred stage ≠ reciprocalInput stage := by fin_cases stage <;> decide
    have h13 : reciprocalPred stage ≠ reciprocalReg stage := by fin_cases stage <;> decide
    have hv : u.regs (reciprocalPred stage) = some (.pred (decide (sum ≠ 0))) := by
      simp only [u, recipState, next, setReg, Function.update_of_ne h12,
        Function.update_of_ne h13, Function.update_self]
    exact ⟨hv, holds_update (holds_update (holds_update ht.2.2.2.2 h1) h2) h3⟩

variable {l : Launch} {X : Execution} {g pos : Nat} {t : TState} (stage : Fin 2) {value : Value}
    {sum : ℝ} {F : List (Nat × Value)} (ht : At t (reciprocalPc stage) F)
    (hReg : t.regs (statsReg stage .sum) = some value) (hVal : valFloat .f32 value = .ok sum)
    (hFrame : ∀ pair ∈ F, pair.1 ∉
      [reciprocalPred stage, reciprocalInput stage, reciprocalReg stage])
include stage ht hReg hVal hFrame

theorem finalReciprocalWithPredicate
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, At u (reciprocalPc stage + 3)
        ((reciprocalReg stage, fl (1 / (if sum = 0 then 1 else sum))) ::
          (reciprocalPred stage, .pred (decide (sum ≠ 0))) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) none := by
  obtain ⟨u,hu,hLocal⟩ := finalReciprocalWithPredicateLocal (l := l) (g := g)
    stage ht hReg hVal hFrame
  exact ⟨u,hu,hr.after_local hLocal⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
