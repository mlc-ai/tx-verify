-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleBallot
public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemLoads
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

def rescaleSkipPc (stage : Fin 2) : Nat := 8222 + 219 * stage.val

def maskZeroReg (stage : Fin 2) : Nat := 732 + 2 * stage.val

private theorem testCode (stage : Fin 2) :
    kernel.code[statsPc stage .alpha + 3]? =
      some ⟨none, .int ⟨.setp .eq none, .int .b 32, false, [some (maskZeroReg stage)],
        [.reg (rescaleVoteReg stage), .imm 0]⟩⟩ := by
  fin_cases stage
  · exact Flow.code_8010
  · exact Flow.code_8229

private theorem branchCode (stage : Fin 2) :
    kernel.code[statsPc stage .alpha + 4]? =
      some ⟨some (maskZeroReg stage, false), .bra (rescaleSkipPc stage) false⟩ := by
  fin_cases stage
  · exact Flow.code_8011
  · exact Flow.code_8230

/-- The local ballot test skips rescaling exactly when its full-mask word is zero. -/
theorem rescaleDecisionSteps {l : Launch} {g : Nat} {t : TState}
    (stage : Fin 2) (word : BitVec 32) {F : List (Nat × Value)}
    (ht : At t (statsPc stage .alpha + 3) F)
    (hMask : t.regs (rescaleVoteReg stage) = some (b32 word.toNat))
    (hFrame : ∀ pair ∈ F, pair.1 ≠ maskZeroReg stage) :
    ∃ u, At u (if word = 0 then rescaleSkipPc stage else rescaleLoadPc stage 0) F ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  let s := next (setReg t (maskZeroReg stage) (.pred (word = 0)))
  have hState := ht.set (r := maskZeroReg stage) (v := .pred (word = 0)) hFrame
  have hWordEq : word.toNat = 0 ↔ word = 0 := by
    constructor
    · intro h
      exact BitVec.eq_of_toNat_eq h
    · rintro rfl
      rfl
  have hCmp : compare .eq .b 32 (BitVec.ofNat 64 word.toNat)
      (truncBits 32 (BitVec.ofInt 64 0)) = decide (word = 0) := by
    have hb : word.toNat < 2 ^ 64 := by have := word.isLt; omega
    change decide (((BitVec.ofNat 64 word.toNat).toNat : Int) =
      ((truncBits 32 (BitVec.ofInt 64 0)).toNat : Int)) = _
    rw [toNat_ofNat_lt hb]
    exact decide_eq_decide.mpr (Int.ofNat_inj.trans hWordEq)
  have hTest : run kernel [] l g 1 t = some s := by
    apply run_local (testCode stage) rfl ht
    rw [execLocalA_nil, execLocal_int rfl]
    simp only [execInt, DType.width, DType.kind?, readReg, readBits, hMask, b32,
      bind, Except.bind, pure, Except.pure, truncBits_ofNat word.isLt (by decide)]
    change Except.ok (next (setReg t (maskZeroReg stage) (.pred
      (compare .eq .b 32 (BitVec.ofNat 64 word.toNat) (truncBits 32 (BitVec.ofInt 64 0)))))) =
      Except.ok s
    rw [hCmp]
  obtain ⟨u, hBranch, hu⟩ := run_bra (A := []) (branchCode stage) (decide (word = 0)) hState
    hState.2.2.2.2.1 (by simp)
  have hLift {a b : TState} {pc : Nat} {ins : Instr}
      (hPc : a.pc = pc) (hRange : 8009 ≤ pc) (hc : kernel.code[pc]? = some ins)
      (hCore : Assumptions.coreOp ins.op = true) (hRun : run kernel [] l g 1 a = some b) :
      run kernel Assumptions.all l g 1 a = some b := by
    have hSeg : a.pc ∉ Assumptions.swExp2Sites := by
      rw [hPc]
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    simpa only [run, Assumptions.tauStep_all_eq_nil hSeg (hPc.symm ▸ hc) hCore] using hRun
  have hRun := run_comp (hLift ht.1 (by fin_cases stage <;> decide) (testCode stage) rfl hTest)
    (hLift hState.1 (by fin_cases stage <;> decide) (branchCode stage) rfl hBranch)
  have hFall : statsPc stage .alpha + 4 + 1 = rescaleLoadPc stage 0 := by
    fin_cases stage <;> rfl
  refine ⟨u, ?_, run_rtg hRun⟩
  have hAt := hu.mono hu.2.2.2.2.2
  rw [hFall] at hAt
  simpa only [decide_eq_true_eq] using hAt

/-- In the actual trace the zero ballot skips all Tensor Memory rescaling. A nonzero ballot
continues at the first sixteen-word load of the same stage. -/
theorem rescaleBranch {l : Launch} {X : Execution} {g pos : Nat} {t : TState}
    (stage : Fin 2) (word : BitVec 32) {F : List (Nat × Value)}
    (ht : At t (statsPc stage .alpha + 3) F)
    (hMask : t.regs (rescaleVoteReg stage) = some (b32 word.toNat))
    (hFrame : ∀ pair ∈ F, pair.1 ≠ maskZeroReg stage)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, At u (if word = 0 then rescaleSkipPc stage else rescaleLoadPc stage 0) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) none := by
  obtain ⟨u, hAt, hSteps⟩ := rescaleDecisionSteps (l := l) (g := g) stage word ht hMask hFrame
  exact ⟨u, hAt, hr.after_local hSteps⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
