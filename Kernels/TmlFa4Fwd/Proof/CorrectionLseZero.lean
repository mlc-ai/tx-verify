-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseNumerics
import all Kernels.TmlFa4Fwd.Proof.CorrectionLseNumerics
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreNumeric

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.Assumption

private theorem classifyPayloadZero : classify .f32 (fl 0) = .ok (.zero false) := by
  have hDecode : FloatFmt.f32.layout.decode 0 = some (.zero false) := by decide
  have hRound : FloatFmt.f32.layout.round .rn FloatFmt.f32.overflow 0 false =
      some (.zero false) := Layout.round_zero (by trivial)
  have hEncode := Layout.encode_decode (by decide : 0 < 2^FloatFmt.f32.layout.width) hDecode
  have hBits : FloatFmt.f32.encode 0 = 0 := by
    rw [FloatFmt.encode,hRound,Option.bind_some,hEncode]
    rfl
  simp only [fl,classify,Value.bitPattern,hBits]
  rfl

private theorem execLogZero {l : Launch} {g : Nat} {t : TState} (stage : Fin 2)
    (hPc : t.pc = lsePc stage) (hSum : t.regs (statsReg stage .sum) = some (fl 0)) :
    execLocalA Assumptions.numeric l g t (.float (logInstr stage)) =
      .ok (next (setReg t (lseLogReg stage) (Softmax.scoreValue none))) := by
  have hBound : 9061 ≤ t.pc := by rw [hPc]; unfold lsePc; omega
  have hRead : readERealOpnd t .f32 (.reg (statsReg stage .sum)) = some (.ok 0) := by
    rw [readERealOpnd_reg hSum]
    rfl
  have hIdeal : Assumptions.idealArith.localRule l g t (.float (logInstr stage)) = none :=
    idealReal_localRule_none (by simp [FloatForm.ofOp,logInstr])
  have hApprox : Assumptions.approx.localRule l g t (.float (logInstr stage)) = none :=
    approxExact_localRule_none (by simp [ApproxForm.ofOp,logInstr])
  have hNoLog : Assumptions.lg2.localRule l g t (.float (logInstr stage)) = none := by
    have hSites : t.pc ∈ Assumptions.lg2Sites := by
      rw [hPc]
      fin_cases stage <;> decide
    simp [Assumptions.lg2,Assumptions.lg2Operands,logInstr,hSites,readFinite,hRead,bindRead,
      pure,Except.pure]
  rw [((segmentFree hBound).at rfl).exec]
  simp only [execLocalRule,Assumptions.numeric,List.findSome?,hIdeal,hApprox,hNoLog]
  change execFloat l g t (logInstr stage) = _
  simp [execFloat,logInstr,boolCombine,readValue,readReg,hSum,
    classifyPayloadZero,floatLane,List.range_one,bind,Except.bind,pure,Except.pure]
  rfl

private theorem fmaNegativeInfinity {scale : ℝ} (hs : 0 < scale) (maximum : Option ℝ) :
    (mulEReal (scale : EReal) (Softmax.scoreReal maximum)).bind (addEReal · ⊥) =
      some (⊥ : EReal) := by
  cases maximum with
  | none =>
    have hScale : (scale : EReal) ≠ 0 := ne_of_gt (EReal.coe_pos.mpr hs)
    simp [Softmax.scoreReal,mulEReal,addEReal,hScale,EReal.coe_mul_bot_of_pos hs]
  | some value =>
    simp [Softmax.scoreReal,mulEReal,addEReal,← EReal.coe_mul,EReal.add_bot]

variable {l : Launch}

private theorem execFmaZero {g : Nat} {t : TState} {scaleWord : Value} {scale : ℝ} (stage : Fin 2)
    (hPc : 9061 ≤ t.pc) (maximum : Option ℝ) (hScale : t.regs 7134 = some scaleWord)
    (hMax : t.regs (statsReg stage .maximum) = some (Softmax.scoreValue maximum))
    (hLog : t.regs (lseLogReg stage) = some (Softmax.scoreValue none))
    (hValue : valFloat .f32 scaleWord = .ok scale) (hPos : 0 < scale) :
    execLocalA Assumptions.numeric l g t (.float (fmaInstr stage)) =
      .ok (next (setReg t (lseFmaReg stage) (Softmax.scoreValue none))) := by
  have hIdeal : IdealAt Assumptions.numeric (.fma .f32) l g t :=
    idealAt_head (by decide) (segmentFree hPc).tail
  apply hIdeal _ rfl
  have hm := (readERealOpnd_reg hMax).trans (Softmax.readScoreValue maximum)
  have hl : readERealOpnd t .f32 (.reg (lseLogReg stage)) = some (.ok (⊥ : EReal)) :=
    (readERealOpnd_reg hLog).trans (Softmax.readScoreValue none)
  simp only [fmaInstr,execIdealFloat,readRealReg hScale hValue,hm,hl,bindRead,
    fmaNegativeInfinity hPos maximum,Option.map_some,pure,Except.pure]
  exact congrArg (fun word => some (Except.ok (next (setReg t (lseFmaReg stage) word))))
    (Softmax.scoreReal_value none)

private theorem positiveLnTwoWord : 0 < abiFloat 0x3F317218 := by
  have h : f32Value 0x3F317218 = some (1453635 / 2097152) := by
    norm_num [f32Value,FloatFmt.decode,FloatFmt.layout,Layout.decode,Layout.fieldVal,
      Layout.magnitude,Layout.bias,Layout.width,FVal.num]
  rw [abiFloat,h]
  norm_num

private theorem execMultiplyZero {g : Nat} {t : TState} (stage : Fin 2) (hPc : 9061 ≤ t.pc)
    (hReg : t.regs (lseFmaReg stage) = some (Softmax.scoreValue none)) :
    execLocalA Assumptions.numeric l g t (.float (multiplyInstr stage)) =
      .ok (next (setReg t (lseMulReg stage) (Softmax.scoreValue none))) := by
  have hIdeal : IdealAt Assumptions.numeric (.mul .f32) l g t :=
    idealAt_head (by decide) (segmentFree hPc).tail
  apply hIdeal _ rfl
  have hLit : readERealOpnd t .f32 (.f32imm 0x3F317218) =
      some (.ok ((abiFloat 0x3F317218 : ℝ) : EReal)) := readEReal_of_valFloat abiLnTwo
  have hNeg := (readERealOpnd_reg hReg).trans (Softmax.readScoreValue none)
  have hNZ : (abiFloat 0x3F317218 : EReal) ≠ 0 := ne_of_gt (EReal.coe_pos.mpr positiveLnTwoWord)
  simp [multiplyInstr,execIdealFloat,hNeg,hLit,bindRead,Softmax.scoreReal,mulEReal,hNZ,
    EReal.bot_mul_coe_of_pos positiveLnTwoWord,pure,Except.pure]
  rfl

private theorem execSelectZero {g : Nat} {t : TState} (stage : Fin 2) (hPc : 9061 ≤ t.pc)
    (hp : t.regs (lsePredReg stage) = some (.pred false)) :
    execLocalA Assumptions.numeric l g t (.int (selectInstr stage)) =
      .ok (next (setReg t (lseOutReg stage) (Softmax.scoreValue none))) := by
  rw [((segmentFree hPc).at rfl).exec,execLocalRule_of_none]
  · rw [execLocal_selp (i := selectInstr stage) rfl]
    simp [selectInstr,execMove,DType.width,readReg,hp,readValue,Softmax.scoreValue,
      bind,Except.bind,pure,Except.pure]
    rfl
  · intro asm hm
    simp only [Assumptions.numeric,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A zero-mass LSE row uses the nonfinite logarithm and the decoded infinity selection. -/
theorem finalLseZeroLocal {g : Nat} {t : TState} {F : List (Nat × Value)} (stage : Fin 2)
    (maximum : Option ℝ) {scaleWord : Value} {scale : ℝ} (ht : At t (lsePc stage) F)
    (hSum : t.regs (statsReg stage .sum) = some (fl 0))
    (hMax : t.regs (statsReg stage .maximum) = some (Softmax.scoreValue maximum))
    (hScale : t.regs 7134 = some scaleWord) (hPred : t.regs (lsePredReg stage) = some (.pred false))
    (hScaleValue : valFloat .f32 scaleWord = .ok scale) (hScalePositive : 0 < scale)
    (hFrame : ∀ rv ∈ F, rv.1 ≠ lseLogReg stage ∧ rv.1 ≠ lseFmaReg stage ∧
      rv.1 ≠ lseMulReg stage ∧ rv.1 ≠ lseOutReg stage) :
    ∃ u, At u (lsePc stage+4) ((lseOutReg stage,Softmax.scoreValue none)::F) ∧
      run kernel Assumptions.all l g 4 t = some u := by
  let n := Softmax.scoreValue none
  let s := next (setReg t (lseLogReg stage) n)
  let u := next (setReg s (lseFmaReg stage) n)
  let v := next (setReg u (lseMulReg stage) n)
  let w := next (setReg v (lseOutReg stage) n)
  have hS : At s (lsePc stage+1) ((lseLogReg stage,n)::F) :=
    ht.set (fun rv hm => (hFrame rv hm).1)
  have hS' : At s (lsePc stage+1) F := hS.mono hS.2.2.2.2.2
  have hU : At u (lsePc stage+2) ((lseFmaReg stage,n)::F) :=
    hS'.set (fun rv hm => (hFrame rv hm).2.1)
  have hU' : At u (lsePc stage+2) F := hU.mono hU.2.2.2.2.2
  have hV : At v (lsePc stage+3) ((lseMulReg stage,n)::F) :=
    hU'.set (fun rv hm => (hFrame rv hm).2.2.1)
  have hV' : At v (lsePc stage+3) F := hV.mono hV.2.2.2.2.2
  have hW : At w (lsePc stage+4) ((lseOutReg stage,n)::F) :=
    hV'.set (fun rv hm => (hFrame rv hm).2.2.2)
  have h1 : run kernel Assumptions.numeric l g 1 t = some s :=
    run_local (logCode stage) rfl ht (execLogZero stage ht.1 hSum)
  have h2 : run kernel Assumptions.numeric l g 1 s = some u := by
    have hN1 : 7134 ≠ lseLogReg stage := by fin_cases stage <;> decide
    have hN2 : statsReg stage .maximum ≠ lseLogReg stage := by fin_cases stage <;> decide
    apply run_local (fmaCode stage) rfl hS'
    exact execFmaZero stage (by rw [hS.1]; unfold lsePc; omega) maximum
      (by simpa only [s,next,setReg,Function.update_of_ne hN1] using hScale)
      (by simpa only [s,next,setReg,Function.update_of_ne hN2] using hMax)
      hS.2.2.2.2.1 hScaleValue hScalePositive
  have h3 : run kernel Assumptions.numeric l g 1 u = some v := by
    apply run_local (multiplyCode stage) rfl hU'
    exact execMultiplyZero stage (by rw [hU.1]; unfold lsePc; omega) hU.2.2.2.2.1
  have h4 : run kernel Assumptions.numeric l g 1 v = some w := by
    have hKeep : lsePredReg stage ≠ lseLogReg stage ∧ lsePredReg stage ≠ lseFmaReg stage ∧
        lsePredReg stage ≠ lseMulReg stage := by fin_cases stage <;> decide
    apply run_local (selectCode stage) rfl hV'
    exact execSelectZero stage (by rw [hV.1]; unfold lsePc; omega)
      (by simpa only [s,u,v,next,setReg,Function.update_of_ne hKeep.1,
        Function.update_of_ne hKeep.2.1,Function.update_of_ne hKeep.2.2] using hPred)
  refine ⟨w,hW,?_⟩
  rw [Assumptions.run_all_eq_numeric]
  exact run_comp (run_comp (run_comp h1 h2) h3) h4

/-- A terminal denominator determines the local LSE path including the zero-mass rows. -/
theorem finalLseOfDenominatorLocal {g : Nat} {t : TState} {F : List (Nat × Value)} (stage : Fin 2)
    (sum : ℝ) (maximum : Option ℝ) {scaleWord : Value} {scale : ℝ}
    (hValid : Softmax.DenominatorValid sum maximum) (ht : At t (lsePc stage) F)
    (hSum : t.regs (statsReg stage .sum) = some (fl sum))
    (hMax : t.regs (statsReg stage .maximum) = some (Softmax.scoreValue maximum))
    (hScale : t.regs 7134 = some scaleWord)
    (hPred : t.regs (lsePredReg stage) = some (.pred (decide (sum ≠ 0))))
    (hScaleValue : valFloat .f32 scaleWord = .ok scale) (hScalePositive : 0 < scale)
    (hFrame : ∀ rv ∈ F, rv.1 ≠ lseLogReg stage ∧ rv.1 ≠ lseFmaReg stage ∧
      rv.1 ≠ lseMulReg stage ∧ rv.1 ≠ lseOutReg stage) :
    ∃ value u, value.bytes = 4 ∧ At u (lsePc stage+4) ((lseOutReg stage,value)::F) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  by_cases hPositive : 0 < sum
  · obtain ⟨mx, rfl⟩ := hValid.finiteMaximum hPositive
    have hNonzero : decide (sum ≠ 0) = true := decide_eq_true (ne_of_gt hPositive)
    obtain ⟨u,hAt,hRun⟩ := finalLseLocal (l := l) (g := g) stage ht hSum hMax hScale
      (by simpa only [hNonzero] using hPred) rfl rfl hScaleValue hPositive hFrame
    exact ⟨_,u,rfl,hAt,run_rtg hRun⟩
  · have hz : sum = 0 := le_antisymm (le_of_not_gt hPositive) hValid.nonnegative
    subst sum
    obtain ⟨u,hAt,hRun⟩ := finalLseZeroLocal (l := l) (g := g) stage maximum ht hSum hMax
      hScale (by simpa using hPred) hScaleValue hScalePositive hFrame
    exact ⟨_,u,rfl,hAt,run_rtg hRun⟩

end PTX.Kernels.TmlFa4Fwd.Correction
