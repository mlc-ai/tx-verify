-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStats
public import Lemmas.Flow.Recip
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.FloatOutcome

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

def lsePc (stage : Fin 2) : Nat := 9061 + 14 * stage.val

def lseLogReg (stage : Fin 2) : Nat := 7074 + 4 * stage.val

def lseFmaReg (stage : Fin 2) : Nat := lseLogReg stage + 1

def lseMulReg (stage : Fin 2) : Nat := lseLogReg stage + 2

def lseOutReg (stage : Fin 2) : Nat := 1655 + stage.val

def lsePredReg (stage : Fin 2) : Nat := 739 + 3 * stage.val

private def logInstr (stage : Fin 2) : FloatInstr :=
  { op := .lg2, ty := ⟨.f32, 1⟩, mode := .approx, ftz := true,
    dsts := [some (lseLogReg stage)], srcs := [.reg (statsReg stage .sum)] }

private def fmaInstr (stage : Fin 2) : FloatInstr :=
  { op := .fma, ty := ⟨.f32, 1⟩, rnd := some .rn,
    dsts := [some (lseFmaReg stage)],
    srcs := [.reg 7134, .reg (statsReg stage .maximum), .reg (lseLogReg stage)] }

private def multiplyInstr (stage : Fin 2) : FloatInstr :=
  { op := .mul, ty := ⟨.f32, 1⟩,
    dsts := [some (lseMulReg stage)], srcs := [.reg (lseFmaReg stage), .f32imm 0x3F317218] }

private def selectInstr (stage : Fin 2) : IntInstr :=
  ⟨.selp, .float .f32, false, [some (lseOutReg stage)],
    [.reg (lseMulReg stage), .f32imm 4286578688, .reg (lsePredReg stage)]⟩

private theorem logCode (stage : Fin 2) :
    kernel.code[lsePc stage]? = some ⟨none, .float (logInstr stage)⟩ := by
  fin_cases stage
  · exact Flow.code_9061
  · exact Flow.code_9075

private theorem fmaCode (stage : Fin 2) :
    kernel.code[lsePc stage + 1]? = some ⟨none, .float (fmaInstr stage)⟩ := by
  fin_cases stage
  · exact Flow.code_9062
  · exact Flow.code_9076

private theorem multiplyCode (stage : Fin 2) :
    kernel.code[lsePc stage + 2]? = some ⟨none, .float (multiplyInstr stage)⟩ := by
  fin_cases stage
  · exact Flow.code_9063
  · exact Flow.code_9077

private theorem selectCode (stage : Fin 2) :
    kernel.code[lsePc stage + 3]? = some ⟨none, .int (selectInstr stage)⟩ := by
  fin_cases stage
  · exact Flow.code_9064
  · exact Flow.code_9078

private theorem segmentFree {pc : Nat} (h : 9061 ≤ pc) :
    SegFreePc Assumptions.numeric pc :=
  Assumptions.numeric_segSites.pc (by
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
    omega)

private theorem abiLnTwo : valFloat .f32 (b32 0x3F317218) = .ok (abiFloat 0x3F317218) := by
  have h : f32Value 0x3F317218 = some (1453635 / 2097152) := by
    norm_num [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
      Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  rw [abiFloat, h]
  exact valFloat_b32 (by decide) h

private theorem execLog {l : Launch} {g : Nat} {t : TState} {v : Value} {x : ℝ}
    (stage : Fin 2) (hPc : t.pc = lsePc stage) (hReg : t.regs (statsReg stage .sum) = some v)
    (hv : valFloat .f32 v = .ok x) (hx : 0 < x) :
    execLocalA Assumptions.numeric l g t (.float (logInstr stage)) =
      .ok (next (setReg t (lseLogReg stage) (fl (Real.logb 2 x)))) := by
  have hBound : 9061 ≤ t.pc := by rw [hPc]; unfold lsePc; omega
  rw [((segmentFree hBound).at rfl).exec]
  have hIdeal : Assumptions.idealArith.localRule l g t (.float (logInstr stage)) = none :=
    idealReal_localRule_none (by simp [FloatForm.ofOp, logInstr])
  have hApprox : Assumptions.approx.localRule l g t (.float (logInstr stage)) = none :=
    approxExact_localRule_none (by simp [ApproxForm.ofOp, logInstr])
  have hSites : t.pc ∈ Assumptions.lg2Sites := by
    rw [hPc]
    fin_cases stage <;> decide
  have hRead : readERealOpnd t .f32 (.reg (statsReg stage .sum)) = some (.ok (x : EReal)) := by
    rw [readERealOpnd_reg hReg]
    exact readEReal_of_valFloat hv
  have hLog : Assumptions.lg2.localRule l g t (.float (logInstr stage)) =
      some (.ok (next (setReg t (lseLogReg stage) (fl (Real.logb 2 x))))) := by
    simp [Assumptions.lg2, Assumptions.lg2Operands, logInstr, hSites, readFinite, hRead,
      bindRead, hx, pure, Except.pure, fl]
  simp only [execLocalRule, Assumptions.numeric, List.findSome?, hIdeal, hApprox, hLog]

private theorem readRealReg {t : TState} {r : Nat} {v : Value} {x : ℝ}
    (hr : t.regs r = some v) (hv : valFloat .f32 v = .ok x) :
    readERealOpnd t .f32 (.reg r) = some (.ok (x : EReal)) := by
  rw [readERealOpnd_reg hr]
  exact readEReal_of_valFloat hv

private theorem readRealPayload {t : TState} {r : Nat} {x : ℝ}
    (hr : t.regs r = some (fl x)) :
    readERealOpnd t .f32 (.reg r) = some (.ok (x : EReal)) :=
  readRealReg hr (by rfl)

private theorem execFma {l : Launch} {g : Nat} {t : TState} {sval mval : Value}
    {scale maximum logSum : ℝ} (stage : Fin 2) (hPc : 9061 ≤ t.pc)
    (hScale : t.regs 7134 = some sval) (hMax : t.regs (statsReg stage .maximum) = some mval)
    (hLog : t.regs (lseLogReg stage) = some (fl logSum))
    (hs : valFloat .f32 sval = .ok scale) (hm : valFloat .f32 mval = .ok maximum) :
    execLocalA Assumptions.numeric l g t (.float (fmaInstr stage)) =
      .ok (next (setReg t (lseFmaReg stage) (fl (scale * maximum + logSum)))) := by
  have hIdeal : IdealAt Assumptions.numeric (.fma .f32) l g t :=
    idealAt_head (by decide) (segmentFree hPc).tail
  apply hIdeal _ rfl
  simp only [fmaInstr, execIdealFloat, readRealReg hScale hs, readRealReg hMax hm,
    readRealPayload hLog, bindRead, mulEReal_coe, Option.bind_some, addEReal_coe, Option.map_some,
    erealValue_coe, pure, Except.pure, fl]

private theorem execMultiply {l : Launch} {g : Nat} {t : TState} {fma : ℝ}
    (stage : Fin 2) (hPc : 9061 ≤ t.pc) (hReg : t.regs (lseFmaReg stage) = some (fl fma)) :
    execLocalA Assumptions.numeric l g t (.float (multiplyInstr stage)) =
      .ok (next (setReg t (lseMulReg stage) (fl (fma * abiFloat 0x3F317218)))) := by
  have hIdeal : IdealAt Assumptions.numeric (.mul .f32) l g t :=
    idealAt_head (by decide) (segmentFree hPc).tail
  apply hIdeal _ rfl
  have hLit : readERealOpnd t .f32 (.f32imm 0x3F317218) =
      some (.ok ((abiFloat 0x3F317218 : ℝ) : EReal)) := readEReal_of_valFloat abiLnTwo
  simp only [multiplyInstr, execIdealFloat, readRealPayload hReg, hLit, bindRead, mulEReal_coe,
    Option.map_some, erealValue_coe, pure, Except.pure, fl]

variable {l : Launch}

private theorem execSelect {g : Nat} {t : TState} {v : ℝ} (stage : Fin 2) (hPc : 9061 ≤ t.pc)
    (hp : t.regs (lsePredReg stage) = some (.pred true))
    (hv : t.regs (lseMulReg stage) = some (fl v)) :
    execLocalA Assumptions.numeric l g t (.int (selectInstr stage)) =
      .ok (next (setReg t (lseOutReg stage) (fl v))) := by
  rw [((segmentFree hPc).at rfl).exec, execLocalRule_of_none]
  · rw [execLocal_selp (i := selectInstr stage) rfl]
    simp [selectInstr, execMove, DType.width, readReg, hp, readValue, hv, Value.bytes, fl,
      bind, Except.bind, pure, Except.pure]
    rfl
  · intro asm hm
    simp only [Assumptions.numeric, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- On a row with positive mass, the final LSE register uses the decoded scale and the ABI's
encoded natural-log conversion factor. The four decoded steps are local. -/
theorem finalLseLocal {g : Nat} {t : TState} {F : List (Nat × Value)} (stage : Fin 2)
    {sumWord maxWord scaleWord : Value} {sum maximum scale : ℝ} (ht : At t (lsePc stage) F)
    (hsr : t.regs (statsReg stage .sum) = some sumWord)
    (hmr : t.regs (statsReg stage .maximum) = some maxWord) (hkr : t.regs 7134 = some scaleWord)
    (hpr : t.regs (lsePredReg stage) = some (.pred true)) (hs : valFloat .f32 sumWord = .ok sum)
    (hm : valFloat .f32 maxWord = .ok maximum) (hk : valFloat .f32 scaleWord = .ok scale)
    (hPositive : 0 < sum)
    (hFrame : ∀ rv ∈ F, rv.1 ≠ lseLogReg stage ∧ rv.1 ≠ lseFmaReg stage ∧
      rv.1 ≠ lseMulReg stage ∧ rv.1 ≠ lseOutReg stage) :
    ∃ u, At u (lsePc stage + 4)
        ((lseOutReg stage, fl (abiFloat 0x3F317218 * (scale * maximum + Real.logb 2 sum))) :: F) ∧
      run kernel Assumptions.all l g 4 t = some u := by
  let logSum := Real.logb 2 sum
  let fma := scale * maximum + logSum
  let product := fma * abiFloat 0x3F317218
  let s := next (setReg t (lseLogReg stage) (fl logSum))
  let u := next (setReg s (lseFmaReg stage) (fl fma))
  let v := next (setReg u (lseMulReg stage) (fl product))
  let w := next (setReg v (lseOutReg stage) (fl product))
  have hS := ht.set (r := lseLogReg stage) (v := fl logSum) (fun rv hm => (hFrame rv hm).1)
  have hS' : At s (lsePc stage + 1) F := hS.mono hS.2.2.2.2.2
  have hU := hS'.set (r := lseFmaReg stage) (v := fl fma) (fun rv hm => (hFrame rv hm).2.1)
  have hU' : At u (lsePc stage + 2) F := hU.mono hU.2.2.2.2.2
  have hV := hU'.set (r := lseMulReg stage) (v := fl product) (fun rv hm => (hFrame rv hm).2.2.1)
  have hV' : At v (lsePc stage + 3) F := hV.mono hV.2.2.2.2.2
  have hW := hV'.set (r := lseOutReg stage) (v := fl product) (fun rv hm => (hFrame rv hm).2.2.2)
  have h1 : run kernel Assumptions.numeric l g 1 t = some s := by
    apply run_local (logCode stage) rfl ht
    exact execLog stage ht.1 hsr hs hPositive
  have h2 : run kernel Assumptions.numeric l g 1 s = some u := by
    have hn1 : 7134 ≠ lseLogReg stage := by fin_cases stage <;> decide
    have hn2 : statsReg stage .maximum ≠ lseLogReg stage := by fin_cases stage <;> decide
    apply run_local (fmaCode stage) rfl hS'
    exact execFma stage (by rw [hS.1]; unfold lsePc; omega)
      (by simpa only [s, next, setReg, Function.update_of_ne hn1] using hkr)
      (by simpa only [s, next, setReg, Function.update_of_ne hn2] using hmr)
      hS.2.2.2.2.1 hk hm
  have h3 : run kernel Assumptions.numeric l g 1 u = some v := by
    apply run_local (multiplyCode stage) rfl hU'
    exact execMultiply stage (by rw [hU.1]; unfold lsePc; omega) hU.2.2.2.2.1
  have h4 : run kernel Assumptions.numeric l g 1 v = some w := by
    have hFresh : lsePredReg stage ≠ lseLogReg stage ∧ lsePredReg stage ≠ lseFmaReg stage ∧
        lsePredReg stage ≠ lseMulReg stage := by fin_cases stage <;> decide
    apply run_local (selectCode stage) rfl hV'
    exact execSelect stage (by rw [hV.1]; unfold lsePc; omega)
      (by simpa only [s, u, v, next, setReg, Function.update_of_ne hFresh.1,
        Function.update_of_ne hFresh.2.1, Function.update_of_ne hFresh.2.2] using hpr)
      hV.2.2.2.2.1
  have hRun : run kernel Assumptions.all l g 4 t = some w := by
    rw [Assumptions.run_all_eq_numeric]
    exact run_comp (run_comp (run_comp h1 h2) h3) h4
  refine ⟨w, ?_, hRun⟩
  have hValue : product = abiFloat 0x3F317218 * (scale * maximum + Real.logb 2 sum) := by
    exact mul_comm _ _
  rw [← hValue]
  exact hW

/-- The first stage's nonzero predicate survives normalization. The second stage reads its
own sum again at PC9074 for the LSE selection. -/
theorem secondLsePredicateRun {g : Nat} {t : TState} {F : List (Nat × Value)} (sum : ℝ)
    (ht : At t 9074 F) (hSum : t.regs 1653 = some (fl sum)) (hFresh : ∀ rv ∈ F, rv.1 ≠ 742) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 9075 ((742, .pred (decide (sum ≠ 0))) :: F) := by
  have hSite : t.pc ∉ Assumptions.swExp2Sites := by rw [ht.1]; decide
  have hI : IdealAt Assumptions.numeric (.setp .f32) l g t :=
    idealAt_head (by decide) (Assumptions.numeric_segSites.pc hSite).tail
  have ho := (fsetp_imm (ht.1.symm ▸ Flow.code_9074) (Or.inl rfl) rfl hI ht.2.2.2.1
    hSum valFloat_zero).1 sum (by rfl)
  rw [erealCompare_ne_coe_zero] at ho
  have hRun : run kernel Assumptions.all l g 1 t =
      some (next (setReg t 742 (.pred (decide (sum ≠ 0))))) := by
    rw [Assumptions.run_all_eq_numeric]
    simp only [run, tauStep, ho, Option.bind_some]
  exact ⟨_, hRun, ht.set hFresh⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
