-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxConvert
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreNumeric

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

private theorem classifyMaskedBias : classify .bf16 (biasValue none) = .ok (.inf true) :=
  classify_bits (fmt := .bf16) (n := 0xFF80) (x := .inf true) (by decide) (by decide)

private theorem widenMaskedCore {l : Launch} {g dst src : Nat} {t : TState}
    (hs : t.regs src = some (biasValue none)) :
    execLocal l g t (biasConvertOp dst src) = .ok (next (setReg t dst (scoreValue none))) := by
  let c : CvtInstr := {dst := .float .f32, src := .float .bf16, d := dst, srcs := [.reg src]}
  have hRead : readCvtFloat (FType.bf16 != FType.bf16) t .bf16 (.reg src) = .ok (.inf true) :=
    (readCvtFloat_reg hs rfl).trans classifyMaskedBias
  change execCvt l g t c = _
  simp only [execCvt, c, FType.fmt?, hRead, bind, Except.bind]
  rfl

/-- A decoded BF16 bias widening preserves the finite payload or the negative-infinity mask. -/
theorem widenBiasRun {l : Launch} {g pc dst src : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t pc F) (hCode : kernel.code[pc]? = some ⟨none, biasConvertOp dst src⟩)
    (hSite : pc ∈ Assumptions.biasWidenSites) (hOff : pc ∉ Assumptions.swExp2Sites)
    (x : Option ℝ) (hs : t.regs src = some (biasValue x)) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t dst (scoreValue x))) := by
  cases x with
  | some x =>
    apply biasConvertRun ht hCode hSite
    rw [readFinite, readERealOpnd_reg hs]
    simp [biasValue, readEReal, bindRead, pure, Except.pure]
  | none =>
    apply run_local hCode rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric,
      ((Assumptions.numeric_segSites.pc hOff).at ht.1).exec]
    have hRead : readFinite t .bf16 (.reg src) = none := by
      rw [readFinite, readERealOpnd_reg hs]
      change bindRead (readEReal.ofDatum (classify .bf16 (biasValue none))) _ = _
      rw [classifyMaskedBias]
      simp [readEReal.ofDatum, bindRead, pure, Except.pure]
    have hRule : Assumptions.bf16Convert.localRule l g t (biasConvertOp dst src) = none := by
      change (if !Assumptions.biasWidenSites.contains t.pc then none else
        bindRead (readFinite t .bf16 (.reg src)) (fun y =>
          some (.ok (next (setReg t dst (.float .f32 y)))))) = _
      split <;> simp [hRead, bindRead]
    rw [← widenMaskedCore hs, execLocalRule]
    simp only [Assumptions.numeric, List.findSome?_cons, hRule, List.findSome?_nil]
    rfl

end
end PTX.Kernels.TmlFa4Fwd.Softmax
