-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleStage
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part131

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

def rescaleSignalPc (stage : Fin 2) : Nat := rescaleStorePc stage 7 + 2

def rescaleCountReg (stage : Fin 2) : Nat := 6236 + 258 * stage.val

def rescaleSignalDst (stage : Fin 2) : Nat := 9124 + 131 * stage.val

def rescaleReuseReg (stage : Fin 2) : Nat := if stage.val = 0 then 1628 else 1069

def rescaleReuseLoc (l : Launch) (g : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + (200 - 8 * stage.val)⟩

private theorem rescaleCountCode (stage : Fin 2) :
    kernel.code[rescaleSignalPc stage]? =
      some ⟨none, .move ⟨.scalar, .int .b 32, [some (rescaleCountReg stage)], [.imm 1]⟩⟩ := by
  fin_cases stage
  · exact Flow.code_8222
  · exact Flow.code_8441

private theorem rescaleCreditCode (stage : Fin 2) :
    kernel.code[rescaleSignalPc stage + 1]? = some
      ⟨none, .mbarArrive (outputCreditReg stage) 0 (.imm 0) (.reg (rescaleCountReg stage))
        false true .cta (some (rescaleSignalDst stage))⟩ := by
  fin_cases stage
  · exact Flow.code_8223
  · exact Flow.code_8442

private theorem rescaleReuseCode (stage : Fin 2) :
    kernel.code[rescaleSignalPc stage + 2]? = some
      ⟨none, .mbarArrive (rescaleReuseReg stage) 0 (.imm 0) (.reg (rescaleCountReg stage))
        false true .cta (some (rescaleSignalDst stage + 1))⟩ := by
  fin_cases stage
  · exact Flow.code_8224
  · exact Flow.code_8443

private theorem rescaleSignalCore {l : Launch} {g off : Nat} {t : TState} {ins : Instr}
    (stage : Fin 2) (hOff : off < 3) (ht : t.pc = rescaleSignalPc stage + off)
    (hCode : kernel.code[rescaleSignalPc stage + off]? = some ins)
    (hCore : Assumptions.coreOp ins.op = true) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (ht.symm ▸ hCode) hCore
  all_goals rw [ht]; fin_cases stage <;> interval_cases off <;> decide

/-- After either the skipped or the taken rescale path, the correction lane returns its
accumulator credit and releases the statistics-buffer slot. Both are actual trace arrivals. -/
theorem observeRescaleSignals {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (ht : At t (rescaleSignalPc stage)
      ((outputCreditReg stage, b32 (creditLoc l g stage).addr) ::
        (rescaleReuseReg stage, b32 (rescaleReuseLoc l g stage).addr) :: F))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ rescaleCountReg stage ∧
      pair.1 ≠ rescaleSignalDst stage ∧ pair.1 ≠ rescaleSignalDst stage + 1)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, At u (rescaleSignalPc stage + 3) F ∧
      X.get (g, pos) = some ⟨rescaleSignalPc stage + 1,
        .arrive (creditLoc l g stage) 0 1 true .cta⟩ ∧
      X.get (g, pos + 1) = some ⟨rescaleSignalPc stage + 2,
        .arrive (rescaleReuseLoc l g stage) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 2)) none := by
  let s := next (setReg t (rescaleCountReg stage) (b32 1))
  have hMove : run kernel [] l g 1 t = some s := by
    apply run_local (rescaleCountCode stage) rfl ht
    rw [execLocalA_nil, execLocal_move rfl]
    simp [execMove, readValue, readBits, Value.bytes, b32, bind, Except.bind, pure, Except.pure,
      DType.width, s, truncBits]
  have hModel : out kernel Assumptions.all l g t = out kernel [] l g t :=
    rescaleSignalCore stage (off := 0) (by decide) (by simpa using ht.1)
      (by simpa using rescaleCountCode stage) rfl
  have hRun : run kernel Assumptions.all l g 1 t = some s := by
    simpa only [run, tauStep, hModel] using hMove
  have hLocal (pair : Nat × Value)
      (hm : pair ∈ (outputCreditReg stage, b32 (creditLoc l g stage).addr) ::
        (rescaleReuseReg stage, b32 (rescaleReuseLoc l g stage).addr) :: F) :
      pair.1 ≠ rescaleCountReg stage := by
    simp only [List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · fin_cases stage <;> dsimp only <;> decide
    · fin_cases stage <;> dsimp only <;> decide
    · exact (hFresh pair hm).1
  have hs := ht.set (r := rescaleCountReg stage) (v := b32 1) hLocal
  have hKeep (pair : Nat × Value)
      (hm : pair ∈ (rescaleCountReg stage, b32 1) ::
        (outputCreditReg stage, b32 (creditLoc l g stage).addr) ::
        (rescaleReuseReg stage, b32 (rescaleReuseLoc l g stage).addr) :: F) :
      pair.1 ≠ rescaleSignalDst stage ∧ pair.1 ≠ rescaleSignalDst stage + 1 := by
    simp only [List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | hm
    · fin_cases stage <;> dsimp only <;> decide
    · fin_cases stage <;> dsimp only <;> decide
    · fin_cases stage <;> dsimp only <;> decide
    · exact (hFresh pair hm).2
  have hLimit := hp.shared.2.1
  have hAlign := hp.shared.1
  have hStage := stage.isLt
  have hcB : (creditLoc l g stage).addr + 0 < 2 ^ 32 := by
    unfold creditLoc
    simp only
    omega
  have hcA : ((creditLoc l g stage).addr + 0) % 8 = 0 := by
    unfold creditLoc
    simp only
    omega
  obtain ⟨v, hv, hc, hTail⟩ := observeCorrectionRelease hs
    (rescaleSignalCore stage (by decide) hs.1 (rescaleCreditCode stage) rfl)
    (rescaleCreditCode stage) hs.2.2.2.2.2.1 hs.2.2.2.2.1 hcB hcA
    (fun pair hm => (hKeep pair hm).1) (hr.after_local (run_rtg hRun))
  have hve : At v (rescaleSignalPc stage + 2) _ := hv
  have hrB : (rescaleReuseLoc l g stage).addr + 0 < 2 ^ 32 := by
    unfold rescaleReuseLoc
    simp only
    omega
  have hrA : ((rescaleReuseLoc l g stage).addr + 0) % 8 = 0 := by
    unfold rescaleReuseLoc
    simp only
    omega
  obtain ⟨u, hu, he, hRest⟩ := observeCorrectionRelease hve
    (rescaleSignalCore stage (by decide) hve.1 (rescaleReuseCode stage) rfl)
    (rescaleReuseCode stage) hve.2.2.2.2.2.2.1 hve.2.2.2.2.1 hrB hrA
    (fun pair hm => (hKeep pair hm).2) hTail
  refine ⟨u, hu.mono hu.2.2.2.2.2.2.2, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, creditLoc] using hc
  · simpa only [Nat.add_zero, rescaleReuseLoc] using he
  · simpa only [Nat.add_assoc] using hRest

end
end PTX.Kernels.TmlFa4Fwd.Correction
