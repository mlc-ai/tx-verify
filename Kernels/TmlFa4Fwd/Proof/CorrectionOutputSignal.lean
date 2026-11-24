-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputStores
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

def outputFencePc (stage : Fin 2) : Nat := 8758 + 296 * stage.val

def outputCreditReg (stage : Fin 2) : Nat := 1614 + stage.val

def outputCreditDst (stage : Fin 2) : Nat := 9388 + 132 * stage.val

def outputReadyReg (stage : Fin 2) : Nat := if stage.val = 0 then 2390 else 2535

def outputReadyBase (l : Launch) (stage : Fin 2) : Nat :=
  l.sharedBase + if stage.val = 0 then 208 else 0

private def outputReadyImm (stage : Fin 2) : Nat := 216 * stage.val

def outputSignalFacts (l : Launch) (g : Nat) (stage : Fin 2) : List (Nat × Value) :=
  [(outputCreditReg stage, b32 (creditLoc l g stage).addr),
    (outputReadyReg stage, b32 (outputReadyBase l stage)), (6498, b32 1)]

private theorem fenceCode (stage : Fin 2) :
    kernel.code[outputFencePc stage]? =
      some ⟨none, .fence (.proxy (.async (some (.shared .cta))))⟩ := by
  fin_cases stage
  · exact Flow.code_8758
  · exact Flow.code_9054

private theorem creditCode (stage : Fin 2) :
    kernel.code[outputFencePc stage + 1]? = some
      ⟨none, .mbarArrive (outputCreditReg stage) 0 (.imm 0) (.reg 6498) false true .cta
        (some (outputCreditDst stage))⟩ := by
  fin_cases stage
  · exact Flow.code_8759
  · exact Flow.code_9055

private theorem readyCode (stage : Fin 2) :
    kernel.code[outputFencePc stage + 2]? = some
      ⟨none, .mbarArrive (outputReadyReg stage) (outputReadyImm stage : Nat)
        (.imm 0) (.reg 6498) false true .cta (some (outputCreditDst stage + 1))⟩ := by
  fin_cases stage
  · exact Flow.code_8760
  · exact Flow.code_9056

private theorem signalModel {l : Launch} {g : Nat} {t : TState} {pc : Nat} {ins : Instr}
    (hPc : t.pc = pc) (hLo : 8758 ≤ pc)
    (hCode : kernel.code[pc]? = some ins) (hCore : Assumptions.coreOp ins.op = true) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (hPc.symm ▸ hCode) hCore
  all_goals
    rw [hPc]
    simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites, Assumptions.delayedTmemSites,
      List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- A decoded correction unit-arrival template retains its exact address and return. -/
theorem correctionReleaseOut {l : Launch}
    {g pc reg countReg dst base off : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t pc F)
    (hModel : out kernel Assumptions.all l g t = out kernel [] l g t)
    (hCode : kernel.code[pc]? = some
      ⟨none, .mbarArrive reg (off : Int) (.imm 0) (.reg countReg) false true .cta (some dst)⟩)
    (hAddress : t.regs reg = some (b32 base)) (hCount : t.regs countReg = some (b32 1))
    (hBound : base + off < 2 ^ 32) (hAlign : (base + off) % 8 = 0) :
    out kernel Assumptions.all l g t = .ev
      (.arrive ⟨.shared,g/l.block,base+off⟩ 0 (next (mbarStateDest t (some dst))) 1 true .cta) := by
  let u := next (mbarStateDest t (some dst))
  let loc : Loc := ⟨.shared, g / l.block, base + off⟩
  have hLoc : mbarLoc l g t reg (off : Int) = .ok loc := by
    simp [mbarLoc, effAddr_b32_off hAddress hBound, hAlign, loc, bind, Except.bind,
      pure, Except.pure]
  have hOne : readBits l g t 32 (.reg countReg) = .ok (1 : BitVec 64) := by
    simp [readBits, readReg, hCount, b32, truncBits, bind, Except.bind, pure, Except.pure]
  rw [hModel]
  unfold out
  rw [ht.1, ht.2.2.2.1, hCode]
  change Out.ev (tmaTmpl l g t (.mbarArrive reg (off : Int) (.imm 0) (.reg countReg)
    false true .cta (some dst))) = _
  simp only [tmaTmpl, hLoc, hOne, bind, Except.bind, ofExec, pure, Except.pure,
    Bool.false_eq_true, ↓reduceIte]
  rfl

section
variable {l : Launch} {X : Execution} {g pos pc reg countReg dst base off : Nat} {t : TState}

/-- One checked correction release advances the actual trace and retains every
register other than the acknowledgement destination. -/
theorem observeCorrectionReleasePrefix {F : List (Nat × Value)} {result : Option TState}
    (ht : At t pc F) (hModel : out kernel Assumptions.all l g t = out kernel [] l g t)
    (hCode : kernel.code[pc]? = some
      ⟨none, .mbarArrive reg (off : Int) (.imm 0) (.reg countReg) false true .cta (some dst)⟩)
    (hAddress : t.regs reg = some (b32 base)) (hCount : t.regs countReg = some (b32 1))
    (hBound : base + off < 2 ^ 32) (hAlign : (base + off) % 8 = 0)
    (hFrame : ∀ pair ∈ F, pair.1 ≠ dst)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) result)
    (hMore : (X.tr g).drop pos ≠ []) :
    ∃ u, At u (pc + 1) F ∧
      X.get (g, pos) = some ⟨pc, .arrive ⟨.shared, g / l.block, base + off⟩ 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) result := by
  let u := next (mbarStateDest t (some dst))
  let loc : Loc := ⟨.shared,g/l.block,base+off⟩
  have hn : Next kernel Assumptions.all l g t t (.arrive loc 0 u 1 true .cta) :=
    ⟨.refl,correctionReleaseOut ht hModel hCode hAddress hCount hBound hAlign⟩
  obtain ⟨_, _, he, hFire, hTail⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hr hMore
  obtain ⟨rfl, hu⟩ := hFire
  obtain rfl := Option.some.inj hu
  rw [ht.1] at he
  exact ⟨u, At.clear_state ht hFrame, he, hTail⟩

/-- A release on a terminated trace uses the current barrier address and returns normally. -/
theorem observeCorrectionRelease {F : List (Nat × Value)} (ht : At t pc F)
    (hModel : out kernel Assumptions.all l g t = out kernel [] l g t)
    (hCode : kernel.code[pc]? = some
      ⟨none, .mbarArrive reg (off : Int) (.imm 0) (.reg countReg) false true .cta (some dst)⟩)
    (hAddress : t.regs reg = some (b32 base)) (hCount : t.regs countReg = some (b32 1))
    (hBound : base + off < 2 ^ 32) (hAlign : (base + off) % 8 = 0)
    (hFrame : ∀ pair ∈ F, pair.1 ≠ dst)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, At u (pc + 1) F ∧
      X.get (g, pos) = some ⟨pc, .arrive ⟨.shared, g / l.block, base + off⟩ 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) none :=
  observeCorrectionReleasePrefix ht hModel hCode hAddress hCount hBound hAlign hFrame hr
    (fun h => by rw [h] at hr; cases hr)
end

/-- Each correction lane fences the final shared stores, returns its accumulator credit, and
releases one arrival on the matching warp-13 output-ready object. -/
theorem observeOutputSignal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (ht : At t (outputFencePc stage) (outputSignalFacts l g stage ++ F))
    (hFrame : ∀ pair ∈ F, pair.1 ≠ outputCreditDst stage ∧ pair.1 ≠ outputCreditDst stage + 1)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, At u (outputFencePc stage + 3) F ∧
      X.get (g, pos) = some ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, pos + 1) = some
        ⟨outputFencePc stage + 1, .arrive (creditLoc l g stage) 0 1 true .cta⟩ ∧
      X.get (g, pos + 2) = some ⟨outputFencePc stage + 2,
        .arrive (Epilogue.readyLoc l g stage) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) none := by
  have hLo : 8758 ≤ outputFencePc stage := by unfold outputFencePc; omega
  let u := next t
  have hNext : Next kernel Assumptions.all l g t t
      (.fenceProxy (.async (some (.shared .cta))) none u) := by
    refine ⟨.refl, ?_⟩
    rw [signalModel ht.1 hLo (fenceCode stage) rfl]
    unfold out
    rw [ht.1, ht.2.2.2.1, fenceCode]
    rfl
  obtain ⟨_, _, he, hFire, hTail⟩ := hNext.continuing_at (by
    rintro e ⟨_, hBad⟩
    cases hBad) hr
  obtain ⟨rfl, hv⟩ := hFire
  obtain rfl := Option.some.inj hv
  rw [ht.1] at he
  have hu := ht.next
  have hFresh {pair : Nat × Value} (hMem : pair ∈ outputSignalFacts l g stage ++ F) :
      pair.1 ≠ outputCreditDst stage ∧ pair.1 ≠ outputCreditDst stage + 1 := by
    rcases List.mem_append.mp hMem with h | h
    · simp only [outputSignalFacts, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> (fin_cases stage <;> dsimp only <;> decide)
    · exact hFrame pair h
  have hLim := hp.shared.2.1
  have hAlign := hp.shared.1
  have hStage := stage.isLt
  have hCreditBound : (creditLoc l g stage).addr + 0 < 2 ^ 32 := by
    unfold creditLoc
    simp only
    omega
  have hCreditAlign : ((creditLoc l g stage).addr + 0) % 8 = 0 := by
    unfold creditLoc
    simp only
    omega
  obtain ⟨v, hv, hCredit, hTail2⟩ := observeCorrectionRelease hu
    (signalModel hu.1 (by omega) (creditCode stage) rfl) (creditCode stage)
    hu.2.2.2.2.1 hu.2.2.2.2.2.2.1 hCreditBound hCreditAlign
    (fun _ hm => (hFresh hm).1) hTail
  have hReadyAddr : outputReadyBase l stage + outputReadyImm stage =
      (Epilogue.readyLoc l g stage).addr := by
    fin_cases stage <;> simp [outputReadyBase, outputReadyImm, Epilogue.readyLoc]
  have hReadyBound : outputReadyBase l stage + outputReadyImm stage < 2 ^ 32 := by
    rw [hReadyAddr]
    unfold Epilogue.readyLoc
    simp only
    omega
  have hReadyAlign : (outputReadyBase l stage + outputReadyImm stage) % 8 = 0 := by
    rw [hReadyAddr]
    unfold Epilogue.readyLoc
    simp only
    omega
  obtain ⟨w, hw, hReady, hTail3⟩ := observeCorrectionRelease hv
    (signalModel hv.1 (by omega) (readyCode stage) rfl) (readyCode stage)
    hv.2.2.2.2.2.1 hv.2.2.2.2.2.2.1 hReadyBound hReadyAlign
    (fun _ hm => (hFresh hm).2) hTail2
  refine ⟨w, hw.mono hw.2.2.2.2.2.2.2, he, ?_, ?_, ?_⟩
  · simpa only [creditLoc, Nat.add_zero] using hCredit
  · simpa only [Nat.add_assoc, hReadyAddr, Epilogue.readyLoc] using hReady
  · simpa only [Nat.add_assoc] using hTail3

end
end PTX.Kernels.TmlFa4Fwd.Correction
