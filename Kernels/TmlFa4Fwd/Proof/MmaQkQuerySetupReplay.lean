-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkSetup
import Lemmas.Flow.TauFrame
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue

noncomputable section

/-- The first Q0 and Q1 blocks execute before the steady QK loop. -/
def initialQkBlock (stage : Fin 2) : Fin 4 := ⟨stage.val, stage.isLt.trans (by decide)⟩

/-- The first local instruction of one query-bank retarget. -/
def qkSetupStart (block : Fin 4) : Nat := qkPc block - 40

private def unguardedLocal (ins : Instr) : Bool :=
  ins.guard.isNone && ins.op.isLocal && schedulerFallsThrough ins.op

private theorem querySetupCode (block : Fin 4) :
    ((kernel.code.drop (qkSetupStart block)).take 40).all unguardedLocal = true := by
  fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem setupInstruction (block : Fin 4) {pc : Nat}
    (hLo : qkSetupStart block ≤ pc) (hHi : pc < qkSetupStart block + 40)
    (hc : pc < kernel.code.length) : ∃ ins, kernel.code[pc]? = some ins ∧
      ins.guard = none ∧ ins.op.isLocal = true ∧ schedulerFallsThrough ins.op = true := by
  let ins := kernel.code[pc]
  have hCode : kernel.code[pc]? = some ins := List.getElem?_eq_getElem hc
  have hCheck := List.all_eq_true.mp (querySetupCode block) ins (List.mem_of_getElem?
    (i := pc - qkSetupStart block) (by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hCode))
  have hParts : (ins.guard.isNone = true ∧ ins.op.isLocal = true) ∧
      schedulerFallsThrough ins.op = true := by
    simpa only [unguardedLocal, Bool.and_eq_true] using hCheck
  exact ⟨ins, hCode, Option.isNone_iff_eq_none.mp hParts.1.1, hParts.1.2, hParts.2⟩

private theorem setupFallthrough {op : Op} {pc after : Nat}
    (h : schedulerFallsThrough op = true) (hPc : after = nextPc op pc ∨ BrxTarget op after) :
    after = pc + 1 := by
  cases op <;> simp_all [schedulerFallsThrough, nextPc, BrxTarget]

private theorem setupRunPrefix {l : Launch} {g n : Nat} (block : Fin 4)
    {t : TState} {es : List Event} {vs : List Visit} {e : Event}
    (hLo : qkSetupStart block ≤ t.pc) (hLen : t.pc + n ≤ qkSetupStart block + 40)
    (ht : At t t.pc []) (hWalk : Walk kernel Assumptions.all l g t es vs)
    (hMem : e ∈ es) (hTarget : qkSetupStart block+40 ≤ e.pc ∨ ∀ fault, e.kind ≠ .ub fault) :
    ∃ u after, run kernel [] l g n t = some u ∧ At u (t.pc + n) [] ∧
      after.length + n = vs.length ∧ Walk kernel Assumptions.all l g u es after := by
  induction n generalizing t vs with
  | zero => exact ⟨t, vs, rfl, ht, rfl, hWalk⟩
  | succ n ih =>
    have hSetup : 1904 ≤ qkSetupStart block ∧ qkSetupStart block + 40 ≤ 2768 := by
      fin_cases block <;> decide
    have hCodeSize : 2768 < kernel.code.length := by
      decide +kernel
    have hlt : t.pc < qkSetupStart block + 40 := by omega
    obtain ⟨ins, hc, hGuard, hLocal, hStraight⟩ :=
      setupInstruction block hLo hlt (by omega)
    have hOutEq := out_eq_core (l := l) (g := g) (t := t) (by omega) (by omega)
    have hOut : out kernel [] l g t = match execLocalA [] l g t ins.op with
        | .ok u => .tau u
        | .error fault => .ev (.ub fault) := by
      simp only [out, ht.2.2.2.1, hc, hGuard, guardHolds, pure, Except.pure, hLocal, ↓reduceIte]
      rfl
    cases hWalk with
    | stop => cases hMem
    | last h =>
      obtain rfl := List.mem_singleton.mp hMem
      rcases hTarget with hEnd | hClean
      · have hc := estep_source_pc h
        omega
      · obtain ⟨m,hm,hf⟩ := h
        rw [hOutEq,hOut] at hm
        cases hs : execLocalA [] l g t ins.op with
        | ok u => rw [hs] at hm; cases hm
        | error fault =>
          rw [hs] at hm
          obtain rfl := Out.ev.inj hm
          exact (hClean fault (congrArg Event.kind hf.1)).elim
    | ev h _ =>
      obtain ⟨m, hm, hf⟩ := h
      rw [hOutEq, hOut] at hm
      cases hExec : execLocalA [] l g t ins.op with
      | ok u => rw [hExec] at hm; cases hm
      | error fault =>
        rw [hExec] at hm
        obtain rfl := Out.ev.inj hm
        cases hf.2
    | @tau _ u _ rest hTau hTail =>
      have hCore : Tau kernel [] l g t u := by unfold Tau at *; rwa [← hOutEq]
      have hAt : At u (t.pc + 1) [] := by
        rcases tau_core_frame hc hCore with rfl | hFrame
        · exact ⟨rfl, rfl, rfl, ht.2.2.2.1, trivial⟩
        · exact ⟨setupFallthrough hStraight hFrame.pc, hFrame.sub.trans ht.2.1,
            hFrame.acc.trans ht.2.2.1, hFrame.fault.trans ht.2.2.2.1, trivial⟩
      obtain ⟨v, trail, hRun, hv, hSize, hRest⟩ := ih (by have := hAt.1; omega)
        (by have := hAt.1; omega) ⟨rfl, hAt.2⟩ hTail
      have hFirst : run kernel [] l g 1 t = some u := by
        simp [run, tauStep_iff.mpr hCore]
      exact ⟨v, trail, by simpa only [Nat.add_comm 1] using run_comp hFirst hRun,
        by simpa only [hAt.1, Nat.add_assoc, Nat.add_comm 1] using hv,
        by simp only [List.length_cons]; omega, hRest⟩

variable {l : Launch}

/-- A later recorded event forces a query descriptor setup to take its real local
steps. All events, including pending continuations after the target, remain from the same run. -/
theorem qkSetupRunBeforeEvent {g : Nat} (block : Fin 4) {t : TState} {es : List Event}
    {vs : List Visit} {e : Event} (ht : At t (qkPc block - 40) [])
    (hWalk : Walk kernel Assumptions.all l g t es vs) (hMem : e ∈ es)
    (hTarget : qkPc block ≤ e.pc ∨ ∀ fault, e.kind ≠ .ub fault) :
    ∃ u after, run kernel [] l g 40 t = some u ∧ At u (qkPc block) [] ∧
      after.length + 40 = vs.length ∧ Walk kernel Assumptions.all l g u es after := by
  have hLen : qkSetupStart block + 40 = qkPc block := by
    fin_cases block <;> decide
  have hHere : t.pc = qkSetupStart block := ht.1
  obtain ⟨u, after, hRun, hu, hSize, hTail⟩ := setupRunPrefix block hHere.ge
    (show t.pc + 40 ≤ qkSetupStart block + 40 by rw [hHere]) ⟨rfl, ht.2⟩ hWalk hMem
    (hLen.symm ▸ hTarget)
  exact ⟨u, after, hRun, by simpa only [hHere, hLen] using hu, hSize, hTail⟩

/-- A successful local setup slice retains the scalar shape and has a decoded fallthrough. -/
theorem qkSetupLocalFrame {g n : Nat} (block : Fin 4) {t u : TState} (hLo : qkPc block - 40 ≤ t.pc)
    (hHi : t.pc + n ≤ qkPc block) (ht : At t t.pc []) (hRun : run kernel [] l g n t = some u) :
    At u (t.pc + n) [] := by
  have hEnd : qkSetupStart block + 40 = qkPc block := by
    fin_cases block <;> decide
  induction n generalizing t with
  | zero =>
    obtain rfl := Option.some.inj hRun
    exact ht
  | succ n ih =>
    have hCodeSize : qkPc block < kernel.code.length := by
      fin_cases block <;> decide +kernel
    obtain ⟨ins, hc, _, _, hStraight⟩ := setupInstruction block hLo (by omega) (by omega)
    simp only [run] at hRun
    cases hStep : tauStep kernel [] l g t with
    | none => simp [hStep] at hRun
    | some w =>
      have hAt : At w (t.pc + 1) [] := by
        rcases tau_core_frame hc (tauStep_iff.mp hStep) with rfl | hFrame
        · exact ⟨rfl, rfl, rfl, ht.2.2.2.1, trivial⟩
        · exact ⟨setupFallthrough hStraight hFrame.pc, hFrame.sub.trans ht.2.1,
            hFrame.acc.trans ht.2.2.1, hFrame.fault.trans ht.2.2.2.1, trivial⟩
      have hPc := hAt.1
      have hTail : run kernel [] l g n w = some u := by
        simpa only [hStep, Option.bind_some] using hRun
      have hRest := ih (by omega) (by omega) ⟨rfl, hAt.2⟩ hTail
      simpa only [hPc, Nat.add_assoc, Nat.add_comm 1] using hRest

/-- A recorded event at the far side of the first QK setup retains that local replay. -/
theorem querySetupRunBeforeEvent {g : Nat} (stage : Fin 2) {t : TState} {es : List Event}
    {vs : List Visit} {e : Event} (ht : At t (qkPc (initialQkBlock stage) - 40) [])
    (hWalk : Walk kernel Assumptions.all l g t es vs) (hMem : e ∈ es)
    (hEnd : qkPc (initialQkBlock stage) ≤ e.pc) :
    ∃ u after, run kernel [] l g 40 t = some u ∧ At u (qkPc (initialQkBlock stage)) [] ∧
      Walk kernel Assumptions.all l g u es after := by
  obtain ⟨u,after,hRun,hu,_,hw⟩ :=
    qkSetupRunBeforeEvent (initialQkBlock stage) ht hWalk hMem (.inl hEnd)
  exact ⟨u,after,hRun,hu,hw⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
