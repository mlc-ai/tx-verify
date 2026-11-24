-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingControlRegions
public import Lemmas.Execution.EventRegisterFrame
public import Lemmas.Flow.WarpUniform

@[expose] public section

/-! # Register facts through a concrete instruction window -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

def inRegisterWindow (first last : Nat) (pc : Nat) : Prop := first ≤ pc ∧ pc ≤ last

instance (first last : Nat) : DecidablePred (inRegisterWindow first last) := fun pc =>
  inferInstanceAs (Decidable (first ≤ pc ∧ pc ≤ last))

def stableWindowInstr (r first last pc : Nat) (ins : Instr) : Bool :=
  if pc = last then ins.guard.isNone && !ins.op.isLocal
  else closesControlRegion (inRegisterWindow first last) pc ins &&
    (if ins.op.isLocal then decide (r ∉ writesRegs ins.op) else preservesReg r ins.op)

/-- The last instruction is an unguarded event. Local steps and intermediate
events stay inside the window and preserve the register. -/
def stableRegisterWindow (r first last : Nat) : Bool :=
  kernel.code.zipIdx.all (fun p => !decide (inRegisterWindow first last p.2) ||
    stableWindowInstr r first last p.2 p.1)

private theorem stable_code {r first last : Nat} (h : stableRegisterWindow r first last = true)
    {pc : Nat} {ins : Instr} (hp : inRegisterWindow first last pc)
    (hc : kernel.code[pc]? = some ins) :
    stableWindowInstr r first last pc ins = true := by
  have hAt := List.all_eq_true.mp h (ins, pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  simpa only [decide_eq_true hp, Bool.not_true, Bool.false_or] using hAt

variable {L : Launch} {g r first last : Nat}

private theorem stable_tau {t u : TState} (hChecked : stableRegisterWindow r first last = true)
    (ht : inRegisterWindow first last t.pc) (hTau : Tau kernel Assumptions.all L g t u) :
    inRegisterWindow first last u.pc ∧ u.regs r = t.regs r := by
  unfold Tau out at hTau
  split at hTau
  · cases hTau
  split at hTau
  · cases hTau
  rename_i ins hc
  have hAudit := stable_code hChecked ht hc
  by_cases hStop : t.pc = last
  · have ⟨hg, hl⟩ : ins.guard.isNone = true ∧ ins.op.isLocal = false := by
      simpa only [stableWindowInstr, ite_eq_left hStop, Bool.and_eq_true,
        Bool.not_eq_true'] using hAudit
    have hg' : ins.guard = none := Option.isNone_iff_eq_none.mp hg
    simp [hg', hl, guardHolds, pure, Except.pure] at hTau
  · simp only [stableWindowInstr, ite_eq_right hStop, Bool.and_eq_true] at hAudit
    obtain ⟨hClosed, hReg⟩ := hAudit
    split at hTau
    · cases hTau
    · rename_i hg
      cases hTau
      have hg' : ins.guard.isSome = true := by
        cases hGuard : ins.guard
        · simp [hGuard, guardHolds, pure, Except.pure] at hg
        · rfl
      exact ⟨control_fallthrough hClosed hg', rfl⟩
    split at hTau
    · rename_i hLocal
      split at hTau
      · rename_i v hv
        cases hTau
        have hf := local_frame hv
        have hn : r ∉ writesRegs ins.op := by
          simpa only [hLocal, ite_true, decide_eq_true_eq] using hReg
        exact ⟨control_local_step rfl hClosed hf, hf.regs r hn⟩
      · cases hTau
    · cases hTau

private theorem stable_locals {t u : TState} (hChecked : stableRegisterWindow r first last = true)
    (ht : inRegisterWindow first last t.pc)
    (hTau : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) :
    inRegisterWindow first last u.pc ∧ u.regs r = t.regs r := by
  induction hTau with
  | refl => exact ⟨ht, rfl⟩
  | tail _ hStep ih =>
    obtain ⟨hPos, hReg⟩ := stable_tau hChecked ih.1 hStep
    exact ⟨hPos, hReg.trans ih.2⟩

/-- Local steps remain in the audited register window until its final event. -/
theorem local_path_in_register_window {t u : TState}
    (hChecked : stableRegisterWindow r first last = true) (ht : inRegisterWindow first last t.pc)
    (hTau : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) :
    inRegisterWindow first last u.pc :=
  (stable_locals hChecked ht hTau).1

private theorem stable_return {t u : TState} {e : Event}
    (hChecked : stableRegisterWindow r first last = true) (ht : inRegisterWindow first last t.pc)
    (he : EStep kernel Assumptions.all L g t e (some u)) (hTag : e.pc ≠ last)
    : inRegisterWindow first last u.pc ∧ u.regs r = t.regs r := by
  obtain ⟨ins, hc, hLocal, hf⟩ := estep_event_source he
  have hStop : t.pc ≠ last := (estep_source_pc he) ▸ hTag
  have hAudit := stable_code hChecked ht hc
  have hReg : preservesReg r ins.op = true := by
    simp only [stableWindowInstr, ite_eq_right hStop, Bool.and_eq_true, hLocal, Bool.false_eq_true,
      ite_false] at hAudit
    exact hAudit.2
  refine ⟨?_, callbackFrame_fires (eventTmpl_preserves_reg hReg) hf⟩
  rcases (estep_return_pc he (fun _ _ _ h => local_frame h)).2 with h | h
  · exact h ▸ ht
  · rw [h]
    rcases ht with ⟨hl, hh⟩
    exact ⟨by omega, by omega⟩

private theorem return_before_window_end {L : Launch} {g last : Nat}
    {t u : TState} {ins : Instr} {e : Event}
    (hc : kernel.code[last - 1]? = some ins) (hLocal : ins.op.isLocal = true)
    (hLt : t.pc < last) (he : EStep kernel Assumptions.all L g t e (some u)) :
    u.pc < last := by
  rcases (estep_return_pc he (fun _ _ _ h => local_frame h)).2 with h | h
  · exact h ▸ hLt
  · by_contra! hEnd
    have hEq : t.pc = last - 1 := by omega
    obtain ⟨op, hCode, hl, _⟩ := estep_event_source he
    rw [hEq] at hCode
    obtain rfl := Option.some.inj (hc.symm.trans hCode)
    rw [hLocal] at hl
    cases hl

/-- A run sees its selected event from a local suffix starting before the window's end.
Intermediate events and that suffix's starting state preserve the register. -/
theorem register_at_event_in_window {t : TState} {e : Event} {before tail : List Event}
    {o : Option TState} {ins : Instr} (hChecked : stableRegisterWindow r first last = true)
    (hc : kernel.code[last - 1]? = some ins) (hLocal : ins.op.isLocal = true)
    (hFirst : first ≤ t.pc) (hLast : t.pc < last) (hPrev : ∀ f ∈ before, f.pc ≠ last)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ v u q, first ≤ v.pc ∧ v.pc < last ∧ v.regs r = t.regs r ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) v u ∧
      EStep kernel Assumptions.all L g u e q := by
  induction before generalizing t with
  | nil =>
    change Run kernel Assumptions.all L g t (e :: tail) o at hRun
    cases hRun with
    | step hTau hStep _ => exact ⟨_, _, _, hFirst, hLast, rfl, hTau, hStep⟩
    | last hTau hStep => exact ⟨_, _, _, hFirst, hLast, rfl, hTau, hStep⟩
  | cons f before ih =>
    change Run kernel Assumptions.all L g t (f :: (before ++ e :: tail)) o at hRun
    generalize hList : f :: (before ++ e :: tail) = events at hRun
    cases hRun with
    | nil => cases hList
    | step hTau hStep hTail =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hList
      obtain ⟨hPos, hReg⟩ := stable_locals hChecked ⟨hFirst, hLast.le⟩ hTau
      have hNotLast := hPrev f (by simp)
      have hSource := estep_source_pc hStep
      have hBeforeEnd : _ < last := lt_of_le_of_ne hPos.2 (hSource ▸ hNotLast)
      obtain ⟨hPos', hReg'⟩ := stable_return hChecked hPos hStep hNotLast
      have hBeforeEnd' := return_before_window_end hc hLocal hBeforeEnd hStep
      obtain ⟨v, u, o, hv, hv', hreg, hLocalSuffix, hChosen⟩ :=
        ih hPos'.1 hBeforeEnd' (fun f hf => hPrev f (List.mem_cons_of_mem _ hf)) hTail
      exact ⟨v, u, o, hv, hv', hreg.trans (hReg'.trans hReg), hLocalSuffix, hChosen⟩
    | last =>
      have hNil := (List.cons.inj hList).2
      simp at hNil

/-- A local step into a position with no branch edge is its predecessor's fallthrough. -/
theorem tau_step_before_non_target {L : Launch} {g : Nat} {v u : TState}
    (hTau : Tau kernel Assumptions.all L g v u) (hNoBranch : kernel.branchTarget u.pc = false) :
    u.pc = v.pc + 1 := by
  unfold Tau out at hTau
  split at hTau
  · cases hTau
  split at hTau
  · cases hTau
  rename_i ins hc
  split at hTau
  · cases hTau
  · cases hTau
    rfl
  split at hTau
  · split at hTau
    · rename_i w hw
      cases hTau
      exact LocalFrame.pc_succ hc (local_frame hw) hNoBranch
    · cases hTau
  · cases hTau

/-- A selected end event reached across a stable register window fires immediately
after the final local instruction if no branch targets the event. -/
theorem register_before_window_end {t : TState} {e : Event} {before tail : List Event}
    {o : Option TState} {ins : Instr} (hChecked : stableRegisterWindow r first last = true)
    (hc : kernel.code[last - 1]? = some ins) (hLocal : ins.op.isLocal = true)
    (hNoBranch : kernel.branchTarget last = false) (hFirst : first ≤ t.pc) (hLast : t.pc < last)
    (hTag : e.pc = last) (hPrev : ∀ f ∈ before, f.pc ≠ last)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ v u q, v.pc = last - 1 ∧ v.regs r = t.regs r ∧
      Tau kernel Assumptions.all L g v u ∧ EStep kernel Assumptions.all L g u e q := by
  obtain ⟨v, u, q, hv, hv', hr, hTau, hStep⟩ :=
    register_at_event_in_window hChecked hc hLocal hFirst hLast hPrev hRun
  have hPos := (estep_source_pc hStep).symm.trans hTag
  cases hTau with
  | refl => exact (Nat.ne_of_lt hv' hPos).elim
  | @tail w z hPrefix hLastStep =>
    have hSucc := tau_step_before_non_target hLastStep (hPos ▸ hNoBranch)
    have hPc : w.pc = last - 1 := by omega
    have hReg := stable_locals hChecked ⟨hv, hv'.le⟩ hPrefix
    exact ⟨w, u, q, hPc, hReg.2.trans hr, hLastStep, hStep⟩

/-- Recover the actual continuation at the window's last event with every audited register
still at its starting value. -/
theorem resume_register_window_end {L : Launch} {g first last : Nat} {t : TState}
    {e : Event} {before tail : List Event} {o : Option TState} {rs : List Nat}
    (hChecked : ∀ r ∈ rs, stableRegisterWindow r first last = true)
    (hRegs : rs ≠ []) (hFirst : first ≤ t.pc) (hLast : t.pc ≤ last)
    (hTag : e.pc = last) (hPrev : ∀ f ∈ before, f.pc ≠ last)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ u, u.pc = last ∧ (∀ r ∈ rs, u.regs r = t.regs r) ∧
      Run kernel Assumptions.all L g u (e :: tail) o := by
  obtain ⟨r₀, _, hList⟩ := List.exists_cons_of_ne_nil hRegs
  have hAnchor : r₀ ∈ rs := by rw [hList]; simp
  induction before generalizing t with
  | nil =>
    change Run kernel Assumptions.all L g t (e :: tail) o at hRun
    cases hRun with
    | step hTau hStep hTail =>
      exact ⟨_, (estep_source_pc hStep).symm.trans hTag,
        fun r hr => (stable_locals (hChecked r hr) ⟨hFirst, hLast⟩ hTau).2,
        .step .refl hStep hTail⟩
    | last hTau hStep =>
      exact ⟨_, (estep_source_pc hStep).symm.trans hTag,
        fun r hr => (stable_locals (hChecked r hr) ⟨hFirst, hLast⟩ hTau).2, .last .refl hStep⟩
  | cons f before ih =>
    change Run kernel Assumptions.all L g t (f :: (before ++ e :: tail)) o at hRun
    generalize hListEvents : f :: (before ++ e :: tail) = events at hRun
    cases hRun with
    | nil => cases hListEvents
    | step hTau hStep hTail =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hListEvents
      have hNotLast := hPrev f (by simp)
      have hLoc := stable_locals (hChecked r₀ hAnchor) ⟨hFirst, hLast⟩ hTau
      have hRet := stable_return (hChecked r₀ hAnchor) hLoc.1 hStep hNotLast
      obtain ⟨u, hPc, hSaved, hTail⟩ :=
        ih hRet.1.1 hRet.1.2 (fun f hf => hPrev f (List.mem_cons_of_mem _ hf)) hTail
      refine ⟨u, hPc, fun r hr => ?_, hTail⟩
      exact (hSaved r hr).trans ((stable_return (hChecked r hr) hLoc.1 hStep hNotLast).2.trans
        (stable_locals (hChecked r hr) ⟨hFirst, hLast⟩ hTau).2)
    | last =>
      have hNil := (List.cons.inj hListEvents).2
      simp at hNil

/-- A run can leave an audited window only after its final event. -/
theorem event_before_window_exit {t : TState} {e : Event} {before tail : List Event}
    {o : Option TState} (hChecked : stableRegisterWindow r first last = true)
    (hStart : inRegisterWindow first last t.pc) (hPrev : ∀ f ∈ before, f.pc ≠ last)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    e.pc ≤ last := by
  induction before generalizing t with
  | nil =>
    change Run kernel Assumptions.all L g t (e :: tail) o at hRun
    cases hRun with
    | step hTau hStep _ =>
      rw [estep_source_pc hStep]
      exact (stable_locals hChecked hStart hTau).1.2
    | last hTau hStep =>
      rw [estep_source_pc hStep]
      exact (stable_locals hChecked hStart hTau).1.2
  | cons f before ih =>
    change Run kernel Assumptions.all L g t (f :: (before ++ e :: tail)) o at hRun
    generalize hList : f :: (before ++ e :: tail) = events at hRun
    cases hRun with
    | nil => cases hList
    | step hTau hStep hTail =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hList
      have hPosition := (stable_locals hChecked hStart hTau).1
      have hReturn := (stable_return hChecked hPosition hStep (hPrev f (by simp))).1
      exact ih hReturn (fun f hf => hPrev f (List.mem_cons_of_mem _ hf)) hTail
    | last =>
      have hNil := (List.cons.inj hList).2
      simp at hNil

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
