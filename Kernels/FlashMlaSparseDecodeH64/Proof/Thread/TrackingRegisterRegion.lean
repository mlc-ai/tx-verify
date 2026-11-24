-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterWindow

@[expose] public section

/-! # Register invariants of concrete execution in audited regions -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.EventFrame PTX.Proof

/-- A control successor in the inspected region, including a retry at the same event. -/
def entersRegion (active : Nat → Bool) (pc : Nat) (ins : Instr) : Bool :=
  active pc || active (pc + 1) ||
    match ins.op with
    | .bra dst _ => active dst
    | .brx _ ds _ => ds.any active
    | _ => false

/-- Each instruction that can reach the region already has and preserves the register
invariant, apart from explicitly inspected update sites. -/
def registerRegionChecked (r : Nat) (active : Nat → Bool) (updates : List Nat) : Bool :=
  kernel.code.zipIdx.all (fun (ins, pc) =>
    decide (pc ∈ updates) || !entersRegion active pc ins ||
      (active pc && (if ins.op.isLocal then decide (r ∉ writesRegs ins.op)
        else preservesReg r ins.op)))

private theorem register_region_instr {r pc : Nat} {active : Nat → Bool}
    {updates : List Nat} {ins : Instr}
    (hChecked : registerRegionChecked r active updates = true)
    (hCode : kernel.code[pc]? = some ins) (hOutside : pc ∉ updates)
    (hEnter : entersRegion active pc ins = true) :
    active pc = true ∧ (if ins.op.isLocal then decide (r ∉ writesRegs ins.op)
      else preservesReg r ins.op) = true := by
  have h := List.all_eq_true.mp hChecked (ins, pc) (List.mem_zipIdx_iff_getElem?.mpr hCode)
  simpa only [decide_eq_false hOutside, hEnter, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] using h

private theorem enters_stay {active : Nat → Bool} {pc : Nat} {ins : Instr}
    (h : active pc = true) : entersRegion active pc ins = true := by
  simp [entersRegion, h]

private theorem enters_next {active : Nat → Bool} {pc : Nat} {ins : Instr}
    (h : active (pc + 1) = true) : entersRegion active pc ins = true := by
  simp [entersRegion, h]

private theorem enters_local {active : Nat → Bool} {ins : Instr} {t u : TState}
    (hLocal : LocalFrame ins.op t u) (hRegion : active u.pc = true) :
    entersRegion active t.pc ins = true := by
  rcases hLocal.pc with h | h
  · cases hop : ins.op <;> simp_all [nextPc, entersRegion]
  · cases hop : ins.op <;> simp_all [BrxTarget, entersRegion, List.any_eq_true]
    exact Or.inr ⟨_, h, hRegion⟩

/-- A concrete local step preserves the audited register predicate, or uses an explicit update. -/
theorem register_region_tau {L : Launch} {g r : Nat} {active : Nat → Bool}
    {updates : List Nat} {property : Option Value → Prop} {t u : TState}
    (hAudit : registerRegionChecked r active updates = true)
    (hOld : active t.pc = true → property (t.regs r))
    (hUpdate : t.pc ∈ updates → active u.pc = true → property (u.regs r))
    (hTau : Tau kernel Assumptions.all L g t u) (hIn : active u.pc = true) :
    property (u.regs r) := by
  by_cases hu : t.pc ∈ updates
  · exact hUpdate hu hIn
  unfold Tau out at hTau
  split at hTau
  · cases hTau
  split at hTau
  · cases hTau
  rename_i ins hc
  split at hTau
  · cases hTau
  · cases hTau
    exact hOld (register_region_instr hAudit hc hu (enters_next hIn)).1
  split at hTau
  · rename_i hLocal
    split at hTau
    · rename_i v hv
      cases hTau
      have hf := local_frame hv
      obtain ⟨hBefore, hReg⟩ :=
        register_region_instr hAudit hc hu (enters_local hf hIn)
      simp only [hLocal, ite_true, decide_eq_true_eq] at hReg
      rw [hf.regs r hReg]
      exact hOld hBefore
    · cases hTau
  · cases hTau

/-- Returning from a recorded event preserves the audited register predicate. -/
theorem register_region_event {L : Launch} {g r : Nat} {active : Nat → Bool}
    {updates : List Nat} {property : Option Value → Prop} {t u : TState} {e : Event}
    (hAudit : registerRegionChecked r active updates = true)
    (hUpdatesLocal : ∀ pc ∈ updates, ∀ ins, kernel.code[pc]? = some ins →
      ins.op.isLocal = true)
    (hOld : active t.pc = true → property (t.regs r))
    (he : EStep kernel Assumptions.all L g t e (some u)) (hIn : active u.pc = true) :
    property (u.regs r) := by
  obtain ⟨ins, hc, hLocal, hf⟩ := estep_event_source he
  have hOutside : t.pc ∉ updates := by
    intro h
    rw [hUpdatesLocal t.pc h ins hc] at hLocal
    cases hLocal
  have hEnter : entersRegion active t.pc ins = true := by
    rcases (estep_return_pc he (fun _ _ _ h => local_frame h)).2 with h | h
    · exact enters_stay (h ▸ hIn)
    · exact enters_next (h ▸ hIn)
  obtain ⟨hBefore, hReg⟩ := register_region_instr hAudit hc hOutside hEnter
  simp only [hLocal, Bool.false_eq_true, ite_false] at hReg
  rw [callbackFrame_fires (eventTmpl_preserves_reg hReg) hf]
  exact hOld hBefore

/-- A local transition begins at a state with no pending fault. -/
theorem tau_fault_free {L : Launch} {g : Nat} {t u : TState}
    (h : Tau kernel Assumptions.all L g t u) :
    t.fault = none := by
  cases hFault : t.fault
  · rfl
  · simp [Tau, out, hFault] at h

/-- A local transition agrees with a one-instruction footprint evaluation. -/
theorem one_step_matches {L : Launch} {g : Nat} {t u v : TState}
    (h : Tau kernel Assumptions.all L g t u) (hRun : run kernel Assumptions.all L g 1 t = some v) :
    u = v := by
  have hStep := tauStep_iff.mpr h
  simpa [run, hStep] using hRun

/-- A finite list of exceptional sites can be checked to contain only local instructions. -/
theorem register_updates_local {updates : List Nat}
    (h : updates.all (fun pc => ((kernel.code[pc]?).map (·.op.isLocal)).getD true) = true) :
    ∀ pc ∈ updates, ∀ ins, kernel.code[pc]? = some ins → ins.op.isLocal = true := by
  intro pc hp ins hc
  have hAt := List.all_eq_true.mp h pc hp
  simpa only [hc, Option.map_some, Option.getD_some] using hAt

/-- Every concrete event source in a run satisfies an invariant preserved by the actual
local transitions and event callbacks. -/
theorem actual_event_invariant {L : Launch} {g : Nat} {t : TState} {events : List Event}
    {e : Event} {o : Option TState} {valid : TState → Prop}
    (hLocal : ∀ {a b}, valid a → Tau kernel Assumptions.all L g a b → valid b)
    (hEvent : ∀ {a b f}, valid a → EStep kernel Assumptions.all L g a f (some b) → valid b)
    (hStart : valid t) (hRun : Run kernel Assumptions.all L g t events o) (he : e ∈ events) :
    ∃ v q, valid v ∧ EStep kernel Assumptions.all L g v e q := by
  have localSteps {a b : TState} (ha : valid a)
      (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) a b) : valid b := by
    induction h with
    | refl => exact ha
    | tail _ h ih => exact hLocal ih h
  induction hRun with
  | nil => simp at he
  | step hTau hStep _ ih =>
    have hv := localSteps hStart hTau
    rcases List.mem_cons.mp he with rfl | hMem
    · exact ⟨_, _, hv, hStep⟩
    · exact ih (hEvent hv hStep) hMem
  | last hTau hStep =>
    obtain rfl := List.mem_singleton.mp he
    exact ⟨_, _, localSteps hStart hTau, hStep⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
