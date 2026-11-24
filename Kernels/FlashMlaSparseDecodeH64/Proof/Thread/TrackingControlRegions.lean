-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.LocalRuleFrame
public import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # Control regions of concrete runs across dismissed data states -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow PTX.EventFrame

variable {inRegion : Nat → Prop} [DecidablePred inRegion]

/-- Successful branch, fallthrough and skip destinations stay in the region. -/
def closesControlRegion (inRegion : Nat → Prop) [DecidablePred inRegion]
    (pc : Nat) (ins : Instr) : Bool :=
  match ins.op with
  | .bra dst _ => decide (inRegion dst) && (ins.guard.isNone || decide (inRegion (pc + 1)))
  | .brx _ ds _ => decide (inRegion (pc + 1)) && ds.all fun dst => decide (inRegion dst)
  | _ => decide (inRegion (pc + 1))

/-- The frozen code is closed on each position in the region. -/
def controlRegionClosed (inRegion : Nat → Prop) [DecidablePred inRegion] : Bool :=
  kernel.code.zipIdx.all (fun p => !decide (inRegion p.2) || closesControlRegion inRegion p.2 p.1)

private theorem audited_instruction (hClosed : controlRegionClosed inRegion = true)
    {pc : Nat} {ins : Instr} (hp : inRegion pc) (hc : kernel.code[pc]? = some ins) :
    closesControlRegion inRegion pc ins = true := by
  have ha := List.all_eq_true.mp hClosed (ins, pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  simpa only [decide_eq_true hp, Bool.not_true, Bool.false_or] using ha

theorem control_fallthrough {pc : Nat} {ins : Instr}
    (h : closesControlRegion inRegion pc ins = true)
    (hg : ins.guard.isSome = true) : inRegion (pc + 1) := by
  cases hop : ins.op <;>
    simp only [closesControlRegion, hop, Bool.and_eq_true, decide_eq_true_eq] at h
  case bra d flag =>
    cases hguard : ins.guard <;> simp_all
  all_goals first | exact h.1 | exact h

theorem control_local_step {pc : Nat} {ins : Instr} {t u : TState}
    (hpc : t.pc = pc) (h : closesControlRegion inRegion pc ins = true)
    (hf : LocalFrame ins.op t u) :
    inRegion u.pc := by
  rcases hf.pc with he | he
  · rw [he, hpc]
    cases op : ins.op <;>
      simp only [closesControlRegion, op, nextPc, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    all_goals first | exact h.1 | exact h
  · cases op : ins.op <;> simp [op, BrxTarget, closesControlRegion] at h he
    exact h.2 _ he

variable (hClosed : controlRegionClosed inRegion = true)
include hClosed

/-- One actual local step stays in a closed control region. -/
theorem control_region_tau {L : Launch} {g : Nat} {t u : TState} (ht : inRegion t.pc)
    (hu : Tau kernel Assumptions.all L g t u) : inRegion u.pc := by
  unfold Tau out at hu
  split at hu
  · cases hu
  split at hu
  · cases hu
  rename_i ins hc
  have ha := audited_instruction hClosed ht hc
  split at hu
  · cases hu
  · rename_i hg
    cases hu
    apply control_fallthrough ha
    cases hguard : ins.guard
    · rw [hguard] at hg
      change Except.ok true = Except.ok false at hg
      cases hg
    · rfl
  split at hu
  · split at hu
    · rename_i u' h
      cases hu
      exact control_local_step rfl ha (local_frame h)
    · cases hu
  · cases hu

private theorem locals_outside {L : Launch} {g : Nat} {t u : TState} (ht : inRegion t.pc)
    (hu : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) :
    inRegion u.pc := by
  induction hu with
  | refl => exact ht
  | tail _ h ih => exact control_region_tau hClosed ih h

/-- A returning actual event stays in a closed control region. -/
theorem control_region_event {L : Launch} {g : Nat} {t u : TState} {e : Event} (ht : inRegion t.pc)
    (he : EStep kernel Assumptions.all L g t e (some u)) :
    inRegion u.pc := by
  obtain ⟨ins, hc, hlocal, _⟩ := estep_event_source he
  have ha := audited_instruction hClosed ht hc
  rcases (estep_return_pc he (fun _ _ _ h => local_frame h)).2 with h | h
  · exact h ▸ ht
  · rw [h]
    cases hop : ins.op <;>
      simp only [hop, closesControlRegion, Bool.and_eq_true, decide_eq_true_eq] at ha
    case bra dst uni =>
      rw [hop] at hlocal
      change true = false at hlocal
      cases hlocal
    all_goals first | exact ha.1 | exact ha

/-- Every event of a run starting in an audited closed region stays in that region. -/
theorem run_in_control_region {L : Launch} {g : Nat} {t : TState} {events : List Event}
    {o : Option TState} (ht : inRegion t.pc) (hr : Run kernel Assumptions.all L g t events o) :
    ∀ e ∈ events, inRegion e.pc := by
  induction hr with
  | nil => simp
  | step hTau hStep _ ih =>
    have hu := locals_outside hClosed ht hTau
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rwa [estep_source_pc hStep]
    · exact ih (control_region_event hClosed hu hStep) e hm
  | last hTau hStep =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    rw [estep_source_pc hStep]
    exact locals_outside hClosed ht hTau

/-- Once a concrete run issues an event in a closed control region, its remaining
events stay there even when the role's data guards no longer follow the trace. -/
theorem later_in_control_region {L : Launch} {g : Nat} {t : TState} {pre events : List Event}
    {first : Event} {o : Option TState} (hpc : inRegion first.pc)
    (hRun : Run kernel Assumptions.all L g t (pre ++ first :: events) o) :
    ∀ e ∈ first :: events, inRegion e.pc := by
  induction pre generalizing t with
  | nil =>
    cases hRun with
    | step _ he hr =>
      intro e hem
      rcases List.mem_cons.mp hem with rfl | hem
      · exact hpc
      · have hp := control_region_event hClosed ((estep_source_pc he) ▸ hpc) he
        exact run_in_control_region hClosed hp hr e hem
    | last _ _ =>
      intro e he
      obtain rfl := List.mem_singleton.mp he
      exact hpc
  | cons head tail ih =>
    generalize hlist : (head :: tail) ++ first :: events = all at hRun
    cases hRun with
    | nil => simp at hlist
    | step _ _ hr =>
      simp only [List.cons_append, List.cons.injEq] at hlist
      obtain ⟨_, rfl⟩ := hlist
      exact ih hr
    | last _ _ => simp at hlist

/-- The region reached by one event also bounds every later event of its thread. -/
theorem later_event_in_control_region {L : Launch} {mem0 : Mem0} {X : Execution} {g i j : Nat}
    {early late : Event} (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (he : X.get (g, i) = some early) (hl : X.get (g, j) = some late) (hij : i < j)
    (hStart : inRegion early.pc) :
    inRegion late.pc := by
  have hi := PTX.len_of_get he
  have hSplit := List.take_append_drop i (X.tr g)
  rw [List.drop_eq_getElem_cons hi, (List.getElem?_eq_some_iff.mp he).2] at hSplit
  obtain ⟨o, hr⟩ := hX.thr g hg
  rw [← hSplit] at hr
  have hmem : late ∈ (X.tr g).drop (i + 1) := by
    apply List.mem_of_getElem? (i := j - (i + 1))
    simpa only [List.getElem?_drop, Nat.add_sub_of_le (Nat.succ_le_of_lt hij)] using
      (show (X.tr g)[j]? = some late from hl)
  exact later_in_control_region hClosed hStart hr late (.tail early hmem)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
