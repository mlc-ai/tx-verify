-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources
public import Lemmas.Execution.EventFrameSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.LocalRuleFrame

@[expose] public section

/-! # The control region after the CTA initialization gate -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.EventFrame PTX.Proof

private def postGateOp (op : Op) : Bool :=
  !initOp op && match op with
  | .bra dst _ => decide (98 ≤ dst)
  | .brx _ ds _ => ds.all fun dst => decide (98 ≤ dst)
  | _ => true

set_option maxRecDepth 100000 in
private theorem postGate_code :
    (kernel.code.drop 98).all (postGateOp ·.op) = true := by
  decide +kernel

private theorem postGate_instruction {pc : Nat} {ins : Instr} (hp : 98 ≤ pc)
    (hc : kernel.code[pc]? = some ins) : postGateOp ins.op = true := by
  apply List.all_eq_true.mp postGate_code
  apply List.mem_of_getElem? (i := pc - 98)
  simpa only [List.getElem?_drop, Nat.add_sub_of_le hp] using hc

private theorem postGate_tau {L : Launch} {g : Nat} {t u : TState}
    (hloc : ∀ t op u, execLocalA Assumptions.all L g t op = .ok u → LocalFrame op t u)
    (ht : 98 ≤ t.pc) (hu : Tau kernel Assumptions.all L g t u) : 98 ≤ u.pc := by
  unfold Tau out at hu
  split at hu
  · cases hu
  split at hu
  · cases hu
  rename_i ins hc
  split at hu
  · cases hu
  · cases hu
    change 98 ≤ t.pc + 1
    omega
  split at hu
  · split at hu
    · rename_i u' hexec
      cases hu
      have hf := (hloc t ins.op u hexec).pc
      have ha := postGate_instruction ht hc
      rcases hf with hf | hf
      · rw [hf]
        cases hop : ins.op <;> simp only [hop, postGateOp, nextPc] at ha ⊢
        all_goals first | omega | simpa [initOp] using ha
      · cases hop : ins.op <;> simp [hop, BrxTarget, postGateOp, initOp] at ha hf
        exact ha _ hf
    · cases hu
  · cases hu

private theorem postGate_locals {L : Launch} {g : Nat} {t u : TState}
    (hloc : ∀ t op u, execLocalA Assumptions.all L g t op = .ok u → LocalFrame op t u)
    (ht : 98 ≤ t.pc) (hu : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) :
    98 ≤ u.pc := by
  induction hu with
  | refl => exact ht
  | tail _ h ih => exact postGate_tau hloc ih h

private theorem postGate_read {L : Launch} {g : Nat} {t u : TState} {e : Event}
    (ht : 98 ≤ t.pc) (hstep : EStep kernel Assumptions.all L g t e (some u))
    {m : Loc} {count : Nat} (hk : e.kind = .mbInit m count) : False := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source hstep
  have hop := postGate_instruction ht hc
  have hn : initOp ins.op = false := by
    unfold postGateOp at hop
    simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp hop).1
  exact notInit_of_op hn hf m count hk

/-- A concrete continuation after the initialization gate contains no initialization event.
This statement applies even to a continuation that the role machine stops following. -/
private theorem no_init_after_gate {L : Launch} {g : Nat} {t : TState} {events : List Event}
    {o : Option TState}
    (hloc : ∀ t op u, execLocalA Assumptions.all L g t op = .ok u → LocalFrame op t u)
    (ht : 98 ≤ t.pc) (hRun : Run kernel Assumptions.all L g t events o) :
    ∀ e ∈ events, ∀ m count, e.kind ≠ .mbInit m count := by
  induction hRun with
  | nil => simp
  | @step t t1 t2 e rest o hTau hstep _ ih =>
    have hpc := postGate_locals hloc ht hTau
    have hret := (estep_return_pc hstep hloc).2
    have ht' : 98 ≤ t2.pc := by omega
    intro e he m count hk
    rcases List.mem_cons.mp he with rfl | he
    · exact postGate_read hpc hstep hk
    · exact ih ht' e he m count hk
  | last _ hstep =>
    obtain ⟨_, _, hf⟩ := hstep
    intro e he m count hk
    obtain rfl := List.mem_singleton.mp he
    rcases fires_none_ends hf with ⟨_, huh⟩ | heq
    · rw [hk] at huh; cases huh
    · rw [hk] at heq; cases heq

/-- Once the actual instruction trace reaches the region after the initialization gate, its
remaining event list has no initializations, including the event at that position. -/
theorem no_init_from_later_event {L : Launch} {g : Nat} {t : TState}
    {pre events : List Event} {first : Event} {o : Option TState}
    (hpc : 98 ≤ first.pc)
    (hRun : Run kernel Assumptions.all L g t (pre ++ first :: events) o) :
    ∀ e ∈ first :: events, ∀ m count, e.kind ≠ .mbInit m count := by
  have hloc (t : TState) (op : Op) (u : TState)
      (h : execLocalA Assumptions.all L g t op = .ok u) : LocalFrame op t u :=
    local_frame h
  induction pre generalizing t with
  | nil =>
    cases hRun with
    | @step _ t1 t2 _ _ _ _ he hr =>
      have hp : 98 ≤ t1.pc := by rw [← estep_source_pc he]; exact hpc
      have hout := (estep_return_pc he hloc).2
      have ht2 : 98 ≤ t2.pc := by omega
      intro e h eLoc n hk
      rcases List.mem_cons.mp h with rfl | h
      · exact postGate_read hp he hk
      · exact no_init_after_gate hloc ht2 hr e h eLoc n hk
    | last _ he =>
      intro e he' m count hk
      obtain rfl := List.mem_singleton.mp he'
      obtain ⟨_, _, hf⟩ := he
      rcases fires_none_ends hf with ⟨_, hu⟩ | hx
      · rw [hk] at hu; cases hu
      · rw [hk] at hx; cases hx
  | cons head tail ih =>
    generalize hlist : (head :: tail) ++ first :: events = all at hRun
    cases hRun with
    | nil => simp at hlist
    | step _ _ hr =>
      simp only [List.cons_append, List.cons.injEq] at hlist
      obtain ⟨_, rfl⟩ := hlist
      exact ih hr
    | last _ _ => simp at hlist

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
