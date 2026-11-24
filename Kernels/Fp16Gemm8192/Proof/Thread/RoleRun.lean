-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderArrivals
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCommits
public import Lemmas.Flow.RunInv
public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Invariants along a thread's run, by role

A thread runs the prologue and then one role. The prologue polls, arrives on, commits to and
copies to no object (`Quiet`), and a role's step leads to a state of the same role
(`next_of_loader`, `next_of_mma`, `next_of_sched`, `next_of_cons`). So a run invariant of one role
is
stated as `Quiet` in the prologue, the role's relation in its states and `True` in the other
roles, and proved with `Code.run_inv`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- No poll, arrival, commit, copy or cancellation request on any object among the events. -/
def Quiet (es : List Event) : Prop :=
  ∀ m, okPolls m es = 0 ∧ arrivals m es = 0 ∧ es.countP (commitsTo m) = 0 ∧
    es.countP (issuesTo m) = 0 ∧ es.countP (clcIssuesTo m) = 0

theorem quiet_nil : Quiet [] := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Quiet.snoc {es : List Event} {e : Event} (h : Quiet es)
    (he : ∀ m, okPoll m e = false ∧ arrivesOn m e = false ∧ commitsTo m e = false ∧
      issuesTo m e = false ∧ clcIssuesTo m e = false) : Quiet (es ++ [e]) := by
  intro m
  obtain ⟨h1, h2, h3, h4, h5⟩ := h m
  obtain ⟨e1, e2, e3, e4, e5⟩ := he m
  rw [okPolls_snoc, arrivals_snoc, commits_snoc, issues_snoc, clcIssues_snoc]
  simp [h1, h2, h3, h4, h5, e1, e2, e3, e4, e5]

variable {L : Launch} {g : Nat}

/-- The prologue's `init` instructions are not cancellation requests (decided on the code). -/
theorem Prologue.init_clcOp : ∀ i : Fin 18,
    (kernel.code[(Prologue.Site.init i).pc]?).map (fun ins => clcOp ins.op) ≠ some true := by
  table_decide

/-- No prologue instruction is a cancellation request. -/
theorem Prologue.code_clcOp (s : Prologue.Site) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : clcOp ins.op = false := by
  cases s with
  | init i =>
    have h := Prologue.init_clcOp i
    rw [hc] at h
    simpa using h
  | _ => code_at hc; subst hc; rfl

/-- The prologue's events touch no object count. -/
theorem Prologue.fires_quiet {p : Prologue.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[p.site.pc]? = some ins)
    (hf : Fires p.site.pc (eventTmpl Prod L g t ins.op) e o) (m : Loc) :
    okPoll m e = false ∧ arrivesOn m e = false ∧ commitsTo m e = false ∧
      issuesTo m e = false ∧ clcIssuesTo m e = false :=
  ⟨okPoll_of_notPoll (Prologue.code_notPoll _ hc) hf,
    arrivesOn_of_arriveOp (Prologue.code_arriveOp _ hc) hf,
    commitsTo_of_notCommit (Prologue.notCommit_fires _ hc hf),
    issuesTo_notTensor (fires_notTensor (eventTmpl_notTensor (Prologue.code_tensorOp _ hc)) hf),
    clcIssuesTo_of_op (Prologue.code_clcOp _ hc) hf⟩

theorem next_of_loader {l : Loader.D} {e : Event} {d' : ThreadD}
    (hn : (code L g).next (.inr (.loader l)) e = some (some d')) :
    ∃ l', Loader.next L g l e = some (some l') ∧ d' = .inr (.loader l') := by
  change (Loader.next L g l e).map
    (Option.map (Sum.inr ∘ Prologue.Role.loader : Loader.D → ThreadD)) = _ at hn
  cases h : Loader.next L g l e with
  | none => rw [h] at hn; cases hn
  | some r => rw [h] at hn; cases r <;> simp at hn; exact ⟨_, rfl, hn.symm⟩

theorem next_of_mma {m : Mma.D} {e : Event} {d' : ThreadD}
    (hn : (code L g).next (.inr (.mma m)) e = some (some d')) :
    ∃ m', Mma.next L g m e = some (some m') ∧ d' = .inr (.mma m') := by
  change (Mma.next L g m e).map
    (Option.map (Sum.inr ∘ Prologue.Role.mma : Mma.D → ThreadD)) = _ at hn
  cases h : Mma.next L g m e with
  | none => rw [h] at hn; cases hn
  | some r => rw [h] at hn; cases r <;> simp at hn; exact ⟨_, rfl, hn.symm⟩

theorem next_of_sched {s : Scheduler.D} {e : Event} {d' : ThreadD}
    (hn : (code L g).next (.inr (.sched s)) e = some (some d')) :
    ∃ s', Scheduler.next L g s e = some (some s') ∧ d' = .inr (.sched s') := by
  change (Scheduler.next L g s e).map
    (Option.map (Sum.inr ∘ Prologue.Role.sched : Scheduler.D → ThreadD)) = _ at hn
  cases h : Scheduler.next L g s e with
  | none => rw [h] at hn; cases hn
  | some r => rw [h] at hn; cases r <;> simp at hn; exact ⟨_, rfl, hn.symm⟩

theorem next_of_cons {c : Consumer.D} {e : Event} {d' : ThreadD}
    (hn : (code L g).next (.inr (.cons c)) e = some (some d')) :
    ∃ c', Consumer.next L g c e = some (some c') ∧ d' = .inr (.cons c') := by
  change (Consumer.next L g c e).map
    (Option.map (Sum.inr ∘ Prologue.Role.cons : Consumer.D → ThreadD)) = _ at hn
  cases h : Consumer.next L g c e with
  | none => rw [h] at hn; cases hn
  | some r => rw [h] at hn; cases r <;> simp at hn; exact ⟨_, rfl, hn.symm⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
