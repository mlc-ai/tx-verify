-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Scheduler
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The no-claim exit facts of the scheduler and the loader: definitions

A scheduler or a loader leaves its task loop only after a query of a CLC response that names no
first CTA (`NoClaimQ`), or after an election that left it unelected (`ElectOut`). The definitions
sit below the interface, which states the facts for every thread (`ThreadFacts.sched_exit_query`
and `ThreadFacts.loader_exit_query`); they are conjuncts of the scheduler's and the loader's run
invariants (`Scheduler.Run`, `LoaderTasks.Counts`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Whether an instruction is `exit`. -/
def exitOp : Op → Bool
  | .exit => true
  | _ => false

/-- The kernel has no `exit` instruction; its threads leave through `ret` (decided on the
code). -/
theorem kernel_exit_pcs : OpPcs kernel.code exitOp [] = true :=
  OpPcsFast.opPcs (by decide +kernel)

/-- No instruction of the kernel is `exit`. -/
theorem not_exit {pc : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins) :
    ins.op ≠ .exit := fun h => by
  simpa using OpPcs.mem kernel_exit_pcs hc (by rw [h]; rfl)

/-- The trace has a query of a CLC response that names no first CTA. -/
def NoClaimQ (es : List Event) : Prop :=
  ∃ (i : Nat) (e : Event), es[i]? = some e ∧ ∃ q r, e.kind = .clcQuery q r ∧ ¬ Loader.claims r

/-- The trace has an election whose leader is not the lane of thread `g`. -/
def ElectOut (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∃ (i : Nat) (e : Event), es[i]? = some e ∧ ∃ x y leader, e.kind = .elect x y leader ∧
    leader ≠ laneOf L g

theorem NoClaimQ.append {es : List Event} (e : Event) (h : NoClaimQ es) :
    NoClaimQ (es ++ [e]) := by
  obtain ⟨i, e', hi, hq⟩ := h
  refine ⟨i, e', ?_, hq⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]
  exact hi

theorem ElectOut.append {L : Launch} {g : Nat} {es : List Event} (e : Event)
    (h : ElectOut L g es) : ElectOut L g (es ++ [e]) := by
  obtain ⟨i, e', hi, hq⟩ := h
  refine ⟨i, e', ?_, hq⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]
  exact hi

theorem noClaimQ_snoc {es : List Event} {e : Event} {q : _} {r : ClcResponse}
    (hk : e.kind = .clcQuery q r) (hr : ¬ Loader.claims r) : NoClaimQ (es ++ [e]) :=
  ⟨es.length, e, by simp, q, r, hk, hr⟩

namespace Scheduler

/-- The scheduler's exit-stage facts along its run: its exit stage follows a no-claim query or an
election that left it unelected, and it acknowledges or fences a no-CTA value only after such a
query. -/
def ExitQ (L : Launch) (g : Nat) (s : D) (es : List Event) : Prop :=
  ((s.site = .exitArrive ∨ s.site = .exitWait ∨ s.site = .exit) →
    NoClaimQ es ∨ ElectOut L g es) ∧
  ((s.site = .clcFence ∨ s.site = .ack) → s.x = Loader.none32 → NoClaimQ es)

end Scheduler

namespace Loader

/-- The loader's exit facts along its run: its drain and exit stages come after a query that names
no first CTA (or after its election left it unelected). -/
def ExitQ (L : Launch) (g : Nat) (l : D) (es : List Event) : Prop :=
  ((l.site = .exitArrive ∨ l.site = .exitWait ∨ l.site = .exit ∨ ∃ i, l.site = .drain i) →
    NoClaimQ es ∨ ElectOut L g es) ∧
  ((l.site = .clcFence ∨ l.site = .ack) → l.x = Loader.none32 → NoClaimQ es)

end Loader

end
end PTX.Kernels.Fp16Gemm8192.Proof
