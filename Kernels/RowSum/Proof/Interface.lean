-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Thread.Events
public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.PlainStep

@[expose] public section

/-! # The interface between the thread layer and the layers above

The layers above the thread layer see the threads only through `ThreadFacts`: what each
thread does along its own events, stated with the abstract state its machine (`codes`) is in
before an event (`stateAt`). The thread layer proves `ThreadFacts` (`Thread/Facts.lean`). -/

namespace PTX.Kernels.RowSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

/-- The machines of the threads. -/
abbrev codes (L : Launch) (A B M K : Nat) (g : Nat) : Flow.Code kernel Prod L g :=
  code L A B M K g

/-- The abstract state of thread `g` before its `k`-th event: `some none` when the machine no
longer follows the thread, `none` after an event into a dead state. -/
abbrev stateAt (L : Launch) (A B M K : Nat) (X : Execution) (g k : Nat) :
    Option (Option ThreadD) :=
  Frame.stateAt (codes L A B M K) X g k

/-- Every event is the event of its state's site, at the position the state's counter gives:
the read of element `k` of row `g`, the store of the accumulator at position `K`, or the exit. -/
def EventAt (A B M K g k : Nat) (d : ThreadD) (e : Event) : Prop :=
  (d.site = .load ∧ g < M ∧ k < K ∧ d.i = k ∧ ∃ bs, e = rdE A K g k bs) ∨
  (d.site = .store ∧ g < M ∧ k = K ∧ d.i = K ∧ e = wrE B g d.a) ∨
  (d.site = .exit ∧ e = exE)

/-- Per-thread facts of an execution. -/
structure ThreadFacts (L : Launch) (A B M K : Nat) (x : Nat → ℝ) (X : Execution) : Prop where
  /-- Every launched thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (codes L A B M K) X
  /-- An event of a followed thread is its state's event. -/
  event : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → X.get (g, k) = some e →
    stateAt L A B M K X g k = some (some d) → EventAt A B M K g k d e
  /-- The machine stops only after a read whose bytes are not the launch content; the thread's
  next event is its undefined behaviour. -/
  dead : ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e →
    stateAt L A B M K X g k = none →
    ∃ pc f j bs, e = ⟨pc, .ub f⟩ ∧ k = j + 1 ∧ X.get (g, j) = some (rdE A K g j bs) ∧
      bs ≠ good x K g j
  /-- The accumulator of a followed thread is the sum of the elements it has read, when every
  read returned the launch content. -/
  value : ∀ {g k : Nat} {d : ThreadD}, g < L.threads →
    stateAt L A B M K X g k = some (some d) →
    (∀ j bs, X.get (g, j) = some (rdE A K g j bs) → bs = good x K g j) →
    d.a = accV x K g d.i
  /-- A thread of a row that exits has stored its accumulator at position `K`, which is the sum
  of its row when every read returned the launch content. -/
  exit_write : ∀ {g : Nat}, g < L.threads → g < M → (∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) →
    ∃ a, X.get (g, K) = some (wrE B g a) ∧
      ((∀ j bs, X.get (g, j) = some (rdE A K g j bs) → bs = good x K g j) →
        a = accV x K g K)

/-- Facts of the threads' machines, for a launch: every launched thread is simulated by its
machine, and no thread begins with a barrier. -/
structure CodeFacts (L : Launch) (A B M K : Nat) : Prop where
  sound : ∀ g < L.threads, (codes L A B M K g).Sound
  init_not_bar : ∀ g : Nat, ∀ ins,
    kernel.code[(codes L A B M K g).pc (codes L A B M K g).init]? = some ins →
      ins.op.isBar = false

end
end PTX.Kernels.RowSum.Proof
