-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Thread.Run
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The interface between the thread layer and the layers above

The layers above the thread layer see the threads only through `ThreadFacts`: what each
thread does along its own events, stated with the abstract state its machine (`code`) is in
before an event (`stateAt`). The thread layer proves `ThreadFacts` (`Thread/Facts.lean`). -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The abstract state of thread `g` before its `k`-th event. -/
abbrev stateAt (L : Launch) (A B N : Nat) (X : Execution) (g k : Nat) :
    Option (Option Site) :=
  Frame.stateAt (code L A B N) X g k

/-- The machines are sound along every thread of a launch satisfying the precondition. -/
theorem sound_all {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0}
    (hpre : Pre L A B N x mem0) : ∀ g < L.threads, (code L A B N g).Sound :=
  fun _ hg => sound hpre hg

/-- Per-thread facts of an execution. -/
structure ThreadFacts (L : Launch) (A B N : Nat) (X : Execution) : Prop where
  /-- Every thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (code L A B N) X
  /-- The events a thread has performed before a followed state are the state's `RunFacts`. -/
  run_facts : ∀ {g k : Nat} {d : Site}, g < L.threads → stateAt L A B N X g k = some (some d) →
    RunFacts A B N g d ((X.tr g).take k)
  /-- An event at a followed state is the event of the state's site. -/
  site_event : ∀ {g k : Nat} {e : Event} {d : Site}, X.get (g, k) = some e →
    stateAt L A B N X g k = some (some d) → SiteEvent A B g d e
  /-- The machine stops only on the read of four bytes of `A[g]` that are no word, and the
  event it stops at is the undefined behaviour after it. -/
  dead_ub : ∀ {g k : Nat} {e : Event}, X.get (g, k) = some e → stateAt L A B N X g k = none →
    (∃ pc f, e = ⟨pc, .ub f⟩) ∧ g < N ∧
      ∃ bs, bs.length = 4 ∧ (∀ v, rebuild 3 bs ≠ .ok v) ∧ (X.tr g).take k = [ncE A g bs]

end
end PTX.Kernels.CopyLdg.Proof
