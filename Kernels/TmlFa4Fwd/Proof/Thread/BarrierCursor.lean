-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX

/-- Advance the ordinal of an observed named-barrier ID. -/
def advanceBarrierCursor (cursor : Nat → Nat) (e : Event) (id : Nat) : Nat :=
  cursor id + if Execution.isBarId id e then 1 else 0

/-- A cursor updated by an event predicate counts those events in every prefix. -/
theorem foldEventCount {σ : Type} (cursor : σ → Nat) (advance : σ → Event → σ)
    (mark : Event → Bool)
    (step : ∀ s e, cursor (advance s e) = cursor s + if mark e then 1 else 0)
    (es : List Event) (s : σ) :
    cursor (es.foldl advance s) = cursor s + es.countP mark := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, step, List.countP_cons]
    cases mark e <;> simp
    omega

/-- A role that records barrier observations counts them exactly at each event boundary. -/
theorem foldBarrierCursor {σ : Type} (cursor : σ → Nat → Nat) (advance : σ → Event → σ)
    (step : ∀ s e, cursor (advance s e) = advanceBarrierCursor (cursor s) e)
    (es : List Event) (s : σ) (id : Nat) :
    cursor (es.foldl advance s) id = cursor s id + es.countP (Execution.isBarId id) := by
  exact foldEventCount (fun s => cursor s id) advance (Execution.isBarId id)
    (fun s e => congrFun (step s e) id) es s

end PTX.Kernels.TmlFa4Fwd.Thread
