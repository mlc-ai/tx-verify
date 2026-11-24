-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

@[expose] public section

namespace PTX.CtaBarrier

/-! ## OBJ-CTA-BARRIER-STATE — named CTA barrier resources and generations

Statement: Each of the sixteen barrier resources of a CTA counts the distinct warps that arrive in
  its current generation. The generation completes when the requested number of warps has arrived,
  or when every warp that still has a live thread has arrived, and the resource then starts a new
  generation. A warp that arrives twice in one generation, or an arrival whose count differs from
  the count of the open generation, is a fault.

Defs: CtaBarrier.Slot, CtaBarrier.State, CtaBarrier.Error, CtaBarrier.Error.isFault,
  CtaBarrier.warps, CtaBarrier.target, CtaBarrier.warpLive, CtaBarrier.allArrived,
  CtaBarrier.complete, CtaBarrier.settle, CtaBarrier.arrive, CtaBarrier.exitThread

Source:
- §9.7.15.1 (named resources, warp arrivals, counts, reset)
- §9.7.14.7 (exit)

Direction: reading

Applies: The sixteen CTA barrier resources; sync/arrive completion, without reductions

Premises: An arrival represents all non-exited lanes of one warp reaching a barrier with matching
  operands. Thread/event matching and aligned-instruction requirements are checked separately.

Effect: Object-local resource transitions; faults are reported by ERR-CTA-BARRIER
  (`CtaBarFault`), and the executions are not removed. The bank is local to one CTA. An explicit
  count counts warp slots, including the slots of exited lanes in an arriving warp. An omitted or
  zero sync count waits for all non-exited warps. The instruction layer must reject zero for
  `bar.arrive`, which requires a nonzero operand. The actual arrivals determine the participating
  warps. A sync return must be linked to completion of its recorded generation by the execution
  layer. OBJ-CTA-BARRIER-SYNC uses checked source-event histories built from these resource
  operations.

Review: §9.7.15.1 gives meaning only to warps using "the same barrier name and thread count", and
  warns against a warp executing "more barrier{.cta} instructions than intended ... prior to the
  reset of the barrier". Both are faults: the model gives them no outcome, and an execution that
  issues one is unsafe.
-/

/-- One of the sixteen barrier resources of a CTA (§9.7.15.1): the number of its current
generation, the number of warp arrivals that generation requests, and the warps that have
arrived in it. -/
structure Slot where
  /-- The number of the current generation; completion increments it. -/
  generation : Nat := 0
  /-- Number of warp arrivals requested in the active generation. -/
  expected : Option Nat := none
  /-- The warps that have arrived in the current generation. -/
  arrived : Finset Nat := ∅
  deriving DecidableEq

/-- The barrier resources of one CTA together with the threads of the CTA that have exited. -/
structure State where
  /-- The resource with each barrier number. -/
  slots : Nat → Slot := fun _ => {}
  /-- The threads of the CTA that have exited. -/
  exited : Finset Nat := ∅

/-- The ways an update of the barrier resources fails. -/
inductive Error where
  | badId | badCount | badWarp | countMismatch | duplicateArrival | badExit
  deriving DecidableEq, Repr

/-- Faults of the resource caused by the arrivals a program performs. Invalid operands
(`badId`, `badCount`) are instruction faults of THREAD-BAR and never reach the resource;
`badWarp` and `badExit` mark records that do not describe actual warp arrivals or exits. -/
def Error.isFault : Error → Bool
  | .countMismatch | .duplicateArrival => true
  | .badId | .badCount | .badWarp | .badExit => false

def warps (block : Nat) : Nat := (block + 31) / 32

/-- Decode the thread-count operand, retaining a generic warp count. -/
def target (block : Nat) : Option Nat → Except Error Nat
  | none | some 0 => .ok (warps block)
  | some n =>
    if n < 2 ^ 32 ∧ n % 32 = 0 then .ok (n / 32)
    else .error .badCount

/-- A warp is live when at least one of its lanes is a non-exited CTA thread. -/
def warpLive (block : Nat) (exited : Finset Nat) (w : Nat) : Prop :=
  ∃ lane ∈ Finset.range 32, w * 32 + lane < block ∧ w * 32 + lane ∉ exited

instance (block : Nat) (exited : Finset Nat) (w : Nat) :
    Decidable (warpLive block exited w) := by
  unfold warpLive
  infer_instance

/-- Every still-live warp has arrived. -/
def allArrived (block : Nat) (exited : Finset Nat) (s : Slot) : Prop :=
  ∀ w ∈ Finset.range (warps block), warpLive block exited w → w ∈ s.arrived

instance (block : Nat) (exited : Finset Nat) (s : Slot) :
    Decidable (allArrived block exited s) := by
  unfold allArrived
  infer_instance

/-- Exit cannot invent missing participants beyond the CTA's actual warp slots. -/
def complete (block : Nat) (exited : Finset Nat) (s : Slot) : Bool :=
  match s.expected with
  | none => false
  | some n => decide (n ≤ s.arrived.card ∨
      (n ≤ warps block ∧ allArrived block exited s))

/-- Start a new generation of the resource if its current generation is complete. -/
def settle (block : Nat) (exited : Finset Nat) (s : Slot) : Slot :=
  if complete block exited s then { generation := s.generation + 1 } else s

/-- One warp's arrival at one named resource. The old generation identifies its wait. -/
def arrive (block : Nat) (s : State) (id warp : Nat) (count : Option Nat) :
    Except Error State := do
  unless id < 16 do throw .badId
  unless warp < warps block ∧
      warpLive block s.exited warp do throw .badWarp
  let n ← target block count
  let old := s.slots id
  if warp ∈ old.arrived then throw .duplicateArrival
  if let some k := old.expected then
    unless k = n do throw .countMismatch
  let new := settle block s.exited
    { old with expected := some n, arrived := insert warp old.arrived }
  return { s with slots := fun j => if j = id then new else s.slots j }

/-- Exit is visible to every resource of this CTA; it is not a barrier arrival. -/
def exitThread (block : Nat) (s : State) (g : Nat) : Except Error State := do
  unless g < block ∧ g ∉ s.exited do throw .badExit
  let exited := insert g s.exited
  return { exited, slots := fun id => settle block exited (s.slots id) }

end PTX.CtaBarrier
