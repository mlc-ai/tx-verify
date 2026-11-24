-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.MBarrierObject

@[expose] public section

namespace PTX.MBarrier

/-! ## OBJ-MBAR-PHASES — object histories and phase identities
Statement: Each mbarrier address has a history that lists the operations on it in the object's
  atomic order. A counter update belongs to the phase it changes and a successful wait to the
  completed phase it observed, and phase numbers are compared only within one lifetime of the
  object, which runs from an initialization to the next invalidation.

Defs: MBarrier.Record, MBarrier.stateBefore, MBarrier.phaseAt, MBarrier.observedAt,
  MBarrier.SameLifetime

Source:
- §9.7.15.16.3 (phases)
- §9.7.15.16.12 (init): "The primary and conditional phases are initialized to zero."
- §9.7.15.16.13 (inval)
- §9.7.15.16.19 (successful waits)

Direction: representation

Applies: The operation history of one mbarrier address

Premises: Each record names the unique instruction or asynchronous notification that performs the
  operation.

Effect: Object-local provenance stored in Execution.objects. Parity alone never identifies a
  completion. The list is the atomic operation order of this one object. It gives no global order
  of thread instructions or memory accesses. An initial opposite-parity poll has no observed phase.
  Initialization restarts phases at zero, so phase numbers identify a phase only together with the
  lifetime: positions with no invalidation between them (`SameLifetime`).
-/

/-- One entry of an object's history: the identity of the operation (a thread event or an
asynchronous notification), the operation, the object's reply, and the object fault it caused,
if any. -/
structure Record (ι : Type) where
  id : ι
  action : Action
  reply : Reply
  /-- Object UB is recorded, not removed from the set of executions. -/
  fault : Option Error := none
  deriving DecidableEq, Repr

/-- The object state before position `i` of the history: the state after the previous record,
or no valid object at the start. -/
def stateBefore (log : List (Record ι)) (i : Nat) : Option State :=
  if i = 0 then none else log[i - 1]?.bind (fun r => r.reply.state)

/-- The phase a counter update changes; absent before initialization. -/
def phaseAt (log : List (Record ι)) (i : Nat) : Option Nat :=
  (stateBefore log i).map (·.phase)

/-- The completed phase observed by a successful poll. -/
def observedAt (log : List (Record ι)) (i : Nat) : Option Nat :=
  log[i]?.bind (·.reply.completed)

/-- No invalidation lies strictly between positions `i` and `j`. -/
def SameLifetime (log : List (Record ι)) (i j : Nat) : Prop :=
  ∀ k s, i < k → k < j → log[k]? = some s → s.action ≠ .inval

/-! ## OBJ-MBAR-HISTORY — checked operations of one object
Statement: Every record of an object's history carries the reply that the object operations
  determine from the state before it, or an explicit object fault. A successful wait is matched
  only with the counter updates that precede it in the history and belong to the phase it
  observed, in the same lifetime.

Defs: MBarrier.RecordOk, MBarrier.RecordedHistory, MBarrier.CheckedLog, MBarrier.UpdateBeforeWait,
  MBarrier.InitBefore, MBarrier.Before

Source:
- §9.7.15.16.5–9 (phase completion, expect/complete transaction operations)
- §9.7.15.16.19 (wait observation)
- §9.7.15.16.4: "An mbarrier object must be invalidated to repurpose its memory for any purpose,
    including repurposing it for another mbarrier object."

Direction: reading

Applies: A per-object history over arbitrarily many phases

Premises: Records use distinct operation identities and each transition is the one OBJ-MBAR-STATE
  determines, or its explicit fault.

Effect: Validity and provenance predicates used by Consistent; object faults are kept in the history
  and rejected by safety. `InitBefore` names the initialization of an operation's own object
  lifetime: the successful initialization before it with no invalidation in between. A manual
  complete_tx changes the counter but is not a data transfer: copy visibility also requires that the
  observed update is the completed copy's own notification (`AsyncCopy.Notifies`,
  OBJ-MBAR-OBSERVE).
-/

/-- The ISA determines either a valid response or an explicit object fault. -/
def RecordOk (before : Option State) (r : Record ι) : Prop :=
  match perform before r.action with
  | .ok expected => r.reply = expected ∧ r.fault = none
  | .error fault => r.reply = ⟨before, none, none⟩ ∧ r.fault = some fault

/-- The records lead from the first state to the last, each record being a valid step
(`RecordOk`). -/
inductive RecordedHistory : Option State → List (Record ι) → Option State → Prop where
  | nil (s) : RecordedHistory s [] s
  | cons {s r rest t} : RecordOk s r → RecordedHistory r.reply.state rest t →
      RecordedHistory s (r :: rest) t

/-- A valid history of one address: the operation identities are distinct, and the records form a
sequence of valid steps that starts at a location without a valid object. -/
def CheckedLog (log : List (Record ι)) : Prop :=
  (log.map Record.id).Nodup ∧ ∃ last, RecordedHistory none log last

/-- A specific counter update belongs to the phase actually observed by this wait. -/
def UpdateBeforeWait (log : List (Record ι)) (update waiter : ι) : Prop :=
  ∃ i j r w phase,
    log[i]? = some r ∧ r.id = update ∧ r.fault = none ∧
    log[j]? = some w ∧ w.id = waiter ∧ w.fault = none ∧ w.reply.waited = some true ∧
    i < j ∧ phaseAt log i = some phase ∧ observedAt log j = some phase ∧ SameLifetime log i j

/-- `init` is the successful initialization of the object lifetime that `operation` belongs
to: it precedes the operation and no invalidation lies between them. -/
def InitBefore (log : List (Record ι)) (init operation : ι) : Prop :=
  ∃ (i j : Nat) (r op : Record ι) (n : Nat),
    log[i]? = some r ∧ r.id = init ∧ r.action = .init n ∧ r.fault = none ∧
    log[j]? = some op ∧ op.id = operation ∧ i < j ∧ SameLifetime log i j

/-- Atomic object order, separate from memory visibility. -/
def Before (log : List (Record ι)) (a b : ι) : Prop :=
  ∃ (i j : Nat) (r s : Record ι), log[i]? = some r ∧ r.id = a ∧ log[j]? = some s ∧ s.id = b ∧ i < j

end PTX.MBarrier
