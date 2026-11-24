-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Int.Basic

@[expose] public section

namespace PTX.MBarrier

/-! ## OBJ-MBAR-STATE — layout::v0 mbarrier object operations
Statement: An mbarrier object counts the pending arrivals and the transaction bytes of its current
  phase; when both counts reach zero, the phase completes, the phase number advances and the pending
  count is reset to the expected count; a poll may fail at any time, and a successful poll reports
  the completed phase it observed. An object fault occurs when an operation other than
  initialization uses a location that holds no valid object, when a valid object is initialized,
  when a count leaves its range, when more arrivals occur than are pending, or when an arrival in a
  new phase comes before a successful wait observed the previous completion.

Defs: MBarrier.State, MBarrier.Action, MBarrier.Error, MBarrier.Reply, MBarrier.limit,
  MBarrier.validCount, MBarrier.validTx, MBarrier.validTxOperand, MBarrier.advance, MBarrier.perform

Source:
- §9.7.15.16.3, .5, .6, .8, .9, .12, .14–.16, .19
- §9.7.15.16.18: "When .noinc modifier is not specified, the pending count of the mbarrier object is
    incremented by 1 prior to the asynchronous arrive-on operation ."
- §9.7.15.16.18: "The pending count of the mbarrier object after the increment should not exceed the
    limit as mentioned in Contents of the mbarrier object . Otherwise, the behavior is undefined."
- §9.7.15.16: "An mbarrier object is an opaque object in memory which can be initialized and
    invalidated using : mbarrier.init mbarrier.inval"
- §9.7.15.16: "Performing any mbarrier operation except mbarrier.init on an uninitialized mbarrier
    object results in undefined behavior."
- §9.7.15.16.4: "An mbarrier object must be invalidated to repurpose its memory for any purpose,
    including repurposing it for another mbarrier object."
- §9.7.15.16.12: "The behavior of performing an mbarrier.init operation on a memory location
    containing a valid mbarrier object is undefined"
- §9.7.15.16.13: "mbarrier.inval invalidates the mbarrier object at the location specified by the
    address operand addr"
- §9.7.15.16.13: "Performing any mbarrier operation except mbarrier.init on a memory location that
    does not contain a valid mbarrier object , results in undefined behavior."

Direction: reading

Applies: One layout::v0 object and the operations the decoder produces on it: initialization,
  invalidation, arrivals (with optional expected transaction bytes), the pending-count increment of
  `cp.async.mbarrier.arrive`, transaction completion and parity polls

Premises: Operations belong to this object's history; counts are in the ISA ranges.

Effect: Object-local transitions used by the object history; memory ordering and completion
  provenance are separate rules. Initialization of a location without a valid object creates one,
  and invalidation of a valid object removes it, so a later initialization creates a new object.
  Transaction updates are signed. A successful poll agrees with the current parity. The rule that a
  successful poll observes a phase before an arrival in the next phase is §9.7.15.16.5.1.
-/

/-- The contents of a valid layout::v0 mbarrier object (§9.7.15.16.3): the current phase, the
expected arrival count, the pending arrival count, the tx-count, and whether the preceding
completed phase has been observed. -/
structure State where
  /-- The number of the current phase. Initialization sets it to zero and each phase completion
  increments it; `try_wait.parity` tests its parity. -/
  phase : Nat
  /-- The expected arrival count that `mbarrier.init` sets. Each phase completion reloads the
  pending arrival count with it. -/
  expected : Nat
  /-- The pending arrival count: the number of arrivals the current phase still needs. -/
  pending : Nat
  /-- The tx-count of the current phase: the transaction bytes added by expect-tx operations
  minus the bytes signalled by complete-tx operations. It is negative when complete-tx
  operations have signalled more bytes than were expected so far. -/
  tx : Int
  /-- Has the preceding completed phase been successfully observed? Initially true. -/
  observed : Bool
  deriving DecidableEq, Repr

/-- An operation on an mbarrier object, as its history records it: an initialization, a
complete-tx, an arrival with optional expect-tx, a pending-count increment, a parity poll, or an
invalidation. -/
inductive Action where
  /-- `mbarrier.init` with expected arrival count `count`. -/
  | init (count : Nat)
  /-- An asynchronous operation's complete-tx of `count` bytes. -/
  | completeTx (count : Nat)
  /-- `count` arrivals after expecting `tx` transaction bytes (`arrive.expect_tx`). -/
  | arrive (count : Nat) (tx : Nat := 0)
  /-- The increment of the pending count by 1 that `cp.async.mbarrier.arrive` without `.noinc`
  performs before its asynchronous arrive-on. -/
  | increment
  /-- A try_wait.parity observation: `false` may be returned without observing completion. -/
  | pollParity (parity : Nat) (success : Bool)
  /-- `mbarrier.inval`: the location no longer contains a valid object. -/
  | inval
  deriving DecidableEq, Repr

/-- An object fault, each of which the ISA makes undefined behaviour: an operation other than
`mbarrier.init` on a location without a valid object (`invalidObject`), `mbarrier.init` on a valid
object (`alreadyInitialized`), an arrival count or transaction operand out of range
(`countRange`), a tx-count that leaves its range (`transactionRange`), more arrivals than are
pending (`arrivalUnderflow`), and an arrival in a phase whose preceding completion no successful
poll observed (`precedingPhaseNotObserved`, §9.7.15.16.5.1). -/
inductive Error where
  | invalidObject | alreadyInitialized | countRange | transactionRange
  | arrivalUnderflow | precedingPhaseNotObserved
  deriving DecidableEq, Repr

/-- The reply of the object to one operation. -/
structure Reply where
  /-- The object state after the operation; `none` when the location then holds no valid
  object. -/
  state : Option State
  /-- The result of a parity poll; absent for the other operations. -/
  waited : Option Bool := none
  /-- The completed phase actually observed; absent on an initial opposite-parity poll. -/
  completed : Option Nat := none
  deriving DecidableEq, Repr

/-- The largest expected arrival count and the largest magnitude of the tx-count of a
layout::v0 object, 2^20 - 1 (§9.7.15.16.3). -/
def limit : Nat := 2 ^ 20 - 1
/-- An arrival count lies between 1 and `limit`. -/
abbrev validCount (n : Nat) : Prop := 0 < n ∧ n ≤ limit
/-- A tx-count lies between `-limit` and `limit`. -/
abbrev validTx (n : Int) : Prop := -(limit : Int) ≤ n ∧ n ≤ limit
/-- Transaction operands are u32; the signed bound is on the resulting counter. -/
abbrev validTxOperand (n : Nat) : Prop := n < 2 ^ 32

/-- Completion and reinitialization of pending arrivals are one atomic transition. -/
def advance (s : State) : State :=
  if s.pending = 0 ∧ s.tx = 0 then
    { s with phase := s.phase + 1, pending := s.expected, observed := false }
  else s

/-- The effect of one operation on the object at one location: from the state before it
(`none` when the location holds no valid object) to the reply, or to an object fault. An
arrival or complete-tx that leaves both the pending arrival count and the tx-count at zero
completes the phase (`advance`). A successful poll tests the parity of the phase before the
current one, which has completed; a poll may also fail when that phase has completed. An increment
raises the pending count by one and completes no phase. -/
def perform (current : Option State) (a : Action) : Except Error Reply := do
  match a with
  | .init n =>
    if current.isSome then throw .alreadyInitialized
    unless validCount n do throw .countRange
    return ⟨some ⟨0, n, n, 0, true⟩, none, none⟩
  | _ =>
    let some s := current | throw .invalidObject
    match a with
    | .inval => return ⟨none, none, none⟩
    | .completeTx n =>
      unless validTxOperand n do throw .countRange
      let tx := s.tx - n
      unless validTx tx do throw .transactionRange
      return ⟨some (advance { s with tx }), none, none⟩
    | .arrive n tx =>
      unless validCount n ∧ validTxOperand tx do throw .countRange
      unless s.observed do throw .precedingPhaseNotObserved
      unless n ≤ s.pending do throw .arrivalUnderflow
      let tx' := s.tx + tx
      unless validTx tx' do throw .transactionRange
      return ⟨some (advance { s with pending := s.pending - n, tx := tx' }), none, none⟩
    | .increment =>
      unless s.pending + 1 ≤ limit do throw .countRange
      return ⟨some { s with pending := s.pending + 1 }, none, none⟩
    | .pollParity p success =>
      let ok := success && (s.phase % 2 != p % 2)
      return ⟨some { s with observed := s.observed || ok }, some ok,
        if ok ∧ 0 < s.phase then some (s.phase - 1) else none⟩
    | .init _ => throw .alreadyInitialized

end PTX.MBarrier
