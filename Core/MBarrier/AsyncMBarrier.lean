-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
public import Core.Async.AsyncCopy
public import Core.MBarrier.MBarrierHistory

@[expose] public section

namespace PTX.AsyncCopy
noncomputable section

/-! ## OBJ-MBAR-ORIGIN — copy effects name actual issuing instructions
Statement: Every operation in an mbarrier's history comes from an actual instruction or from the
  actual completion notification of an asynchronous operation, and every such operation, including
  a failed wait, appears in the history. A copy or a tracked MMA counts as observed only through its
  own completion notification on its target object, so a manual `complete_tx` never stands for the
  completion of a copy. A `cp.async.mbarrier.arrive` tracks every earlier `cp.async` of its thread,
  and its arrive-on occurs only after all of them have written their destinations.

Defs: AsyncCopy.issuedBy, AsyncCopy.objectAction, AsyncCopy.MatchesObject, AsyncCopy.CoversObject,
  AsyncCopy.TracksMma, AsyncCopy.CommitOk, AsyncCopy.TcEffectsOk, AsyncCopy.TracksCpAsync,
  AsyncCopy.ArriveOk, AsyncCopy.ObjectsOk

Source:
- §9.7.10.28.4.1 (the copy's own complete_tx notification)
- §9.7.15.16.15 (manual complete_tx does not perform a memory operation)
- §9.7.15.16.19 (wait observation)
- §9.7.15.16.18: "Causes an arrive-on operation to be triggered by the system on the mbarrier object
    upon the completion of all prior cp.async operations initiated by the executing thread."
- §9.7.15.16.18: "When .noinc modifier is not specified, the pending count of the mbarrier object is
    incremented by 1 prior to the asynchronous arrive-on operation ."
- §9.7.15.16.18: "When the .noinc modifier is specified, the increment to the pending count of the
    mbarrier object is not performed."

Direction: reading

Applies: Linear and tensor copy, CLC, tcgen05 commit and cp.async.mbarrier.arrive events,
  independent effects and per-object histories

Premises: The history's operations resolve to actual instructions or actual copy notifications;
  successful-wait results agree.

Effect: Provenance and validity predicates used by Consistent and memory visibility. A manual
  complete_tx may change a counter but is not an async notification. A `cp.async.mbarrier.arrive`
  without `.noinc` records its pending-count increment as its own thread operation; with `.noinc`
  the instruction records no operation. Its arrive-on is an asynchronous operation (`.arriveOn`) of
  one arrival. Failed polls do not advance the object but are included, so use of an invalid object
  is still checked. Matching the histories to thread/proxy ordering, and checking that every
  required operation occurs, are separate obligations.
-/

/-- Extract the copy specification from the real issuing event. -/
def issuedBy (X : Execution) (i : EvId) : Option Spec :=
  match X.get i with
  | some ⟨_, .copy s⟩ => some s
  | _ => none

/-- The object operation associated with a real instruction or completion notification. -/
def objectAction (X : Execution) (A : Snapshot) (m : Loc) : Ref → Option MBarrier.Action
  | .thread e => match X.get e with
    | some ⟨_, .mbInit m' count⟩ => if m' = m then some (.init count) else none
    | some ⟨_, .mbInval m'⟩ => if m' = m then some .inval else none
    | some ⟨_, .arrive m' tx count _ _⟩ => if m' = m then some (.arrive count tx) else none
    | some ⟨_, .wait m' parity ok _ _⟩ => if m' = m then some (.pollParity parity ok) else none
    | some ⟨_, .asyncArrive m' false⟩ => if m' = m then some .increment else none
    | _ => none
  | .async i (.notify .load) => do
    let some ⟨_, .tensorIssue _ s⟩ := X.get i | none
    let observation ← X.tensor i
    if s.mbar = m ∧ observation.effects.notified = true
    then some (.completeTx (TensorTransfer.bytes s.descriptor)) else none
  | .async i (.notify .copy) => do
    let spec ← issuedBy X i
    if spec.completion = .mbarrier m ∧ (A.copies i).notified = true then
      some (.completeTx spec.dst.size) else none
  | .async i (.tcNotify rank) => do
    let some ⟨_, .tc (.commit s)⟩ := X.get i | none
    if TcCommit.target s rank = some m ∧ rank ∈ X.tcNotified i
    then some (.arrive 1 0) else none
  | .async i (.notify (.cta c)) =>
    match X.get i with
    | some ⟨_, .clcIssue s targets⟩ =>
      if c ∈ targets ∧ c ∈ (X.clc i).notified ∧ m = { s.mbar with cta := c }
      then some (.completeTx 16) else none
    | _ => none
  | .async i .arriveOn =>
    match X.get i with
    | some ⟨_, .asyncArrive m' _⟩ =>
      if m' = m ∧ A.arrived i = true then some (.arrive 1 0) else none
    | _ => none
  | .async _ _ => none

/-- Every entry has an actual source; a recorded successful wait must actually succeed
in the object state it observes. Responses and explicit object faults are checked by
MBarrier.CheckedLog. -/
def MatchesObject (X : Execution) (A : Snapshot) (m : Loc)
    (log : List (MBarrier.Record Ref)) : Prop :=
  ∀ r ∈ log, objectAction X A m r.id = some r.action ∧
    (∀ p ok, r.action = .pollParity p ok → r.fault = none → r.reply.waited = some ok)

/-- Every object operation, including failed polls, must be represented. -/
def CoversObject (X : Execution) (A : Snapshot) (m : Loc)
    (log : List (MBarrier.Record Ref)) : Prop :=
  ∀ id action, objectAction X A m id = some action → ∃ r ∈ log, r.id = id

/-- A commit tracks every earlier MMA or copy of its issuing thread. The kernel's cta_group
is uniform, so the operation and the commit share it. -/
def TracksMma (X : Execution) (mma commit : EvId) : Prop :=
  mma.1 = commit.1 ∧ mma.2 < commit.2 ∧ X.TcAsync mma ∧
  ∃ s, X.Commit commit s

/-- Delivery to one selected target requires completion of all tracked operations. -/
def CommitOk (X : Execution) : Prop :=
  ∀ i rank, rank ∈ X.tcNotified i →
    (∃ s m, X.Commit i s ∧ TcCommit.target s rank = some m) ∧
    ∀ mma, TracksMma X mma i → X.async.mmaDone mma = true

/-- No fabricated completion; notification cannot precede the tracked work. -/
def TcEffectsOk (X : Execution) : Prop :=
  (∀ i, X.async.mmaStarted i = true →
    (∃ d s accum mask operands,
      X.MmaIssue i d s accum mask ∧ X.async.mmaOperands i = some operands ∧
      TcMma.Valid s.descriptor ∧
      operands.a.length = TcMma.Operand.a.bytes s.descriptor ∧
      operands.b.length = TcMma.Operand.b.bytes s.descriptor) ∨
    (∃ c operands, X.CpIssue i c ∧ X.async.mmaOperands i = some operands ∧
      operands.a.length = c.ctas.length * c.shape.sourceBytes ∧ operands.b = []) ∨
    (∃ s operands, X.ShiftIssue i s ∧ X.async.mmaOperands i = some operands ∧
      operands.a = [] ∧ operands.b = [])) ∧
  (∀ i, X.async.mmaDone i = true → X.async.mmaStarted i = true)

/-- The `cp.async.mbarrier.arrive` issued by `arrive` tracks the `cp.async` issued by `copy`: an
earlier `cp.async` of the same thread. -/
def TracksCpAsync (X : Execution) (copy arrive : EvId) : Prop :=
  copy.1 = arrive.1 ∧ copy.2 < arrive.2 ∧
  (∃ s, X.Copy copy s ∧ s.completion = .asyncGroup) ∧ ∃ m noinc, X.AsyncArrive arrive m noinc

/-- An arrive-on belongs to an actual `cp.async.mbarrier.arrive` and occurs only after every
`cp.async` it tracks has written its destination. -/
def ArriveOk (X : Execution) : Prop :=
  ∀ i, X.async.arrived i = true →
    (∃ m noinc, X.AsyncArrive i m noinc) ∧
    ∀ copy, TracksCpAsync X copy i → (X.async.copies copy).writeBytes.isSome

/-- Histories include legal replies or explicit faults, each with an actual origin.
Faults are rejected by safety, not by this predicate. -/
def ObjectsOk (X : Execution) : Prop :=
  ∀ m, MBarrier.CheckedLog (X.objects m) ∧
    MatchesObject X X.async m (X.objects m) ∧ CoversObject X X.async m (X.objects m)

/-! ## OBJ-MBAR-OBSERVE — a successful wait observes an update in its phase
Statement: A successful wait on an mbarrier observes every update recorded in the phase it saw
  complete, including the completion notifications of the asynchronous operations that phase tracks.
  The observation requires no acquire semantics and no scope, and each rule that uses it states the
  qualifiers it needs, such as the scopes that include each other in memory synchronization
  (MEM-MBAR-SYNCHRONIZES).

Defs: AsyncCopy.WaitObserves, AsyncCopy.NotifyOn, AsyncCopy.Notifies, AsyncCopy.AsyncObserved,
  AsyncCopy.notifies_copy_of_mbarrier

Source:
- §9.7.15.16.19: "Checks whether the mbarrier object has completed the phase"
- §9.7.15.16.19: "The test_wait and try_wait operations are valid only for : the current incomplete
    phase, for which waitComplete returns False . the immediately preceding phase, for which
    waitComplete returns True ."
- §9.7.15.16.8 (phase completion)
- §9.7.10.28.1.2: "When the current phase of the mbarrier object is complete, it implies that all
    asynchronous operations tracked by this phase are complete, and all threads participating in
    that mbarrier object can access the result of the asynchronous operations."
- §9.7.10.28.3.3: "Writes performed by cp.async operations are made visible to the executing thread
    only after: The completion of cp.async.wait_all or The completion of cp.async.wait_group on the
    cp.async-group in which the cp.async belongs to or mbarrier.test_wait and mbarrier.try_wait
    returns True on an mbarrier object which is tracking the completion of the cp.async operation."
- §9.7.18.6.2.1.1: "Completion of the following instruction’s asynchronous operations is observed
    through the mbarrier based waiting mechanism: tcgen05.mma tcgen05.cp tcgen05.shift"
- §9.7.10.28.4.1
- §9.7.10.28.5.3
- §9.7.15.18
- §9.7.18.12.1 (the notification each asynchronous operation performs on its mbarrier)

Direction: equal

Applies: Every successful mbarrier wait and every update recorded in the object history: thread
  arrivals, the complete-tx of linear and tensor copies and of CLC responses, and the arrive-on of
  commits and of `cp.async.mbarrier.arrive`

Premises: The wait's record has no fault and returned True; the update's record has no fault,
  precedes the wait in the object's history and belongs to the phase the wait observed.

Effect: The observation used by MSync, MbarExec, TcMma.CommitObserved, TcMma.DoneBefore,
  AsyncFinished, CopyReleaseSync and MbarObserved. `WaitObserves x w m acq ws` says that the
  successful wait `w` on `m`, with acquire flag `acq` and scope `ws`, observed the update `x`.
  `NotifyOn i t m` says that the notification `t` of `i` occurred on `m`; it is the copy's own
  complete-tx, the tensor load's, or the CLC response's to one target CTA. `Notifies i p n m` says
  that `n` is the notification on `m` that signals the completion of part `p` of the asynchronous
  operation issued by `i`: its notification `p.target` (`NotifyOn`), or the arrive-on of a commit
  tracking the MMA. `AsyncObserved i p w acq ws` says that the wait observed that notification. A
  `cp.async` has no notification of its own; the arrive-on of a `cp.async.mbarrier.arrive` that
  tracks it signals its completion (§9.7.10.28.3.3: "mbarrier.test_wait and mbarrier.try_wait
  returns True on an mbarrier object which is tracking the completion of the cp.async operation").
  Every observation of an update, by any rule, is `WaitObserves`. Memory synchronization requires
  the scopes of both operations to include each other (`ScopesMeet`, MEM-MBAR-SYNCHRONIZES), and the
  visibility of a completed operation's accesses requires an acquire wait whose scope and the
  notification's scope include each other's thread (MEM-OBSERVED-COMPLETION). The needs of a
  successful poll (`MbarObserved`, DEP-ORDER) require no acquire and no scope. The source part names
  the operation through its actual notification, so a manual complete_tx (`objectAction` of a thread
  instruction) cannot stand in for a copy, and a multicast delivery to one CTA does not imply
  delivery to another.
-/

/-- The successful wait `w` on `m`, with acquire flag `acq` and scope `ws`, observed the update
`x`: the record of `x` belongs to the phase whose completion `w` observed. -/
def WaitObserves (X : Execution) (x : Ref) (w : EvId) (m : Loc) (acq : Bool) (ws : MbarScope) :
    Prop :=
  (∃ pc parity, X.get w = some ⟨pc, .wait m parity true acq ws⟩) ∧
    MBarrier.UpdateBeforeWait (X.objects m) x (.thread w)

/-- The notification `t` of the operation issued by `i` has occurred on mbarrier `m`: the
copy's complete-tx on its mbarrier, the tensor load's on its mbarrier, or the CLC response's
on the mbarrier at target CTA `c`. -/
def NotifyOn (X : Execution) (i : EvId) : Target → Loc → Prop
  | .copy, m => ∃ bytes, Notification (issuedBy X) X.async i m bytes
  | .load, m => ∃ o a, X.tensor i = some o ∧ X.TensorIssue i a o.spec ∧
      o.spec.mbar = m ∧ o.effects.notified = true
  | .cta c, m => ∃ s targets, X.ClcIssue i s targets ∧ c ∈ targets ∧
      c ∈ (X.clc i).notified ∧ m = { s.mbar with cta := c }

/-- `n` is the notification on mbarrier `m` signalling the completion of part `p` of the
asynchronous operation issued by `i`: the notification `p.target` of `i`, for an MMA the arrive-on
of a commit tracking it, and for a `cp.async` the arrive-on of a `cp.async.mbarrier.arrive`
tracking it. -/
def Notifies (X : Execution) (i : EvId) : Part → Ref → Loc → Prop
  | .mmaRead .., n, m | .mmaDone, n, m =>
    ∃ commit s rank, n = .async commit (.tcNotify rank) ∧ TracksMma X i commit ∧
      X.Commit commit s ∧ TcCommit.target s rank = some m ∧ rank ∈ X.tcNotified commit
  | .read .copy, n, m | .write .copy, n, m =>
    (n = .async i (.notify .copy) ∧ NotifyOn X i .copy m) ∨
    ∃ j noinc, n = .async j .arriveOn ∧ TracksCpAsync X i j ∧ X.AsyncArrive j m noinc ∧
      X.async.arrived j = true
  | p, n, m => match p.target with
    | some t => n = .async i (.notify t) ∧ NotifyOn X i t m
    | none => False

/-- The successful wait `w` observed the notification of part `p` of the operation `i`. -/
def AsyncObserved (X : Execution) (i : EvId) (p : Part) (w : EvId) (acq : Bool)
    (ws : MbarScope) : Prop :=
  ∃ n m, Notifies X i p n m ∧ WaitObserves X n w m acq ws

/-- For a copy completed through an mbarrier (every `cp.async.bulk` form of the earlier
representation), the notification of its read or write is its own complete-tx. -/
theorem notifies_copy_of_mbarrier {X : Execution} {i : EvId} {s : Spec} {m' : Loc}
    (hc : X.Copy i s) (hm : s.completion = .mbarrier m') {p : Part}
    (hp : p = .read .copy ∨ p = .write .copy) {n : Ref} {m : Loc} :
    Notifies X i p n m ↔ n = .async i (.notify .copy) ∧ NotifyOn X i .copy m := by
  have key : ∀ j noinc, ¬ (n = .async j .arriveOn ∧ TracksCpAsync X i j ∧
      X.AsyncArrive j m noinc ∧ X.async.arrived j = true) := by
    rintro j noinc ⟨-, ⟨-, -, ⟨s', hc', hs'⟩, -⟩, -⟩
    obtain ⟨pc, h1⟩ := hc
    obtain ⟨pc', h2⟩ := hc'
    rw [h1] at h2
    cases h2
    rw [hm] at hs'
    cases hs'
  rcases hp with rfl | rfl <;>
  · simp only [Notifies]
    exact ⟨fun h => h.resolve_right fun ⟨j, noinc, hj⟩ => key j noinc hj, Or.inl⟩

end
end PTX.AsyncCopy
