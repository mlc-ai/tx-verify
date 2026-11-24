-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine
public import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
public import Kernels.TmlFa4Fwd.Proof.NonzeroRoleCounts
public import Lemmas.Flow.Polls

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow Prologue
open PTX.Kernels.TmlFa4Fwd.Loader (readySlot emptySlot)

noncomputable section

/-- The most recent pipeline activity observed in an MMA lane. -/
inductive Phase where
  | startup | allocating | awaitingOperands | queryKey | probabilityValue | draining
  | exited | faulted

/-- MMA lane observations. Issue counts record instructions, including asynchronous requests. -/
structure D where
  phase : Phase := .startup
  allocationColumns : Option Nat := none
  queryAcquires : Fin 2 → Nat := fun _ => 0
  kvAcquires : Fin 3 → Nat := fun _ => 0
  latestKvParity : Fin 3 → Option Nat := fun _ => none
  kvReleaseIssues : Fin 3 → Nat := fun _ => 0
  qkIssues : Nat := 0
  pvIssues : Nat := 0
  outputReadyIssues : Fin 2 → Nat := fun _ => 0
  countedEvents : Nat := 0

def initial : D := {}

namespace Observation

def queryObject (l : Launch) (g : Nat) (stage : Fin 2) : Loc :=
  initObject l (g / l.block) ⟨stage, by omega⟩

def readyObject (l : Launch) (g : Nat) (slot : Fin 3) : Loc :=
  initObject l (g / l.block) (readySlot slot)

def emptyObject (l : Launch) (g : Nat) (slot : Fin 3) : Loc :=
  initObject l (g / l.block) (emptySlot slot)

def outputObject (l : Launch) (g : Nat) (stage : Fin 2) : Loc :=
  initObject l (g / l.block) ⟨18 + stage, by omega⟩

/-- A commit issue names the local shared-memory operand. -/
def commitsOn (loc : Loc) (e : Event) : Bool :=
  match e.kind with
  | .tc (.commit spec) => decide (spec.mbar = loc)
  | _ => false

/-- A shared-memory A operand denotes QK, while a Tensor Memory A operand denotes PV. -/
def qkIssue (e : Event) : Bool :=
  match e.kind with
  | .tc (.mma _ operands _ _) => operands.aTmem.isNone
  | _ => false

def pvIssue (e : Event) : Bool :=
  match e.kind with
  | .tc (.mma _ operands _ _) => operands.aTmem.isSome
  | _ => false

def observedPhase (phase : Phase) (e : Event) : Phase :=
  match e.kind with
  | .tc (.resource _ _ (.alloc _)) => .allocating
  | .tc (.resource _ _ _) => .draining
  | .wait .. => .awaitingOperands
  | .tc (.mma _ operands _ _) =>
    if operands.aTmem.isSome then .probabilityValue else .queryKey
  | .exit => .exited
  | .ub _ => .faulted
  | _ => phase

def observedAllocation (columns : Option Nat) (e : Event) : Option Nat :=
  match e.kind with
  | .tc (.resource _ _ (.alloc columns)) => some columns
  | _ => columns

def observedReadyParity (loc : Loc) (parity : Option Nat) (e : Event) : Option Nat :=
  match e.kind with
  | .wait target requested true _ _ => if target = loc then some requested else parity
  | _ => parity

def tick (count : Nat) (seen : Bool) : Nat :=
  count + if seen then 1 else 0

end Observation

open Observation

/-- Observe an MMA issue, a barrier operation, or another event in the lane's prefix. -/
def advance (l : Launch) (g : Nat) (d : D) (e : Event) : D where
  phase := observedPhase d.phase e
  allocationColumns := observedAllocation d.allocationColumns e
  queryAcquires i := tick (d.queryAcquires i) (okPoll (queryObject l g i) e)
  kvAcquires i := tick (d.kvAcquires i) (okPoll (readyObject l g i) e)
  latestKvParity i := observedReadyParity (readyObject l g i) (d.latestKvParity i) e
  kvReleaseIssues i := tick (d.kvReleaseIssues i) (commitsOn (emptyObject l g i) e)
  qkIssues := tick d.qkIssues (qkIssue e)
  pvIssues := tick d.pvIssues (pvIssue e)
  outputReadyIssues i := tick (d.outputReadyIssues i) (commitsOn (outputObject l g i) e)
  countedEvents := tick d.countedEvents e.counts

abbrev machine (l : Launch) (g : Nat) := observationMachine l g initial (advance l g)

theorem sound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    (machine l g).Sound :=
  observationSound hp g initial (advance l g)

/-- The abstract state after a prefix of the lane's events. -/
def summary (l : Launch) (g : Nat) (es : List Event) : D :=
  es.foldl (advance l g) initial

/-- The state at the indicated event boundary, including at the end of a truncated run. -/
def atPrefix (l : Launch) (X : Execution) (g index : Nat) : D :=
  summary l g ((X.tr g).take index)

@[simp] theorem stateAtPrefix (l : Launch) (X : Execution) (g index : Nat) :
    stateAt (machine l g) X index = some (atPrefix l X g index) :=
  observationAfter l g initial initial (advance l g) _

/-- A reached event fires at the state summarizing the events that precede it. -/
theorem fired {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e) :
    ∃ o, (machine l g).Fired (atPrefix l X g index) e o :=
  observationFired hp hX he initial (advance l g)

theorem prefixStep {l : Launch} {X : Execution} {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) :
    atPrefix l X g (index + 1) = advance l g (atPrefix l X g index) e := by
  have h : Transition (machine l g) X index e.kind (atPrefix l X g index)
      (advance l g (atPrefix l X g index) e) := ⟨e, he, rfl, stateAtPrefix l X g index, rfl⟩
  have hAfter := h.stateAfter
  rw [stateAtPrefix] at hAfter
  exact Option.some.inj hAfter

/-- A successful ready poll advances the indicated slot's observation and its latest parity. -/
theorem readyAcquireStep {l : Launch} {X : Execution} {g index pc parity : Nat} {i : Fin 3}
    {acquire : Bool} {scope : MbarScope}
    (he : X.get (g, index) =
      some ⟨pc, .wait (initObject l (g / l.block) (readySlot i)) parity true acquire scope⟩) :
    (atPrefix l X g (index + 1)).phase = .awaitingOperands ∧
    (atPrefix l X g (index + 1)).kvAcquires i = (atPrefix l X g index).kvAcquires i + 1 ∧
    (atPrefix l X g (index + 1)).latestKvParity i = some parity := by
  rw [prefixStep he]
  simp [advance, observedPhase, observedReadyParity, tick, readyObject, okPoll, sourceWaitSuccess]

private theorem foldCounter {l : Launch} {g : Nat} (read : D → Nat) (test : Event → Bool)
    (h : ∀ d e, read (advance l g d e) = tick (read d) (test e))
    (d : D) (es : List Event) :
    read (es.foldl (advance l g) d) = read d + es.countP test := by
  induction es generalizing d with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, ih, h, tick, List.countP_cons]
    split <;> omega

theorem kvAcquireCount (l : Launch) (g : Nat) (es : List Event) (i : Fin 3) :
    (summary l g es).kvAcquires i = okPolls (initObject l (g / l.block) (readySlot i)) es := by
  simpa [summary, initial, okPolls, readyObject] using
    foldCounter (l := l) (g := g) (fun d => d.kvAcquires i) (okPoll (readyObject l g i))
      (fun _ _ => rfl) initial es

theorem counted (l : Launch) (g : Nat) (es : List Event) :
    (summary l g es).countedEvents = es.countP Event.counts := by
  simpa [summary, initial] using
    foldCounter (l := l) (g := g) D.countedEvents Event.counts (fun _ _ => rfl) initial es

/-- The first empty-slot release requires a successful ready-slot-zero acquisition in the
abstract prefix. -/
theorem initialReleaseGuard {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨2274, .tc (.commit spec)⟩) :
    0 < (atPrefix l X g index).kvAcquires 0 := by
  obtain ⟨j, hj, hPoll, _⟩ := PTX.Kernels.TmlFa4Fwd.Mma.initialReadyBeforeCommit hp hX he
  rw [atPrefix, kvAcquireCount]
  apply List.countP_pos_iff.mpr
  let event : Event := ⟨2145, .wait (readyObject l g 0) 0 true true .cta⟩
  refine ⟨event, ?_, ?_⟩
  · have hGet : ((X.tr g).take index)[j]? = some event :=
      (List.getElem?_take_of_lt hj).trans hPoll
    exact List.mem_of_getElem? hGet
  · rw [okPoll_wait (e := event) rfl]
    simp [readyObject]

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
