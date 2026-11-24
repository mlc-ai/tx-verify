-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.ClusterBarrierObject

@[expose] public section

namespace PTX.ClusterBarrier

/-! ## OBJ-CLUSTER-BARRIER-HISTORY — collective arrivals and completed waits

Statement: The history of a cluster barrier lists, in order, the collective arrivals and waits of
  whole warps and the exits of threads. An arrival uses the phase that is open when it is recorded,
  and a wait observes the phase of its thread's own preceding arrival. A release arrival
  synchronizes with a wait only when both are of the same phase. A lane that arrives twice before
  its phase completes is a fault, even if another lane of the same warp arrival completes the phase.

Defs: ClusterBarrier.Record, ClusterBarrier.Record.refs, ClusterBarrier.liveWarp,
  ClusterBarrier.performAll, ClusterBarrier.Record.perform, ClusterBarrier.run, ClusterBarrier.At,
  ClusterBarrier.ArrivalOf, ClusterBarrier.WaitOf, ClusterBarrier.Synchronizes

Source:
- §9.7.15.3 (barrier.cluster)

Direction: scope

Applies: The matched arrive/wait protocol of OBJ-CLUSTER-BARRIER-STATE, for arbitrary CTA and
  cluster sizes

Premises: Each collective record contains exactly the live lanes of one warp in one CTA. References,
  instruction qualifiers and per-thread order must separately match source events.

Effect: Source-reference associations used by OBJ-CLUSTER-BARRIER-SYNC. History order is
  barrier-object order. It is not a global order on memory. A blocked wait cannot be a completed
  record, and arrival and wait records both enforce warp rendezvous. The adapter must distinguish
  events before arrival from those between arrival and wait, and exclude asynchronous operations
  from this generic-proxy synchronization.
-/

/-- One update of the barrier of a cluster, naming its source events by references of type `α`:
the collective arrival or wait of the live lanes of one warp, or the exit of a thread. -/
inductive Record (α : Type) where
  | arrival (cta warp : Nat) (release : Bool) (lanes : List (Nat × α))
  | wait (cta warp : Nat) (lanes : List (Nat × α))
  | exit (thread : Nat) (ref : α)

def Record.refs {α : Type} : Record α → List α
  | .arrival _ _ _ lanes | .wait _ _ lanes => lanes.map Prod.snd
  | .exit _ e => [e]

/-- Thread indices are cluster-local. A warp never crosses a CTA boundary, including
when the block size is not a multiple of 32. -/
def liveWarp (block ctas : Nat) (s : State) (cta warp : Nat) (gs : List Nat) : Bool :=
  decide (0 < block ∧ cta < ctas ∧ warp * 32 < block ∧ gs ≠ [] ∧ gs.Nodup ∧
    (∀ g ∈ gs, g < block * ctas ∧ g / block = cta ∧
      (g % block) / 32 = warp ∧ g ∉ s.exited) ∧
    (∀ lane ∈ Finset.range 32,
      let localThread := warp * 32 + lane
      let g := cta * block + localThread
      localThread < block → g ∉ s.exited → g ∈ gs))

def performAll (threads : Nat) : State → List Action → Outcome
  | s, [] => .done s
  | s, a :: actions => match perform threads s a with
    | .done t => performAll threads t actions
    | other => other

def Record.perform {α : Type} (block ctas : Nat) (s : State) : Record α → Outcome
  | .exit g _ => ClusterBarrier.perform (block * ctas) s (.exit g)
  | .arrival cta warp release lanes =>
    if liveWarp block ctas s cta warp (lanes.map Prod.fst) then
      if lanes.any (fun p => decide (p.1 ∈ s.arrived)) then .fault .earlyArrival
      else performAll (block * ctas) s (lanes.map fun p => .arrive p.1 release)
    else .fault .badWarp
  | .wait cta warp lanes =>
    if liveWarp block ctas s cta warp (lanes.map Prod.fst) then
      performAll (block * ctas) s (lanes.map fun p => .wait p.1)
    else .fault .badWarp

/-- Apply the records of a history in order, stopping at a blocked record or a fault. -/
def run {α : Type} (block ctas : Nat) : State → List (Record α) → Outcome
  | s, [] => .done s
  | s, r :: rs => match r.perform block ctas s with
    | .done t => run block ctas t rs
    | other => other

def At {α : Type} (block ctas : Nat) (h : List (Record α)) (i : Nat) (s : State) : Prop :=
  run block ctas {} (h.take i) = .done s

/-- Event `e` is a lane of a collective arrival of the given kind that is recorded in phase
`phase`. -/
def ArrivalOf {α : Type} (block ctas : Nat) (h : List (Record α))
    (e : α) (phase : Nat) (release : Bool) : Prop :=
  ∃ i s t cta warp lanes g,
    h[i]? = some (.arrival cta warp release lanes) ∧ At block ctas h i s ∧
    (g, e) ∈ lanes ∧ s.phase = phase ∧
    Record.perform block ctas s (.arrival cta warp release lanes) = .done t

/-- Event `e` is a lane of a recorded wait whose thread's latest arrival was in phase `phase`. -/
def WaitOf {α : Type} (block ctas : Nat) (h : List (Record α)) (e : α) (phase : Nat) : Prop :=
  ∃ i s t cta warp lanes g,
    h[i]? = some (.wait cta warp lanes) ∧ At block ctas h i s ∧
    (g, e) ∈ lanes ∧ s.lastArrival g = some phase ∧
    Record.perform block ctas s (.wait cta warp lanes) = .done t

/-- Arrival `a` and wait `w` synchronize: `a` is a release arrival and `w` is a wait for its
phase. Only release arrivals publish memory through this rule; counter completion alone
is not a visibility edge. -/
def Synchronizes {α : Type} (block ctas : Nat) (h : List (Record α)) (a w : α) : Prop :=
  ∃ phase, ArrivalOf block ctas h a phase true ∧ WaitOf block ctas h w phase

end PTX.ClusterBarrier
