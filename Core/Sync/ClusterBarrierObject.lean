-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

@[expose] public section

namespace PTX.ClusterBarrier

/-! ## OBJ-CLUSTER-BARRIER-STATE — cluster arrival, completion and observation

Statement: A cluster barrier completes a phase when every non-exited thread of the cluster has
  arrived in it, and it then starts the next phase. A wait returns once the phase of the waiting
  thread's own latest arrival has completed, and it stays blocked for a thread that has not arrived.
  A thread that arrives a second time before its phase has completed is a fault.

Defs: ClusterBarrier.State, ClusterBarrier.Action, ClusterBarrier.Error,
  ClusterBarrier.Error.isFault, ClusterBarrier.Outcome, ClusterBarrier.finish,
  ClusterBarrier.perform

Source:
- §9.7.15.3 (barrier.cluster)
- §9.7.15.3 (barrier.cluster): "barrier.cluster.wait instruction causes the executing thread to wait
    for all non-exited threads of the cluster to perform barrier.cluster.arrive ."
- §9.7.15.3 (barrier.cluster): "When all non-exited threads in the cluster have executed
    barrier.cluster.arrive , the barrier completes and is automatically reinitialized. After using
    barrier.cluster.wait to detect completion of the barrier, a thread may immediately arrive at the
    barrier once again. Each thread must arrive at the barrier only once before the barrier
    completes."
- §9.7.14.7 (exit)
- EXT-CLUSTER-WAIT-PHASE

Direction: reading

Applies: One cluster's barrier, with an arbitrary number of threads and unbounded generations

Premises: The execution layer separately enforces the warp rendezvous required by both instructions.

Effect: Object transitions only; the fault is reported by ERR-CLUSTER-BARRIER
  (`ClusterFault`), and the execution is not removed. OBJ-CLUSTER-BARRIER-SYNC uses checked
  source-event histories built from these resource operations.

Review: Only the last sentence of the quoted `barrier.cluster.wait` description is a prohibition
  (`earlyArrival`); arriving again after completion without a wait is allowed. Arrival does not
  block across warps; a wait on an incomplete phase is blocked. The wait observes the phase of the
  thread's own latest arrival (EXT-CLUSTER-WAIT-PHASE), so a repeated wait for one arrival returns,
  all non-exited threads having performed that arrive. A thread that has not arrived is itself a
  non-exited thread that has not performed `barrier.cluster.arrive`, so no phase can complete for it
  and its wait stays blocked. Release and relaxed arrivals have identical counter effects; only the
  release form publishes earlier memory accesses in the execution adapter.

### EXT-CLUSTER-WAIT-PHASE — a cluster wait waits for the phase of its thread's latest arrival

Statement: A `barrier.cluster.wait` waits for the completion of the phase in which the executing
  thread most recently arrived. It returns once that phase has completed, even when other threads
  have already arrived in the next phase, and it returns every time it is executed for that arrival.
  A wait of a thread that has not arrived stays blocked.

Source:
- §9.7.15.3: "barrier.cluster.wait instruction causes the executing thread to wait for all
    non-exited threads of the cluster to perform barrier.cluster.arrive ."
- §9.7.15.3: "When all non-exited threads in the cluster have executed barrier.cluster.arrive , the
    barrier completes and is automatically reinitialized. After using barrier.cluster.wait to detect
    completion of the barrier, a thread may immediately arrive at the barrier once again. Each
    thread must arrive at the barrier only once before the barrier completes."
- §9.7.15.3: "The barrier.cluster.wait instruction guarantees that when it completes the execution,
    memory accesses (except asynchronous operations) requested, in program order, prior to the
    preceding barrier.cluster.arrive by all threads in the cluster are complete and visible to the
    executing thread."

Why it is not spec text: The text says the wait is for "all non-exited threads of the cluster to
  perform barrier.cluster.arrive", without saying which arrival of a reinitialized barrier: the
  current phase of the barrier, the phase after the executing thread's arrival, or the phase of the
  executing thread's "preceding barrier.cluster.arrive" (the phrase of the memory guarantee). The
  model takes the last, which also fixes what a second wait for one arrival, and a wait while other
  threads have arrived in the next phase, return. A wait read as waiting for the barrier's current
  phase would block in those two cases. If it does not hold, i.e. the hardware wait is for a
  different phase than the executing thread's most recent arrive, the model can accept a program
  that hangs, and the ordering edges it gives come from the wrong phase.

Evidence: Hardware probe on B200, driver 595.58.03, CUDA 13.2.51: a second `barrier.cluster.wait`
  after one arrive returns, immediately and after a delay; SASS keeps both `UCGABAR_WAIT`.

Direction: reading

Effect: Disclosed by every kernel whose statement names `ClusterOp.wait`: FlashAttn4Fwd,
  Fp16Gemm8192.
-/

/-- The state of the barrier of one cluster (§9.7.15.3). -/
structure State where
  /-- The number of the current phase; completion increments it. -/
  phase : Nat := 0
  /-- The threads that have arrived in the current phase. -/
  arrived : Finset Nat := ∅
  /-- The threads of the cluster that have exited. -/
  exited : Finset Nat := ∅
  /-- The phase of each thread's latest arrival, if it has arrived. -/
  lastArrival : Nat → Option Nat := fun _ => none

/-- An operation on the cluster barrier: `barrier.cluster.arrive` (release or relaxed),
`barrier.cluster.wait`, or the exit of a thread. -/
inductive Action where
  | arrive (thread : Nat) (release : Bool := true)
  | wait (thread : Nat)
  | exit (thread : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | badThread | badWarp | earlyArrival
  deriving DecidableEq, Repr

/-- Errors caused by the operations a program performs, as opposed to records that do not
describe actual live warps (`badThread`, `badWarp`). -/
def Error.isFault : Error → Bool
  | .earlyArrival => true
  | .badThread | .badWarp => false

/-- The result of an operation: the new state, a blocked wait, or a fault. -/
inductive Outcome where
  | done (state : State)
  | blocked
  | fault (error : Error)

/-- Complete the current phase if every non-exited thread has arrived in it. -/
def finish (threads : Nat) (s : State) : State :=
  if ∀ g ∈ Finset.range threads, g ∈ s.arrived ∨ g ∈ s.exited then
    { s with phase := s.phase + 1, arrived := ∅ }
  else s

/-- The effect of one operation on the barrier of a cluster with `threads` threads. -/
def perform (threads : Nat) (s : State) (a : Action) : Outcome :=
  let g := match a with | .arrive g _ | .wait g | .exit g => g
  if ¬ (g < threads ∧ g ∉ s.exited) then .fault .badThread
  else match a with
    | .arrive g _ =>
      if g ∈ s.arrived then .fault .earlyArrival
      else .done (finish threads { s with
        arrived := insert g s.arrived
        lastArrival := fun h => if h = g then some s.phase else s.lastArrival h })
    | .wait g =>
      match s.lastArrival g with
      | none => .blocked
      | some phase => if phase < s.phase then .done s else .blocked
    | .exit g => .done (finish threads { s with exited := insert g s.exited })

end PTX.ClusterBarrier
