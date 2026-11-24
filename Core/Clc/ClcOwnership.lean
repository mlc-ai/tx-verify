-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Logic.Function.Basic

@[expose] public section

namespace PTX.Clc

/-! ## OBJ-CLC-OWNERSHIP — atomic launch or cancellation of a cluster
Statement: Each cluster of the grid is either launched or canceled, and only while no one has
  claimed it. A successful cancellation request claims exactly one unclaimed cluster, which stays
  assigned to that request; a failed request claims no cluster. Each request is resolved once. Task
  identifiers are abstract cluster identities; they are not CTA ranks or output tile numbers. A
  canceled task stays assigned to its successful request, including after the requesting cluster
  exits. Multicast copies of one response retain the same request identity.

Defs: Clc.Owner, Clc.State, Clc.initial, Clc.Step, Clc.StateExtends

Source:
- §9.7.15.18 (clusterlaunchcontrol.try_cancel)

Direction: reading

Applies: Cluster tasks of one grid and distinct dynamic cancellation requests

Premises: Task identifiers designate clusters in that grid; request identifiers designate individual
  dynamic requests.

Effect: An ownership history for launch/cancellation arbitration only; no ordering of kernel
  instructions or memory accesses. Execution.clcState stores this common arbitration state. ClcOk
  connects it to actual requests and launched traces; separate rules connect responses,
  notifications and failure observations.
-/

/-- Who has claimed a cluster task: the launch of the cluster, or the cancellation request that
canceled it. -/
inductive Owner where
  | launched
  | canceled (request : Nat)
  deriving DecidableEq, Repr

/-- The arbitration state of a grid: the claim on each cluster task and the response to each
request. -/
structure State where
  /-- The claim on each cluster task; `none` while it is unclaimed. -/
  owner : Nat → Option Owner
  /-- None: unresolved; some none: failed; some (some task): successful. -/
  response : Nat → Option (Option Nat)

/-- The state before any task is claimed or request resolved. -/
def initial : State := ⟨fun _ => none, fun _ => none⟩

/-- One atomic step of scheduler arbitration: launching an unclaimed cluster, canceling an
unclaimed cluster for a fresh request, or failing a fresh request. It is neither the issue of
an instruction nor the write of its response. -/
inductive Step (validTask : Nat → Prop) : State → State → Prop where
  | launch (s : State) (task : Nat) (valid : validTask task)
      (pending : s.owner task = none) :
      Step validTask s { s with owner := Function.update s.owner task (some .launched) }
  | success (s : State) (request task : Nat) (valid : validTask task)
      (fresh : s.response request = none) (pending : s.owner task = none) :
      Step validTask s {
        owner := Function.update s.owner task (some (.canceled request))
        response := Function.update s.response request (some (some task)) }
  | failure (s : State) (request : Nat) (fresh : s.response request = none) :
      Step validTask s { s with response := Function.update s.response request (some none) }

/-- Existing ownership and responses cannot be revised by execution extension. -/
def StateExtends (s t : State) : Prop :=
  (∀ task owner, s.owner task = some owner → t.owner task = some owner) ∧
  (∀ request response, s.response request = some response → t.response request = some response)

end PTX.Clc
