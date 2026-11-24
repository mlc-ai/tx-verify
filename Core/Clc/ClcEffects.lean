-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Clc.ClcOwnership
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Logic.Relation
public import Core.Sync.Cluster
public import Core.Data.AsyncTypes
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace PTX.Clc
noncomputable section

/-! ## OBJ-CLC-ARBITRATION — responses derived from grid arbitration
Statement: The response to a cancellation request is the outcome that arbitration assigned to that
  request: failure, or the canceled cluster, reported as the coordinates of its first CTA. The
  response does not carry the shape of the cluster. Arbitration chooses among the clusters of the
  launch's placement, of either shape. The canceled CTAs are those of the canceled cluster
  (`Launch.clusterOfCta`, OBJ-CLC-OWNERSHIP). All requests of an execution share one arbitration
  history that starts from the empty ownership state.

Defs: Clc.requestId, Clc.ValidTask, Clc.validTask_oneDim, Clc.ArbitrationOk, Clc.responseOf,
  Clc.responseOf_oneDim, Clc.Result

Source:
- §9.7.15.18 (unique canceled cluster and its first CTA)
- EXT-CLUSTER-RANK (the first CTA of cluster `t` is its CTA of rank 0, CTA number
    `Launch.clusterStart t`, whose `%ctaid` is the cluster's origin; in a one-dimensional launch it
    is `(t * clusterSize, 0, 0)`)
- EXT-PREFERRED-CLUSTER

Direction: scope

Applies: Launches of any shape, with 32-bit CTA coordinates

Premises: One common arbitration state is reachable from the empty grid ownership state. Dynamic
  requests are identified by their actual issuing event.

Effect: Connects response payloads to the launch/cancellation ownership rules. The state must be
  shared by all requests of an execution; a response does not choose its own state.
-/
/-- The identity of the request issued by event `i`. -/
def requestId (i : EvId) : Nat := Nat.pair i.1 i.2

/-- `task` designates a cluster of a valid launch whose first CTA's coordinates fit in 32 bits. -/
def ValidTask (L : Launch) (task : Nat) : Prop :=
  L.clusterGridValid ∧ task < L.nclusters ∧
    (L.ctaidOf (L.clusterStart task)).x < 2 ^ 32 ∧ (L.ctaidOf (L.clusterStart task)).y < 2 ^ 32 ∧
    (L.ctaidOf (L.clusterStart task)).z < 2 ^ 32

/-- `state` is reachable from the empty ownership state by arbitration steps. -/
def ArbitrationOk (L : Launch) (state : State) : Prop :=
  Relation.ReflTransGen (Step (ValidTask L)) initial state

/-- The response for request `i` with outcome `task`: the `%ctaid` of the first CTA of the
canceled cluster, the CTA of rank 0, or failure. -/
def responseOf (L : Launch) (i : EvId) (task : Option Nat) : ClcResponse :=
  ⟨requestId i, task.map fun t =>
    let c := L.ctaidOf (L.clusterStart t)
    (BitVec.ofNat 32 c.x, BitVec.ofNat 32 c.y, BitVec.ofNat 32 c.z)⟩

/-- In a one-dimensional launch the first CTA of cluster `t` is `(t * clusterSize, 0, 0)`, the
response of the one-dimensional model. -/
theorem responseOf_oneDim {L : Launch} (h : L.OneDim) (i : EvId) (task : Option Nat) :
    responseOf L i task =
      ⟨requestId i, task.map fun t => (BitVec.ofNat 32 (t * L.clusterSize.val), 0, 0)⟩ := by
  simp only [responseOf, Launch.oneDim_clusterStart h, Launch.oneDim_ctaidOf h]
  rfl

/-- In a one-dimensional launch a task is the condition of the one-dimensional model: a cluster
number below `grid / clusterSize` whose first CTA number fits in 32 bits. -/
theorem validTask_oneDim {L : Launch} (h : L.OneDim) (task : Nat) :
    ValidTask L task ↔
      L.clusterGridValid ∧ task < L.grid / L.clusterSize.val ∧
        task * L.clusterSize.val < 2 ^ 32 := by
  simp [ValidTask, Launch.oneDim_clusterStart h, Launch.oneDim_ctaidOf h, h.2.2.2.1]

/-- `r` is the response that `state` assigns to the request of event `i`. -/
def Result (L : Launch) (i : EvId) (state : State) (r : ClcResponse) : Prop :=
  ∃ task, state.response (requestId i) = some task ∧ r = responseOf L i task

/-! ## DEP-CLC-EFFECTS — per-CTA response writes and completion notifications
Statement: A cancellation request writes one 16-byte response to the response address in each target
  CTA, which is the issuing CTA or, with multicast, every CTA of its cluster. It then signals a
  16-byte complete-tx on the mbarrier of that CTA. All copies carry the same response, and each
  write follows the resolution of the request and each notification follows its write.

Defs: Clc.Spec, Clc.Target, Clc.Effects, Clc.EffectsOk, Clc.ResponseWrite, Clc.Completion,
  Clc.Extends

Source:
- §9.7.15.18 (try_cancel, multicast and complete-tx)

Direction: reading

Applies: One issued cancellation request with local shared response/mbarrier addresses, optionally
  multicast to every CTA of its cluster

Premises: The response is a result of this dynamic request. Writes and notifications target only the
  selected CTAs. A notification requires that CTA's response write.

Effect: Operation-local effects; their stage order (issue → resolve → write c → notify c) is
  `StageOrder` (DEP-ASYNC-STAGE-ORDER). A response failure is also written and notified. Neither it
  nor a successful response implicitly completes a memory write. A notification in one CTA does not
  establish that another CTA's copy or notification is present. The response location and mbarrier
  keep their offsets in every target CTA. Execution.clc stores these effects; the active memory and
  object queries use them.
-/

/-- The operands of a cancellation request: the shared address of the response, the shared
address of the mbarrier to notify, and whether the response is multicast to the cluster. -/
structure Spec where
  response : Loc
  mbar : Loc
  multicast : Bool
  deriving DecidableEq, Repr

/-- CTA `cta` is a target of the request that `issuer` issues: the issuing CTA, or with
multicast every CTA of its cluster. -/
def Target (L : Launch) (issuer : EvId) (s : Spec) (cta : Nat) : Prop :=
  L.clusterGridValid ∧ issuer.1 < L.threads ∧
  s.response.space = .shared ∧ s.mbar.space = .shared ∧
  s.response.cta = issuer.1 / L.block ∧ s.mbar.cta = issuer.1 / L.block ∧
  cta < L.grid ∧
  (if s.multicast then L.clusterOfCta cta = L.clusterOfCta (issuer.1 / L.block)
   else cta = issuer.1 / L.block)

/-- The effects of one request so far: its resolved response, and the CTAs that received the
response write and the completion notification. -/
structure Effects where
  /-- Arbitration has resolved; this is not a shared memory write. -/
  resolved : Option ClcResponse := none
  /-- The target CTAs whose response write is present. -/
  written : Finset Nat := ∅
  /-- The target CTAs whose completion notification is present. -/
  notified : Finset Nat := ∅

/-- Every request uses the same execution-level arbitration state. -/
structure EffectsOk (L : Launch) (issuer : EvId) (s : Spec)
    (state : State) (e : Effects) : Prop where
  arbitration : ArbitrationOk L state
  result : ∀ r, e.resolved = some r → Result L issuer state r
  writes : ∀ c ∈ e.written, Target L issuer s c ∧ e.resolved.isSome
  notified : ∀ c ∈ e.notified, c ∈ e.written

/-- The write of the 16-byte response into the response address of CTA `cta`. -/
def ResponseWrite (s : Spec) (e : Effects) (cta : Nat) (a : Acc) (bs : List Byte) : Prop :=
  cta ∈ e.written ∧ ∃ r, e.resolved = some r ∧
    a = { loc := { s.response with cta := cta }, size := 16 } ∧ bs = (Value.clc r).toBytes

/-- The 16-byte complete-tx on the mbarrier of CTA `cta` that notifies the response write. -/
def Completion (s : Spec) (e : Effects) (cta : Nat) (m : Loc) (bytes : Nat) : Prop :=
  cta ∈ e.notified ∧ m = { s.mbar with cta := cta } ∧ bytes = 16

def Extends (e f : Effects) : Prop :=
  (∀ r, e.resolved = some r → f.resolved = some r) ∧
  e.written ⊆ f.written ∧ e.notified ⊆ f.notified

end
end PTX.Clc
