-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
public import Core.Sync.Cluster

@[expose] public section

namespace PTX

/-! ## OBJ-CLUSTER-BARRIER-SYNC — cluster synchronization and rendezvous

Statement: A `barrier.cluster.arrive` returns once its whole warp has arrived, without waiting for
  the cluster, and a `barrier.cluster.wait` returns only when the phase of its own arrival has
  completed. A release arrival makes the thread's earlier generic accesses visible to the operations
  that follow the matched wait, and a relaxed arrival does not. An arrival or wait that the
  barrier cannot perform is ERR-CLUSTER-BARRIER, and ERR-ALIGNED-MISMATCH checks the `.aligned`
  qualifier.

Defs: ClusterSources, ClusterHistoryOk, ClusterSync, ClusterPoint, isCluster

Source:
- §9.7.15.3: "barrier.cluster.arrive instruction marks warps’ arrival at barrier without causing
    executing thread to wait for threads of other participating warps."
- §9.7.15.3: "barrier.cluster.wait instruction causes the executing thread to wait for all
    non-exited threads of the cluster to perform barrier.cluster.arrive ."
- §9.7.15.3: "The optional .relaxed qualifier on barrier.cluster.arrive specifies that there are no
    memory ordering and visibility guarantees provided for the memory accesses performed prior to
    barrier.cluster.arrive ."
- §8.9.4: "A barrier.cluster.arrive operation synchronizes with a barrier.cluster.wait operation."

Direction: reading

Applies: Matched cluster arrive/wait protocols, including release and relaxed arrival and
  aligned/unqualified forms

Premises: Object records have unique source references, correct cluster-local thread IDs and actual
  instruction operands. Both collectives contain all live warp lanes. A cluster's history has the
  size of that cluster (`Launch.clusterSizeAt`, PROG-CLUSTER), regular or preferred.

Effect: Constrains Consistent, contributes baseCausality (`ClusterSync`) and object-order edges
  (MEM-OBJECT-ORDER-CAUSALITY), gives the history the needs of both forms use (`KindNeeds`,
  DEP-ORDER: every lane of the warp in the same record or exited before it, and for a wait every
  arrival of its phase and every exit of the cluster recorded before its record), and gives the
  history that ERR-CLUSTER-BARRIER checks for an operation the barrier cannot perform. Aligned
  divergence and an aligned instruction skipped by an exited lane of its warp are
  ERR-ALIGNED-MISMATCH. Async effects have distinct references and receive no generic-memory edge
  here; accesses between arrival and wait are not published. Each
  history orders this barrier's operations only: arrival is recorded at collective issue, completed
  wait at return. A source trace may end at a pending collective without claiming that it returned.
-/

/-- Each record of the history of cluster `cluster` is backed by actual source events: the lanes
and threads belong to that cluster and execute the matching instruction. -/
def ClusterSources (L : Launch) (X : Execution) (cluster : Nat) :
    ClusterBarrier.Record EvId → Prop
  | .exit g e => g < L.block * L.clusterSizeAt cluster ∧
      e.1 = L.clusterStart cluster * L.block + g ∧
      ∃ pc, X.get e = some ⟨pc, .exit⟩
  | .arrival _ _ release lanes => ∀ p ∈ lanes,
      p.1 < L.block * L.clusterSizeAt cluster ∧
      p.2.1 = L.clusterStart cluster * L.block + p.1 ∧
      ∃ pc aligned, X.get p.2 = some ⟨pc, .cluster (.arrive release aligned)⟩
  | .wait _ _ lanes => ∀ p ∈ lanes,
      p.1 < L.block * L.clusterSizeAt cluster ∧
      p.2.1 = L.clusterStart cluster * L.block + p.1 ∧
      ∃ pc aligned, X.get p.2 = some ⟨pc, .cluster (.wait aligned)⟩

/-- The recorded histories of all clusters of the launch are valid: no source event is counted
twice, every record is backed by source events, and the barrier accepts the records in order. -/
def ClusterHistoryOk (L : Launch) (X : Execution) : Prop :=
  L.clusterGridValid ∧
  (∀ c, L.nclusters ≤ c → X.clusters c = []) ∧
  ∀ c < L.nclusters,
    ((X.clusters c).flatMap ClusterBarrier.Record.refs).Nodup ∧
    (∀ r ∈ X.clusters c, ClusterSources L X c r) ∧
    ∃ s, ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s

/-- Cluster barrier synchronization from `e` to `f`: a release arrival at or after `e` in `e`'s
thread synchronizes with a wait that precedes `f` in `f`'s thread (`Synchronizes`). -/
def ClusterSync (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  SameCluster L e.1 f.1 ∧ ∃ i j,
    ClusterBarrier.Synchronizes L.block (L.clusterSizeOf (e.1 / L.block))
      (X.clusters (L.clusterOfCta (e.1 / L.block))) (e.1, i) (f.1, j) ∧
    i < (X.tr e.1).length ∧ e.2 < i ∧ j < f.2 ∧ f.2 < (X.tr f.1).length

/-- Arrival updates the resource at collective issue; wait records a completed return. -/
def ClusterPoint : ClusterBarrier.Record EvId → Bool
  | .arrival .. => false
  | .wait .. | .exit .. => true

def isCluster (e : Event) : Bool := match e.kind with
  | .cluster _ => true
  | _ => false

/-! ## ERR-CLUSTER-BARRIER — an operation the cluster barrier cannot perform
Statement: An execution is unsafe when a thread arrives at the cluster barrier a second time before
  its phase completes.

Defs: ClusterFault

Source:
- §9.7.15.3 (barrier.cluster): "Each thread must arrive at the barrier only once before the barrier
    completes."
- OBJ-CLUSTER-BARRIER-SYNC

Direction: stricter

Applies: Cluster arrive and wait collectives of a whole warp that are not in the history of their
  cluster

Premises: The recorded history of the cluster is accepted by its barrier, and the collective's
  threads execute the matching instruction with the recorded operands (`ClusterSources`).

Effect: Safety rejection (part of Unsafe). An issued collective that the object cannot perform
  (`ClusterBarrier.Error.isFault`) stays pending and unrecorded, and `ClusterFault` rejects the
  execution: the faulting operation is outside the history, which records every operation the
  object performed before it, and nothing is removed from the possible executions.
-/

/-- A whole warp has issued an arrival or wait that the object cannot perform after its
recorded history. -/
def ClusterFault (L : Launch) (X : Execution) : Prop :=
  ∃ c < L.nclusters, ∃ s,
    ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s ∧
    ∃ (r : ClusterBarrier.Record EvId) (err : ClusterBarrier.Error), ClusterSources L X c r ∧
      (∀ e ∈ r.refs, e ∉ (X.clusters c).flatMap ClusterBarrier.Record.refs) ∧
      r.perform L.block (L.clusterSizeAt c) s = .fault err ∧ err.isFault

end PTX
