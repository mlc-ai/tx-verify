-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Dependency

@[expose] public section

/-! The joint wait relation, a proof device.

`Waits` unions, on issue/completion nodes, the issue-to-completion step, the immediate program-order
step, every object's recorded order, the CTA and cluster barrier dependencies, the warp rendezvous,
synchronizes-with and fence-synchronization edges, the stage order, the dependency layer's issue and
witness edges and the `setmaxnreg` and Tensor Memory allocation orders, and is read through its
transitive closure. It is
not part of `Consistent` and no rule of `Unsafe` uses it: Core orders events only through
`stageCausality`, `SyncObserved`, `ObjectOrder` (one object at a time) and `DepStep`
(MEM-OBJECT-ORDER-CAUSALITY, DEP-ORDER). A `Waits` path may compose the orders of several objects
with program order, and such a path can be cyclic in a consistent execution (load buffering through
two mbarriers, `Tests/Memory/WaitOrderLitmusWitness.lean`). The proofs that use it are rank and
termination arguments over finite executions (`Lemmas/Order/WaitingClosure.lean`,
`Lemmas/Kernel/Existence.lean`) and the implications from `WaitAcyclic` to the split predicates
(`Lemmas/Order/WaitOrderObject.lean`). -/

namespace PTX

noncomputable section

/-- CTA barrier dependencies: the records of one CTA's barrier history in order (all barrier
IDs), arrivals of one instance before its returns, and the update completing an instance
before its returns. -/
def CtaBarWaits (L : Launch) (X : Execution) (e f : EvId) (b b' : Bool) : Prop :=
  (∃ ev, X.get e = some ev) ∧ (∃ ev, X.get f = some ev) ∧
  ((b = false ∧ b' = false ∧ ∃ (c i j : Nat) (r q : CtaBarrier.Record EvId),
      (X.barriers c)[i]? = some r ∧ (X.barriers c)[j]? = some q ∧ i < j ∧
      e ∈ r.refs ∧ f ∈ q.refs) ∨
   (b = false ∧ b' = true ∧ SameCta L e.1 f.1 ∧
      ∃ key, CtaBarArrivalK L X e key ∧ CtaBarK L X f key) ∨
   (b = false ∧ b' = true ∧ ∃ (key i : Nat) (r : CtaBarrier.Record EvId),
      CtaBarK L X f key ∧
      (X.barriers (f.1 / L.block))[i]? = some r ∧ e ∈ r.refs ∧
      CtaBarrier.CompletesAt L.block (X.barriers (f.1 / L.block))
        i (key % 16) (key / 16)))

/-- Cluster barrier dependencies: the records of one cluster history in order, the warp
rendezvous of one record, and each arrival (release or relaxed) of a phase before each wait
of that phase. -/
def ClusterWaits (L : Launch) (X : Execution) (e f : EvId) (b b' : Bool) : Prop :=
  (∃ ev, X.get e = some ev) ∧ (∃ ev, X.get f = some ev) ∧
  ((∃ (c i j : Nat) (r q : ClusterBarrier.Record EvId), (X.clusters c)[i]? = some r ∧
      (X.clusters c)[j]? = some q ∧
      i < j ∧ e ∈ r.refs ∧ f ∈ q.refs ∧ b = ClusterPoint r ∧ b' = ClusterPoint q) ∨
   (b = false ∧ b' = true ∧ ∃ c r, r ∈ X.clusters c ∧ e ∈ r.refs ∧ f ∈ r.refs) ∨
   (b = false ∧ b' = true ∧ ∃ phase c,
      ClusterBarrier.ArrivalOf L.block (L.clusterSizeOf (e.1 / L.block)) (X.clusters c) e phase
        true ∧
      ClusterBarrier.WaitOf L.block (L.clusterSizeOf (e.1 / L.block)) (X.clusters c) f phase) ∨
   (b = false ∧ b' = true ∧ ∃ phase c,
      ClusterBarrier.ArrivalOf L.block (L.clusterSizeOf (e.1 / L.block)) (X.clusters c) e phase
        false ∧
      ClusterBarrier.WaitOf L.block (L.clusterSizeOf (e.1 / L.block)) (X.clusters c) f phase))

/-- `setmaxnreg` warp rendezvous: the issue of every matching lane request precedes each return. -/
def SetMaxNReg.WaitEdge (L : Launch) (X : Execution) (e f : EvId) (b b' : Bool) : Prop :=
  b = false ∧ b' = true ∧ SetMaxNReg.SameRequest L X e f

variable (L : Launch)

/-- Issue/return points for thread instructions, and start/completion points for async
stages, joined into one relation with the immediate program-order step. -/
def Waits (X : Execution) : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop
  | (e, b), (f, b') =>
    (e = f ∧ b = false ∧ b' = true ∧ X.RefPresent e) ∨
    (b = true ∧ b' = false ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧
      i.1 = j.1 ∧ j.2 = i.2 + 1 ∧ j.2 < (X.tr j.1).length) ∨
    (∃ i j, e = .thread i ∧ f = .thread j ∧ CtaBarWaits L X i j b b') ∨
    (b = false ∧ b' = true ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧
      SameWarp L i.1 j.1 ∧ ∃ n, X.ShflK i n ∧ X.ShflK j n) ∨
    (b = false ∧ b' = true ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧
      SameWarp L i.1 j.1 ∧ ∃ k, X.TcK i k ∧ X.TcK j k) ∨
    (b = true ∧ b' = false ∧ StageOrder X (e, b) (f, b')) ∨
    (b = true ∧ b' = true ∧ ∃ m, MBarrier.Before (X.objects m) e f) ∨
    (∃ i j, e = .thread i ∧ f = .thread j ∧ ClusterWaits L X i j b b') ∨
    (b = false ∧ b' = true ∧ ∃ j, f = .thread j ∧ Witness L X e j) ∨
    (b = false ∧ b' = true ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧ WarpBarEdge L X i j) ∨
    (b = true ∧ b' = false ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧ synchronizesWith L X i j) ∨
    (∃ i j, e = .thread i ∧ f = .thread j ∧ SetMaxNReg.WaitEdge L X i j b b') ∨
    (b = true ∧ b' = true ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧
      ∃ cta, Tmem.Pair.Precedes L X cta i j) ∨
    (b = true ∧ b' = false ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧ FenceSync L X i j) ∨
    (b = false ∧ b' = false ∧ IssueStage X (e, b) (f, b'))

variable {L} in
/-- A present node's issue/start point precedes its return/completion point. -/
theorem Waits.node {X : Execution} {e : AsyncCopy.Ref} (h : X.RefPresent e) :
    Waits L X (e, false) (e, true) :=
  .inl ⟨rfl, rfl, rfl, h⟩

/-- The joint wait relation has no cycle. -/
def WaitAcyclic (X : Execution) : Prop :=
  ∀ n, ¬ Relation.TransGen (Waits L X) n n

end

end PTX
