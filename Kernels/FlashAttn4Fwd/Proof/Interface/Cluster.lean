-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bars
public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Lemmas.Kernel.Progress.Cluster

@[expose] public section

/-! # What the thread layer exports for the cluster start

Every thread runs the prologue first: shuffles, elections, the barrier initializations of warps
0 and 12 and the two `fence.mbarrier_init.release.cluster`; then the start cluster barrier, a
`barrier.cluster.arrive.relaxed` (`.arrive false false`: relaxed, not aligned) and a
`barrier.cluster.wait` (`.wait false`), its only cluster-barrier operations; every other event
(but undefined behaviour) follows the wait. `clFirst X g` is the index of thread `g`'s first
cluster-barrier operation. The fields are facts of each thread's own events (`ClusterFacts`),
proved from the prologue's run invariant and the roles' (which have no cluster-barrier operation
and start after the wait). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof

noncomputable section

/-- The index of thread `g`'s first cluster-barrier operation (`Sched.clFirst`). -/
scoped notation "clFirst" => Sched.clFirst

/-- The kinds of the prologue's events, which come before the start cluster barrier: shuffles,
elections, barrier initializations, their fences and the cluster-barrier operations. (The roles
also shuffle and elect, after the wait.) -/
def PreKind : Kind → Prop
  | .shfl .. | .elect .. | .mbInit .. | .fenceMbarInit | .cluster _ => True
  | _ => False

/-- The cluster start, from the threads' own events. -/
structure ClusterFacts (L : Launch) (X : Execution) : Prop where
  /-- The first cluster-barrier operation is the relaxed, unaligned arrival. -/
  arrive : ∀ {g : Nat}, g < L.threads → clFirst X g < (X.tr g).length →
    ∃ pc, X.get (g, clFirst X g) = some ⟨pc, .cluster (.arrive false false)⟩
  /-- The next event is the unaligned wait. -/
  wait : ∀ {g : Nat}, g < L.threads → clFirst X g + 1 < (X.tr g).length →
    ∃ pc, X.get (g, clFirst X g + 1) = some ⟨pc, .cluster (.wait false)⟩
  /-- These are the thread's only cluster-barrier operations. -/
  cl_only : ∀ {g k pc : Nat} {op : ClusterOp}, g < L.threads →
    X.get (g, k) = some ⟨pc, .cluster op⟩ → k = clFirst X g ∨ k = clFirst X g + 1
  /-- Every event of a kind other than the prologue's (and other than undefined behaviour)
  follows the wait. -/
  post : ∀ {g j : Nat} {ev : Event}, g < L.threads → X.get (g, j) = some ev →
    ¬ PreKind ev.kind → (∀ f, ev.kind ≠ .ub f) → clFirst X g + 1 < j
  /-- A thread that reaches the arrival shuffled first (`shfl_0`, the shared base). -/
  shfl0 : ∀ {g : Nat}, g < L.threads → clFirst X g < (X.tr g).length →
    0 < clFirst X g ∧ ∃ pc md a b c r o, X.get (g, 0) = some ⟨pc, .shfl md a b c r o⟩
  /-- In a thread that reaches the arrival, a barrier initialization is followed by a
  `fence.mbarrier_init` before the arrival. -/
  fence : ∀ {g a pc c : Nat} {m : Loc}, g < L.threads → clFirst X g < (X.tr g).length →
    X.get (g, a) = some ⟨pc, .mbInit m c⟩ →
      ∃ f pcf, a < f ∧ f < clFirst X g ∧ X.get (g, f) = some ⟨pcf, .fenceMbarInit⟩
  /-- Every barrier initialization is of a table barrier of the thread's CTA, with its count:
  warp 12's of the handshake barrier, warp 0's of the others. -/
  init_site : ∀ {g k pc c : Nat} {m : Loc}, g < L.threads →
    X.get (g, k) = some ⟨pc, .mbInit m c⟩ →
      ∃ b : FBar, m = b.loc L (ctaOf L g) ∧ c = b.count ∧
        (b = .dealloc → warpOf L g = 12) ∧ (b ≠ .dealloc → warpOf L g = 0)

/-- The kernel's threads synchronize at a cluster start barrier (`Sched.ClusterStart`). -/
theorem ClusterFacts.toStart {L : Launch} {X : Execution} (hc : ClusterFacts L X) :
    Sched.ClusterStart L X :=
  ⟨hc.arrive, hc.wait, hc.cl_only, fun hg hj => hc.post hg hj id fun _ h => by cases h⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
