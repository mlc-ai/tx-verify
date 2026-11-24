-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Cluster
public import Lemmas.Cluster.ClusterStartAny
public import Lemmas.Protocol.ClusterLaneCount
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The cluster start

All 1024 threads of a cluster pass one cluster-barrier phase, after the barrier initializations
and their `fence.mbarrier_init.release.cluster`: a relaxed, unaligned arrival and an unaligned
wait (`ClusterFacts`). From it:

* **ClusterOk.** Each thread's operations alternate (`Sched.ops_alternate`), so no cluster-barrier
  collective faults (`no_cluster_fault`); none is aligned, so none mismatches
  (`no_cluster_mismatch`).
* **InitPublished.** Every barrier initialization is published to every event of the cluster
  that is not of the prologue's kinds (`init_published`): the restricted pattern of
  OBJ-MBAR-INIT-PUBLICATION (initialization, `fence.mbarrier_init`, relaxed arrival, wait of the
  same generation, program order), since a relaxed arrival does not synchronize.
* **PeerStarted.** Every CTA of the cluster started before the issue of such an event
  (`peer_started`): thread 0 of the CTA shuffled before its arrival, the event's thread waited
  for that arrival, and the wait guards the event.

Publication is not order: the history of a barrier puts its initialization before an operation
only when the initialization happens before the operation (`object_not_before_of_baseCausality`),
and the relaxed arrival gives no such order. That a table barrier's initialization is the first
record of its history is therefore not a consequence of this protocol. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.ClusterStart
open PTX PTX.Proof ClusterLanes

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread's events before its first cluster-barrier operation are neither cluster-barrier
operations nor exits. -/
theorem before (hc : ClusterFacts L X) :
    ∀ g < L.threads, ∀ j < clFirst X g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit := by
  intro g hg j hj ev he
  refine ⟨fun op hk => ?_, fun hk => ?_⟩
  · have h := Sched.not_cluster_before hj he
    simp [PTX.isCluster, hk] at h
  · have h := hc.post hg he (by rw [hk]; exact id) (by rw [hk]; exact fun f h => by cases h)
    omega

theorem arrive' (hc : ClusterFacts L X) : ∀ g < L.threads, clFirst X g < (X.tr g).length →
    ∃ pc al, X.get (g, clFirst X g) = some ⟨pc, .cluster (.arrive false al)⟩ :=
  fun _ hg hl => (hc.arrive hg hl).imp fun _ h => ⟨_, h⟩

theorem wait' (hc : ClusterFacts L X) : ∀ g < L.threads, clFirst X g + 1 < (X.tr g).length →
    ∃ pc al, X.get (g, clFirst X g + 1) = some ⟨pc, .cluster (.wait al)⟩ :=
  fun _ hg hl => (hc.wait hg hl).imp fun _ h => ⟨_, h⟩

/-- **No cluster-barrier collective of the kernel faults.** -/
theorem no_cluster_fault (hX : Consistent L kernel asms mem0 X) (hc : ClusterFacts L X) :
    ¬ ClusterFault L X :=
  no_fault_of_ops hX.cluster (ClusterBlocking.of_consistent hX) hX.object
    (Sched.ops_alternate hX hc.toStart)

/-- **No cluster-barrier operation of the kernel mismatches**: none is aligned, so neither
`barrier.cluster` clause of `AlignedMismatch` applies. -/
theorem no_cluster_mismatch (hX : Consistent L kernel asms mem0 X) (hc : ClusterFacts L X) :
    ¬ AlignedClass.cluster.Divergent L kernel X ∧ ¬ AlignedClass.cluster.Exited L kernel X := by
  have hal : ∀ {e : EvId} {pc : Nat} {op : ClusterOp},
      X.get e = some ⟨pc, .cluster op⟩ → op.aligned = false := by
    intro e pc op he
    rcases Sched.cl_event hX hc.toStart he with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨g, h, i, j, pc, pc', op, op', -, hi, hj, -, hor, -⟩ :=
      (AlignedClass.divergent_cluster_iff L).mp h
    rcases hor with ho | ho
    · rw [hal hi] at ho; cases ho
    · rw [hal hj] at ho; cases ho
  · obtain ⟨e, f, k, pc, op, -, he, ha, -⟩ := (AlignedClass.exited_cluster_iff L).mp h
    rw [hal he] at ha; cases ha

/-- **Every barrier initialization is published to every later event of its cluster**: an event
of a thread of the same cluster whose kind is not the prologue's (nor undefined behaviour). -/
theorem init_published (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) {g0 a pc c : Nat} {m : Loc}
    (hinit : X.get (g0, a) = some ⟨pc, .mbInit m c⟩) {g j : Nat} {ev : Event}
    (he : X.get (g, j) = some ev) (hk : ¬ PreKind ev.kind) (hub : ∀ f, ev.kind ≠ .ub f)
    (hcl : clusterOf L g0 = clusterOf L g) : InitPublished L X (g0, a) (g, j) m := by
  have hg0 := Frame.lt_of_get hX hinit
  have hg := Frame.lt_of_get hX he
  -- `g` passed the start barrier, so `g0`, of its cluster, reached its arrival.
  obtain ⟨-, ha, -⟩ := start_of_post_event hX (by rw [hpre.block]; decide)
    hpre.oneDimLaunch.1 (before hc) (arrive' hc) (wait' hc) ⟨hg0, hg, hcl⟩ he
    (hc.post hg he hk hub)
  obtain ⟨_, _, hapres⟩ := hX.cluster.arrival_present ha
  obtain ⟨f, pcf, haf, hf, hfe⟩ := hc.fence hg0 (len_of_get hapres) hinit
  obtain ⟨b, rfl, -, -⟩ := hc.init_site hg0 hinit
  exact init_fence_published_of_post hX (by rw [hpre.block]; decide) hpre.oneDimLaunch.1
    (before hc) (arrive' hc)
    (wait' hc) ⟨pc, hinit⟩ hfe haf hf rfl rfl ⟨hg0, hg, hcl⟩ he (hc.post hg he hk hub)

/-- **Every CTA of a cluster started before the issue of a later event of the cluster**, an
event whose kind is not the prologue's: its thread 0's first shuffle precedes the event's issue
in the enabling order. -/
theorem peer_started (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) {g j : Nat} {ev : Event} (he : X.get (g, j) = some ev)
    (hk : ¬ PreKind ev.kind) (hub : ∀ f, ev.kind ≠ .ub f) {owner : Nat} (how : owner < L.grid)
    (hcl : L.clusterOfCta owner = clusterOf L g) (e : AsyncCopy.Ref) (hi : e.issuer = (g, j)) :
    PeerSharedStarted L kernel asms X e owner := by
  have hb : 0 < L.block := by rw [hpre.block]; decide
  have hg := Frame.lt_of_get hX he
  have hj := hc.post hg he hk hub
  have hg0 : owner * L.block < L.threads := by
    simp only [Launch.threads]
    exact Nat.mul_lt_mul_of_pos_right how hb
  have hdiv : owner * L.block / L.block = owner := Nat.mul_div_cancel _ hb
  have hsc : SameCluster L (owner * L.block) g := ⟨hg0, hg, by rw [hdiv]; exact hcl⟩
  obtain ⟨-, ha, -⟩ := start_of_post_event hX hb hpre.oneDimLaunch.1 (before hc) (arrive' hc)
    (wait' hc) hsc he hj
  obtain ⟨_, _, hapres⟩ := hX.cluster.arrival_present ha
  obtain ⟨h0, pc, md, x, y, z, r, o, hs⟩ := hc.shfl0 hg0 (len_of_get hapres)
  refine ⟨(owner * L.block, 0), _, hg0, hdiv, hs, ?_⟩
  rw [hi]
  exact lifetime_of_post hX hb hpre.oneDimLaunch.1 (before hc) (arrive' hc) (wait' hc) hsc
    (blockingReturn_of_shfl hs h0 (len_of_get hapres)) he hj

end
end PTX.Kernels.FlashAttn4Fwd.Proof.ClusterStart
