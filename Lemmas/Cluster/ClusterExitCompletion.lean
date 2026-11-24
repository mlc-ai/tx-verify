-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Execution.NoAsyncExtension
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Execution.NoAsync
public import Lemmas.Order.WaitingClosure
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Protocol.ClusterLaneCount

@[expose] public section

namespace PTX
open AsyncCopy
noncomputable section

/-- Resource-local cluster histories identify their references' launch cluster. -/
theorem ClusterSources.ref_cluster {L : Launch} {X : Execution} {c : Nat}
    {r : ClusterBarrier.Record EvId} {e : EvId}
    (hs : ClusterSources L X c r) (he : e ∈ r.refs) (hc : c < L.nclusters) :
    L.clusterOfCta (e.1/L.block) = c := by
  have localToCluster {g : Nat} (hg : g < L.block*L.clusterSizeAt c)
      (ht : e.1 = L.clusterStart c*L.block+g) :
      L.clusterOfCta (e.1/L.block) = c := by
    have hb : 0 < L.block := by
      rcases Nat.eq_zero_or_pos L.block with h | h
      · rw [h,Nat.zero_mul] at hg
        omega
      · exact h
    rw [ht,Nat.add_comm,Nat.add_mul_div_right _ _ hb,Nat.add_comm]
    refine Launch.clusterOfCta_clusterStart_add hc ?_
    rw [Nat.div_lt_iff_lt_mul hb,Nat.mul_comm]
    exact hg
  cases r with
  | exit g q =>
    have heq : e = q := by simpa only [ClusterBarrier.Record.refs,List.mem_singleton] using he
    subst q
    exact localToCluster hs.1 hs.2.1
  | arrival cta warp release lanes =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    exact localToCluster (hs p hp).1 (hs p hp).2.1
  | wait cta warp lanes =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    exact localToCluster (hs p hp).1 (hs p hp).2.1

theorem ClusterHistoryOk.ref_cluster {L : Launch} {X : Execution}
    (hh : ClusterHistoryOk L X) {c : Nat} {r : ClusterBarrier.Record EvId} {e : EvId}
    (hr : r ∈ X.clusters c) (he : e ∈ r.refs) : L.clusterOfCta (e.1/L.block) = c := by
  have hc : c < L.nclusters := by
    by_contra hn
    rw [hh.2.1 c (by omega)] at hr
    cases hr
  exact ((hh.2.2 c hc).2.1 r hr).ref_cluster he hc

/-- Source inclusion suffices for checking the provenance of an existing cluster
resource history; the independent resource order itself is retained. -/
theorem ClusterSources.of_events {L : Launch} {X Y : Execution} {c : Nat}
    {r : ClusterBarrier.Record EvId} (hr : ClusterSources L X c r)
    (hevents : ∀ e ev, X.get e = some ev → Y.get e = some ev) : ClusterSources L Y c r := by
  cases r with
  | exit g e =>
    obtain ⟨hg,ht,pc,hget⟩ := hr
    exact ⟨hg,ht,pc,hevents e _ hget⟩
  | arrival cta warp release lanes =>
    intro p hp
    obtain ⟨hg,ht,pc,aligned,hget⟩ := hr p hp
    exact ⟨hg,ht,pc,aligned,hevents p.2 _ hget⟩
  | wait cta warp lanes =>
    intro p hp
    obtain ⟨hg,ht,pc,aligned,hget⟩ := hr p hp
    exact ⟨hg,ht,pc,aligned,hevents p.2 _ hget⟩

theorem ClusterHistoryOk.of_events {L : Launch} {X Y : Execution}
    (hh : ClusterHistoryOk L X) (hc : Y.clusters = X.clusters)
    (hevents : ∀ e ev, X.get e = some ev → Y.get e = some ev) : ClusterHistoryOk L Y := by
  refine ⟨hh.1,?_,?_⟩
  · intro c hct
    rw [hc]
    exact hh.2.1 c hct
  · intro c hct
    obtain ⟨hnd,hs,hrun⟩ := hh.2.2 c hct
    rw [hc]
    exact ⟨hnd,fun r hr => (hs r hr).of_events hevents,hrun⟩

end
end PTX
