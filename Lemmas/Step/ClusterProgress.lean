-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Cluster
public import Lemmas.Step.Released
public import Lemmas.Snoc.ExtensionSnocFrame
public import Lemmas.Protocol.ClusterLaneCount

@[expose] public section

/-! # Recording a warp's cluster-barrier operation

A proof tool for the progress step at an unrecorded cluster-barrier operation. When every lane of
a warp has the same cluster-barrier operation as its last event, unrecorded, the warp's record
(`Step.warpArrival`, `Step.warpWait`) is appended (`Step.arrival_maximal`,
`Step.wait_maximal`). The record holds each lane's last event (`recorded_in_record`), the last
event of every lane of the warp, so each lane's last event is ready and released
(`released_of_recorded`, `released_of_record`); the lanes form a live warp of the cluster barrier
when none has exited (`liveWarp_warpLanes`). -/

namespace PTX.Step

open PTX

noncomputable section

variable {L : Launch} {X : Execution}

/-- A last event that is a cluster barrier operation is released when a record of its cluster
holds it together with an event of every lane of its warp: the record fills the warp needs
(`clusterWarpNeeds`), and every reference that a wait counts is a present event of a record. -/
theorem released_of_recorded {g pc i : Nat} {op : ClusterOp} {r : ClusterBarrier.Record EvId}
    (hc : ClusterHistoryOk L X)
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster op⟩)
    (hi : (X.clusters (L.clusterOfCta (g / L.block)))[i]? = some r)
    (hg : (g, (X.tr g).length - 1) ∈ r.refs)
    (hwarp : ∀ h ∈ PTX.warpLanes L g, ∃ y ∈ r.refs, y.1 = h) : Released L X g := by
  refine ⟨fun pc' k _ _ => ?_⟩
  intro n hn
  simp only [Needs, hlast, KindNeeds, clusterNeeds, List.mem_append] at hn
  rcases hn with hw | hcount
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hw
    obtain ⟨y, hy, hy1⟩ := hwarp h hh
    exact ⟨.thread y, hc.ref_present (List.mem_of_getElem? hi) hy, i, r, y, hi, hg, rfl, hy1,
      .inl hy⟩
  · cases op with
    | arrive release aligned => simp at hcount
    | wait aligned =>
      obtain ⟨y, hy, hcc⟩ := List.mem_flatMap.mp hcount
      unfold needsIf at hcc
      split at hcc
      · rw [List.mem_singleton] at hcc
        subst hcc
        obtain ⟨r', hr', hyr⟩ := List.mem_flatMap.mp hy
        exact ⟨.thread y, hc.ref_present hr' hyr, rfl⟩
      · simp at hcc

/-- A lane of a warp is in the warp's record, with its last event. -/
theorem mem_warpLanes_of {cta w lt : Nat} (hlt : lt < L.block) (hw : lt / 32 = w) :
    (L.rankOfCta cta * L.block + lt, (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1)) ∈
      warpLanes L X cta w :=
  List.mem_map.mpr ⟨lt, List.mem_filter.mpr ⟨List.mem_range.mpr hlt, by simpa using hw⟩, rfl⟩

/-- The warp's record holds the last event of each of its lanes. -/
theorem recorded_in_record {g : Nat} (hb : 0 < L.block) {R : ClusterBarrier.Record EvId}
    (hR : R.refs = (warpLanes L X (g / L.block) (g % L.block / 32)).map Prod.snd) :
    ClusterRecorded L (X.withClusterRecord (L.clusterOfCta (g / L.block)) R)
      (g, (X.tr g).length - 1) := by
  refine ⟨R, ?_, ?_⟩
  · show R ∈ (X.withClusterRecord (L.clusterOfCta (g / L.block)) R).clusters
      (L.clusterOfCta (g / L.block))
    rw [Execution.clusters_withClusterRecord_self]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · rw [hR]
    have hm := mem_warpLanes_of (L := L) (X := X) (cta := g / L.block) (Nat.mod_lt g hb)
      (rfl : g % L.block / 32 = g % L.block / 32)
    have hgeq : g / L.block * L.block + g % L.block = g := Nat.div_add_mod' g L.block
    rw [hgeq] at hm
    exact List.mem_map.mpr ⟨_, hm, rfl⟩

/-- After the record of the warp of `g` is appended to the history of its cluster, the last event
of `g`, a cluster barrier operation of the record, is released: the record holds the last event of
every lane of the warp. -/
theorem released_of_record {g pc : Nat} {op : ClusterOp} (hb : 0 < L.block)
    {R : ClusterBarrier.Record EvId}
    (hR : R.refs = (warpLanes L X (g / L.block) (g % L.block / 32)).map Prod.snd)
    (hc : ClusterHistoryOk L (X.withClusterRecord (L.clusterOfCta (g / L.block)) R))
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster op⟩) :
    Released L (X.withClusterRecord (L.clusterOfCta (g / L.block)) R) g := by
  have hi : ((X.withClusterRecord (L.clusterOfCta (g / L.block)) R).clusters
      (L.clusterOfCta (g / L.block)))[(X.clusters (L.clusterOfCta (g / L.block))).length]? =
        some R := by
    rw [Execution.clusters_withClusterRecord_self]
    simp
  have hgd : g / L.block * L.block + g % L.block = g := Nat.div_add_mod' g L.block
  have hgm : g % L.block < L.block := Nat.mod_lt g hb
  refine released_of_recorded hc hlast hi ?_ ?_
  · rw [hR]
    have hm := mem_warpLanes_of (L := L) (X := X) (cta := g / L.block) hgm
      (rfl : g % L.block / 32 = g % L.block / 32)
    rw [hgd] at hm
    exact List.mem_map.mpr ⟨_, hm, rfl⟩
  · intro h hh
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hh
    rw [List.mem_range] at hl
    unfold warpSize at hl
    have hlt : g % L.block / 32 * 32 + l < L.block := by omega
    have hw : (g % L.block / 32 * 32 + l) / 32 = g % L.block / 32 := by omega
    refine ⟨(g / L.block * L.block + (g % L.block / 32 * 32 + l),
      (X.tr (g / L.block * L.block + (g % L.block / 32 * 32 + l))).length - 1), ?_, ?_⟩
    · rw [hR]
      exact List.mem_map.mpr ⟨_, mem_warpLanes_of hlt hw, rfl⟩
    · show g / L.block * L.block + (g % L.block / 32 * 32 + l) = warpLane L g l
      unfold warpLane laneOf
      omega

/-- The local threads of a warp's record are a live warp when none of them has exited. -/
theorem liveWarp_warpLanes {s : ClusterBarrier.State} {cta w : Nat} (hv : L.clusterGridValid)
    (hcta : cta < L.grid) (hb : 0 < L.block) (hw : w * 32 < L.block)
    (hlive : ∀ lt, lt < L.block → lt / 32 = w → L.rankOfCta cta * L.block + lt ∉ s.exited) :
    ClusterBarrier.liveWarp L.block (L.clusterSizeAt (L.clusterOfCta cta)) s (L.rankOfCta cta) w
      ((warpLanes L X cta w).map Prod.fst) = true := by
  have hmap : (warpLanes L X cta w).map Prod.fst =
      ((List.range L.block).filter fun lt => decide (lt / 32 = w)).map
        (L.rankOfCta cta * L.block + ·) := by
    simp [warpLanes, List.map_map, Function.comp_def]
  have hrank : L.rankOfCta cta < L.clusterSizeAt (L.clusterOfCta cta) := (cta_cluster hv hcta).2.1
  rw [hmap]
  apply decide_eq_true
  refine ⟨hb, hrank, hw, ?_, ?_, ?_, ?_⟩
  · intro hnil
    have : w * 32 ∈ (List.range L.block).filter fun lt => decide (lt / 32 = w) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hw, by simp⟩
    rw [List.map_eq_nil_iff] at hnil
    rw [hnil] at this
    cases this
  · exact (List.nodup_range.filter _).map (fun a b h => by simpa using h)
  · intro y hy
    obtain ⟨lt, hlt, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hlr, hlw⟩ := List.mem_filter.mp hlt
    have hl := List.mem_range.mp hlr
    simp only [decide_eq_true_eq] at hlw
    obtain ⟨h1, -⟩ := lane_index hv hcta hl
    refine ⟨h1, ?_, ?_, hlive lt hl hlw⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hl, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl, hlw]
  · intro lane hlane
    dsimp only
    intro hloc hne
    refine List.mem_map.mpr ⟨w * 32 + lane, List.mem_filter.mpr ⟨List.mem_range.mpr hloc, ?_⟩, rfl⟩
    have := Finset.mem_range.mp hlane
    simp only [decide_eq_true_eq]
    omega

end

end PTX.Step
