-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Cluster.ClusterRecordSnoc
public import Lemmas.Execution.ExecutionGrowth

@[expose] public section

namespace PTX

variable {L : Launch} {X Y : Execution}

theorem ClusterSources.mono {c : Nat} {r : ClusterBarrier.Record EvId}
    (hr : ClusterSources L X c r) (h : X.le Y) : ClusterSources L Y c r := by
  cases r with
  | exit g e =>
    obtain ⟨hg, he, pc, hp⟩ := hr
    exact ⟨hg, he, pc, Execution.le_get h hp⟩
  | arrival cta warp release lanes =>
    intro p hp
    obtain ⟨hg, he, pc, aligned, hb⟩ := hr p hp
    exact ⟨hg, he, pc, aligned, Execution.le_get h hb⟩
  | wait cta warp lanes =>
    intro p hp
    obtain ⟨hg, he, pc, aligned, hb⟩ := hr p hp
    exact ⟨hg, he, pc, aligned, Execution.le_get h hb⟩

/-- The event is a reference of a record of the history of the cluster of its CTA: the record half
of the cluster needs of a returned cluster operation (`KindNeeds`, `clusterWarpNeeds`), which
`DependencyOk.ready` demands of it. -/
def ClusterRecorded (L : Launch) (X : Execution) (e : EvId) : Prop :=
  ∃ r ∈ X.clusters (L.clusterOfCta (e.1 / L.block)), e ∈ r.refs

theorem ClusterRecorded.mono {e : EvId} (hr : ClusterRecorded L X e) (h : X.le Y) :
    ClusterRecorded L Y e := by
  obtain ⟨r, hr, he⟩ := hr
  exact ⟨r, (h.2.2.2.2.2.1 _).subset hr, he⟩

/-- Every returned cluster operation is a reference of a record of its cluster's history: an
arrival and a wait both need their record. This is the record half of the cluster needs of a
returned operation (`KindNeeds`, `clusterWarpNeeds`), which `DependencyOk.ready` demands of it. -/
def ClusterBlocking (L : Launch) (X : Execution) : Prop :=
  ∀ e pc op, X.get e = some ⟨pc, .cluster op⟩ → e.2 + 1 < (X.tr e.1).length →
    ClusterRecorded L X e

/-- A returned cluster operation is recorded: each lane of its warp needs a record of its cluster's
history that holds the operation (`clusterWarpNeeds`). -/
theorem ClusterBlocking.of_consistent {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) : ClusterBlocking L X := by
  intro e pc op he hl
  have hth : e.1 < L.threads := by
    by_contra hn
    rw [hX.outside e.1 (by omega)] at hl
    simp at hl
  have hb : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h | h
    · unfold Launch.threads at hth
      rw [h, Nat.mul_zero] at hth
      omega
    · exact h
  have hw : 0 < warpSize L e.1 := by
    rw [warpSize, Nat.lt_min]
    refine ⟨by omega, ?_⟩
    have h1 : e.1 % L.block / 32 * 32 ≤ e.1 % L.block := Nat.div_mul_le_self _ _
    have h2 := Nat.mod_lt e.1 hb
    omega
  have hret : Returned X e := by
    simp [Returned, he, Kind.resume, hl]
  have hEq : Needs L X e = clusterNeeds L X e op := by
    unfold Needs
    rw [he]
    rfl
  have hmem : Need.node (fun x => ∃ i, ∃ r : ClusterBarrier.Record EvId, ∃ y,
      (X.clusters (L.clusterOfCta (e.1 / L.block)))[i]? = some r ∧ e ∈ r.refs ∧
        x = .thread y ∧ y.1 = warpLane L e.1 0 ∧
        (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
          (X.clusters (L.clusterOfCta (e.1 / L.block)))[j]? =
            some (ClusterBarrier.Record.exit g y))) ∈ Needs L X e := by
    rw [hEq]
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr hw, rfl⟩, rfl⟩)
  obtain ⟨x, -, i, r, y, hi, her, -⟩ := hX.dependency.ready e hret _ hmem
  exact ⟨r, List.mem_of_getElem? hi, her⟩

theorem ClusterSync.mono {e f : EvId} (hs : ClusterSync L X e f) (h : X.le Y) :
    ClusterSync L Y e f := by
  obtain ⟨hc, i, j, hs, hi, hei, hjf, hf⟩ := hs
  refine ⟨hc, i, j, ?_, lt_of_lt_of_le hi (h.1 e.1).length_le, hei, hjf,
    lt_of_lt_of_le hf (h.1 f.1).length_le⟩
  obtain ⟨suffix, hp⟩ := h.2.2.2.2.2.1 (L.clusterOfCta (e.1 / L.block))
  rw [← hp]
  exact hs.append

theorem ClusterHistoryOk.preserving (hx : ClusterHistoryOk L X) (h : X.le Y)
    (hh : Y.clusters = X.clusters) : ClusterHistoryOk L Y := by
  refine ⟨hx.1, ?_, ?_⟩
  · intro c hc
    rw [hh]
    exact hx.2.1 c hc
  · intro c hc
    obtain ⟨hn, hs, ht⟩ := hx.2.2 c hc
    rw [hh]
    exact ⟨hn, fun r hr => (hs r hr).mono h, ht⟩

theorem ClusterHistoryOk.empty (L : Launch) (hl : L.clusterGridValid) :
    ClusterHistoryOk L Execution.empty := by
  refine ⟨hl, fun _ _ => rfl, ?_⟩
  intro c hc
  exact ⟨by simp [Execution.empty], by simp [Execution.empty], ⟨{}, rfl⟩⟩

theorem ClusterSync.not_empty (L : Launch) (e f : EvId) :
    ¬ ClusterSync L Execution.empty e f := by
  rintro ⟨_, i, j, _, hi, _⟩
  simp [Execution.empty] at hi

/-- An arrival of any checked size is a source cluster arrival: the size the barrier was checked
with (`ctas`) enters the run, not the source record. -/
theorem ClusterHistoryOk.arrival_present {L : Launch} {X : Execution} {ctas : Nat}
    (h : ClusterHistoryOk L X) {c : Nat} {e : EvId} {phase : Nat} {release : Bool}
    (ha : ClusterBarrier.ArrivalOf L.block ctas (X.clusters c) e phase release) :
    ∃ pc aligned, X.get e = some ⟨pc, .cluster (.arrive release aligned)⟩ := by
  obtain ⟨i, st, next, cta, warp, lanes, g, hi, _, he, _⟩ := ha
  have hr := List.mem_of_getElem? hi
  by_cases hc : c < L.nclusters
  · exact ((h.2.2 c hc).2.1 _ hr (g, e) he).2.2
  · rw [h.2.1 c (by omega)] at hr
    cases hr

theorem ClusterHistoryOk.ref_present {L : Launch} {X : Execution}
    (h : ClusterHistoryOk L X) {c : Nat} {record : ClusterBarrier.Record EvId} {e : EvId}
    (hr : record ∈ X.clusters c) (he : e ∈ record.refs) : ∃ ev, X.get e = some ev := by
  have hc : c < L.nclusters := by
    by_contra hn
    rw [h.2.1 c (by omega)] at hr
    cases hr
  have hs := (h.2.2 c hc).2.1 record hr
  cases record with
  | exit g f =>
    simp only [ClusterBarrier.Record.refs,List.mem_singleton] at he
    subst f
    obtain ⟨_,_,pc,hp⟩ := hs
    exact ⟨_,hp⟩
  | arrival cta warp release lanes =>
    simp only [ClusterBarrier.Record.refs,List.mem_map] at he
    obtain ⟨p,hp,rfl⟩ := he
    obtain ⟨_,_,pc,aligned,hp⟩ := hs p hp
    exact ⟨_,hp⟩
  | wait cta warp lanes =>
    simp only [ClusterBarrier.Record.refs,List.mem_map] at he
    obtain ⟨p,hp,rfl⟩ := he
    obtain ⟨_,_,pc,aligned,hp⟩ := hs p hp
    exact ⟨_,hp⟩

theorem ClusterHistoryOk.ref_operation {L : Launch} {X : Execution}
    (h : ClusterHistoryOk L X) {c : Nat} {record : ClusterBarrier.Record EvId} {e : EvId}
    (hr : record ∈ X.clusters c) (he : e ∈ record.refs) :
    (∃ pc op, X.get e = some ⟨pc,.cluster op⟩) ∨ ∃ pc, X.get e = some ⟨pc,.exit⟩ := by
  have hc : c < L.nclusters := by
    by_contra hn
    rw [h.2.1 c (by omega)] at hr
    cases hr
  have hs := (h.2.2 c hc).2.1 record hr
  cases record with
  | exit g f =>
    simp only [ClusterBarrier.Record.refs,List.mem_singleton] at he
    subst f
    exact .inr hs.2.2
  | arrival cta warp release lanes =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    obtain ⟨pc,aligned,hp⟩ := (hs p hp).2.2
    exact .inl ⟨pc,_,hp⟩
  | wait cta warp lanes =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    obtain ⟨pc,aligned,hp⟩ := (hs p hp).2.2
    exact .inl ⟨pc,_,hp⟩

theorem ClusterHistoryOk.ref_not_access {L : Launch} {X : Execution}
    (h : ClusterHistoryOk L X) {c : Nat} {record : ClusterBarrier.Record EvId} {e : EvId}
    (hr : record ∈ X.clusters c) (he : e ∈ record.refs) : (X.get e).bind Event.acc = none := by
  rcases h.ref_operation hr he with ⟨pc, op, hp⟩ | ⟨pc, hp⟩ <;> simp [hp, Event.acc]

theorem ClusterHistoryOk.wait_present {L : Launch} {X : Execution} {ctas : Nat}
    (h : ClusterHistoryOk L X) {c : Nat} {e : EvId} {phase : Nat}
    (hw : ClusterBarrier.WaitOf L.block ctas (X.clusters c) e phase) :
    ∃ ev, X.get e = some ev := by
  obtain ⟨i,st,next,cta,warp,lanes,g,hi,_,he,_⟩ := hw
  exact h.ref_present (List.mem_of_getElem? hi) (List.mem_map.mpr ⟨(g,e),he,rfl⟩)

/-- Every source of a cluster waiting dependency is a cluster operation or an exit. -/
theorem ClusterHistoryOk.waits_source {L : Launch} {X : Execution}
    (h : ClusterHistoryOk L X) {e f : EvId} {b b' : Bool}
    (hw : ClusterWaits L X e f b b') :
    (∃ pc op, X.get e = some ⟨pc,.cluster op⟩) ∨ ∃ pc, X.get e = some ⟨pc,.exit⟩ := by
  rcases hw.2.2 with ⟨c,i,j,r,q,hr,_,_,he,_,_⟩ | ⟨_,_,c,r,hr,he,_⟩ |
    ⟨_,_,phase,c,ha,_⟩ | ⟨_,_,phase,c,ha,_⟩
  · exact h.ref_operation (List.mem_of_getElem? hr) he
  · exact h.ref_operation hr he
  all_goals
    obtain ⟨pc,aligned,hp⟩ := h.arrival_present ha
    exact .inl ⟨pc,_,hp⟩

/-- A CTA barrier or cluster barrier instruction issues no asynchronous work, so no
asynchronous update with that origin is recorded on an mbarrier. -/
theorem sync_no_async_before (ht : TmaOk X) {i : EvId} {pc : Nat} {k : Kind}
    (hi : X.get i = some ⟨pc, k⟩)
    (hk : (∃ id count mode, k = .bar id count mode) ∨ ∃ op, k = .cluster op)
    (m : Loc) (p : AsyncCopy.Part) (y : AsyncCopy.Ref) :
    ¬ MBarrier.Before (X.objects m) (.async i p) y := by
  rintro ⟨a, b, ra, rb, ha, hid, _⟩
  have ho := ((ht.2.2.1 m).2.1 ra (List.mem_of_getElem? ha)).1
  rw [hid] at ho
  rcases hk with ⟨id, count, mode, rfl⟩ | ⟨op, rfl⟩ <;>
    cases p <;> simp [AsyncCopy.objectAction, AsyncCopy.issuedBy, hi, bind, Option.bind] at ho

end PTX
