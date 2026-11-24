-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ClusterLanes
public import Lemmas.Protocol.ClusterTrace

@[expose] public section

/-! # A lane's records are its thread's recorded events

In a checked cluster history, the records that contain a cluster-local lane (as an arrival or a
wait) are as many as the recorded events of the lane's thread, when the thread has no exit
event: each such record holds exactly one event of the thread (`countP_ownAny_le_rec`,
`rec_le_countP_ownAny`). A lane whose thread has no exit event has not exited
(`lane_live`).

The cluster barrier object lets a lane arrive again without a wait, so the alternation of a lane's
records comes from the program: when every thread's cluster operations alternate an arrival and a
wait in program order (`OpsAlternate`, for any number of operations per thread), a lane's records
alternate too (`alt_of_ops`), the lane of a pending operation has the status of its records
(`lane_pending`), and no cluster barrier collective faults (`no_fault_of_ops`). -/

namespace PTX

/-- The cluster start of a later cluster is not below that of an earlier one. -/
theorem Launch.clusterStart_succ_le (L : Launch) (k : Nat) :
    L.clusterStart k ≤ L.clusterStart (k + 1) := by
  rw [Launch.clusterStart]
  exact Nat.le_add_right _ _

/-- The cluster start is monotone. -/
theorem Launch.clusterStart_mono {L : Launch} : Monotone L.clusterStart :=
  monotone_nat_of_le_succ (Launch.clusterStart_succ_le L)

/-- The clusters of a launch partition the CTA numbers: after the first `k` clusters, CTA
`clusterStart c + r` lies in cluster `c` at rank `r`. -/
theorem Launch.locate_clusterStart {L : Launch} :
    ∀ (n k c r : Nat), k ≤ c → c < k + n → r < L.clusterSizeAt c →
      L.locate n k (L.clusterStart c + r - L.clusterStart k) = (c, r) := by
  intro n
  induction n with
  | zero =>
    intro k c r hkc hcn _
    omega
  | succ n ih =>
    intro k c r hkc hcn hr
    rcases Nat.lt_or_ge k c with hlt | hge
    · have hmono : L.clusterStart (k + 1) ≤ L.clusterStart c :=
        Launch.clusterStart_mono (L := L) (Nat.succ_le_of_lt hlt)
      have hstep : L.clusterStart (k + 1) = L.clusterStart k + L.clusterSizeAt k := rfl
      simp only [Launch.locate]
      split
      · rename_i hbad
        have hsz : L.clusterSizeAt k = (L.clusterPlaces k).shape.prod := rfl
        omega
      · have hsub : L.clusterStart c + r - L.clusterStart k -
            (L.clusterPlaces k).shape.prod = L.clusterStart c + r - L.clusterStart (k + 1) := by
          rw [hstep]
          exact Nat.sub_sub _ _ _
        rw [hsub]
        exact ih (k + 1) c r (by omega) (by omega) hr
    · have hkc' : c = k := by omega
      rw [hkc'] at hr ⊢
      have hrr : L.clusterStart k + r - L.clusterStart k = r := by omega
      have hr' : r < (L.clusterPlaces k).shape.prod := hr
      simp only [Launch.locate]
      rw [hrr]
      split
      · rfl
      · rename_i hneg
        exact absurd hr (by simpa only [Launch.clusterSizeAt] using hneg)

/-- CTA `clusterStart c + r` lies in cluster `c` when `r` is a rank of cluster `c`. -/
theorem Launch.clusterOfCta_clusterStart_add {L : Launch} {c r : Nat}
    (hc : c < L.nclusters)
    (hr : r < L.clusterSizeAt c) : L.clusterOfCta (L.clusterStart c + r) = c := by
  have h := Launch.locate_clusterStart (L := L) L.nclusters 0 c r (Nat.zero_le c)
    (by simpa using hc) hr
  simp only [Launch.clusterStart, Nat.sub_zero] at h
  unfold Launch.clusterOfCta
  rw [h]

end PTX

namespace PTX.ClusterLanes
open PTX ClusterBarrier ClusterPhase Classical

variable {L : Launch} {X : Execution}

/-- Whether position `j` of thread `h`'s trace is a recorded cluster barrier operation. -/
noncomputable def recAt (L : Launch) (X : Execution) (h j : Nat) : Bool :=
  decide (ClusterRecorded L X (h, j)) && ((X.tr h)[j]?).any isCluster

/-- The number of recorded cluster barrier operations of thread `h`. -/
noncomputable def recCount (L : Launch) (X : Execution) (h : Nat) : Nat :=
  ((List.range (X.tr h).length).filter (recAt L X h)).length

/-- A cluster barrier operation at position `j` of a trace. -/
theorem cluster_get {h j : Nat} (hj : ((X.tr h)[j]?).any isCluster = true) :
    ∃ pc op, X.get (h, j) = some ⟨pc, .cluster op⟩ := by
  cases hj' : (X.tr h)[j]? with
  | none => rw [hj'] at hj; cases hj
  | some ev =>
    rw [hj'] at hj
    obtain ⟨pc, k⟩ := ev
    cases k <;> simp only [Option.any_some, isCluster, Bool.false_eq_true] at hj
    exact ⟨pc, _, hj'⟩

/-- The event of lane `x` in a record. -/
def laneRef (x : Nat) : Record EvId → Option EvId
  | .arrival _ _ _ lanes | .wait _ _ lanes => (lanes.find? (·.1 == x)).map Prod.snd
  | .exit _ _ => none

theorem laneRef_isSome (x : Nat) (r : Record EvId) : (laneRef x r).isSome = ownAny x r := by
  cases r with
  | exit j e => rfl
  | arrival cta warp rel lanes =>
    simp only [laneRef, Option.isSome_map, ownAny, ownArrival, ownWait, Bool.or_false]
    rw [Bool.eq_iff_iff, List.find?_isSome, decide_eq_true_iff]
    simp
  | wait cta warp lanes =>
    simp only [laneRef, Option.isSome_map, ownAny, ownArrival, ownWait, Bool.false_or]
    rw [Bool.eq_iff_iff, List.find?_isSome, decide_eq_true_iff]
    simp

theorem laneRef_mem {x : Nat} {r : Record EvId} {e : EvId} (h : laneRef x r = some e) :
    e ∈ r.refs ∧ ∃ lanes : List (Nat × EvId), (x, e) ∈ lanes ∧
      ((∃ cta warp rel, r = .arrival cta warp rel lanes) ∨
        ∃ cta warp, r = .wait cta warp lanes) := by
  cases r with
  | exit j e' => cases h
  | arrival cta warp rel lanes =>
    simp only [laneRef, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    have hm := List.mem_of_find?_eq_some hp
    have hx := List.find?_some hp
    simp only [beq_iff_eq] at hx
    obtain ⟨a, b⟩ := p
    simp only at hx
    subst hx
    exact ⟨List.mem_map.mpr ⟨_, hm, rfl⟩, lanes, hm, .inl ⟨cta, warp, rel, rfl⟩⟩
  | wait cta warp lanes =>
    simp only [laneRef, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    have hm := List.mem_of_find?_eq_some hp
    have hx := List.find?_some hp
    simp only [beq_iff_eq] at hx
    obtain ⟨a, b⟩ := p
    simp only at hx
    subst hx
    exact ⟨List.mem_map.mpr ⟨_, hm, rfl⟩, lanes, hm, .inr ⟨cta, warp, rfl⟩⟩

/-- Choosing at most one reference per record keeps distinct references distinct. -/
theorem filterMap_laneRef_nodup (x : Nat) {h : List (Record EvId)}
    (hnd : (h.flatMap Record.refs).Nodup) : (h.filterMap (laneRef x)).Nodup := by
  induction h with
  | nil => simp
  | cons r rs ih =>
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨-, hrs, hdis⟩ := hnd
    rw [List.filterMap_cons]
    cases hr : laneRef x r with
    | none => exact ih hrs
    | some e =>
      refine List.nodup_cons.mpr ⟨fun he => ?_, ih hrs⟩
      obtain ⟨r', hr', he'⟩ := List.mem_filterMap.mp he
      have h1 := (laneRef_mem hr).1
      have h2 := (laneRef_mem he').1
      exact hdis e h1 e (List.mem_flatMap.mpr ⟨r', hr', h2⟩) rfl

/-- A filter of `range` by positions of a list counts the list. -/
theorem length_filter_range {β : Type} (p : β → Bool) (l : List β) :
    ((List.range l.length).filter fun i => (l[i]?).any p).length = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      List.countP_cons]
    simp only [List.getElem?_cons_zero, Option.any_some, Function.comp_def,
      List.getElem?_cons_succ]
    split <;> simp_all

/-- The cluster of a thread given by its cluster-local lane. -/
theorem clusterOf_lane {c x : Nat} (hc : c < L.nclusters)
    (hx : x < L.block * L.clusterSizeAt c) :
    L.clusterOfCta ((L.clusterStart c * L.block + x) / L.block) = c := by
  have hb : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h | h
    · rw [h, Nat.zero_mul] at hx
      omega
    · exact h
  have h1 : (L.clusterStart c * L.block + x) / L.block =
      L.clusterStart c + x / L.block := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.add_comm]
  rw [h1]
  refine Launch.clusterOfCta_clusterStart_add hc ?_
  rw [Nat.div_lt_iff_lt_mul hb, Nat.mul_comm]
  exact hx

/-- **The lane's records are at most its thread's recorded operations.** -/
theorem countP_ownAny_le_rec (hX : ClusterHistoryOk L X) {c x : Nat}
    (hc : c < L.nclusters) (hx : x < L.block * L.clusterSizeAt c) :
    (X.clusters c).countP (ownAny x) ≤ recCount L X (L.clusterStart c * L.block + x) := by
  obtain ⟨hnd, hsrc, -⟩ := hX.2.2 c hc
  set gx := L.clusterStart c * L.block + x with hgx
  have hlen : (X.clusters c).countP (ownAny x) = ((X.clusters c).filterMap (laneRef x)).length := by
    rw [List.length_filterMap_eq_countP]
    congr 1
    funext r
    exact (laneRef_isSome x r).symm
  -- every chosen reference is a recorded operation of the thread
  have hmem : ∀ e ∈ (X.clusters c).filterMap (laneRef x),
      e.1 = gx ∧ e.2 < (X.tr gx).length ∧ recAt L X gx e.2 = true := by
    intro e he
    obtain ⟨r, hr, hre⟩ := List.mem_filterMap.mp he
    obtain ⟨href, lanes, hle, hk⟩ := laneRef_mem hre
    have hs := hsrc r hr
    have hsrcl : e.1 = gx ∧ ∃ pc op, X.get e = some ⟨pc, .cluster op⟩ := by
      rcases hk with ⟨cta, warp, rel, rfl⟩ | ⟨cta, warp, rfl⟩
      · obtain ⟨-, h1, pc, al, h2⟩ := hs (x, e) hle
        exact ⟨h1, _, _, h2⟩
      · obtain ⟨-, h1, pc, al, h2⟩ := hs (x, e) hle
        exact ⟨h1, _, _, h2⟩
    obtain ⟨h1, pc, op, hev⟩ := hsrcl
    have hlt := len_of_get hev
    have he' : (gx, e.2) = e := by rw [← h1]
    refine ⟨h1, by rw [← h1]; exact hlt, ?_⟩
    simp only [recAt, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨r, ?_, by rw [he']; exact href⟩, ?_⟩
    · rw [clusterOf_lane hc hx]
      exact hr
    · have hg : (X.tr gx)[e.2]? = some ⟨pc, .cluster op⟩ := by
        rw [← h1]
        exact hev
      rw [hg]
      rfl
  have hnd2 : (((X.clusters c).filterMap (laneRef x)).map Prod.snd).Nodup := by
    refine List.Nodup.map_on ?_ (filterMap_laneRef_nodup x hnd)
    intro a ha b hb hab
    exact Prod.ext ((hmem a ha).1.trans (hmem b hb).1.symm) hab
  have hsub : ((X.clusters c).filterMap (laneRef x)).map Prod.snd ⊆
      (List.range (X.tr gx).length).filter (recAt L X gx) := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hj
    obtain ⟨-, h2, h3⟩ := hmem e he
    exact List.mem_filter.mpr ⟨List.mem_range.mpr h2, h3⟩
  rw [hlen, ← List.length_map (f := Prod.snd)]
  exact (hnd2.subperm hsub).length_le

/-- **A thread's recorded operations are at most its lane's records.** -/
theorem rec_le_countP_ownAny (hX : ClusterHistoryOk L X) {c x : Nat}
    (hc : c < L.nclusters) (hx : x < L.block * L.clusterSizeAt c) :
    recCount L X (L.clusterStart c * L.block + x) ≤ (X.clusters c).countP (ownAny x) := by
  obtain ⟨-, hsrc, -⟩ := hX.2.2 c hc
  set gx := L.clusterStart c * L.block + x with hgx
  set H := X.clusters c
  set P := (List.range (X.tr gx).length).filter (recAt L X gx) with hP
  have hex : ∀ j ∈ P, (∃ (i : Nat) (r : Record EvId), H[i]? = some r ∧ (gx, j) ∈ r.refs) ∧
      ∃ pc op, X.get (gx, j) = some ⟨pc, .cluster op⟩ := by
    intro j hj
    have hrec := (List.mem_filter.mp hj).2
    simp only [recAt, Bool.and_eq_true, decide_eq_true_eq] at hrec
    obtain ⟨⟨r, hr, he⟩, hcl⟩ := hrec
    rw [clusterOf_lane hc hx] at hr
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    refine ⟨⟨i, r, hi, he⟩, ?_⟩
    exact cluster_get hcl
  let f : Nat → Nat := fun j =>
    if h : ∃ (i : Nat) (r : Record EvId), H[i]? = some r ∧ (gx, j) ∈ r.refs then
      Classical.choose h else 0
  have hf : ∀ j ∈ P, ∃ r, H[f j]? = some r ∧ (gx, j) ∈ r.refs := by
    intro j hj
    have h := (hex j hj).1
    simp only [f, h, ↓reduceDIte]
    exact Classical.choose_spec h
  have hnd : (P.map f).Nodup := by
    refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
    intro a ha b hb hab
    obtain ⟨r, hr, har⟩ := hf a ha
    obtain ⟨r', hr', hbr⟩ := hf b hb
    rw [hab, hr'] at hr
    cases hr
    have := ClusterTrace.record_refs_thread_eq hX (List.mem_of_getElem? hr') har hbr rfl
    simp only [Prod.mk.injEq, true_and] at this
    exact this
  have hsub : P.map f ⊆ (List.range H.length).filter fun i => (H[i]?).any (ownAny x) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    obtain ⟨r, hr, hjr⟩ := hf j hj
    obtain ⟨pc, op, hget⟩ := (hex j hj).2
    have hlt := (List.getElem?_eq_some_iff.mp hr).1
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩
    rw [hr]
    simp only [Option.any_some]
    have hs := hsrc r (List.mem_of_getElem? hr)
    cases r with
    | exit y e =>
      simp only [Record.refs, List.mem_singleton] at hjr
      obtain ⟨-, -, pc', hget'⟩ := hs
      rw [← hjr, hget] at hget'
      cases hget'
    | arrival cta warp rel lanes =>
      obtain ⟨⟨p, e⟩, hpl, hpe⟩ := List.mem_map.mp hjr
      simp only at hpe
      subst hpe
      obtain ⟨hp, h1, -⟩ := hs (p, (gx, j)) hpl
      simp only at h1 hp
      have hpx : p = x := by omega
      subst hpx
      simp only [ownAny, ownArrival, ownWait, Bool.or_false, decide_eq_true_eq]
      exact List.mem_map.mpr ⟨_, hpl, rfl⟩
    | wait cta warp lanes =>
      obtain ⟨⟨p, e⟩, hpl, hpe⟩ := List.mem_map.mp hjr
      simp only at hpe
      subst hpe
      obtain ⟨hp, h1, -⟩ := hs (p, (gx, j)) hpl
      simp only at h1 hp
      have hpx : p = x := by omega
      subst hpx
      simp only [ownAny, ownWait, ownArrival, Bool.false_or, decide_eq_true_eq]
      exact List.mem_map.mpr ⟨_, hpl, rfl⟩
  have := (hnd.subperm hsub).length_le
  rw [List.length_map, length_filter_range] at this
  exact this

/-- Positions below `m` holding an operation count the operations of the prefix. -/
theorem length_filter_range_take {β : Type} (p : β → Bool) (l : List β) {m : Nat}
    (hm : m ≤ l.length) :
    ((List.range m).filter fun i => (l[i]?).any p).length = (l.take m).countP p := by
  rw [← length_filter_range p (l.take m), List.length_take, Nat.min_eq_left hm]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [List.getElem?_take_of_lt (List.mem_range.mp hi)]

/-- **Recorded operations, when the last position is not one.** -/
theorem recCount_le_take {h : Nat} (hnr : recAt L X h ((X.tr h).length - 1) = false) :
    recCount L X h ≤ ((X.tr h).take ((X.tr h).length - 1)).countP isCluster := by
  rw [← length_filter_range_take _ _ (Nat.sub_le _ _)]
  apply (List.Nodup.subperm (List.nodup_range.filter _) _).length_le
  intro j hj
  obtain ⟨hjr, hja⟩ := List.mem_filter.mp hj
  have hjl := List.mem_range.mp hjr
  have hne : j ≠ (X.tr h).length - 1 := fun he => by rw [he] at hja; rw [hja] at hnr; cases hnr
  simp only [recAt, Bool.and_eq_true] at hja
  exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), hja.2⟩

/-- **Every operation but the last is recorded** (`ClusterBlocking`). -/
theorem take_le_recCount (hb : ClusterBlocking L X) (h : Nat) :
    ((X.tr h).take ((X.tr h).length - 1)).countP isCluster ≤ recCount L X h := by
  rw [← length_filter_range_take _ _ (Nat.sub_le _ _)]
  apply (List.Nodup.subperm (List.nodup_range.filter _) _).length_le
  intro j hj
  obtain ⟨hjr, hja⟩ := List.mem_filter.mp hj
  have hjl := List.mem_range.mp hjr
  obtain ⟨pc, op, hget⟩ := cluster_get hja
  have hlt : j < (X.tr h).length := len_of_get hget
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩
  simp only [recAt, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hb (h, j) pc op hget (by show j + 1 < (X.tr h).length; omega), hja⟩

/-- **When the last operation is recorded too, every operation is.** -/
theorem countP_le_recCount (hb : ClusterBlocking L X) {h : Nat}
    (hl : ∀ pc op, X.get (h, (X.tr h).length - 1) = some ⟨pc, .cluster op⟩ →
      ClusterRecorded L X (h, (X.tr h).length - 1)) :
    (X.tr h).countP isCluster ≤ recCount L X h := by
  have h0 := length_filter_range_take isCluster (X.tr h) (le_refl _)
  rw [List.take_length] at h0
  rw [← h0]
  apply (List.Nodup.subperm (List.nodup_range.filter _) _).length_le
  intro j hj
  obtain ⟨hjr, hja⟩ := List.mem_filter.mp hj
  have hjl := List.mem_range.mp hjr
  obtain ⟨pc, op, hget⟩ := cluster_get hja
  refine List.mem_filter.mpr ⟨hjr, ?_⟩
  simp only [recAt, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, hja⟩
  by_cases hj1 : j + 1 < (X.tr h).length
  · exact hb (h, j) pc op hget hj1
  · have hje : j = (X.tr h).length - 1 := by omega
    subst hje
    exact hl pc op hget

/-- **A lane whose thread has no exit event has not exited.** -/
theorem lane_live (hX : ClusterHistoryOk L X) {c x : Nat} (hc : c < L.nclusters)
    (hnx : ∀ j pc, X.get (L.clusterStart c * L.block + x, j) ≠ some ⟨pc, .exit⟩)
    {s : State} (hs : run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s) :
    x ∉ s.exited := by
  intro hxe
  rcases run_exited_source hs hxe with h0 | ⟨e, he⟩
  · simp at h0
  obtain ⟨-, h1, pc, h2⟩ := (hX.2.2 c hc).2.1 _ he
  apply hnx e.2 pc
  rw [← h1]
  exact h2

/-- **A lane's records before one of its records are its thread's operations before that
record's event**: the history keeps the thread's events in trace order
(`ClusterTrace.record_lt_of_lt`), and every operation before an event is recorded
(`ClusterBlocking`). -/
theorem countP_take_ownAny (hX : ClusterHistoryOk L X) (hb : ClusterBlocking L X)
    (hac : ObjectCoherent L X) {c x i : Nat} (hc : c < L.nclusters)
    (hx : x < L.block * L.clusterSizeAt c) {r : Record EvId} {z : EvId}
    (hi : (X.clusters c)[i]? = some r) (hz : laneRef x r = some z) :
    ((X.clusters c).take i).countP (ownAny x) =
      ((X.tr (L.clusterStart c * L.block + x)).take z.2).countP isCluster := by
  obtain ⟨hnd, hsrc, -⟩ := hX.2.2 c hc
  set gx := L.clusterStart c * L.block + x with hgx
  set H := X.clusters c with hH
  have hlane : ∀ {q : Nat} {r' : Record EvId} {e : EvId}, H[q]? = some r' →
      laneRef x r' = some e →
        e ∈ r'.refs ∧ e.1 = gx ∧ ∃ pc op, X.get e = some ⟨pc, .cluster op⟩ := by
    intro q r' e hq he
    obtain ⟨href, lanes, hle, hk⟩ := laneRef_mem he
    have hs := hsrc r' (List.mem_of_getElem? hq)
    rcases hk with ⟨cta, warp, rel, rfl⟩ | ⟨cta, warp, rfl⟩
    · obtain ⟨-, h1, pc, al, h2⟩ := hs (x, e) hle
      exact ⟨href, h1, _, _, h2⟩
    · obtain ⟨-, h1, pc, al, h2⟩ := hs (x, e) hle
      exact ⟨href, h1, _, _, h2⟩
  obtain ⟨hzr, hz1, pcz, opz, hgz⟩ := hlane hi hz
  have hzlt : z.2 < (X.tr gx).length := by
    have := len_of_get hgz
    rw [hz1] at this
    exact this
  have hil : i < H.length := (List.getElem?_eq_some_iff.mp hi).1
  have hnd' := hnd
  rw [← List.take_append_drop i H, List.flatMap_append, List.nodup_append] at hnd'
  apply le_antisymm
  · -- each record before `i` holds an earlier operation of the thread
    have hlen : (H.take i).countP (ownAny x) = ((H.take i).filterMap (laneRef x)).length := by
      rw [List.length_filterMap_eq_countP]
      congr 1
      funext r'
      exact (laneRef_isSome x r').symm
    have hzd : z ∈ (H.drop i).flatMap Record.refs := by
      have hd : (H.drop i)[0]? = some r := by rw [List.getElem?_drop]; simpa using hi
      exact List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hd, hzr⟩
    have hmem : ∀ e ∈ (H.take i).filterMap (laneRef x),
        e.1 = gx ∧ e.2 < z.2 ∧ ((X.tr gx)[e.2]?).any isCluster = true := by
      intro e he
      obtain ⟨r', hr', hre⟩ := List.mem_filterMap.mp he
      obtain ⟨k, hk, hkr⟩ := ClusterTrace.exists_idx_of_mem_take hr'
      obtain ⟨href, h1, pc, op, hget⟩ := hlane hkr hre
      have hne : e ≠ z := hnd'.2.2 e (List.mem_flatMap.mpr ⟨r', hr', href⟩) z hzd
      have h2 : e.2 < z.2 := by
        rcases Nat.lt_trichotomy e.2 z.2 with h | h | h
        · exact h
        · exact (hne (Prod.ext (h1.trans hz1.symm) h)).elim
        · have := ClusterTrace.record_lt_of_lt hX hac hi hkr hzr href (hz1.trans h1.symm) h
          omega
      refine ⟨h1, h2, ?_⟩
      have hg : (X.tr gx)[e.2]? = some ⟨pc, .cluster op⟩ := by rw [← h1]; exact hget
      rw [hg]
      rfl
    have hnd2 : (((H.take i).filterMap (laneRef x)).map Prod.snd).Nodup := by
      refine List.Nodup.map_on ?_ (filterMap_laneRef_nodup x hnd'.1)
      intro a ha b hb hab
      exact Prod.ext ((hmem a ha).1.trans (hmem b hb).1.symm) hab
    have hsub : ((H.take i).filterMap (laneRef x)).map Prod.snd ⊆
        (List.range z.2).filter fun j => ((X.tr gx)[j]?).any isCluster := by
      intro j hj
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hj
      obtain ⟨-, h2, h3⟩ := hmem e he
      exact List.mem_filter.mpr ⟨List.mem_range.mpr h2, h3⟩
    rw [hlen, ← List.length_map (f := Prod.snd), ← length_filter_range_take _ _ hzlt.le]
    exact (hnd2.subperm hsub).length_le
  · -- each operation before `z` is recorded before `i`
    set P := (List.range z.2).filter fun j => ((X.tr gx)[j]?).any isCluster with hP
    have hex : ∀ j ∈ P, ∃ q R, q < i ∧ H[q]? = some R ∧ (gx, j) ∈ R.refs ∧
        ownAny x R = true := by
      intro j hj
      obtain ⟨hjr, hja⟩ := List.mem_filter.mp hj
      have hjl := List.mem_range.mp hjr
      obtain ⟨pc, op, hget⟩ := cluster_get hja
      have hrc := hb (gx, j) pc op hget (by show j + 1 < (X.tr gx).length; omega)
      obtain ⟨q, R, hq, hjR⟩ := ClusterTrace.rec_at (c := c) (clusterOf_lane hc hx).symm hrc
      have hqi : q < i := ClusterTrace.record_lt_of_lt hX hac hq hi hjR hzr hz1.symm hjl
      refine ⟨q, R, hqi, hq, hjR, ?_⟩
      have hs := hsrc R (List.mem_of_getElem? hq)
      cases R with
      | exit y e =>
        simp only [Record.refs, List.mem_singleton] at hjR
        obtain ⟨-, -, pc', hget'⟩ := hs
        rw [← hjR, hget] at hget'
        cases hget'
      | arrival cta warp rel lanes =>
        obtain ⟨⟨p, e⟩, hpl, hpe⟩ := List.mem_map.mp hjR
        simp only at hpe
        subst hpe
        obtain ⟨hp, h1, -⟩ := hs (p, (gx, j)) hpl
        simp only at h1 hp
        have hpx : p = x := by omega
        subst hpx
        simp only [ownAny, ownArrival, ownWait, Bool.or_false, decide_eq_true_eq]
        exact List.mem_map.mpr ⟨_, hpl, rfl⟩
      | wait cta warp lanes =>
        obtain ⟨⟨p, e⟩, hpl, hpe⟩ := List.mem_map.mp hjR
        simp only at hpe
        subst hpe
        obtain ⟨hp, h1, -⟩ := hs (p, (gx, j)) hpl
        simp only at h1 hp
        have hpx : p = x := by omega
        subst hpx
        simp only [ownAny, ownWait, ownArrival, Bool.false_or, decide_eq_true_eq]
        exact List.mem_map.mpr ⟨_, hpl, rfl⟩
    let f : Nat → Nat := fun j =>
      if h : ∃ q R, q < i ∧ H[q]? = some R ∧ (gx, j) ∈ R.refs ∧ ownAny x R = true then
        Classical.choose h else 0
    have hf : ∀ j ∈ P, ∃ R, f j < i ∧ H[f j]? = some R ∧ (gx, j) ∈ R.refs ∧
        ownAny x R = true := by
      intro j hj
      have h := hex j hj
      simp only [f, h, ↓reduceDIte]
      exact Classical.choose_spec h
    have hndf : (P.map f).Nodup := by
      refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
      intro a ha b hb hab
      obtain ⟨R, -, hR, haR, -⟩ := hf a ha
      obtain ⟨R', -, hR', hbR, -⟩ := hf b hb
      rw [hab, hR'] at hR
      cases hR
      have := ClusterTrace.record_refs_thread_eq hX (List.mem_of_getElem? hR') haR hbR rfl
      simp only [Prod.mk.injEq, true_and] at this
      exact this
    have hsub : P.map f ⊆ (List.range i).filter fun q => (H[q]?).any (ownAny x) := by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      obtain ⟨R, h1, h2, -, h4⟩ := hf j hj
      refine List.mem_filter.mpr ⟨List.mem_range.mpr h1, ?_⟩
      rw [h2]
      exact h4
    have := (hndf.subperm hsub).length_le
    rw [List.length_map, length_filter_range_take _ _ hzlt.le,
      length_filter_range_take _ _ hil.le] at this
    exact this

/-! ## Alternation from the program -/

/-- The parity of the number of a thread's earlier cluster operations at an operation: even
before an arrival, odd before a wait. -/
def opParity : ClusterOp → Nat
  | .arrive .. => 0
  | .wait .. => 1

/-- Every thread's cluster operations alternate an arrival and a wait in program order, starting
with an arrival: before an operation, the thread's earlier cluster operations are even in number
for an arrival and odd for a wait. -/
def OpsAlternate (X : Execution) : Prop :=
  ∀ g k pc op, X.get (g, k) = some ⟨pc, .cluster op⟩ →
    ((X.tr g).take k).countP isCluster % 2 = opParity op

/-- **A lane's records alternate** when the program's operations do: its arrival records come
after an even number of its records and its wait records after an odd number. -/
theorem alt_of_ops (hX : ClusterHistoryOk L X) (hb : ClusterBlocking L X)
    (hac : ObjectCoherent L X) (hops : OpsAlternate X) {c x : Nat}
    (hc : c < L.nclusters) (hx : x < L.block * L.clusterSizeAt c) :
    Alt x (X.clusters c) := by
  intro i r hi
  have common : ownAny x r = true → ∃ z, ((X.clusters c).take i).countP (ownAny x) =
      ((X.tr (L.clusterStart c * L.block + x)).take z.2).countP isCluster ∧
      ∃ lanes, (x, z) ∈ lanes ∧
        ((∃ cta warp rel, r = .arrival cta warp rel lanes) ∨ ∃ cta warp, r =
          .wait cta warp lanes) := by
    intro hany
    rw [← laneRef_isSome] at hany
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hany
    refine ⟨z, countP_take_ownAny hX hb hac hc hx hi hz, ?_⟩
    obtain ⟨-, lanes, hle, hk⟩ := laneRef_mem hz
    exact ⟨lanes, hle, hk⟩
  have hsrc := (hX.2.2 c hc).2.1 r (List.mem_of_getElem? hi)
  constructor
  · intro hown
    obtain ⟨z, hcount, lanes, hle, hk⟩ := common (by simp [ownAny, hown])
    rw [hcount]
    rcases hk with ⟨cta, warp, rel, rfl⟩ | ⟨cta, warp, rfl⟩
    · obtain ⟨-, h1, pc, al, h2⟩ := hsrc (x, z) hle
      have hget : X.get (L.clusterStart c * L.block + x, z.2) =
          some ⟨pc, .cluster (.arrive rel al)⟩ := by rw [← h1]; exact h2
      exact hops _ _ _ _ hget
    · simp [ownArrival] at hown
  · intro hown
    obtain ⟨z, hcount, lanes, hle, hk⟩ := common (by simp [ownAny, hown])
    rw [hcount]
    rcases hk with ⟨cta, warp, rel, rfl⟩ | ⟨cta, warp, rfl⟩
    · simp [ownWait] at hown
    · obtain ⟨-, h1, pc, al, h2⟩ := hsrc (x, z) hle
      have hget : X.get (L.clusterStart c * L.block + x, z.2) =
          some ⟨pc, .cluster (.wait al)⟩ := by rw [← h1]; exact h2
      exact hops _ _ _ _ hget

/-- **The lane of a pending operation.** An issued cluster operation of a lane that no record
holds is its thread's operation `k` (`k` earlier cluster operations, of the operation's parity);
the lane's records are those `k`, and the lane status holds with them. -/
theorem lane_pending (hX : ClusterHistoryOk L X) (hb : ClusterBlocking L X)
    (hac : ObjectCoherent L X) (hops : OpsAlternate X) {c x : Nat}
    (hc : c < L.nclusters) (hx : x < L.block * L.clusterSizeAt c) {s : State}
    (hs : ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s) {z : EvId}
    {pc : Nat} {op : ClusterOp} (hz1 : z.1 = L.clusterStart c * L.block + x)
    (hget : X.get z = some ⟨pc, .cluster op⟩)
    (hfree : z ∉ (X.clusters c).flatMap Record.refs) :
    ((X.tr z.1).take z.2).countP isCluster % 2 = opParity op ∧
      LaneSt x s ((X.clusters c).countP (ownArrival x)) ((X.clusters c).countP (ownWait x)) ∧
      (X.clusters c).countP (ownArrival x) + (X.clusters c).countP (ownWait x) =
        ((X.tr z.1).take z.2).countP isCluster := by
  set gx := L.clusterStart c * L.block + x with hgx
  have hget' : X.get (gx, z.2) = some ⟨pc, .cluster op⟩ := by rw [← hz1]; exact hget
  have hlt : z.2 < (X.tr gx).length := (List.getElem?_eq_some_iff.mp hget').1
  -- the operation is unrecorded, hence the thread's last event
  have hnr : ¬ ClusterRecorded L X (gx, z.2) := by
    rintro ⟨r, hr, hzr⟩
    rw [show (gx, z.2) = z from Prod.ext hz1.symm rfl] at hzr
    have hcl : L.clusterOfCta (z.1 / L.block) = c := by rw [hz1]; exact clusterOf_lane hc hx
    rw [show (gx, z.2).1 = z.1 from hz1.symm, hcl] at hr
    exact hfree (List.mem_flatMap.mpr ⟨r, hr, hzr⟩)
  have hlast : z.2 = (X.tr gx).length - 1 := by
    by_contra hne
    exact hnr (hb (gx, z.2) pc op hget' (by show z.2 + 1 < (X.tr gx).length; omega))
  have hra : recAt L X gx ((X.tr gx).length - 1) = false := by
    simp only [recAt, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    rw [← hlast]
    exact .inl hnr
  have h1 := recCount_le_take hra
  have h2 := take_le_recCount hb gx
  have h3 := countP_ownAny_le_rec hX hc hx
  have h4 := rec_le_countP_ownAny hX hc hx
  rw [countP_ownAny] at h3 h4
  rw [← hlast] at h1 h2
  rw [hz1]
  refine ⟨hops _ _ _ _ hget', run_laneSt hs (alt_of_ops hX hb hac hops hc hx), ?_⟩
  rw [← hgx] at h3 h4
  omega

/-- **No cluster barrier collective faults** when every thread's operations alternate. -/
theorem no_fault_of_ops (hX : ClusterHistoryOk L X) (hb : ClusterBlocking L X)
    (hac : ObjectCoherent L X) (hops : OpsAlternate X) : ¬ ClusterFault L X := by
  rintro ⟨c, hc, s, hs, r, err, hsrc, hfree, hp, hf⟩
  have hsound := sound_run sound_empty hs
  cases r with
  | exit g e =>
    simp only [Record.perform, ClusterBarrier.perform] at hp
    split at hp
    · cases hp
      simp [Error.isFault] at hf
    · cases hp
  | arrival cta warp rel lanes =>
    have hok : ∀ j ∈ lanes.map Prod.fst, ¬ Locked j s := by
      intro j hj
      obtain ⟨p, hpl, rfl⟩ := List.mem_map.mp hj
      obtain ⟨hpx, hp1, pc, al, hget⟩ := hsrc p hpl
      obtain ⟨heven, hst, hsum⟩ := lane_pending hX hb hac hops hc hpx hs hp1 hget
        (hfree p.2 (List.mem_map_of_mem hpl))
      simp only [opParity] at heven
      have hwa := hst.1
      have haw := hst.2.1
      have heq :
          (X.clusters c).countP (ownArrival p.1) = (X.clusters c).countP (ownWait p.1) := by
        omega
      rw [heq] at hst
      exact LaneSt.not_arrived hsound hst
    rw [record_arrival_fault hok hp] at hf
    cases hf
  | wait cta warp lanes =>
    rw [record_wait_fault hp] at hf
    cases hf

end PTX.ClusterLanes
