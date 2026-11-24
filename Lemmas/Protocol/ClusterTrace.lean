-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ClusterPhase

@[expose] public section

/-! # Trace order and lane counts of a cluster barrier history

A thread's cluster barrier arrivals and waits on its trace are matched with the records of its
cluster's checked history. The history keeps one thread's events in trace order
(`ClusterHistoryOk.source_order`), a record holds at most one lane of a thread, and a completed
wait observes the phase of its lane's last arrival. The facts here use only the cluster history,
its checked run, and the kinds of the events. -/

namespace PTX.ClusterTrace

open PTX ClusterBarrier PTX.ClusterPhase

/-- A cluster arrival event, on a thread's trace. -/
def isArr (ev : Event) : Bool :=
  match ev.kind with
  | .cluster (.arrive _ _) => true
  | _ => false

theorem isArr_kind {ev : Event} (ha : isArr ev = true) :
    ∃ rel al, ev.kind = .cluster (.arrive rel al) := by
  obtain ⟨pc, kind⟩ := ev
  cases kind with
  | cluster op =>
    cases op with
    | arrive rel al => exact ⟨rel, al, rfl⟩
    | wait al => simp [isArr] at ha
  | _ => simp [isArr] at ha

theorem isArr_of_kind {ev : Event} {rel al : Bool} (hk : ev.kind = .cluster (.arrive rel al)) :
    isArr ev = true := by
  simp [isArr, hk]

section Counting

variable {α : Type}

theorem countP_take_succ_of {xs : List α} {p : α → Bool} {k : Nat} {r : α}
    (hr : xs[k]? = some r) (hp : p r = true) :
    (xs.take (k + 1)).countP p = (xs.take k).countP p + 1 := by
  rw [List.take_add_one, hr]
  simp [hp]

theorem countP_take_succ_not {xs : List α} {p : α → Bool} {k : Nat} {r : α}
    (hr : xs[k]? = some r) (hp : p r = false) :
    (xs.take (k + 1)).countP p = (xs.take k).countP p := by
  rw [List.take_add_one, hr]
  simp [hp]

theorem countP_take_mono {xs : List α} {p : α → Bool} {m n : Nat} (h : m ≤ n) :
    (xs.take m).countP p ≤ (xs.take n).countP p :=
  (List.take_isPrefix_take.mpr (Or.inl h)).countP_le

/-- A satisfying element at `z < m` adds one to the prefix count before `m`. -/
theorem countP_take_lt {xs : List α} {p : α → Bool} {z m : Nat} {r : α}
    (hz : z < m) (hr : xs[z]? = some r) (hp : p r = true) :
    (xs.take z).countP p + 1 ≤ (xs.take m).countP p := by
  have h1 := countP_take_succ_of hr hp
  have h2 : (xs.take (z + 1)).countP p ≤ (xs.take m).countP p :=
    countP_take_mono (Nat.succ_le_of_lt hz)
  omega

/-- A smaller prefix count comes at an earlier position. -/
theorem lt_of_countP_take_lt {xs : List α} {p : α → Bool} {z z' : Nat}
    (hc : (xs.take z).countP p < (xs.take z').countP p) : z < z' := by
  by_contra hn
  have h := countP_take_mono (p := p) (xs := xs) (show z' ≤ z by omega)
  omega

/-- The `n`-th satisfying element of a prefix: the first position whose prefix before it counts
exactly `n` satisfying elements. -/
theorem exists_occ (xs : List α) (p : α → Bool) (m n : Nat)
    (h : n < (xs.take m).countP p) :
    ∃ k r, k < m ∧ xs[k]? = some r ∧ p r = true ∧ (xs.take k).countP p = n := by
  induction m with
  | zero => simp at h
  | succ m ih =>
    cases hx : xs[m]? with
    | none =>
      have hs : (xs.take (m + 1)).countP p = (xs.take m).countP p := by
        rw [List.take_add_one, hx]
        simp
      obtain ⟨k, r, hk, hr, hp, hc⟩ := ih (by omega)
      exact ⟨k, r, by omega, hr, hp, hc⟩
    | some r =>
      by_cases hp : p r = true
      · have hs := countP_take_succ_of hx hp
        by_cases hlt : n < (xs.take m).countP p
        · obtain ⟨k, r', hk, hr', hp', hc⟩ := ih hlt
          exact ⟨k, r', by omega, hr', hp', hc⟩
        · exact ⟨m, r, by omega, hx, hp, by omega⟩
      · have hs := countP_take_succ_not hx (by simpa using hp)
        obtain ⟨k, r', hk, hr', hp', hc⟩ := ih (by omega)
        exact ⟨k, r', by omega, hr', hp', hc⟩

theorem exists_idx_of_mem_take {xs : List α} {m : Nat} {r : α} (hr : r ∈ xs.take m) :
    ∃ k, k < m ∧ xs[k]? = some r := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hr
  simp only [List.length_take] at hj
  have hjn : j < m := by omega
  have hjx : j < xs.length := by omega
  exact ⟨j, hjn, List.getElem?_eq_some_iff.mpr
    ⟨hjx, by simpa only [List.getElem_take] using hget⟩⟩

end Counting

section Records

variable {L : Launch} {X : Execution}

theorem arrival_lanes_nodup {block ctas cta warp : Nat} {s t : ClusterBarrier.State}
    {rel : Bool} {lanes : List (Nat × EvId)}
    (hp : Record.perform block ctas s (.arrival cta warp rel lanes) = .done t) :
    (lanes.map Prod.fst).Nodup := by
  simp only [Record.perform] at hp
  split at hp
  · rename_i hv
    exact (of_decide_eq_true hv).2.2.2.2.1
  · cases hp

theorem wait_lanes_nodup {block ctas cta warp : Nat} {s t : ClusterBarrier.State}
    {lanes : List (Nat × EvId)}
    (hp : Record.perform block ctas s (.wait cta warp lanes) = .done t) :
    (lanes.map Prod.fst).Nodup := by
  simp only [Record.perform] at hp
  split at hp
  · rename_i hv
    exact (of_decide_eq_true hv).2.2.2.2.1
  · cases hp

/-- An arrival record of a checked run has distinct lanes. -/
theorem arrival_record_nodup {block ctas : Nat} {hist : List (ClusterBarrier.Record EvId)}
    {s : ClusterBarrier.State} (hrun : ClusterBarrier.run block ctas {} hist = .done s)
    {q cta warp : Nat} {rel : Bool} {lanes : List (Nat × EvId)}
    (hq : hist[q]? = some (.arrival cta warp rel lanes)) : (lanes.map Prod.fst).Nodup := by
  obtain ⟨u, v, -, hv⟩ := run_perform_at hrun hq
  exact arrival_lanes_nodup hv

/-- A wait record of a checked run has distinct lanes. -/
theorem wait_record_nodup {block ctas : Nat} {hist : List (ClusterBarrier.Record EvId)}
    {s : ClusterBarrier.State} (hrun : ClusterBarrier.run block ctas {} hist = .done s)
    {q cta warp : Nat} {lanes : List (Nat × EvId)}
    (hq : hist[q]? = some (.wait cta warp lanes)) : (lanes.map Prod.fst).Nodup := by
  obtain ⟨u, v, -, hv⟩ := run_perform_at hrun hq
  exact wait_lanes_nodup hv

/-- Two events of one thread that lie in one record are equal: a record holds one lane of each
thread. -/
theorem record_refs_thread_eq (hX : ClusterHistoryOk L X) {c : Nat}
    {r : ClusterBarrier.Record EvId} (hr : r ∈ X.clusters c) {z y : EvId}
    (hz : z ∈ r.refs) (hy : y ∈ r.refs) (hthr : z.1 = y.1) : z = y := by
  have hc : c < L.nclusters := by
    by_contra hn
    rw [hX.2.1 c (by omega)] at hr
    cases hr
  obtain ⟨-, hsrc, s, hrun⟩ := hX.2.2 c hc
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hr
  have hsr := hsrc r hr
  cases r with
  | exit g f =>
    simp only [ClusterBarrier.Record.refs, List.mem_singleton] at hz hy
    rw [hz, hy]
  | arrival cta warp rel lanes =>
    have hnd := arrival_record_nodup hrun hq
    obtain ⟨pz, hpz, hzp⟩ := List.mem_map.mp hz
    obtain ⟨py, hpy, hyp⟩ := List.mem_map.mp hy
    have h1 := (hsr pz hpz).2.1
    have h2 := (hsr py hpy).2.1
    rw [hzp] at h1
    rw [hyp] at h2
    have hfst : pz.1 = py.1 := by omega
    rw [← hzp, ← hyp, List.inj_on_of_nodup_map hnd hpz hpy hfst]
  | wait cta warp lanes =>
    have hnd := wait_record_nodup hrun hq
    obtain ⟨pz, hpz, hzp⟩ := List.mem_map.mp hz
    obtain ⟨py, hpy, hyp⟩ := List.mem_map.mp hy
    have h1 := (hsr pz hpz).2.1
    have h2 := (hsr py hpy).2.1
    rw [hzp] at h1
    rw [hyp] at h2
    have hfst : pz.1 = py.1 := by omega
    rw [← hzp, ← hyp, List.inj_on_of_nodup_map hnd hpz hpy hfst]

/-- Trace order is record order for one thread's events: if `z` precedes `y` on the trace, then
`z`'s record comes first in the history. -/
theorem record_lt_of_lt (hX : ClusterHistoryOk L X) (hac : ObjectCoherent L X) {c qz qy : Nat}
    {rz ry : ClusterBarrier.Record EvId} {z y : EvId}
    (hrz : (X.clusters c)[qz]? = some rz) (hry : (X.clusters c)[qy]? = some ry)
    (hzr : z ∈ rz.refs) (hyr : y ∈ ry.refs) (hthr : z.1 = y.1) (hlt : z.2 < y.2) :
    qz < qy := by
  by_contra hn
  rcases Nat.lt_or_ge qy qz with h | h
  · have := hX.source_order hac hry hrz h hyr hzr hthr.symm
    omega
  · have hq : qz = qy := by omega
    subst hq
    have hrr : rz = ry := Option.some.inj (hrz.symm.trans hry)
    subst hrr
    have hzy := record_refs_thread_eq hX (List.mem_of_getElem? hrz) hzr hyr hthr
    subst hzy
    omega

/-- The lane of an arrival record entry: its event is a thread of the cluster at the lane. -/
theorem arrival_lane {c cta warp : Nat} {rel : Bool} {lanes : List (Nat × EvId)}
    (hX : ClusterHistoryOk L X)
    (hr : ClusterBarrier.Record.arrival cta warp rel lanes ∈ X.clusters c)
    {p : Nat} {z : EvId} (hpz : (p, z) ∈ lanes) :
    z.1 = L.clusterStart c * L.block + p ∧ p < L.block * L.clusterSizeAt c ∧
      ∃ pc aligned, X.get z = some ⟨pc, .cluster (.arrive rel aligned)⟩ := by
  have hc : c < L.nclusters := by
    by_contra hn
    rw [hX.2.1 c (by omega)] at hr
    cases hr
  have h := (hX.2.2 c hc).2.1 _ hr (p, z) hpz
  exact ⟨h.2.1, h.1, h.2.2⟩

/-- The lane of a wait record entry. -/
theorem wait_lane {c cta warp : Nat} {lanes : List (Nat × EvId)}
    (hX : ClusterHistoryOk L X)
    (hr : ClusterBarrier.Record.wait cta warp lanes ∈ X.clusters c)
    {p : Nat} {z : EvId} (hpz : (p, z) ∈ lanes) :
    z.1 = L.clusterStart c * L.block + p ∧ p < L.block * L.clusterSizeAt c ∧
      ∃ pc aligned, X.get z = some ⟨pc, .cluster (.wait aligned)⟩ := by
  have hc : c < L.nclusters := by
    by_contra hn
    rw [hX.2.1 c (by omega)] at hr
    cases hr
  have h := (hX.2.2 c hc).2.1 _ hr (p, z) hpz
  exact ⟨h.2.1, h.1, h.2.2⟩

/-- An event recorded by an arrival record is an arrival of that record's release kind, in the
lane the record names. -/
theorem arrival_of_ref {c : Nat} {r : ClusterBarrier.Record EvId} (hX : ClusterHistoryOk L X)
    (hr : r ∈ X.clusters c) {z : EvId} (hz : z ∈ r.refs) {pc : Nat} {rel al : Bool}
    (hget : X.get z = some ⟨pc, .cluster (.arrive rel al)⟩) :
    ∃ cta warp lanes p, r = .arrival cta warp rel lanes ∧ (p, z) ∈ lanes := by
  have hc : c < L.nclusters := by
    by_contra hn
    rw [hX.2.1 c (by omega)] at hr
    cases hr
  have hsr := (hX.2.2 c hc).2.1 r hr
  cases r with
  | exit g f =>
    simp only [ClusterBarrier.Record.refs, List.mem_singleton] at hz
    subst hz
    obtain ⟨-, -, pc', hp⟩ := hsr
    rw [hget] at hp
    cases hp
  | wait cta warp lanes =>
    obtain ⟨⟨p1, p2⟩, hp, hpe⟩ := List.mem_map.mp hz
    change p2 = z at hpe
    obtain ⟨-, -, pc', al', hp'⟩ := hsr (p1, p2) hp
    dsimp only at hp'
    rw [hpe, hget] at hp'
    cases hp'
  | arrival cta warp rel' lanes =>
    obtain ⟨⟨p1, p2⟩, hp, hpe⟩ := List.mem_map.mp hz
    change p2 = z at hpe
    obtain ⟨-, -, pc', al', hp'⟩ := hsr (p1, p2) hp
    dsimp only at hp'
    rw [hpe, hget] at hp'
    cases hp'
    exact ⟨cta, warp, lanes, p1, rfl, by rw [← hpe]; exact hp⟩

/-- Ownership of a lane by an arrival record. -/
theorem ownArrival_iff {lh : Nat} {r : ClusterBarrier.Record EvId} :
    ownArrival lh r = true ↔
      ∃ cta warp rel lanes, r = .arrival cta warp rel lanes ∧ ∃ z, (lh, z) ∈ lanes := by
  cases r with
  | arrival cta warp rel lanes =>
    constructor
    · intro h
      have hm : lh ∈ lanes.map Prod.fst := by simpa [ownArrival] using h
      obtain ⟨⟨a, b⟩, hab, hfst⟩ := List.mem_map.mp hm
      change a = lh at hfst
      subst hfst
      exact ⟨cta, warp, rel, lanes, rfl, b, hab⟩
    · rintro ⟨cta', warp', rel', lanes', hr, z, hz⟩
      cases hr
      simp only [ownArrival, decide_eq_true_eq]
      exact List.mem_map.mpr ⟨(lh, z), hz, rfl⟩
  | wait cta warp lanes => simp [ownArrival]
  | exit g e => simp [ownArrival]

/-- A recorded event's record, located in the cluster's history. -/
theorem rec_at {c : Nat} {e : EvId} (hc : c = L.clusterOfCta (e.1 / L.block))
    (hr : ClusterRecorded L X e) :
    ∃ (q : Nat) (R : ClusterBarrier.Record EvId), (X.clusters c)[q]? = some R ∧ e ∈ R.refs := by
  obtain ⟨r, hr', he⟩ := hr
  subst hc
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hr'
  exact ⟨q, r, hq, he⟩

/-- The kind of a satisfying trace event, with its record's event kind. -/
theorem isArr_get {z : EvId} {ev : Event} (hget : X.get z = some ev) (ha : isArr ev = true) :
    ∃ rel al, X.get z = some ⟨ev.pc, .cluster (.arrive rel al)⟩ := by
  obtain ⟨rel, al, hk⟩ := isArr_kind ha
  refine ⟨rel, al, ?_⟩
  have hev : ev = ⟨ev.pc, .cluster (.arrive rel al)⟩ := by
    obtain ⟨pc, kind⟩ := ev
    have hk' : kind = .cluster (.arrive rel al) := hk
    subst hk'
    rfl
  rw [hget]
  exact congrArg some hev

/-- A trace position of thread `h` holds the event of `z`. -/
theorem trace_get {h : Nat} {z : EvId} {ev : Event} (hz : z.1 = h)
    (hget : X.get z = some ev) : (X.tr h)[z.2]? = some ev := by
  subst hz
  exact hget

end Records

section Phases

variable {L : Launch} {X : Execution}

/-- A completed cluster wait of lane `lh` in cluster `c`, whose thread `h` has exactly two
arrivals before its wait event, observes phase one. -/
theorem wait_phase_one (hX : ClusterHistoryOk L X) (hb : ClusterBlocking L X)
    (hac : ObjectCoherent L X) {c i h j lh φ cta warp : Nat} {lanes : List (Nat × EvId)}
    {s t : ClusterBarrier.State}
    (hc : c = L.clusterOfCta (h / L.block))
    (hi : (X.clusters c)[i]? = some (.wait cta warp lanes))
    (hs : ClusterBarrier.At L.block (L.clusterSizeAt c) (X.clusters c) i s)
    (hwl : (lh, ((h, j) : EvId)) ∈ lanes) (hφ : s.lastArrival lh = some φ)
    (hp : ClusterBarrier.Record.perform L.block (L.clusterSizeAt c) s (.wait cta warp lanes) =
      .done t)
    (hwget : ∃ pc al, X.get (h, j) = some ⟨pc, .cluster (.wait al)⟩)
    (hcount : ((X.tr h).take j).countP isArr = 2) :
    φ = 1 := by
  have hcl : c < L.nclusters := by
    by_contra hn
    rw [hX.2.1 c (by omega)] at hi
    simp at hi
  have hwr : (ClusterBarrier.Record.wait cta warp lanes : ClusterBarrier.Record EvId) ∈
      X.clusters c := List.mem_of_getElem? hi
  obtain ⟨hwh, -, -⟩ := wait_lane hX hwr hwl
  have hwh' : h = L.clusterStart c * L.block + lh := hwh
  have hN := wait_phase_count hs hwl hφ hp
  obtain ⟨pcw, alw, hw'⟩ := hwget
  have hjlen : j < (X.tr h).length := len_of_get hw'
  obtain ⟨k1, ev1, hk1, hget1, ha1, hc1⟩ := exists_occ (X.tr h) isArr j 0 (by omega)
  obtain ⟨k2, ev2, hk2, hget2, ha2, hc2⟩ := exists_occ (X.tr h) isArr j 1 (by omega)
  have hk12 : k1 < k2 := by
    by_contra hn
    rcases Nat.lt_or_ge k2 k1 with hlt | hge
    · have := countP_take_lt hlt hget2 ha2
      omega
    · have heq : k1 = k2 := by omega
      subst heq
      omega
  obtain ⟨rel1, al1, hg1⟩ := isArr_get (z := (h, k1)) hget1 ha1
  obtain ⟨rel2, al2, hg2⟩ := isArr_get (z := (h, k2)) hget2 ha2
  have hrec1 : ClusterRecorded L X (h, k1) :=
    hb (h, k1) _ _ hg1 (by show k1 + 1 < (X.tr h).length; omega)
  have hrec2 : ClusterRecorded L X (h, k2) :=
    hb (h, k2) _ _ hg2 (by show k2 + 1 < (X.tr h).length; omega)
  obtain ⟨q1, R1, hq1, hm1⟩ := rec_at hc hrec1
  obtain ⟨q2, R2, hq2, hm2⟩ := rec_at hc hrec2
  obtain ⟨cta1, warp1, lanes1, p1, hR1, hp1⟩ :=
    arrival_of_ref hX (List.mem_of_getElem? hq1) hm1 hg1
  obtain ⟨cta2, warp2, lanes2, p2, hR2, hp2⟩ :=
    arrival_of_ref hX (List.mem_of_getElem? hq2) hm2 hg2
  subst hR1 hR2
  have hl1 := arrival_lane hX (List.mem_of_getElem? hq1) hp1
  have hl2 := arrival_lane hX (List.mem_of_getElem? hq2) hp2
  have hl1' : h = L.clusterStart c * L.block + p1 := hl1.1
  have hl2' : h = L.clusterStart c * L.block + p2 := hl2.1
  have hown1 : ownArrival lh (ClusterBarrier.Record.arrival cta1 warp1 rel1 lanes1) = true :=
    ownArrival_iff.mpr ⟨cta1, warp1, rel1, lanes1, rfl, (h, k1), by
      have hp1eq : p1 = lh := by omega
      rw [← hp1eq]
      exact hp1⟩
  have hown2 : ownArrival lh (ClusterBarrier.Record.arrival cta2 warp2 rel2 lanes2) = true :=
    ownArrival_iff.mpr ⟨cta2, warp2, rel2, lanes2, rfl, (h, k2), by
      have hp2eq : p2 = lh := by omega
      rw [← hp2eq]
      exact hp2⟩
  have hq12 : q1 < q2 := record_lt_of_lt hX hac hq1 hq2 hm1 hm2 rfl hk12
  have hmW : ((h, j) : EvId) ∈ (ClusterBarrier.Record.wait cta warp lanes).refs :=
    List.mem_map.mpr ⟨(lh, (h, j)), hwl, rfl⟩
  have hq2i : q2 < i := record_lt_of_lt hX hac hq2 hi hm2 hmW rfl hk2
  have hlow : 2 ≤ ((X.clusters c).take i).countP (ownArrival lh) := by
    have e1 := countP_take_lt (p := ownArrival lh) hq12 hq1 hown1
    have e2 := countP_take_lt (p := ownArrival lh) hq2i hq2 hown2
    omega
  have hup : ((X.clusters c).take i).countP (ownArrival lh) ≤ 2 := by
    by_contra hgt
    obtain ⟨s0, R0, hs0, hR0, hown0, hc0⟩ :=
      exists_occ (X.clusters c) (ownArrival lh) i 0 (by omega)
    obtain ⟨s1, R1', hs1, hR1', hown1', hc1'⟩ :=
      exists_occ (X.clusters c) (ownArrival lh) i 1 (by omega)
    obtain ⟨s2, R2', hs2, hR2', hown2', hc2'⟩ :=
      exists_occ (X.clusters c) (ownArrival lh) i 2 (by omega)
    have o01 : s0 < s1 :=
      lt_of_countP_take_lt (p := ownArrival lh) (xs := X.clusters c) (by omega)
    have o12 : s1 < s2 :=
      lt_of_countP_take_lt (p := ownArrival lh) (xs := X.clusters c) (by omega)
    obtain ⟨cta0, warp0, rel0, lanes0, hR0eq, z0, hz0⟩ := ownArrival_iff.mp hown0
    obtain ⟨cta1', warp1', rel1', lanes1', hR1eq, z1, hz1⟩ := ownArrival_iff.mp hown1'
    obtain ⟨cta2', warp2', rel2', lanes2', hR2eq, z2, hz2⟩ := ownArrival_iff.mp hown2'
    rw [hR0eq] at hR0
    rw [hR1eq] at hR1'
    rw [hR2eq] at hR2'
    obtain ⟨hz0c, -, pcz0, alz0, hgz0⟩ := arrival_lane hX (List.mem_of_getElem? hR0) hz0
    obtain ⟨hz1c, -, pcz1, alz1, hgz1⟩ := arrival_lane hX (List.mem_of_getElem? hR1') hz1
    obtain ⟨hz2c, -, pcz2, alz2, hgz2⟩ := arrival_lane hX (List.mem_of_getElem? hR2') hz2
    have hz0m : z0 ∈ (ClusterBarrier.Record.arrival cta0 warp0 rel0 lanes0).refs :=
      List.mem_map.mpr ⟨(lh, z0), hz0, rfl⟩
    have hz1m : z1 ∈ (ClusterBarrier.Record.arrival cta1' warp1' rel1' lanes1').refs :=
      List.mem_map.mpr ⟨(lh, z1), hz1, rfl⟩
    have hz2m : z2 ∈ (ClusterBarrier.Record.arrival cta2' warp2' rel2' lanes2').refs :=
      List.mem_map.mpr ⟨(lh, z2), hz2, rfl⟩
    have hz0h : z0.1 = h := by omega
    have hz1h : z1.1 = h := by omega
    have hz2h : z2.1 = h := by omega
    have l2 : z2.2 < j := hX.source_order hac hR2' hi hs2 hz2m hmW (by omega)
    have m01 : z0.2 < z1.2 := hX.source_order hac hR0 hR1' o01 hz0m hz1m (by omega)
    have m12 : z1.2 < z2.2 := hX.source_order hac hR1' hR2' o12 hz1m hz2m (by omega)
    have t0 := trace_get hz0h hgz0
    have t1 := trace_get hz1h hgz1
    have t2 := trace_get hz2h hgz2
    have a0 := countP_take_lt (xs := X.tr h) (p := isArr) m01 t0 (isArr_of_kind rfl)
    have a1 := countP_take_lt (xs := X.tr h) (p := isArr) m12 t1 (isArr_of_kind rfl)
    have a2 := countP_take_lt (xs := X.tr h) (p := isArr) l2 t2 (isArr_of_kind rfl)
    omega
  omega

/-- A phase-one arrival of a thread has an earlier arrival of the same thread, recorded before
it. -/
theorem prior_arrival (hX : ClusterHistoryOk L X) (hac : ObjectCoherent L X) {c : Nat} {y : EvId}
    {rel : Bool}
    (hA : ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt c) (X.clusters c) y 1 rel) :
    ∃ (z : EvId) (pc : Nat) (rel' al : Bool), z.1 = y.1 ∧ z.2 < y.2 ∧
      X.get z = some ⟨pc, .cluster (.arrive rel' al)⟩ := by
  obtain ⟨i, s, t, cta, warp, lanes, g, hi, hs, hgy, hph, hp⟩ := hA
  have hi' := List.mem_of_getElem? hi
  obtain ⟨hyc, -, -⟩ := arrival_lane hX hi' hgy
  have hcount := arrival_phase_count hs hgy hp
  obtain ⟨k, R, hk, hR, hown, -⟩ :=
    exists_occ (X.clusters c) (ownArrival g) i 0 (by omega)
  obtain ⟨cta', warp', rel', lanes', hReq, z, hz⟩ := ownArrival_iff.mp hown
  rw [hReq] at hR
  obtain ⟨hzc, -, pc, al, hzget⟩ := arrival_lane hX (List.mem_of_getElem? hR) hz
  refine ⟨z, pc, rel', al, by omega, ?_, hzget⟩
  have hzm : z ∈ (ClusterBarrier.Record.arrival cta' warp' rel' lanes').refs :=
    List.mem_map.mpr ⟨(g, z), hz, rfl⟩
  have hym : y ∈ (ClusterBarrier.Record.arrival cta warp rel lanes).refs :=
    List.mem_map.mpr ⟨(g, y), hgy, rfl⟩
  exact hX.source_order hac hR hi hk hzm hym (by omega)

/-- A thread with two arrivals before position `M` of its trace has a second arrival, recorded
at phase one: the arrival with exactly one earlier arrival of its thread. -/
theorem arrival_second (hX : ClusterHistoryOk L X) (hb : ClusterBlocking L X)
    (hac : ObjectCoherent L X) {c g M : Nat} (hc : c = L.clusterOfCta (g / L.block))
    (hM : M < (X.tr g).length) (hcount : 2 ≤ ((X.tr g).take M).countP isArr) :
    ∃ (a : EvId) (rel al : Bool) (pc : Nat), a.1 = g ∧ a.2 < M ∧
      X.get a = some ⟨pc, .cluster (.arrive rel al)⟩ ∧
      ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt c) (X.clusters c) a 1 rel := by
  obtain ⟨k2, ev2, hk2, hget2, ha2, hc2⟩ := exists_occ (X.tr g) isArr M 1 (by omega)
  obtain ⟨k1, ev1, hk1, hget1, ha1, hc1⟩ := exists_occ (X.tr g) isArr k2 0 (by omega)
  obtain ⟨rel2, al2, hg2⟩ := isArr_get (z := (g, k2)) hget2 ha2
  obtain ⟨rel1, al1, hg1⟩ := isArr_get (z := (g, k1)) hget1 ha1
  have hrec2 : ClusterRecorded L X (g, k2) :=
    hb (g, k2) _ _ hg2 (by show k2 + 1 < (X.tr g).length; omega)
  have hrec1 : ClusterRecorded L X (g, k1) :=
    hb (g, k1) _ _ hg1 (by show k1 + 1 < (X.tr g).length; omega)
  obtain ⟨q2, R2, hq2, hm2⟩ := rec_at hc hrec2
  obtain ⟨q1, R1, hq1, hm1⟩ := rec_at hc hrec1
  have hcl : c < L.nclusters := by
    by_contra hn
    rw [hX.2.1 c (by omega)] at hq2
    simp at hq2
  obtain ⟨-, -, s0, hrun⟩ := hX.2.2 c hcl
  obtain ⟨cta2, warp2, lanes2, p2, hR2, hp2⟩ :=
    arrival_of_ref hX (List.mem_of_getElem? hq2) hm2 hg2
  obtain ⟨cta1, warp1, lanes1, p1, hR1, hp1⟩ :=
    arrival_of_ref hX (List.mem_of_getElem? hq1) hm1 hg1
  subst hR2 hR1
  have hl2 := arrival_lane hX (List.mem_of_getElem? hq2) hp2
  have hl1 := arrival_lane hX (List.mem_of_getElem? hq1) hp1
  have hl2' : g = L.clusterStart c * L.block + p2 := hl2.1
  have hl1' : g = L.clusterStart c * L.block + p1 := hl1.1
  have hp12 : p1 = p2 := by omega
  have hown2 : ownArrival p2 (ClusterBarrier.Record.arrival cta2 warp2 rel2 lanes2) = true :=
    ownArrival_iff.mpr ⟨cta2, warp2, rel2, lanes2, rfl, (g, k2), hp2⟩
  have hown1 : ownArrival p2 (ClusterBarrier.Record.arrival cta1 warp1 rel1 lanes1) = true :=
    ownArrival_iff.mpr ⟨cta1, warp1, rel1, lanes1, rfl, (g, k1), by rw [← hp12]; exact hp1⟩
  have hq12 : q1 < q2 := record_lt_of_lt hX hac hq1 hq2 hm1 hm2 rfl hk1
  -- at most one earlier lane record: the first arrival's record
  have hN1 : 1 ≤ ((X.clusters c).take q2).countP (ownArrival p2) := by
    have e1 := countP_take_lt (p := ownArrival p2) hq12 hq1 hown1
    omega
  have hN2 : ((X.clusters c).take q2).countP (ownArrival p2) ≤ 1 := by
    by_contra hgt
    obtain ⟨s', R', hs', hR', hown', hc'⟩ :=
      exists_occ (X.clusters c) (ownArrival p2) q2 1 (by omega)
    obtain ⟨s'', R'', hs'', hR'', hown'', -⟩ :=
      exists_occ (X.clusters c) (ownArrival p2) s' 0 (by omega)
    obtain ⟨cta', warp', rel'', lanes', hR'eq, z', hz'⟩ := ownArrival_iff.mp hown'
    obtain ⟨cta'', warp'', rel''', lanes'', hR''eq, z'', hz''⟩ := ownArrival_iff.mp hown''
    rw [hR'eq] at hR'
    rw [hR''eq] at hR''
    obtain ⟨hz'c, -, pc', al', hg'⟩ := arrival_lane hX (List.mem_of_getElem? hR') hz'
    obtain ⟨hz''c, -, pc'', al'', hg''⟩ := arrival_lane hX (List.mem_of_getElem? hR'') hz''
    have hm' : z' ∈ (ClusterBarrier.Record.arrival cta' warp' rel'' lanes').refs :=
      List.mem_map.mpr ⟨(p2, z'), hz', rfl⟩
    have hm'' : z'' ∈ (ClusterBarrier.Record.arrival cta'' warp'' rel''' lanes'').refs :=
      List.mem_map.mpr ⟨(p2, z''), hz'', rfl⟩
    have o1 : z''.2 < z'.2 := hX.source_order hac hR'' hR' hs'' hm'' hm' (by omega)
    have o2 : z'.2 < k2 := hX.source_order hac hR' hq2 hs' hm' hm2 (by omega)
    have t'' := trace_get (show z''.1 = g by omega) hg''
    have t' := trace_get (show z'.1 = g by omega) hg'
    have A'' := countP_take_lt (xs := X.tr g) (p := isArr) o1 t'' (isArr_of_kind rfl)
    have A' := countP_take_lt (xs := X.tr g) (p := isArr) o2 t' (isArr_of_kind rfl)
    omega
  have hArr : ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt c) (X.clusters c) (g, k2) 1
      rel2 := by
    obtain ⟨u, v, hu, hv⟩ := run_perform_at (s := {}) hrun hq2
    have hph := arrival_phase_count hu hp2 hv
    exact ⟨q2, u, v, cta2, warp2, lanes2, p2, hq2, hu, hp2, by omega, hv⟩
  exact ⟨(g, k2), rel2, al2, ev2.pc, rfl, hk2, hg2, hArr⟩

end Phases

end PTX.ClusterTrace
