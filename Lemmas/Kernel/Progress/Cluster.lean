-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Step.ClusterProgress
public import Lemmas.Step.DrainInOrder
public import Lemmas.Protocol.NamedBarLedger

@[expose] public section

/-! # Progress at a cluster start barrier

A kernel whose threads synchronize their cluster once, by one relaxed arrival on the cluster
barrier and the wait right after it, both before the thread exits (`ClusterStart`), steps at an
unrecorded cluster-barrier operation (`ClusterWait`), given the times of the states around the
two operations (`ClusterTimes`: a thread that has made neither is at most at `a`, one with the
arrival made is at the wait's time `w` or at most there, one with both made is at least at `r`,
`a < w < r`). Let the operation be the thread's `n`-th (`n = 0`: the arrival; `n = 1`: the wait).

* A thread of the cluster that has made at most `n` operations has not exited (an exit follows
  both operations, `exit_two`) and is earlier (`low_steps`).
* Otherwise every lane of the thread's warp has its operation `n` as its last event, unrecorded,
  at the operation's site (`cluster_lane`): a lane ahead would have more records than the warp.
  The warp's record is appended (`Step.arrival_maximal`, `Step.wait_maximal`; the extension
  performs no commit arrive-on, so the assumptions keep their constraints, `hwf`), which releases
  the thread and lowers its rank by one. An arrival is accepted: no lane has arrived in the open
  phase. A wait is accepted when phase 0 has completed; while it is open, a live thread of the
  cluster has not arrived in it, so it has made at most one operation, and it is earlier
  (`clusterWait_steps`). -/

namespace PTX.Sched

open PTX ClusterBarrier ClusterLanes ClusterPhase

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {a w r pcA pcW : Nat}

/-- The index of thread `g`'s first cluster-barrier operation (its trace's length if none). -/
def clFirst (X : Execution) (g : Nat) : Nat := (X.tr g).findIdx PTX.isCluster

/-- **The cluster start barrier**: a thread's first cluster-barrier operation is the relaxed,
unaligned arrival, the next event the unaligned wait, these are its only cluster-barrier
operations, and an exit follows both. -/
structure ClusterStart (L : Launch) (X : Execution) : Prop where
  arrive : ∀ {g : Nat}, g < L.threads → clFirst X g < (X.tr g).length →
    ∃ pc, X.get (g, clFirst X g) = some ⟨pc, .cluster (.arrive false false)⟩
  wait : ∀ {g : Nat}, g < L.threads → clFirst X g + 1 < (X.tr g).length →
    ∃ pc, X.get (g, clFirst X g + 1) = some ⟨pc, .cluster (.wait false)⟩
  cl_only : ∀ {g k pc : Nat} {op : ClusterOp}, g < L.threads →
    X.get (g, k) = some ⟨pc, .cluster op⟩ → k = clFirst X g ∨ k = clFirst X g + 1
  exit_after : ∀ {g j pc : Nat}, g < L.threads → X.get (g, j) = some ⟨pc, .exit⟩ →
    clFirst X g + 1 < j

/-- **The times around the cluster start barrier**, in the time table `M`: a state after the
arrival only is at the wait's time `w`, one after both at least at `r`; a thread's current time
with no operation made is at most `a`, with the arrival only at most `w`; after an operation the
machine is at a state; the arrival is at `pcA` and the wait at `pcW`; `a < w < r`. -/
structure ClusterTimes (M : Timed K A L) (X : Execution) (a w r pcA pcW : Nat) : Prop where
  state_time : ∀ {g k : Nat} {d : (M.code g).D}, g < L.threads →
    Frame.stateAt M.code X g k = some (some d) →
    (((X.tr g).take k).countP PTX.isCluster = 1 → M.time g d = w) ∧
    (((X.tr g).take k).countP PTX.isCluster = 2 → r ≤ M.time g d)
  end_time : ∀ {g : Nat}, g < L.threads →
    ((X.tr g).countP PTX.isCluster = 0 → threadTime M X g ≤ a) ∧
    ((X.tr g).countP PTX.isCluster = 1 → threadTime M X g ≤ w)
  live : ∀ {g k pc : Nat} {op : ClusterOp}, g < L.threads →
    X.get (g, k) = some ⟨pc, .cluster op⟩ → ∃ d, Frame.stateAt M.code X g (k + 1) = some (some d)
  arrive_pc : ∀ {g k pc : Nat} {rel al : Bool}, g < L.threads →
    X.get (g, k) = some ⟨pc, .cluster (.arrive rel al)⟩ → pc = pcA
  wait_pc : ∀ {g k pc : Nat} {al : Bool}, g < L.threads →
    X.get (g, k) = some ⟨pc, .cluster (.wait al)⟩ → pc = pcW
  order : a < w ∧ w < r

/-- A cluster-local lane of a cluster of the launch is a thread of the launch. -/
theorem lane_thread_lt (hv : L.clusterGridValid) {c x : Nat} (hc : c < L.nclusters)
    (hx : x < L.block * L.clusterSizeAt c) : L.clusterStart c * L.block + x < L.threads := by
  have h1 : L.clusterStart (c + 1) ≤ L.clusterStart L.nclusters :=
    Launch.clusterStart_mono (Nat.succ_le_of_lt hc)
  have h2 : L.clusterStart (c + 1) = L.clusterStart c + L.clusterSizeAt c := rfl
  have h3 : (L.clusterStart c + L.clusterSizeAt c) * L.block ≤ L.grid * L.block :=
    Nat.mul_le_mul_right _ (by rw [← h2, ← hv.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact h1)
  show _ < L.grid * L.block
  rw [Nat.add_mul] at h3
  rw [Nat.mul_comm L.block] at hx
  omega

/-- The cluster-barrier operation a thread makes after `n` of them. -/
def clOpEvent (pcA pcW n : Nat) : Event :=
  if n = 0 then ⟨pcA, .cluster (.arrive false false)⟩
  else ⟨pcW, .cluster (.wait false)⟩

/-- An event before a thread's first cluster-barrier operation is not one. -/
theorem not_cluster_before {g j : Nat} {ev : Event} (hj : j < clFirst X g)
    (he : X.get (g, j) = some ev) : PTX.isCluster ev = false := by
  obtain ⟨_, hev⟩ := List.getElem?_eq_some_iff.mp he
  have h := List.not_of_lt_findIdx (p := PTX.isCluster) hj
  rw [← hev]
  exact h

/-- No cluster-barrier operation precedes a thread's first. -/
theorem countP_first (g : Nat) : ((X.tr g).take (clFirst X g)).countP PTX.isCluster = 0 := by
  rw [List.countP_eq_zero]
  intro a ha
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp ha
  simp only [List.length_take] at hj
  have he : X.get (g, j) = some a := by
    simp only [Execution.get]
    rw [← hget, List.getElem_take]
    exact List.getElem?_eq_getElem _
  simp [not_cluster_before (by omega) he]

/-- A thread's cluster-barrier operations: the arrival after none, the wait after one. -/
theorem cl_event (hX : Consistent L K A mem0 X) (hc : ClusterStart L X) {g k pc : Nat}
    {op : ClusterOp} (he : X.get (g, k) = some ⟨pc, .cluster op⟩) :
    (k = clFirst X g ∧ op = .arrive false false ∧
        ((X.tr g).take k).countP PTX.isCluster = 0) ∨
      (k = clFirst X g + 1 ∧ op = .wait false ∧
        ((X.tr g).take k).countP PTX.isCluster = 1) := by
  have hg := Frame.lt_of_get hX he
  have hlen := len_of_get he
  rcases hc.cl_only hg he with rfl | rfl
  · obtain ⟨pc', h'⟩ := hc.arrive hg hlen
    rw [he] at h'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.cluster.injEq] at h'
    exact .inl ⟨rfl, h'.2, countP_first g⟩
  · obtain ⟨pc', h'⟩ := hc.wait hg hlen
    rw [he] at h'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.cluster.injEq] at h'
    refine .inr ⟨rfl, h'.2, ?_⟩
    have hl : clFirst X g + 1 < (X.tr g).length := hlen
    obtain ⟨pca, ha⟩ := hc.arrive hg (by omega)
    rw [List.take_add_one, List.countP_append, countP_first g]
    have : (X.tr g)[clFirst X g]? = some ⟨pca, .cluster (.arrive false false)⟩ := ha
    simp [this, PTX.isCluster]

/-- The kernel's cluster-barrier operations alternate: an arrival after none, a wait after
one. -/
theorem ops_alternate (hX : Consistent L K A mem0 X) (hc : ClusterStart L X) :
    OpsAlternate X := by
  intro g k pc op he
  rcases cl_event hX hc he with ⟨-, rfl, h⟩ | ⟨-, rfl, h⟩ <;> rw [h] <;> rfl

/-- A cluster-barrier operation adds one to the count of a prefix. -/
theorem count_take_succ {h k pc : Nat} {op : ClusterOp}
    (he : X.get (h, k) = some ⟨pc, .cluster op⟩) :
    ((X.tr h).take (k + 1)).countP PTX.isCluster =
      ((X.tr h).take k).countP PTX.isCluster + 1 := by
  have he' : (X.tr h)[k]? = some ⟨pc, .cluster op⟩ := he
  rw [List.take_add_one, he', Option.toList_some, List.countP_append]
  simp [PTX.isCluster]

/-- A trace has at most one operation more than its prefix without the last event. -/
theorem count_le_init (es : List Event) :
    es.countP PTX.isCluster ≤ (es.take (es.length - 1)).countP PTX.isCluster + 1 := by
  have h := List.take_append_drop (es.length - 1) es
  have hd : (es.drop (es.length - 1)).countP PTX.isCluster ≤ 1 :=
    List.countP_le_length.trans (by simp only [List.length_drop]; omega)
  conv_lhs => rw [← h]
  rw [List.countP_append]
  omega

/-- **A thread with an exit has made both operations.** -/
theorem exit_two (hX : Consistent L K A mem0 X) (hc : ClusterStart L X) {h j pc : Nat}
    (hh : h < L.threads) (hj : X.get (h, j) = some ⟨pc, .exit⟩) :
    clFirst X h + 1 < j ∧ 2 ≤ (X.tr h).countP PTX.isCluster := by
  have hpost := hc.exit_after hh hj
  have hjl := len_of_get hj
  simp only at hjl
  obtain ⟨pcw, hw⟩ := hc.wait hh (by omega)
  rcases cl_event hX hc hw with ⟨h1, -⟩ | ⟨-, -, h1⟩
  · omega
  · have h2 := count_take_succ hw
    have h3 : ((X.tr h).take (clFirst X h + 1 + 1)).countP PTX.isCluster ≤
        (X.tr h).countP PTX.isCluster := (List.take_sublist _ _).countP_le
    exact ⟨hpost, by omega⟩

/-- A thread's time is bounded by its cluster-barrier operations: none, at most the arrival's
time; one, at most the wait's. -/
theorem time_le_of_count (hw : ClusterTimes M X a w r pcA pcW) {h : Nat} (hh : h < L.threads) :
    ((X.tr h).countP PTX.isCluster = 0 → threadTime M X h ≤ a) ∧
      ((X.tr h).countP PTX.isCluster = 1 → threadTime M X h ≤ w) := by
  exact hw.end_time hh

/-- **A thread of the cluster that has made at most `n` operations lags a thread blocked at its
`n`-th.** -/
theorem low_steps (hX : Maximal L K A mem0 X) (hc : ClusterStart L X)
    (hw : ClusterTimes M X a w r pcA pcW) {g h n : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hnr : ¬ Step.Released L X g) (hn : n ≤ 1)
    (htg : (n = 0 → w ≤ threadTime M X g) ∧ (n = 1 → r ≤ threadTime M X g))
    (hh : h < L.threads) (hcl : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block))
    (hle : (X.tr h).countP PTX.isCluster ≤ n) :
    Steps M mem0 X (.thread g) := by
  have hp : Frame.Pending L X h := pending_of_noExit hX.1 hg hne hh hcl fun j pc hj => by
    have := (exit_two hX.1 hc hh hj).2
    omega
  refine earlier_steps hX hnr hp ?_
  obtain ⟨t0, t1⟩ := time_le_of_count hw hh
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · have := t0 (by omega)
    have := htg.1 rfl
    have := hw.order
    omega
  · have := htg.2 rfl
    rcases (by omega : (X.tr h).countP PTX.isCluster = 0 ∨
      (X.tr h).countP PTX.isCluster = 1) with h0 | h1
    · have := t0 h0
      have := hw.order
      omega
    · have := t1 h1
      have := hw.order
      omega

/-- The facts of one lane of the warp of a thread blocked at its operation `n`, when no lane of
the warp has made at most `n` operations: its last event is the operation `n`, unrecorded; it
has no exit; and its records are `n`. -/
theorem cluster_lane (hX : Consistent L K A mem0 X) (hc : ClusterStart L X)
    (hw : ClusterTimes M X a w r pcA pcW) {y n N : Nat} (hy : y < L.threads)
    (hgt : n < (X.tr y).countP PTX.isCluster) (hR : ClusterLanes.recCount L X y ≤ N)
    (hN : N ≤ n) :
    X.get (y, (X.tr y).length - 1) = some (clOpEvent pcA pcW n) ∧
      ¬ ClusterRecorded L X (y, (X.tr y).length - 1) ∧
      (∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩) ∧ N = n := by
  have hlastY : ∃ pc op, X.get (y, (X.tr y).length - 1) = some ⟨pc, .cluster op⟩ ∧
      ¬ ClusterRecorded L X (y, (X.tr y).length - 1) := by
    by_contra hcon
    push Not at hcon
    have := countP_le_recCount (ClusterBlocking.of_consistent hX) hcon
    omega
  obtain ⟨pc, op, hgy, hny⟩ := hlastY
  have hlen := len_of_get hgy
  simp only at hlen
  have hty := take_le_recCount (ClusterBlocking.of_consistent hX) y
  have hsucc := count_take_succ hgy
  rw [Nat.sub_add_cancel (by omega : 1 ≤ (X.tr y).length), List.take_length] at hsucc
  refine ⟨?_, hny, ?_, by omega⟩
  · rcases cl_event hX hc hgy with ⟨-, rfl, h0⟩ | ⟨-, rfl, h1⟩
    · have hn0 : n = 0 := by omega
      rw [hgy, hw.arrive_pc hy hgy, hn0]
      rfl
    · have hn1 : n = 1 := by omega
      rw [hgy, hw.wait_pc hy hgy, hn1]
      rfl
  · intro j pc' hj
    have hpost := (exit_two hX hc hy hj).1
    have hjl := len_of_get hj
    simp only at hjl
    rcases hc.cl_only hy hgy with h1 | h1 <;> omega

/-- **Progress at an unrecorded cluster-barrier operation.** A pending thread whose last event
is a cluster-barrier operation that no record holds steps: a lane of its cluster that has made
no more operations is earlier, or the record of its warp is appended. -/
theorem clusterWait_steps (hwf : Assumption.WfInOrder (fun _ => true) L K mem0 A)
    (hc : ClusterStart L X) (hw : ClusterTimes M X a w r pcA pcW)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) (hcw : ClusterWait L X g) :
    Steps M mem0 X (.thread g) := by
  obtain ⟨pc, op, hlast, hnr⟩ := hcw
  have hX := hmax.1
  have hg := hp.1
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hp.1
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hlast
    simp only at this
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  -- the last event is the thread's operation `n`
  set n := ((X.tr g).take ((X.tr g).length - 1)).countP PTX.isCluster with hndef
  have hn1 : n ≤ 1 := by
    rcases cl_event hX hc hlast with ⟨-, -, h0⟩ | ⟨-, -, h1⟩ <;> omega
  have hsucc := count_take_succ hlast
  rw [Nat.sub_add_cancel hlen, List.take_length] at hsucc
  -- the thread's time after it
  have htg : (n = 0 → w ≤ threadTime M X g) ∧
      (n = 1 → r ≤ threadTime M X g) := by
    obtain ⟨d, hσ⟩ := hw.live hg hlast
    rw [Nat.sub_add_cancel hlen] at hσ
    have hst := hw.state_time hg hσ
    rw [List.take_length] at hst
    rw [threadTime_of hσ]
    exact ⟨fun h0 => (hst.1 (by omega)).ge, fun h1 => hst.2 (by omega)⟩
  have hblock : ∀ h, h < L.threads →
      L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) →
      (X.tr h).countP PTX.isCluster ≤ n → Steps M mem0 X (.thread g) :=
    fun h hh hcl hle => low_steps hmax hc hw hg hne hrel hn1 htg hh hcl hle
  have hcta : g / L.block < L.grid := by
    have : g < L.grid * L.block := hg
    rw [Nat.div_lt_iff_lt_mul hb]
    exact this
  have hlanelt : ∀ lt, lt < L.block → g / L.block * L.block + lt < L.threads := by
    intro lt hlt
    show _ < L.grid * L.block
    have : (g / L.block + 1) * L.block ≤ L.grid * L.block := Nat.mul_le_mul_right _ hcta
    nlinarith
  have hlanecta : ∀ lt, lt < L.block → (g / L.block * L.block + lt) / L.block = g / L.block := by
    intro lt hlt
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hlt, Nat.zero_add]
  by_cases hA : ∃ lt, lt < L.block ∧ lt / 32 = g % L.block / 32 ∧
      (X.tr (g / L.block * L.block + lt)).countP PTX.isCluster ≤ n
  · obtain ⟨lt, hlt, -, hle⟩ := hA
    exact hblock _ (hlanelt lt hlt) (by rw [hlanecta lt hlt]) hle
  push Not at hA
  -- every lane is at its operation `n`, unrecorded
  have hcl : L.clusterOfCta (g / L.block) < L.nclusters :=
    Step.clusterOf_lt hX.cluster.1 hcta
  obtain ⟨-, -, s, hs⟩ := hX.cluster.2.2 _ hcl
  have hgeq : g / L.block * L.block + g % L.block = g := Nat.div_add_mod' g L.block
  have hgl := Step.lane_index hX.cluster.1 hcta (Nat.mod_lt g hb)
  rw [hgeq] at hgl
  have hnxg : ∀ j pc', X.get (g, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    have hpost := (exit_two hX hc hg hj).1
    have hjl := len_of_get hj
    simp only at hjl
    rcases hc.cl_only hg hlast with h1 | h1 <;> omega
  have hglive : L.rankOfCta (g / L.block) * L.block + g % L.block ∉ s.exited :=
    lane_live hX.cluster hcl (fun j pc' => by rw [← hgl.2]; exact hnxg j pc') hs
  have hrecg : recCount L X g ≤ n := by
    have hra : recAt L X g ((X.tr g).length - 1) = false := by
      simp only [recAt, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact .inl hnr
    exact recCount_le_take hra
  have hNg : (X.clusters (L.clusterOfCta (g / L.block))).countP
      (ownAny (L.rankOfCta (g / L.block) * L.block + g % L.block)) ≤ n := by
    have := countP_ownAny_le_rec hX.cluster hcl hgl.1
    rw [← hgl.2] at this
    omega
  have hlane : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      X.get (g / L.block * L.block + lt, (X.tr (g / L.block * L.block + lt)).length - 1) =
        some (clOpEvent pcA pcW n) ∧
      ¬ ClusterRecorded L X (g / L.block * L.block + lt,
        (X.tr (g / L.block * L.block + lt)).length - 1) ∧
      (∀ j pc, X.get (g / L.block * L.block + lt, j) ≠ some ⟨pc, .exit⟩) ∧
      (X.clusters (L.clusterOfCta (g / L.block))).countP
        (ownAny (L.rankOfCta (g / L.block) * L.block + lt)) = n := by
    intro lt hlt hlw
    obtain ⟨hlk, hly⟩ := Step.lane_index hX.cluster.1 hcta hlt
    have hdiv : ∀ y, y < L.block →
        (L.rankOfCta (g / L.block) * L.block + y) / L.block = L.rankOfCta (g / L.block) :=
      fun y hy => by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hy,
        Nat.zero_add]
    have hmod : ∀ y, y < L.block → (L.rankOfCta (g / L.block) * L.block + y) % L.block = y :=
      fun y hy => by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
    have hNy := countP_ownAny_le (h := X.clusters (L.clusterOfCta (g / L.block)))
      (x := L.rankOfCta (g / L.block) * L.block + lt)
      (y := L.rankOfCta (g / L.block) * L.block + g % L.block) hs
      (by rw [hdiv lt hlt, hdiv _ (Nat.mod_lt g hb)])
      (by rw [hmod lt hlt, hmod _ (Nat.mod_lt g hb), hlw]) hglive
    have hRy := rec_le_countP_ownAny hX.cluster hcl hlk
    rw [← hly] at hRy
    exact cluster_lane hX hc hw (hlanelt lt hlt) (hA lt hlt hlw) hRy (by omega)
  have hw32 : g % L.block / 32 * 32 < L.block := by
    have := Nat.div_mul_le_self (g % L.block) 32
    have := Nat.mod_lt g hb
    omega
  have hlives : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      L.rankOfCta (g / L.block) * L.block + lt ∉ s.exited := by
    intro lt hlt hlw
    have hly := (Step.lane_index hX.cluster.1 hcta hlt).2
    exact lane_live hX.cluster hcl (fun j pc' => by
      rw [← hly]; exact (hlane lt hlt hlw).2.2.1 j pc') hs
  have hlw := Step.liveWarp_warpLanes (X := X) (s := s) hX.cluster.1 hcta hb hw32 hlives
  have hfree : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      ¬ ClusterRecorded L X (g / L.block * L.block + lt,
        (X.tr (g / L.block * L.block + lt)).length - 1) :=
    fun lt hlt hlw => (hlane lt hlt hlw).2.1
  have halt : ∀ {x : Nat}, x < L.block * L.clusterSizeAt (L.clusterOfCta (g / L.block)) →
      Alt x (X.clusters (L.clusterOfCta (g / L.block))) := fun hx =>
    alt_of_ops hX.cluster (ClusterBlocking.of_consistent hX) hX.object (ops_alternate hX hc) hcl hx
  -- the lanes' statuses
  have hst : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      LaneSt (L.rankOfCta (g / L.block) * L.block + lt) s
        ((X.clusters (L.clusterOfCta (g / L.block))).countP
          (ownArrival (L.rankOfCta (g / L.block) * L.block + lt)))
        ((X.clusters (L.clusterOfCta (g / L.block))).countP
          (ownWait (L.rankOfCta (g / L.block) * L.block + lt))) ∧
      (X.clusters (L.clusterOfCta (g / L.block))).countP
          (ownArrival (L.rankOfCta (g / L.block) * L.block + lt)) +
        (X.clusters (L.clusterOfCta (g / L.block))).countP
          (ownWait (L.rankOfCta (g / L.block) * L.block + lt)) = n := by
    intro lt hlt hlw
    refine ⟨run_laneSt hs (halt (Step.lane_index hX.cluster.1 hcta hlt).1), ?_⟩
    rw [← countP_ownAny]
    exact (hlane lt hlt hlw).2.2.2
  -- the released thread ranks one lower
  have hrank : rank M X (.thread g) = 2 * threadTime M X g + 1 :=
    rank_unreleased hrel
  have hrecord : ∀ R : ClusterBarrier.Record EvId,
      R.refs = (Step.warpLanes L X (g / L.block) (g % L.block / 32)).map Prod.snd →
      Maximal L K A mem0 (X.withClusterRecord (L.clusterOfCta (g / L.block)) R) →
      Steps M mem0 X (.thread g) := by
    intro R hR hmaxY
    have hrelY : Step.Released L (X.withClusterRecord (L.clusterOfCta (g / L.block)) R) g :=
      Step.released_of_record hb hR hmaxY.1.cluster hlast
    refine .inr ⟨_, .thread g, hmaxY, hp, ?_⟩
    rw [rank_released hrelY, hrank]
    exact Nat.lt_succ_self _
  have hasm : ∀ R, ∀ a ∈ A,
      a.wf L mem0 (X.withClusterRecord (L.clusterOfCta (g / L.block)) R) := fun R =>
    hwf _ _ hX (Step.ClusterRec.le_withClusterRecord _ _ _)
      (Execution.notifiedInOrder_of_eq rfl)
  by_cases hn0 : n = 0
  · -- an arrival: no lane has arrived in the open phase, so the record is accepted
    have hlastA : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
        X.get (g / L.block * L.block + lt, (X.tr (g / L.block * L.block + lt)).length - 1) =
          some ⟨pcA, .cluster (.arrive false false)⟩ := by
      intro lt hlt hlw
      rw [(hlane lt hlt hlw).1]
      simp [clOpEvent, hn0]
    have hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt (L.clusterOfCta (g / L.block))) {}
        (X.clusters (L.clusterOfCta (g / L.block)) ++
          [Step.warpArrival L X (g / L.block) (g % L.block / 32) false]) = .done t := by
      suffices hok : ∀ j ∈ (Step.warpLanes L X (g / L.block) (g % L.block / 32)).map Prod.fst,
          ¬ Locked j s by
        obtain ⟨t, ht⟩ := record_arrival_done (rel := false) hlw hok
        refine ⟨t, ?_⟩
        rw [ClusterBarrier.run_append, hs]
        simp only [ClusterBarrier.run, Step.warpArrival, ht]
      intro j hj
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hj
      obtain ⟨lt, hlt, hlw', rfl⟩ := Step.mem_warpLanes hpm
      obtain ⟨hst', hsum⟩ := hst lt hlt hlw'
      have h0 : (X.clusters (L.clusterOfCta (g / L.block))).countP
            (ownArrival (L.rankOfCta (g / L.block) * L.block + lt)) =
          (X.clusters (L.clusterOfCta (g / L.block))).countP
            (ownWait (L.rankOfCta (g / L.block) * L.block + lt)) := by
        omega
      rw [h0] at hst'
      exact LaneSt.not_arrived (sound_run sound_empty hs) hst'
    exact hrecord _ rfl (Step.arrival_maximal hmax hcta hlastA hfree hacc (hasm _))
  -- a wait: every lane arrived in phase 0 and has not waited since
  have hn1' : n = 1 := by omega
  have hlastW : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      X.get (g / L.block * L.block + lt, (X.tr (g / L.block * L.block + lt)).length - 1) =
        some ⟨pcW, .cluster (.wait false)⟩ := by
    intro lt hlt hlw
    rw [(hlane lt hlt hlw).1]
    simp [clOpEvent, hn0]
  have hlaneA : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      s.lastArrival (L.rankOfCta (g / L.block) * L.block + lt) = some 0 := by
    intro lt hlt hlw
    obtain ⟨⟨hwa, haw, -, -⟩, hsum⟩ := hst lt hlt hlw
    have hlk := (Step.lane_index hX.cluster.1 hcta hlt).1
    have hlc := run_last_count sound_empty
      (by simp [ClusterPhase.LastCount, ClusterPhase.weight]) hs hlk
      (hlives lt hlt hlw)
    have hwt := run_weight sound_empty hs hlk (hlives lt hlt hlw)
    have hw0 : ClusterPhase.weight (L.rankOfCta (g / L.block) * L.block + lt) ({} : State) = 0 := by
      simp [ClusterPhase.weight]
    unfold ClusterPhase.LastCount at hlc
    rw [hwt, hw0] at hlc
    rw [hlc]
    split
    · omega
    · congr 1
      omega
  by_cases hph : 0 < s.phase
  · -- phase 0 has completed: the record is accepted
    have hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt (L.clusterOfCta (g / L.block))) {}
        (X.clusters (L.clusterOfCta (g / L.block)) ++
          [Step.warpWait L X (g / L.block) (g % L.block / 32)]) = .done t := by
      suffices hok : ∀ j ∈ (Step.warpLanes L X (g / L.block) (g % L.block / 32)).map Prod.fst,
          ∃ p, s.lastArrival j = some p ∧ p < s.phase by
        obtain ⟨t, ht⟩ := record_wait_done hlw hok
        refine ⟨t, ?_⟩
        rw [ClusterBarrier.run_append, hs]
        simp only [ClusterBarrier.run, Step.warpWait, ht]
      intro j hj
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hj
      obtain ⟨lt, hlt, hlw', rfl⟩ := Step.mem_warpLanes hpm
      exact ⟨_, hlaneA lt hlt hlw', hph⟩
    exact hrecord _ rfl (Step.wait_maximal hmax hcta hlastW hfree hacc (hasm _))
  -- phase 0 is open: a live thread of the cluster has not arrived in it
  have hopen : s.lastArrival (L.rankOfCta (g / L.block) * L.block + g % L.block) =
      some s.phase := by
    rw [hlaneA (g % L.block) (Nat.mod_lt g hb) rfl]
    congr 1
    omega
  obtain ⟨h', hh'K, -, hcnt⟩ := Step.wait_open_witness hs hopen
  obtain ⟨hwa, -, -, -⟩ := run_laneSt (x := h') hs (halt hh'K)
  have hR := rec_le_countP_ownAny hX.cluster hcl hh'K
  rw [countP_ownAny] at hR
  have hh := lane_thread_lt hX.cluster.1 hcl hh'K
  have hty := take_le_recCount (ClusterBlocking.of_consistent hX)
    (L.clusterStart (L.clusterOfCta (g / L.block)) * L.block + h')
  have hsy := count_le_init (X.tr (L.clusterStart (L.clusterOfCta (g / L.block)) * L.block + h'))
  refine hblock _ hh (clusterOf_lane hcl hh'K) ?_
  omega

end

end PTX.Sched
