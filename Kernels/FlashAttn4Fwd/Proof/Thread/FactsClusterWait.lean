-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWaits

@[expose] public section

/-! # The cluster barrier's times (`ClusterWaitFacts.state_time`, `end_time`)

A prologue state has made as many cluster-barrier operations as its site's count
(`Prologue.Run.clusters`: one at the wait, none before; `pro_count`). A role state has made
exactly two (`role_count`): the thread's first cluster operation is its arrival, at the
prologue's arrival site; the state after it is the wait site (`cl_wait_state`); the role starts
after the wait, a cluster operation too (`cluster_event`); and a thread makes at most two
(`ThreadFacts_cluster_ops`). With the time tables (the prologue below the arrival's time but at
the arrival and the wait, every role state at least the register requests' time) this gives
the fields. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A prologue state has made its site's count of cluster-barrier operations. -/
theorem pro_count (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) {g k : Nat}
    (hg : g < L.threads) {p : Prologue.D}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inl p))) :
    ((X.tr g).take k).countP PTX.isCluster = p.site.clusters := by
  have h := (Prologue.run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg)
    k p hσ).clusters
  rw [← h]
  exact List.countP_congr fun x _ => by rw [isCluster_kind]

/-- An event fired at the prologue's arrival or wait site is a cluster-barrier operation. -/
theorem cluster_event (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) {g j : Nat}
    {p : Prologue.D} {e : Event} (hs : p.site = .clArrive ∨ p.site = .clWait)
    (hσ : Frame.stateAt (code L) X g j = some (some (.inl p))) (he : X.get (g, j) = some e) :
    PTX.isCluster e = true := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ :=
    Frame.fired_site (C := code L) (fun _ hg => sound hpre hg) hX he hσ
  have hk := site_kindOp (L := L) (g := g) (.inl p) hc
  have hkind : nextKind (.inl p) = .cluster := by
    rcases hs with hs | hs <;> simp [nextKind, prologueKind, hs]
  rw [hkind] at hk
  generalize ins.op = op at hk hf
  cases op <;> simp only [kindOp, Bool.false_eq_true] at hk
  simp only [eventTmpl, Fires] at hf
  obtain ⟨rfl, -⟩ := hf
  rfl

/-- **A role state has made exactly two cluster-barrier operations.** -/
theorem role_count (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} (hg : g < L.threads) {r : Role}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr r))) :
    ((X.tr g).take k).countP PTX.isCluster = 2 := by
  have htr := Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg
  obtain ⟨x, hx, hxc⟩ := role_cluster hpre hg htr k r hσ
  -- the first cluster operation is before `k`
  have hfk : clFirst X g < k := by
    by_contra hle
    have hsub : x ∈ (X.tr g).take (clFirst X g) :=
      (List.take_sublist_take_left (by omega)).subset hx
    have := cl_none x hsub
    rw [hxc] at this
    cases this
  have hfl : clFirst X g < (X.tr g).length :=
    List.findIdx_lt_length_of_exists ⟨x, List.mem_of_mem_take hx, by rw [isCluster_kind]; exact hxc⟩
  have hw := cl_wait_state hpre hX ht hg hfl
  -- the wait's position is an event, a cluster-barrier operation
  have hk2 : clFirst X g + 1 < k := by
    rcases Nat.lt_or_ge (clFirst X g + 1) k with h | h
    · exact h
    · have hk : k = clFirst X g + 1 := by omega
      rw [hk, hw] at hσ
      cases hσ
  have hl2 : clFirst X g + 1 < (X.tr g).length := by
    by_contra hle
    have h1 : Frame.stateAt (code L) X g k = Frame.stateAt (code L) X g (clFirst X g + 1) := by
      rw [Frame.stateAt_of_le (show (X.tr g).length ≤ k by omega),
        Frame.stateAt_of_le (show (X.tr g).length ≤ clFirst X g + 1 by omega)]
    rw [h1, hw] at hσ
    cases hσ
  have he1 : X.get (g, clFirst X g + 1) = some (X.tr g)[clFirst X g + 1] :=
    List.getElem?_eq_getElem hl2
  have hc1 := cluster_event hpre hX (p := ⟨.clWait⟩) (.inr rfl) hw he1
  have hc0 : PTX.isCluster (X.tr g)[clFirst X g] = true := List.findIdx_getElem (w := hfl)
  -- two before `k`, at most two in all
  have hge : 2 ≤ ((X.tr g).take k).countP PTX.isCluster := by
    have hsub : ((X.tr g).take (clFirst X g + 2)).countP PTX.isCluster ≤
        ((X.tr g).take k).countP PTX.isCluster :=
      (List.take_sublist_take_left (by omega)).countP_le
    have h0 : ((X.tr g).take (clFirst X g)).countP PTX.isCluster = 0 :=
      List.countP_eq_zero.mpr fun y hy => by
        have := cl_none y hy
        rw [isCluster_kind]; simpa using this
    have hsplit : (X.tr g).take (clFirst X g + 2) = (X.tr g).take (clFirst X g) ++
        [(X.tr g)[clFirst X g], (X.tr g)[clFirst X g + 1]] := by
      rw [show clFirst X g + 2 = clFirst X g + 1 + 1 by omega,
        List.take_succ_eq_append_getElem hl2, List.take_succ_eq_append_getElem hfl,
        List.append_assoc]
      rfl
    rw [hsplit, List.countP_append, h0] at hsub
    simp [hc0, hc1] at hsub
    omega
  have hle : ((X.tr g).take k).countP PTX.isCluster ≤ 2 := by
    have h := ThreadFacts_cluster_ops hpre hX ht hg
    rw [← List.countP_eq_length_filter] at h
    have h2 : ((X.tr g).take k).countP PTX.isCluster ≤ (X.tr g).countP PTX.isCluster :=
      (List.take_sublist _ _).countP_le
    have h3 : (X.tr g).countP PTX.isCluster =
        (X.tr g).countP (fun e => Prologue.isCluster e.kind) :=
      List.countP_congr fun x _ => by rw [isCluster_kind]
    omega
  omega

theorem prologue_le_arrive (s : Prologue.Site) (h1 : s ≠ .clArrive) (h2 : s ≠ .clWait) :
    Progress.Time.prologue s + 1 ≤ Progress.Time.clArriveT := by
  cases s <;> (try simp at h1 h2) <;> site_decide

theorem role_regT (L : Launch) (g : Nat) (r : Role) :
    Progress.Time.regT ≤ stateTime L g (.inr r) := by
  by_cases h : nextKind (.inr r) = .reg
  · exact (reg_time L g r h).ge
  · exact (regT_lt_role L g r h).le

/-- **The time of a state is fixed by the cluster-barrier operations before it.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ClusterWaitFacts_state_time (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X) :
    ∀ {g k : Nat} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
      (((X.tr g).take k).countP PTX.isCluster = 1 →
        stateTime L g d = Progress.Time.clWaitT) ∧
      (((X.tr g).take k).countP PTX.isCluster = 2 → Progress.Time.regT ≤ stateTime L g d) := by
  intro g k d hg hσ
  rcases d with p | r
  · have hc := pro_count hpre hX hg hσ
    rw [hc]
    obtain ⟨s⟩ := p
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · cases s <;> simp_all [Prologue.Site.clusters, stateTime, Progress.Time.prologue]
    · cases s <;> simp_all [Prologue.Site.clusters]
  · have hc := role_count hpre hX ht hg hσ
    rw [hc]
    exact ⟨fun h => by omega, fun _ => role_regT L g r⟩

/-- **A thread's current time is at most the arrival's time before its arrival, the wait's before
its wait.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ClusterWaitFacts_end_time (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat}, g < L.threads →
      ((X.tr g).countP PTX.isCluster = 0 → endTime L X g ≤ Progress.Time.clArriveT) ∧
      ((X.tr g).countP PTX.isCluster = 1 → endTime L X g ≤ Progress.Time.clWaitT) := by
  intro g hg
  have hall : (X.tr g).take (X.tr g).length = X.tr g := List.take_length
  unfold Sched.threadTime; dsimp only [timed]
  split
  · rename_i d hσ
    rcases d with p | r
    · have hc := pro_count hpre hX hg hσ
      rw [hall] at hc
      rw [hc]
      obtain ⟨s⟩ := p
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · have h1 : s ≠ .clWait := by rintro rfl; simp [Prologue.Site.clusters] at h0
        by_cases h2 : s = .clArrive
        · subst h2; simp [stateTime, Progress.Time.prologue]
        · have := prologue_le_arrive s h2 h1
          simp only [stateTime]; omega
      · have : s = .clWait := by cases s <;> simp_all [Prologue.Site.clusters]
        subst this; simp [stateTime, Progress.Time.prologue]
    · have hc := role_count hpre hX ht hg hσ
      rw [hall] at hc
      rw [hc]
      exact ⟨fun h => by omega, fun h => by omega⟩
  · exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  · rename_i hσ
    split
    · rename_i d hσ'
      have hlen : 0 < (X.tr g).length := by
        by_contra h0
        have hl : (X.tr g).length = 0 := by omega
        have h1 : Frame.stateAt (code L) X g (X.tr g).length = some (some (code L g).init) := by
          rw [hl]; exact Frame.stateAt_zero
        rw [h1] at hσ
        cases hσ
      have hj : (X.tr g).length - 1 < (X.tr g).length := by omega
      have he : X.get (g, (X.tr g).length - 1) = some (X.tr g)[(X.tr g).length - 1] :=
        List.getElem?_eq_getElem hj
      have hsplit : X.tr g = (X.tr g).take ((X.tr g).length - 1) ++
          [(X.tr g)[(X.tr g).length - 1]] := by
        have h := List.take_succ_eq_append_getElem hj
        rwa [Nat.sub_add_cancel hlen, List.take_length] at h
      rcases d with p | r
      · have hc := pro_count hpre hX hg hσ'
        obtain ⟨s⟩ := p
        refine ⟨fun h0 => ?_, fun h1 => ?_⟩
        · rw [hsplit, List.countP_append, hc] at h0
          have hs : s ≠ .clArrive ∧ s ≠ .clWait := by
            constructor <;> rintro rfl <;>
              simp [cluster_event hpre hX (p := ⟨_⟩) (by simp) hσ' he] at h0
          have := prologue_le_arrive s hs.1 hs.2
          simp only [stateTime]; omega
        · rw [hsplit, List.countP_append, hc] at h1
          by_cases hw : s = .clWait
          · subst hw
            simp [cluster_event hpre hX (p := ⟨_⟩) (by simp) hσ' he,
              Prologue.Site.clusters] at h1
          by_cases ha : s = .clArrive
          · subst ha
            simp [stateTime, Progress.Time.prologue, Progress.Time.clArriveT,
              Progress.Time.clWaitT]
          · have := prologue_le_arrive s ha hw
            simp only [stateTime, Progress.Time.clArriveT, Progress.Time.clWaitT] at this ⊢
            omega
      · have hc := role_count hpre hX ht hg hσ'
        rw [hsplit, List.countP_append, hc]
        exact ⟨fun h => by omega, fun h => by omega⟩
    · exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
