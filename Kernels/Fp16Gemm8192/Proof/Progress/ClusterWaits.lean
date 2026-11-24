-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.ClusterStage

@[expose] public section

/-! # Progress at the cluster barrier

The class of the cluster barrier: the prologue's arrival and wait and the exit's arrival and wait
(`ThreadD.AtCluster`). A pending thread steps in two ways.

* At a cluster site with its last event released (`cluster_next_steps`), it performs the
  operation, a counted extension (`Step.cluster_counted_extension`).
* With its last event a cluster operation that no record holds (`cluster_last_steps`), let it be
  the thread's operation number `n` (from 0). If some lane of its warp has made at most `n`
  operations, that lane is pending and earlier in the rank table (`time_lt_of_clOps`). Otherwise
  every lane of the warp has its operation `n` as its last event, unrecorded: a record of the warp
  holds every live lane of it, so a lane ahead would have more records than the warp
  (`ClusterLanes.countP_ownAny_le`, `rec_le_countP_ownAny`, `countP_ownAny_le_rec`). The warp's
  record is then appended (`Step.arrival_maximal`, `Step.wait_maximal`), which releases the thread
  and lowers its rank by one; its lanes have alternated arrivals and waits, by the program's
  order (`cluster_alt`, `ClusterLanes.run_laneSt`), so an arrival is accepted, and so is a wait
  whose phase has completed. A wait whose phase is open has a live thread of the cluster that has
  not arrived in it (`Step.wait_open_witness`); that thread has made at most `n` operations, so it
  is pending and earlier. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow ClusterBarrier ClusterLanes ClusterPhase

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Progress at a cluster site.** A pending thread at a cluster site, whose last event is
released, performs the cluster operation: a counted extension. -/
theorem cluster_next_steps (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hat : d.AtCluster)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 hub hp
  obtain ⟨t1, u, hl, he⟩ := ht.cluster_fire hp.1 hσ hat hrun
  have hne : X.tr g ≠ [] := by
    intro h0
    simp only [Frame.stateAt, h0, List.take_nil] at hσ
    cases hσ
    simp [ThreadD.AtCluster] at hat
  obtain ⟨op, hev⟩ := clEvent_shape d.clOps
  rw [hev] at he
  exact .inl (Step.cluster_counted_extension hmax.1 hp.1 hne hrel (prod_wf _)
    hrun hl he)

/-- The cluster operations of a prefix are at most those of the trace. -/
theorem clOps_take_le (es : List Event) (k : Nat) : clOps (es.take k) ≤ clOps es :=
  (List.take_sublist k es).countP_le

/-- A trace has at most one operation more than its prefix without the last event. -/
theorem clOps_le_init (es : List Event) : clOps es ≤ clOps (es.take (es.length - 1)) + 1 := by
  have h := List.take_append_drop (es.length - 1) es
  have hd : (es.drop (es.length - 1)).countP isCluster ≤ 1 :=
    List.countP_le_length.trans (by simp only [List.length_drop]; omega)
  unfold clOps
  conv_lhs => rw [← h]
  rw [List.countP_append]
  omega

/-- The last event of a trace is at its last position. -/
theorem get_last_of {g pc : Nat} {k : Kind} (h : (X.tr g).getLast? = some ⟨pc, k⟩) :
    X.get (g, (X.tr g).length - 1) = some ⟨pc, k⟩ := by
  change (X.tr g)[(X.tr g).length - 1]? = _
  rw [← List.getLast?_eq_getElem?]
  exact h

/-- A thread whose events up to some position count four cluster operations has made them. -/
theorem four_of_exit (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    {h j pc : Nat}
    (hh : h < L.threads) (he : X.get (h, j) = some ⟨pc, .exit⟩) :
    clOps ((X.tr h).take j) = 4 := by
  obtain ⟨d, hd⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub he
  obtain ⟨h1, h2⟩ := ht.cl_ops hh hd
  rw [h1]
  exact (h2 _ he).2 rfl

/-- **The blocker of a cluster operation.** A thread of `g`'s cluster that has made at most `n`
cluster operations, while `g`'s last event is its operation `n`, unreleased, is pending and has a
smaller rank. -/
theorem cluster_blocker (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hX : Consistent L kernel Prod mem0 X) {g h n : Nat} (hg : g < L.threads)
    (hh : h < L.threads) (hne : X.tr g ≠ [])
    (hc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block)) {dg : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some dg)) (hdg : dg.clOps = n + 1)
    (hrel : ¬ Step.Released L X g) (hle : clOps (X.tr h) ≤ n) :
    Descent.Obl L X (.thread h) ∧ rank L X (.thread h) < rank L X (.thread g) := by
  have hn3 : n ≤ 3 := by have := (clOps_stage dg L g (X.tr g)).2.2.2.2.2; omega
  refine ⟨⟨hh, not_canceled_of_peer hX hg hne hc, fun pc hl => ?_⟩, ?_⟩
  · have h4 := four_of_exit hX ht hub hh (get_last_of hl)
    have := clOps_take_le (X.tr h) ((X.tr h).length - 1)
    omega
  · have hlt : threadTime L X h < threadTime L X g := by
      refine time_lt_of_clOps hh hσ (by omega) ?_
      cases hσh : Frame.stateAt (code L) X h (X.tr h).length with
      | none => exact .inl rfl
      | some σ =>
        cases σ with
        | none => exact absurd hσh (ht.tracked h _ hh)
        | some dh =>
          refine .inr ⟨dh, rfl, ?_⟩
          have := (ht.cl_ops hh hσh).1
          rw [List.take_length] at this
          omega
    have h1 := rank_thread_le (L := L) (X := X) (g := h)
    have h2 : rank L X (.thread g) = threadTime L X g + 1 := by simp [rank, hrel]
    omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
