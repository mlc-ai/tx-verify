-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.ClusterWaits
public import Kernels.Fp16Gemm8192.Proof.ClusterLaneFacts
public import Lemmas.Step.ClusterReady

@[expose] public section

/-! # Progress at an unrecorded cluster operation

A pending thread whose last event is a cluster operation that no record holds steps
(`cluster_last_steps`); see `Progress/ClusterWaits.lean` for the argument. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow ClusterBarrier ClusterLanes ClusterPhase

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The facts of one lane of the warp of a thread blocked at its operation `n`, when no lane of
the warp has made at most `n` operations: its last event is the operation `n`, unrecorded; it has
no exit; and its records are `n`. -/
theorem cluster_lane (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hX : Consistent L kernel Prod mem0 X) {cta lt n : Nat} (hy : cta * L.block + lt < L.threads)
    (hn3 : n ≤ 3) (hgt : n < clOps (X.tr (cta * L.block + lt)))
    (hR : recCount L X (cta * L.block + lt) ≤
      (X.clusters (L.clusterOfCta cta)).countP (ownAny (L.rankOfCta cta * L.block + lt)))
    (hN : (X.clusters (L.clusterOfCta cta)).countP (ownAny (L.rankOfCta cta * L.block + lt)) ≤ n) :
    X.get (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) = some (clEvent n) ∧
      ¬ ClusterRecorded L X (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) ∧
      (∀ j pc, X.get (cta * L.block + lt, j) ≠ some ⟨pc, .exit⟩) ∧
      (X.clusters (L.clusterOfCta cta)).countP (ownAny (L.rankOfCta cta * L.block + lt)) = n := by
  set y := cta * L.block + lt with hydef
  -- the last event is an unrecorded operation
  have hlastY : ∃ pc op, X.get (y, (X.tr y).length - 1) = some ⟨pc, .cluster op⟩ ∧
      ¬ ClusterRecorded L X (y, (X.tr y).length - 1) := by
    by_contra hcon
    push Not at hcon
    have := countP_le_recCount (ClusterBlocking.of_consistent hX) hcon
    change clOps (X.tr y) ≤ _ at this
    omega
  obtain ⟨pc, op, hgy, hny⟩ := hlastY
  obtain ⟨dy, hdy⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub hgy
  obtain ⟨hcy, hevy⟩ := ht.cl_ops hy hdy
  have hey := ((hevy _ hgy).1 rfl).1
  have hty : clOps ((X.tr y).take ((X.tr y).length - 1)) ≤ recCount L X y :=
    take_le_recCount (ClusterBlocking.of_consistent hX) y
  have hsy := clOps_le_init (X.tr y)
  have hdyn : dy.clOps = n := by omega
  refine ⟨by rw [hgy, hey, hdyn], hny, ?_, by omega⟩
  intro j pc' hj
  have h4 := four_of_exit hX ht hub hy hj
  have hjl := len_of_get hj
  have hjne : j ≠ (X.tr y).length - 1 := by
    intro he
    rw [he, hgy] at hj
    cases hj
  have hpre : clOps ((X.tr y).take j) ≤ clOps ((X.tr y).take ((X.tr y).length - 1)) := by
    have : (X.tr y).take j = ((X.tr y).take ((X.tr y).length - 1)).take j := by
      rw [List.take_take]
      congr 1
      simp only at hjl ⊢
      omega
    rw [this]
    exact clOps_take_le _ _
  omega

/-- The operations of a trace split at its last event. -/
theorem clOps_split {es : List Event} {e : Event} (h : es[es.length - 1]? = some e) :
    clOps es = clOps (es.take (es.length - 1)) + (if isCluster e then 1 else 0) := by
  have hl : es.length - 1 < es.length := (List.getElem?_eq_some_iff.mp h).1
  conv_lhs => rw [← List.take_append_drop (es.length - 1) es]
  rw [List.drop_eq_getElem_cons hl, List.drop_eq_nil_of_le (by omega)]
  have he : es[es.length - 1] = e := (List.getElem?_eq_some_iff.mp h).2
  rw [he]
  simp only [clOps, List.countP_append, List.countP_singleton]

/-- **Progress at an unrecorded cluster operation.** A pending thread whose last event is a
cluster operation that no record holds extends a maximal execution or passes to an obligation of
smaller rank. -/
theorem cluster_last_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {dg : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some dg)) {pc : Nat} {op : ClusterOp}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster op⟩)
    (hnready : ¬ Ready L X (g, (X.tr g).length - 1)) : Descent.Steps L kernel Prod mem0
      (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hnr : ¬ ClusterRecorded L X (g, (X.tr g).length - 1) :=
    fun h => hnready (Step.ready_of_recorded hX.cluster hlast h)
  have hg := hp.1
  have hB : L.block = 384 := hpre.block
  have hCS : L.clusterSize.val = 2 := hpre.cluster
  have hG : L.grid = 1024 := hpre.grid
  have hb : 0 < L.block := by omega
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hlast
    simp only at this
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hrel : ¬ Step.Released L X g := fun hr => hnready (hr.ready pc _ hlast rfl)
  -- the last event is the thread's operation `n`
  obtain ⟨d0, hd0⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub hlast
  obtain ⟨hc0, hev0⟩ := ht.cl_ops hg hd0
  have he0 := ((hev0 _ hlast).1 rfl).1
  have hcg : clOps (X.tr g) = dg.clOps := by
    have := (ht.cl_ops hg hσ).1
    rwa [List.take_length] at this
  have hsplit : clOps (X.tr g) = clOps ((X.tr g).take ((X.tr g).length - 1)) + 1 := by
    rw [clOps_split (es := X.tr g) hlast]
    rfl
  have hdg : dg.clOps = d0.clOps + 1 := by omega
  have hn3 : d0.clOps ≤ 3 := by have := (clOps_stage dg L g (X.tr g)).2.2.2.2.2; omega
  -- a thread of the cluster with at most `n` operations blocks
  have hblock : ∀ h, h < L.threads →
      L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) →
      clOps (X.tr h) ≤ d0.clOps → Descent.Steps L kernel Prod mem0 (Descent.Obl L)
        (rank L) X (.thread g) := fun h hh hc hle =>
    .inr ⟨X, .thread h, hmax, cluster_blocker ht hub hX hg hh hne hc hσ hdg hrel hle⟩
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
      clOps (X.tr (g / L.block * L.block + lt)) ≤ d0.clOps
  · obtain ⟨lt, hlt, -, hle⟩ := hA
    exact hblock _ (hlanelt lt hlt) (by rw [hlanecta lt hlt]) hle
  push Not at hA
  -- every lane is at its operation `n`, unrecorded
  have hcl : L.clusterOfCta (g / L.block) < L.nclusters := Step.clusterOf_lt hX.cluster.1 hcta
  obtain ⟨-, -, s, hs⟩ := hX.cluster.2.2 _ hcl
  have hgeq : g / L.block * L.block + g % L.block = g := Nat.div_add_mod' g L.block
  have hgl := Step.lane_index (L := L) (cta := g / L.block) hX.cluster.1 hcta (Nat.mod_lt g hb)
  rw [hgeq] at hgl
  have hnxg : ∀ j pc', X.get (g, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    have h4 := four_of_exit hX ht hub hg hj
    have hjl := len_of_get hj
    have hjne : j ≠ (X.tr g).length - 1 := by
      intro he
      rw [he, hlast] at hj
      cases hj
    have : (X.tr g).take j = ((X.tr g).take ((X.tr g).length - 1)).take j := by
      rw [List.take_take]
      congr 1
      simp only at hjl ⊢
      omega
    have h5 := clOps_take_le ((X.tr g).take ((X.tr g).length - 1)) j
    rw [← this] at h5
    omega
  have hglive : L.rankOfCta (g / L.block) * L.block + g % L.block ∉ s.exited :=
    lane_live hX.cluster hcl (fun j pc' => by rw [← hgl.2]; exact hnxg j pc') hs
  have hrecg : recCount L X g ≤ d0.clOps := by
    have hra : recAt L X g ((X.tr g).length - 1) = false := by
      simp only [recAt, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact .inl hnr
    have := recCount_le_take hra
    change _ ≤ clOps _ at this
    omega
  have hNg : (X.clusters (L.clusterOfCta (g / L.block))).countP
      (ownAny (L.rankOfCta (g / L.block) * L.block + g % L.block)) ≤ d0.clOps := by
    have := countP_ownAny_le_rec hX.cluster hcl hgl.1
    rw [← hgl.2] at this
    omega
  have hlane : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      X.get (g / L.block * L.block + lt, (X.tr (g / L.block * L.block + lt)).length - 1) =
        some (clEvent d0.clOps) ∧
      ¬ ClusterRecorded L X (g / L.block * L.block + lt,
        (X.tr (g / L.block * L.block + lt)).length - 1) ∧
      (∀ j pc, X.get (g / L.block * L.block + lt, j) ≠ some ⟨pc, .exit⟩) ∧
      (X.clusters (L.clusterOfCta (g / L.block))).countP
        (ownAny (L.rankOfCta (g / L.block) * L.block + lt)) = d0.clOps := by
    intro lt hlt hlw
    obtain ⟨hlk, hly⟩ := Step.lane_index (L := L) (cta := g / L.block) hX.cluster.1 hcta hlt
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
    exact cluster_lane ht hub hX (hlanelt lt hlt) hn3 (hA lt hlt hlw) hRy (by omega)
  have hw32 : g % L.block / 32 * 32 < L.block := by
    have := Nat.div_mul_le_self (g % L.block) 32
    have := Nat.mod_lt g hb
    omega
  have hlives : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      L.rankOfCta (g / L.block) * L.block + lt ∉ s.exited := by
    intro lt hlt hlw
    have hly := (Step.lane_index (L := L) (cta := g / L.block) hX.cluster.1 hcta hlt).2
    exact lane_live hX.cluster hcl (fun j pc' => by
      rw [← hly]; exact (hlane lt hlt hlw).2.2.1 j pc') hs
  have hlw := Step.liveWarp_warpLanes (X := X) (s := s) (cta := g / L.block) hX.cluster.1 hcta hb
    hw32 hlives
  have hfree : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      ¬ ClusterRecorded L X (g / L.block * L.block + lt,
        (X.tr (g / L.block * L.block + lt)).length - 1) :=
    fun lt hlt hlw => (hlane lt hlt hlw).2.1
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
          (ownWait (L.rankOfCta (g / L.block) * L.block + lt)) = d0.clOps := by
    intro lt hlt hlw
    refine ⟨run_laneSt hs (cluster_alt hX ht hcl
      (Step.lane_index (L := L) (cta := g / L.block) hX.cluster.1 hcta hlt).1), ?_⟩
    rw [← countP_ownAny]
    exact (hlane lt hlt hlw).2.2.2
  -- the released thread ranks one lower
  have hrank : rank L X (.thread g) = threadTime L X g + 1 := by simp [rank, hrel]
  have hrecord : ∀ R : ClusterBarrier.Record EvId,
      R.refs = (Step.warpLanes L X (g / L.block) (g % L.block / 32)).map Prod.snd →
      Maximal L kernel Prod mem0 (X.withClusterRecord (L.clusterOfCta (g / L.block)) R) →
      Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
    intro R hR hmaxY
    have hrelY : Step.Released L (X.withClusterRecord (L.clusterOfCta (g / L.block)) R) g :=
      Step.released_of_record hb hR hmaxY.1.cluster hlast
    refine .inr ⟨_, .thread g, hmaxY, hp, ?_⟩
    rw [rank_released hrelY, hrank]
    exact Nat.lt_succ_self _
  by_cases hpar : d0.clOps = 0 ∨ d0.clOps = 2
  · -- an arrival: every lane has waited for each earlier arrival, so the record is accepted
    have hev := clEvent_arrive hpar
    have hlastA : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
        X.get (g / L.block * L.block + lt, (X.tr (g / L.block * L.block + lt)).length - 1) =
          some ⟨(clEvent d0.clOps).pc, .cluster (.arrive true true)⟩ := by
      intro lt hlt hlw
      rw [← hev]
      exact (hlane lt hlt hlw).1
    have hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt (L.clusterOfCta (g / L.block))) {}
        (X.clusters (L.clusterOfCta (g / L.block)) ++
          [Step.warpArrival L X (g / L.block) (g % L.block / 32) true]) = .done t := by
      suffices hok : ∀ j ∈ (Step.warpLanes L X (g / L.block) (g % L.block / 32)).map Prod.fst,
          ¬ Locked j s by
        obtain ⟨t, ht⟩ := record_arrival_done (rel := true) hlw hok
        refine ⟨t, ?_⟩
        rw [ClusterBarrier.run_append, hs]
        simp only [ClusterBarrier.run, Step.warpArrival, ht]
      intro j hj
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hj
      obtain ⟨lt, hlt, hlw', rfl⟩ := Step.mem_warpLanes hpm
      obtain ⟨hst', hsum⟩ := hst lt hlt hlw'
      have heq : (X.clusters (L.clusterOfCta (g / L.block))).countP
            (ownArrival (L.rankOfCta (g / L.block) * L.block + lt)) =
          (X.clusters (L.clusterOfCta (g / L.block))).countP
            (ownWait (L.rankOfCta (g / L.block) * L.block + lt)) := by
        have := hst'.1
        have := hst'.2.1
        rcases hpar with h | h <;> omega
      rw [heq] at hst'
      exact LaneSt.not_arrived (sound_run sound_empty hs) hst'
    exact hrecord _ rfl (Step.arrival_maximal hmax hcta hlastA hfree hacc (prod_wf _))
  -- a wait: every lane arrived last in phase `(n - 1) / 2` and has not waited since
  have hpar' : d0.clOps = 1 ∨ d0.clOps = 3 := by omega
  have hev := clEvent_wait hpar'
  have hlastW : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      X.get (g / L.block * L.block + lt, (X.tr (g / L.block * L.block + lt)).length - 1) =
        some ⟨(clEvent d0.clOps).pc, .cluster (.wait true)⟩ := by
    intro lt hlt hlw
    rw [← hev]
    exact (hlane lt hlt hlw).1
  have hlaneA : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      s.lastArrival (L.rankOfCta (g / L.block) * L.block + lt) = some ((d0.clOps - 1) / 2) := by
    intro lt hlt hlw
    obtain ⟨⟨hwa, haw, hla, -⟩, hsum⟩ := hst lt hlt hlw
    have hlk := (Step.lane_index (L := L) (cta := g / L.block) hX.cluster.1 hcta hlt).1
    have hlc := run_last_count sound_empty (by simp [LastCount, weight]) hs hlk
      (hlives lt hlt hlw)
    have hwt := run_weight sound_empty hs hlk (hlives lt hlt hlw)
    have hw0 : weight (L.rankOfCta (g / L.block) * L.block + lt) ({} : State) = 0 := by
      simp [weight]
    unfold LastCount at hlc
    rw [hwt, hw0] at hlc
    rw [hlc]
    split
    · omega
    · congr 1
      omega
  by_cases hph : (d0.clOps - 1) / 2 < s.phase
  · -- the phase has completed: the record is accepted
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
    exact hrecord _ rfl (Step.wait_maximal hmax hcta hlastW hfree hacc (prod_wf _))
  -- the phase is open: a live thread of the cluster has not arrived in it
  push Not at hph
  have hsound := sound_run sound_empty hs
  have hglast := hlaneA (g % L.block) (Nat.mod_lt g hb) rfl
  have hle := hsound.2 _ _ hglast
  have hopen : s.lastArrival (L.rankOfCta (g / L.block) * L.block + g % L.block) =
      some s.phase := by
    rw [hglast]
    congr 1
    omega
  obtain ⟨h', hh'K, -, hcnt⟩ := Step.wait_open_witness hs hopen
  obtain ⟨hwa, -, -, -⟩ := run_laneSt (x := h') hs (cluster_alt hX ht hcl hh'K)
  have hR := rec_le_countP_ownAny hX.cluster hcl hh'K
  rw [countP_ownAny] at hR
  have hh : L.clusterStart (L.clusterOfCta (g / L.block)) * L.block + h' < L.threads := by
    have h1 : L.clusterOfCta (g / L.block) < 512 := by
      have := hcl
      rw [hpre.oneDimLaunch.1.2.2.2.1, hG, hCS] at this
      exact this
    have h2 : h' < 768 := by
      have := hh'K
      rw [Launch.oneDim_clusterSizeAt hpre.oneDimLaunch.1, hB, hCS] at this
      exact this
    show _ < L.grid * L.block
    rw [clusterStart_eq hpre]
    generalize L.clusterOfCta (g / L.block) = c at h1 ⊢
    rw [hG, hB]
    omega
  have hty := take_le_recCount (ClusterBlocking.of_consistent hX)
    (L.clusterStart (L.clusterOfCta (g / L.block)) * L.block + h')
  have hsy := clOps_le_init (X.tr (L.clusterStart (L.clusterOfCta (g / L.block)) * L.block + h'))
  refine hblock _ hh (clusterOf_lane hcl hh'K) ?_
  change clOps _ ≤ _ at hty
  omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
