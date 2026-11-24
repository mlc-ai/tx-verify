-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Kernels.Fp16Gemm8192.Proof.Thread.RingPolls
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderArrivals
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleActors
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCommits
public import Kernels.Fp16Gemm8192.Proof.Thread.RingCounts

public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked
public import Kernels.Fp16Gemm8192.Proof.Thread.WaitAcquire
public import Kernels.Fp16Gemm8192.Proof.Thread.WaitSpins
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerCount
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerTime
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcMulticast
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerLead
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerExit
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerClc
public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterCount
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderRetry
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaOdd
public import Kernels.Fp16Gemm8192.Proof.Thread.RankCounts
public import Kernels.Fp16Gemm8192.Proof.Thread.NoTcCp
public import Kernels.Fp16Gemm8192.Proof.Thread.NoNc
public import Kernels.Fp16Gemm8192.Proof.Thread.BaseAccess
public import Kernels.Fp16Gemm8192.Proof.Thread.ReadPoll
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTileFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ArrivePhase
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLead
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaAccPrev
public import Kernels.Fp16Gemm8192.Proof.Thread.ProgressFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterStart
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaUnelected
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaPoll
public import Kernels.Fp16Gemm8192.Proof.Thread.AccPoll
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderExact
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDrainPoll
public import Kernels.Fp16Gemm8192.Proof.Thread.ElectOnce
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderUnelected
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderFailWait
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedElectedExit
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaExact
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcPoll
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Kernels.Fp16Gemm8192.Proof.Thread.AccExit
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerInit
public import Kernels.Fp16Gemm8192.Proof.Thread.AccCommitRanks
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaExitAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaElectState
public import Kernels.Fp16Gemm8192.Proof.Thread.AckSites
public import Kernels.Fp16Gemm8192.Proof.Thread.ReaderExitCons
public import Kernels.Fp16Gemm8192.Proof.Thread.PollRead
public import Kernels.Fp16Gemm8192.Proof.Thread.AccessAddr
public import Kernels.Fp16Gemm8192.Proof.Thread.RegFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerBar
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerBars
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTcFact
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoadWords
public import Kernels.Fp16Gemm8192.Proof.Thread.AccSides
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerBulk
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerStoreFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.TcSpecs
public import Kernels.Fp16Gemm8192.Proof.Thread.UbStopRead
public import Kernels.Fp16Gemm8192.Proof.Thread.TensorBounds
public import Kernels.Fp16Gemm8192.Proof.Thread.BaseValue
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemAt
public import Kernels.Fp16Gemm8192.Proof.Thread.TcColl
public import Kernels.Fp16Gemm8192.Proof.Thread.Fire
public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.GlobalWrites
public import Kernels.Fp16Gemm8192.Proof.Thread.WarpPeers
public import Kernels.Fp16Gemm8192.Proof.Thread.TensorAligned
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerValFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaPrev
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderOrigin
public import Kernels.Fp16Gemm8192.Proof.Thread.ExitTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemAccess
public import Kernels.Fp16Gemm8192.Proof.Thread.TcSources

@[expose] public section

/-! # The thread facts of an execution

Every execution of the kernel has the per-thread facts the protocol layer uses. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

theorem prologue_no_wait {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {p : Prologue.D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inl p))) :
    ∀ m par ok acq sc, e.kind ≠ .wait m par ok acq sc := by
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  exact fires_notWait (eventTmpl_notWait (Prologue.code_notPoll p.site hc)) hfire

/-- An event of a thread at its response wait polls its CTA's response barrier. -/
theorem clc_wait_event_fact {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {d : ThreadD} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hd : d.AtClcWait) :
    ∃ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc := by
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨ok, acq, sc, rfl⟩ := clc_event hpre hinv hd hat hc hfire
  exact ⟨_, ok, acq, sc, rfl⟩

theorem threadFacts {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) : ThreadFacts L X where
  sound _ := sound hpre
  tracked := tracked hpre hX
  wait_spins _ he := wait_spins hpre hX he
  no_release _ _ _ _ he := write_no_release hpre hX he
  poll_parity hg he hσ hk hb := poll_parity hpre hX hg he hσ hk hb
  arrival_budget hg he hσ hk hb := arrival_budget hpre hX hg he hσ hk hb
  commit_budget hg he hσ hk ht hb := commit_budget hpre hX hg he hσ hk ht hb
  issue_budget hg he hσ hi hb := issue_budget hpre hX hg he hσ hi hb
  clc_budget hg he hσ hk hm hb := clc_budget hpre hX hg he hσ hk hm hb
  sync_flags hg he hσ := sync_flags hpre hX hg he hσ
  ack_fenced hg he hσ hk := by
    obtain ⟨-, j, f, hj, hf, hfe, hc⟩ := (clc_counts hpre hX hg he hσ).2 _ _ _ _ hk
    refine ⟨j, f, hj, hf, ?_, hc⟩
    unfold isFence at hfe
    split at hfe
    · assumption
    · cases hfe
  elected hg he hσ hpc hk := role_elected hpre hX hg he hσ hpc hk
  clc_query hg he hσ hk := by
    obtain ⟨j, pc, p, acq, sc, pcr, a, bs, h1, h2, hw, hr, ha, hs, hres⟩ :=
      clc_query hpre hX hg he hσ hk
    exact ⟨j, pc, p, acq, sc, pcr, a, bs, h1, h2, hw, hr, ⟨ha, hs⟩, hres⟩
  sched_issue hg he hσ hk := by
    obtain ⟨h1, h2⟩ := Scheduler.sched_issue hpre hX hg he hσ hk
    refine ⟨h1, fun j pc p acq sc hj hw => ?_⟩
    obtain ⟨pcr, src, bs, rr, hr, ha, hs, hres, hn⟩ := h2 j pc p acq sc hj hw
    exact ⟨pcr, src, bs, rr, hr, ⟨ha, hs⟩, hres, hn⟩
  consumer_exit hg he hσ hk hw := by
    obtain ⟨r, rfl⟩ := exit_role hpre hX hg he hσ hk
    have hrw := role_warp hpre hX hg _ (List.getElem?_eq_some_iff.mp he).1.le _ hσ
    cases r with
    | cons c =>
      obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hl, hw', hr, h1, h2, h3, h4⟩ :=
        consumer_exit hpre hX hg he hσ hk
      exact ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hl, hw', hr, ⟨h1, h2⟩, h3, h4⟩
    | _ => simp only [roleWarp, Prologue.warpOf] at hrw; omega
  cons_out {g k e c} hg he hσ := by
    have hrw := role_warp hpre hX hg _ (List.getElem?_eq_some_iff.mp he).1.le _ hσ
    have htid : Consumer.tidOf L g < 256 := by
      simp only [roleWarp, Prologue.warpOf] at hrw
      simp only [Consumer.tidOf]
      omega
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cons_out_facts hpre hX hg he hσ htid
    refine ⟨h1, h2, fun a sp hk => ?_, h4, h5, h6⟩
    obtain ⟨s, hs, -, -, -, hfp, hfen⟩ := h3 a sp hk
    exact ⟨s, hs, hfp, hfen⟩
  access_region hg he hσ := access_fact hpre hX he hσ
  cons_slice_stores hg hub hk hσ hs := cons_slice_stores_fact hpre hX hg hk hσ hs hub
  cons_tma_prev hg hk hσ hs := cons_tma_prev_fact hpre hX hg hk hσ hs
  cons_tma hg he hσ := cons_tma_fact hpre hX he hσ
  cons_write_len hg he hσ := cons_write_len_fact hpre hX hg he hσ
  cons_clc hg _ hσ := cons_clc hpre hX hg hσ
  cons_clc_fence hg he hσ hs := cons_clc_fence hpre hX hg he hσ hs
  ack_hold hg he hσ hk := ack_hold hpre hX hg he hσ hk
  mma_odd_quiet hg he hσ hm hodd := mma_odd_quiet hpre hX hg he hσ hm hodd
  bar_role hg he hσ hk := bar_role hpre hX he hσ hk
  bulk_role hg he hσ hk := bulk_role hpre hX he hσ hk
  cluster hg he hσ := cluster_facts hpre hX hg he hσ
  loader_retry hg hσ hs hlast := loader_retry hpre hX hg (Frame.stateAt_end ▸ hσ) hs hlast
  loader_wait hg hσ hs hlast :=
    ⟨loader_last_wait hpre hX (Frame.stateAt_end ▸ hσ) hs hlast,
      loader_wait_parity hpre hX hg (Frame.stateAt_end ▸ hσ) hs⟩
  lead_arrive_after_issue hg he hσ hl hk :=
    Scheduler.lead_arrive_after_issue hpre hX hg he hσ hl hk
  query_role {g k pc q rr} hg he := by
    obtain ⟨d, hσ⟩ := Frame.event_state (fun _ => sound hpre) hX (tracked hpre hX) he nofun
    obtain ⟨r, rfl⟩ := query_role hpre hX hg he hσ rfl
    exact ⟨r, hσ⟩
  prologue_no_wait _ he hσ := prologue_no_wait hpre hX he hσ
  role_warp hg hk hσ := role_warp hpre hX hg _ hk _ hσ
  ring_event hg he hσ := ring_event hpre hX hg he hσ
  wait_local hg he hσ hk := wait_local hpre hX hg he hσ hk
  ring_initialized hg he hσ hb hcta hcl := ring_initialized hpre hX hg he hσ hb hcta hcl
  loader_rank {g l} hg hσ := by
    have h := loader_counts hpre hg (Frame.trace (fun _ => sound hpre) hX hg)
      (k := (X.tr g).length) hσ
    rw [List.take_length] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, fun b hb => ?_⟩
    rw [hb] at h2
    exact h2
  mma_rank {g m} hg hσ := by
    have h := mma_counts hpre hg (Frame.trace (fun _ => sound hpre) hX hg)
      (k := (X.tr g).length) hσ
    rw [List.take_length] at h
    exact h
  loader_poll hg hσ hs hr ok := loader_poll hpre hg (Frame.stateAt_end ▸ hσ) hs hr ok
  mma_poll hg hσ hs hrun ok := mma_poll hpre hg (Frame.stateAt_end ▸ hσ) hs hrun ok
  mma_acc_poll hg hσ hs hrun ok := mma_acc_poll hpre hg (Frame.stateAt_end ▸ hσ) hs hrun ok
  cons_acc_poll hg hσ hs hrun ok := cons_acc_poll hpre hg (Frame.stateAt_end ▸ hσ) hs hrun ok
  clc_poll hg hσ hd hrun ok := clc_poll hpre hg (Frame.stateAt_end ▸ hσ) hd hrun ok
  sched_ack_poll hg hσ hs hrun ok := sched_ack_poll hpre hg (Frame.stateAt_end ▸ hσ) hs hrun ok
  loader_clc_count hg _hub hσ hs := loader_clc_count_fact hpre hX hg (Frame.stateAt_end ▸ hσ) hs
  mma_clc_count hg _hub hσ hs := mma_clc_count_fact hpre hX hg (Frame.stateAt_end ▸ hσ) hs
  mma_task_count hg hσ := mma_task_count_fact hpre hX hg (Frame.stateAt_end ▸ hσ)
  mma_claims_before hg hσ j pc p acq sc hj hcount :=
    mma_claims_before_fact hpre hX hg (Frame.stateAt_end ▸ hσ) j pc p acq sc hj hcount
  sched_ack_count hg _hub hσ hs := Scheduler.sched_ack_count hpre hX hg (Frame.stateAt_end ▸ hσ) hs
  sched_arrive_clc hg hσ hs := Scheduler.sched_arrive hpre hX hg (Frame.stateAt_end ▸ hσ) hs
  sched_exit hg hσ hs hk := by
    obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, h1, h2, h3, h4, h5, h6, h7⟩ :=
      Scheduler.sched_exit hpre hX hg (Frame.stateAt_end ▸ hσ) hs hk
    exact ⟨j, pc, p, acq, sc, pcr, src, bs, rr, h1, h2, h3, ⟨h4, h5⟩, h6, h7⟩
  sched_fail_wait hg hσ hs j pc p acq sc pcr src bs rr h1 h2 h3 h4 := by
    obtain ⟨ha, hz⟩ := h3
    exact Scheduler.sched_fail_wait hpre hX hg (Frame.stateAt_end ▸ hσ) hs j pc p acq sc pcr src bs
      rr
      h1 h2 ha hz h4
  sched_unelected hg hw hnoel := sched_unelected_thm hpre hX hg hw hnoel
  sched_arrivals hg hσ := Scheduler.sched_arrivals hpre hX hg (Frame.stateAt_end ▸ hσ)
  sched_time hg hσ hx hn := Scheduler.sched_time_le hpre hX hg (Frame.stateAt_end ▸ hσ) hx hn
  clc_multicast h ki pc sp tg hget c' hc' hcl :=
    clc_multicast_thm hpre hX h ki pc sp tg hget c' hc' hcl
  mma_fail_wait hg hσ hs j pc p acq sc pcr src bs rr h1 h2 h3 h4 := by
    obtain ⟨ha, hz⟩ := h3
    exact Mma.fail_wait hpre hX hg (Frame.stateAt_end ▸ hσ) hs j pc p acq sc pcr src bs rr h1 h2 ha
      hz h4
  cons_fail_wait hg hσ hs j pc p acq sc pcr src bs rr h1 h2 h3 h4 := by
    obtain ⟨ha, hz⟩ := h3
    exact Consumer.fail_wait hpre hX hg (Frame.stateAt_end ▸ hσ) hs j pc p acq sc pcr src bs rr h1
      h2 ha
      hz h4
  poll_read hg he hj := by
    obtain ⟨pcr, a, bs, h1, h2, h3⟩ := poll_read_thm hpre hX hg he hj
    exact ⟨pcr, a, bs, h1, h2, h3⟩
  loader_fail_wait hg hσ hs j pc p acq sc pcr src bs rr h1 h2 h3 h4 := by
    exact loader_fail_wait_thm hpre hX hg (Frame.stateAt_end ▸ hσ) hs j pc p acq sc pcr src bs rr h1
      h2
      h3 h4
  elect_once hg h h' := elect_once_thm hpre hX hg h h'
  sched_elected_exit hg hel hσ hx := sched_elected_exit_thm hpre hX hg hel hσ hx
  cons_tiles hg _hub hσ := cons_tiles hpre hX hg hσ
  cons_acc_state := by
    intro g k e p ok acq sc hg hw he hk
    obtain ⟨d, hσ⟩ := Frame.event_state (fun _ => sound hpre) hX (tracked hpre hX) he
      (by rintro pc f rfl; cases hk)
    obtain ⟨⟨⟨c, hc⟩, -⟩, -⟩ := (ring_event hpre hX hg he hσ).wait
      ⟨.acc, g % L.block / 32 / 4, true⟩ (g / L.block) p ok acq sc hk
      (by simp only [Bar.Valid, Ring.slots]; omega)
    exact ⟨c, hc ▸ hσ⟩
  cons_acc_init hg hσ hs := cons_acc_init_thm hpre hX hg hσ hs
  acc_commit_ranks rank hg he hσ hk hm hr := acc_commit_ranks_fact hpre hX hg rank he hσ hk hm hr
  mma_exit_acc hg hw hlast := mma_exit_acc_count hpre hX hg hw hlast
  mma_elect_state hg hl hw hel := mma_elect_state hpre hX hg hl hw hel
  loader_tasks hg hσ hs := loader_tasks_fact hpre hX hg (Frame.stateAt_end ▸ hσ) hs
  loader_claims_before hg hσ := loader_claims_before_fact hpre hX hg (Frame.stateAt_end ▸ hσ)
  loader_drain_poll hg hσ hs hr ok := loader_drain_poll hpre hg (Frame.stateAt_end ▸ hσ) hs hr ok
  mma_leader hg hl hw hj := mma_leader_thm hpre hX hg hl hw hj
  mma_unelected hg h1 h2 h3 := mma_unelected_thm hpre hX hg h1 h2 h3
  exited_state hg hl := exited_state_fact hpre hX hg hl
  cluster_started hg he hσ hh hcl := cluster_started_thm hpre hX hg he hσ hh hcl
  commit_ranks s rank hg he hσ hk hm hr := commit_ranks_fact hpre hX hg s rank he hσ hk hm hr
  no_tc_cp hg he hσ := no_tc_cp hpre hX hg he hσ
  no_tc_st hg he hσ := no_tc_st hpre hX hg he hσ
  no_nc _ he hσ := no_nc hpre hX he hσ
  no_tensor_prefetch hg he hσ := no_tensor_prefetch hpre hX hg he hσ
  base_write hg he hσ hk hnc := base_write_fact hpre hX hg he hσ hk hnc
  read_role hg he hσ hk := read_role_fact hpre hX he hσ hk
  read_poll hg he hσ hk := read_poll_fact hpre hX hg he hσ hk
  store_tile hg he hσ := store_tile_fact hpre hX hg he hσ
  arrive_phase hg he hσ hk := arrive_phase_fact hpre hX he hσ hk
  loader_site_count {g l} hg hσ := by
    have h := loader_counts hpre hg (Frame.trace (fun _ => sound hpre) hX hg)
      (k := (X.tr g).length) hσ
    rw [List.take_length] at h
    exact h.2
  mma_lead _ hσ := mma_lead hσ
  ring_init_exists hg h8 hk hσ hb hcta hcl := ring_init_exists_thm hpre hX hg h8 hk hσ hb hcta hcl
  loader_exact hg hub hσ hd := loader_exact_fact hpre hX hg hub hσ hd
  loader_exit_exact hg hub hσ hd hpos := loader_exit_exact_fact hpre hX hg hub hσ hd hpos
  loader_exit_tasks hg hσ hd hpos := loader_exit_tasks_fact hpre hX hg hσ hd hpos
  loader_exit_claim hg hσ hd hpos := loader_exit_claim_fact hpre hX hg hσ hd hpos
  loader_q8 hg hσ := loader_q8_fact hpre hX hg hσ
  loader_elected_exit hg hw hel hσ hd := loader_elected_exit_fact hpre hX hg hw hel hσ hd
  loader_unelected hg hw hnoel := loader_unelected_thm hpre hX hg hw hnoel
  loader_load_tasks hg hσ hs := loader_load_tasks_fact hpre hX hg hσ hs
  mma_exit_tasks hg hσ hs := mma_exit_tasks_fact hpre hX hg hσ hs
  mma_exit_reads hg hk hσ hs := mma_exit_reads_fact hpre hX hg hk hσ hs
  loader_exit_drain hg hw hel hlast := loader_exit_drain_fact hpre hX hg hw hel hlast
  cons_exit_tiles hg hw hlast := cons_exit_tiles_fact hpre hX hg hw hlast
  cons_tmas hg hσ := cons_tmas_fact hpre hX hg hσ
  cons_exit_tmas hg hw hf hub hlast := cons_exit_tmas_fact hpre hX hg hw hf hub hlast
  mma_full_count hg hub hσ hs := mma_full_count_fact hpre hX hg hub hσ hs
  mma_acc_count hg hub hσ := mma_acc_count_fact hpre hX hg hub hσ
  ack_exact hg hsel hk hσ := ack_exact_fact hpre hX hg hsel hk hσ
  cl_phase hg hσ := cl_phase_of hpre hX hg hσ
  cl_ops hg hσ := clOps_facts hpre hX hg hσ
  cluster_fire hg hσ hat hr := cluster_fire hpre hg (Frame.stateAt_end ▸ hσ) hat hr
  fire hg hσ hr := fire_fact hpre hg hσ hr
  bar_fire hg hσ hs hr := cons_bar_fire hpre hg (Frame.stateAt_end ▸ hσ) hs hr
  bulk_fire hg hσ hs hr := cons_bulk_fire hpre hg (Frame.stateAt_end ▸ hσ) hs hr
  cons_exit_read hg hσ hx := cons_exit_read hpre hX hg hσ hx
  cons_acc_count hg hσ := Consumer.cons_acc_count hpre hX hg hσ
  sched_exit_query hg hσ := (Scheduler.run_of hpre hX hg hσ).exitQ
  loader_exit_query hg hσ :=
    (LoaderTasks.runT hpre hg (Frame.trace (fun _ => sound hpre) hX hg) _ _ hσ).2.2.1
  sched_ack_wait_site hg he hσ hk := sched_ack_site_of_wait hpre hX he hσ hk
  sched_ack_claims hg hσ hs := sched_claims_of hpre hX hg hσ hs
  exit_event_state hg he := exit_event_state' hpre hX hg he
  loader_count_ok hg hσ := loader_count_ok_of hpre hX hg hσ
  reg_ops hg hσ := reg_ops_fact hpre hX hg hσ
  reg_event hg he := reg_event_fact hpre hX hg he
  reg_stage hg hσ := reg_stage_fact hpre hX hg hσ
  reg_fire hg hσ hat hr := reg_fire_fact hpre hg (Frame.stateAt_end ▸ hσ) hat hr
  reg_prev hg hσ hat := reg_prev_fact hpre hX hg hσ hat
  cons_bars hg hσ := cons_bars_fact hpre hX hg hσ
  cons_claims hg hσ j pc p acq sc pcr src bs rr h1 h2 h3 h4 h5 := by
    obtain ⟨ha, hz⟩ := h3
    exact cons_claims_fact hpre hX hg hσ j pc p acq sc pcr src bs rr h1 h2 ha hz h4 h5
  cons_after_bar hg he hk hσ0 hσ1 := cons_after_bar_fact hpre hX hg he hk hσ0 hσ1
  cons_tc hg hσ := cons_tc_fact hpre hX hg hσ
  cons_after_tc hg he hd hσ0 hσ1 := cons_after_tc_fact hpre hX he hd hσ0 hσ1
  cons_wait_fire hg hσ hs hr := cons_wait_fire_fact hpre hg hσ hs hr
  cons_data_next hg he hd hσ hw := data_live hpre hX hg he hσ hd hw
  mma_acc_batch hg he hσ hk := mma_acc_batch_fact hpre hX hg he hσ hk
  cons_load hg he hσ := cons_load_fact hpre hX hg he hσ
  ld_shape hg he := ld_shape_fact hpre hX hg he
  ld_len hg he := ld_len_fact hpre hX hg he
  acc_commit_mma hg he hσ hk hm := acc_commit_mma_fact hpre hX hg he hσ hk hm
  tmem_ops hg hnu hσ := (tmem_ops_fact hpre hX hg hnu hσ).1
  tmem_event hg hnu he := tmem_event_fact hpre hX hg hnu he
  tmem_stage hg hnu h0 hσ := tmem_stage_fact hpre hX hg hnu h0 hσ
  tmem_exit hg hnu h0 he := tmem_exit_fact hpre hX hg hnu h0 he
  tmem_fire hg hσ hat hr := tmem_fire_fact hpre hg hσ hat hr
  coll_fire hg hσ hs hr := coll_fire_thm hpre hg (Frame.stateAt_end ▸ hσ) hs hr
  coll_none hg hσ hs he := coll_none_fact hpre hX hg hσ hs _ _ he
  coll_before hg hnu hσ hs := coll_before_fact hpre hX hg hnu hσ hs
  coll_lane hg hσ hs hw hnu := coll_lane_fact hpre hX hg hσ hs hw hnu
  tensor_issue hg he hσ hk := tensor_issue_fact hpre hX hg he hσ hk
  mma_issue hg he hσ hk := mma_issue_fact hpre hX hg he hσ hk
  mma_batch hg he hσ hk hm := mma_batch_fact hpre hX hg he hσ hk hm
  write_shared hg he hσ hk := write_shared_fact hpre hX he hσ hk
  store_map hg he hσ hk := store_map_fact hpre hX he hσ hk
  mma_dst hg he hσ hk := mma_dst_fact hpre hX hg he hσ hk
  mma_acc_prev hg he hσ hk := mma_acc_prev_fact hpre hX hg he hσ hk
  commit_spec hg he hσ hk := commit_spec_fact hpre hX hg he hσ hk
  ub_site hg he := ub_site_fact hpre hX hg he
  stop_read hg he hk hσ hn := stop_read_fact hpre hX hg he hk hσ hn
  tensor_bounds hg he hσ hk := tensor_bounds_fact hpre hX hg he hσ hk
  store_bounds hg he hσ hk := store_bounds_fact hpre hX hg he hσ hk
  base_written hg he hσ := base_written_fact hpre hX hg he hσ
  tmem_event_at hg he := tmem_event_at hpre hX hg he
  tmem_exit_at hg h0 he := tmem_exit_at hpre hX hg h0 he
  dealloc_base hg he := dealloc_base_fact hpre hX hg he
  tc_coll hg he hc := tc_coll_fact hpre hX hg he hc
  tc_exit hg hw he := tc_exit_fact hpre hX hg hw he
  cons_bar_phase hg hσ := cons_bar_phase_fact hpre hX hg hσ
  tensor_aligned hg he hσ hk := tensor_aligned_fact hpre hX hg he hσ hk
  store_box hg he hσ hk := store_box_fact hpre hX hg he hσ hk
  cons_exit_drain hg he hσ hw := by
    obtain ⟨r, rfl⟩ := exit_role hpre hX hg he hσ rfl
    have hrw := role_warp hpre hX hg _ (List.getElem?_eq_some_iff.mp he).1.le _ hσ
    cases r with
    | cons c => exact cons_exit_drain_fact hpre hX hg he hσ
    | _ => simp only [roleWarp, Prologue.warpOf] at hrw; omega
  alloc_before he hr hT hcl := alloc_before_fact hpre hX he hr hT hcl
  dealloc_waited hg he := dealloc_waited_fact hpre hX hg he
  data_loop hg he hd := data_loop_fact hpre hX hg he hd
  mma_tile hg he hσ hk := mma_tile_fact hpre hX hg he hσ hk
  cons_exit_stage hg hk hσ hx := cons_exit_stage_fact hpre hX hg hk hσ hx
  cons_slice_values hg hub hk hσ hs := cons_slice_values_fact hpre hX hg hk hσ hs hub
  cons_tma_epoch hg hσ hs := cons_tma_epoch_fact hpre hX hg hσ hs
  mma_block hg he hσ hs := mma_block_fact hpre hX hg he hσ hs
  mma_prev hg hk hσ hs ha := mma_prev_fact hpre hX hg hk hσ hs ha
  acc_commit_last hg hjc hσ hs := acc_commit_last_fact hpre hX hg hjc hσ hs
  loader_block hg he hσ hs := by
    have h := loader_block_fact hpre hX hg he hσ hs
    simpa only [Loader.loadRow] using h
  clc_wait_event _ he hσ hd := clc_wait_event_fact hpre hX he hσ hd

end
end PTX.Kernels.Fp16Gemm8192.Proof
