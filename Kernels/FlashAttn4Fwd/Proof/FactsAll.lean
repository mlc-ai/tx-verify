-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.FactsAllCross
public import Kernels.FlashAttn4Fwd.Proof.FactsAllPlaced
public import Kernels.FlashAttn4Fwd.Proof.FactsAllBar2
public import Kernels.FlashAttn4Fwd.Proof.SafeGlue3
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsBar2
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsProgressAsync
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCluster
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrRescale
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderCopy
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderRing
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCommitCount
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCover
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaDesc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaElect
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaRead
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaRingCover
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaSteps
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaUses
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOnlyCopies
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsShfl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftLow
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftP2
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftPack
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftScore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftSt
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreIssued
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreOut
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreSpec
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreTma
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemAlloc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemLife
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMachine
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAccess
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid2Access
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid2Polls
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid2Reg
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOAcc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOAccSt
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsGen
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftStoreF32

@[expose] public section

/-! # The thread layer's interface structures (I): the safety inputs

Each structure of the thread layer's interface that `safe_goal` takes (`ThreadInputs`), for
every consistent execution, from its field theorems (`Thread/Facts*.lean`). A field proved
role by role is assembled by cases on the thread's warp. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace FactsAll

theorem writes (hX : Consistent L kernel asms mem0 X) : WriteFacts L X where
  global := WriteFacts_global hX
  started := WriteFacts_started hX

/-- A successful wait is in a canonical spin. -/
theorem spin (hX : Consistent L kernel asms mem0 X) :
    ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit :=
  fun _ _ _ _ _ _ he => kernel_spins hX he

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

theorem cluster : ClusterFacts L X where
  arrive := ClusterFacts_arrive hpre hX (tracked hpre hX)
  wait := ClusterFacts_wait hpre hX (tracked hpre hX)
  cl_only := ClusterFacts_cl_only hpre hX (tracked hpre hX)
  post := ClusterFacts_post hpre hX (tracked hpre hX)
  shfl0 := ClusterFacts_shfl0 hpre hX (tracked hpre hX)
  fence := ClusterFacts_fence hpre hX (tracked hpre hX)
  init_site := ClusterFacts_init_site hpre hX (tracked hpre hX)

theorem ringCopies : RingCopies P L X where
  copy := RingCopies_copy hpre hX (tracked hpre hX)

theorem score : ScoreFacts L X where
  no_cp := ScoreFacts_no_cp hX
  no_shift := ScoreFacts_no_shift hX
  mma_cells := ScoreFacts_mma_cells hpre hX (tracked hpre hX)
  tc_one := ScoreFacts_tc_one hpre hX (tracked hpre hX)
  mma_acc := ScoreFacts_mma_acc' hpre hX (tracked hpre hX)
  qk_polls := ScoreFacts_qk_polls hpre hX (tracked hpre hX)
  pv_polls := ScoreFacts_pv_polls hpre hX (tracked hpre hX)
  pv_qk := ScoreFacts_pv_qk hpre hX (tracked hpre hX)
  tc_role := ScoreFacts_tc_role hpre hX (tracked hpre hX)
  tc_shape := ScoreFacts_tc_shape hpre hX (tracked hpre hX)
  soft_ld := ScoreFacts_soft_ld hpre hX (tracked hpre hX)
  soft_st := ScoreFacts_soft_st hpre hX (tracked hpre hX)
  soft_ld_st := ScoreFacts_soft_ld_st hpre hX (tracked hpre hX)
  soft_st_one := ScoreFacts_soft_st_one hpre hX (tracked hpre hX)

theorem route : RouteFacts L X where
  soft_p := RouteFacts_soft_p hpre hX (tracked hpre hX)
  soft_gen := RouteFacts_soft_gen hpre hX (tracked hpre hX)
  corr_p := RouteFacts_corr_p hpre hX (tracked hpre hX)
  corr_ld := RouteFacts_corr_ld hpre hX (tracked hpre hX)
  mma_commit := RouteFacts_mma_commit hpre hX (tracked hpre hX)
  mma_elect := RouteFacts_mma_elect hpre hX (tracked hpre hX)
  mma_pv := RouteFacts_mma_pv hpre hX (tracked hpre hX)

theorem tcmma : TcMmaThreadFacts L X where
  mma_desc := TcMmaThreadFacts_mma_desc hpre hX (tracked hpre hX)
  qk_acc := TcMmaThreadFacts_qk_acc hpre hX (tracked hpre hX)
  pv_acc := TcMmaThreadFacts_pv_acc hpre hX (tracked hpre hX)
  soft_f16 := TcMmaThreadFacts_soft_f16 hpre hX (tracked hpre hX)
  corr_f32 := TcMmaThreadFacts_corr_f32 hpre hX (tracked hpre hX)
  soft_low := TcMmaThreadFacts_soft_low hpre hX (tracked hpre hX)
  soft_high := TcMmaThreadFacts_soft_high hpre hX (tracked hpre hX)
  mma_collector := TcMmaThreadFacts_mma_collector hpre hX (tracked hpre hX)

theorem store : StoreFacts P L X where
  spec := StoreFacts_spec hpre hX (tracked hpre hX)
  issued := StoreFacts_issued hpre hX (tracked hpre hX)

theorem thread : ThreadFacts L X where
  toPrologueFacts := prologueFacts hpre hX
  tracked := tracked hpre hX
  init_site := ThreadFacts_init_site hpre hX (tracked hpre hX)
  cluster_ops := ThreadFacts_cluster_ops hpre hX (tracked hpre hX)

/-- Every MMA operand read is in a ring region (`mmaReadsRings`). -/
theorem mmaReads : MmaReadsRings L X :=
  SmemElements.mmaReadsRings hpre (score hpre hX) (tcmma hpre hX)
    (mmaSmemFacts hpre hX (tracked hpre hX))

theorem older : OlderFacts P L X where
  access_shared := OlderFacts_access_shared hpre hX (tracked hpre hX)
  access_low := OlderFacts_access_low hpre hX (tracked hpre hX) (Cross.lowAccessLow hpre hX)
  base_write := OlderFacts_base_write hpre hX (tracked hpre hX) (Cross.baseFree hpre hX)
    (Cross.MmaBaseWrite_mma hpre hX (tracked hpre hX))
  base_written := OlderFacts_base_written hpre hX (tracked hpre hX)
  base_read := OlderFacts_base_read hpre hX (tracked hpre hX) (Cross.baseFree hpre hX)
    (Cross.MmaBaseRead_mma hpre hX (tracked hpre hX))
  soft_stats_exit := OlderFacts_soft_stats_exit hpre hX (tracked hpre hX)
  corr_stats_sync := OlderFacts_corr_stats_sync hpre hX (tracked hpre hX)

theorem tmem : TmemFacts L X where
  event := TmemFacts_event hpre hX (tracked hpre hX)
  exit := TmemFacts_exit hpre hX (tracked hpre hX)
  dealloc_base := TmemFacts_dealloc_base hpre hX (tracked hpre hX)
  hs_arrive := by
    intro g k pc tx c cta m rel sc hg he hm
    by_cases h12 : warpOf L g = 12
    · exact TmemFacts_hs_arrive_mma hpre hX (tracked hpre hX) hg h12 he hm
    · exact TmemFacts_hs_arrive_other hpre hX (tracked hpre hX) hg h12 he hm
  hs_wait := by
    intro g k pc p cta m ok acq sc hg he hm
    by_cases h12 : warpOf L g = 12
    · exact TmemFacts_hs_wait_mma hpre hX (tracked hpre hX) hg h12 he hm
    · exact TmemFacts_hs_wait_other hpre hX (tracked hpre hX) hg h12 he hm
  hs_tensor := TmemFacts_hs_tensor hpre hX (tracked hpre hX)
  hs_commit := TmemFacts_hs_commit hpre hX (tracked hpre hX)
  no_bulk := TmemFacts_no_bulk hX
  no_arriveOn := TmemFacts_no_arriveOn hX
  no_prefetch := TmemFacts_no_prefetch hX
  no_rmw := TmemFacts_no_rmw hX
  no_clc := TmemFacts_no_clc hX
  no_inval := TmemFacts_no_inval hX

theorem rings : RingFacts L X where
  poll := by
    intro g k pc p c b ok acq sc hg he hb
    by_cases h12 : warpOf L g = 12
    · exact RingFacts_poll_mma hpre hX (tracked hpre hX) hg h12 he hb
    by_cases h14 : warpOf L g = 14
    · exact RingFacts_poll_loader hpre hX (tracked hpre hX) hg h14 he hb
    · exact RingFacts_poll_other hpre hX (tracked hpre hX) hg h12 h14 he hb
  spins := RingFacts_spins hX
  arrive := by
    intro g k pc tx cnt c b rel sc hg he hb
    by_cases h14 : warpOf L g = 14
    · exact RingFacts_arrive_loader hpre hX (tracked hpre hX) hg h14 he hb
    · exact RingFacts_arrive_other hpre hX (tracked hpre hX) hg h14 he hb
  issue := RingFacts_issue hpre hX (tracked hpre hX)
  issue_use := RingFacts_issue_use hpre hX (tracked hpre hX)
  commit := RingFacts_commit hpre hX (tracked hpre hX)
  write := RingFacts_write hpre hX (tracked hpre hX)
  only_copies := RingFacts_only_copies hpre hX (tracked hpre hX) (Cross.lowAccessLow hpre hX)
  read := RingFacts_read hpre hX (tracked hpre hX)
  cover := RingFacts_cover hpre hX (tracked hpre hX)
  drain := RingFacts_drain hpre hX (tracked hpre hX)
  init := RingFacts_init hpre hX (tracked hpre hX)
  init_done := RingFacts_init_done hpre hX (tracked hpre hX)

theorem async : AsyncFacts P L X where
  mbar_pair := AsyncFacts_mbar_pair hpre hX (tracked hpre hX) (Cross.syncNamed hpre hX)
    (Cross.commitTargets hpre hX) (Cross.commitCluster hpre hX)
  copy_ring := AsyncFacts_copy_ring hpre hX (tracked hpre hX)
  access_own := AsyncFacts_access_own hpre hX (tracked hpre hX)
  mma_pair := AsyncFacts_mma_pair hpre hX (tracked hpre hX)
  store_base := AsyncFacts_store_base hX
  copy_started := AsyncFacts_copy_started hpre hX (tracked hpre hX)
  store_bounds := AsyncFacts_store_bounds hpre hX (tracked hpre hX)
  no_prefetch := AsyncFacts_no_prefetch hX

theorem stats : StatsFacts L X where
  bar_form := by
    intro g i pc id cnt m hg he
    by_cases h8 : warpOf L g < 8
    · exact Facts.Soft.bar_form hpre hX (tracked hpre hX) h8 he
    by_cases h12 : warpOf L g < 12
    · exact Facts.Corr.bar_form hpre hX (tracked hpre hX) (by omega) h12 he
    · exact StatsFacts_bar_form_high hpre hX (tracked hpre hX) hg (by omega) he
  bar_warp := StatsFacts_bar_warp hpre hX (tracked hpre hX) (Cross.barAgree hpre hX)
  soft_credit := StatsFacts_soft_credit hpre hX (tracked hpre hX)
  corr_credit := StatsFacts_corr_credit hpre hX (tracked hpre hX)
  credit_arrive := by
    intro g i pc tx cnt c st rel sc hg hst he
    by_cases hc : 8 ≤ warpOf L g ∧ warpOf L g < 12
    · exact Facts.Corr.credit_arrive hpre hX (tracked hpre hX) hc.1 hc.2 hst he
    · exact StatsFacts_credit_arrive_other hpre hX (tracked hpre hX) hg hc hst he
  credit_poll := StatsFacts_credit_poll hpre hX (tracked hpre hX)
  credit_tensor := StatsFacts_credit_tensor hpre hX (tracked hpre hX)
  credit_commit := StatsFacts_credit_commit hpre hX (tracked hpre hX)
  stats_access := by
    intro g i a w l hg ha hc hin
    by_cases h8 : warpOf L g < 8
    · exact Facts.Soft.stats_access hpre hX (tracked hpre hX) h8 ha hc hin
    by_cases h12 : warpOf L g < 12
    · exact Facts.Corr.stats_access hpre hX (tracked hpre hX) (by omega) h12 ha hc hin
    · exact StatsFacts_stats_access_high hpre hX (tracked hpre hX) hg (by omega) ha hc hin

/-- The correction warps' statistics barriers with their senders (`Cross.StatsGroup`, from
`Stats.shape` and `Stats.sources`). -/
theorem statsGroup : StatsGroup L X := fun k hk =>
  ⟨Stats.pair 0 k, Stats.shape hpre (by decide) hk, Stats.sources (stats hpre hX) hk,
    by simp [Stats.pair]⟩

theorem output : OutputFacts L X where
  staging_access := by
    intro g i a w l hg ha hc hin
    by_cases hw : 8 ≤ warpOf L g ∧ warpOf L g < 12
    · exact Facts.Corr.staging_access hpre hX (tracked hpre hX) hw.1 hw.2 ha hc hin
    · exact OutputFacts_staging_access_other hpre hX (tracked hpre hX) hg hw ha hc hin
  store_tma := OutputFacts_store_tma hpre hX (tracked hpre hX)
  staged_arrive := by
    intro g i pc tx cnt c st rel sc hg hst he
    by_cases hw : 8 ≤ warpOf L g ∧ warpOf L g < 12
    · exact Facts.Corr.staged_arrive hpre hX (tracked hpre hX) hw.1 hw.2 hst he
    · exact OutputFacts_staged_arrive_other hpre hX (tracked hpre hX) hg hw hst he
  staged_poll := OutputFacts_staged_poll hpre hX (tracked hpre hX)
  free_arrive := OutputFacts_free_arrive hpre hX (tracked hpre hX)
  free_poll := by
    intro g i pc p c st ok acq sc hg hst he
    by_cases hw : 8 ≤ warpOf L g ∧ warpOf L g < 12
    · exact Facts.Corr.free_poll hpre hX (tracked hpre hX) hw.1 hw.2 hst he
    · exact OutputFacts_free_poll_other hpre hX (tracked hpre hX) hg hw hst he
  stage_tensor := OutputFacts_stage_tensor hpre hX (tracked hpre hX)
  stage_commit := OutputFacts_stage_commit hpre hX (tracked hpre hX)
  corr_cover := OutputFacts_corr_cover hpre hX (tracked hpre hX)

theorem pready : PReadyFacts L X where
  p_arrive := by
    intro g i pc tx cnt c st rel sc hg hst he
    by_cases h8 : warpOf L g < 8
    · exact Facts.Soft.p_arrive hpre hX (tracked hpre hX) h8 hst he
    by_cases h12 : warpOf L g < 12
    · exact Facts.Corr.p_arrive hpre hX (tracked hpre hX) (by omega) h12 hst he
    · exact PReadyFacts_p_arrive_other hpre hX (tracked hpre hX) hg (by omega) hst he
  p_poll := by
    intro g i pc p c st ok acq sc hg hst he
    by_cases h12 : warpOf L g = 12
    · exact PReadyFacts_p_poll_mma hpre hX (tracked hpre hX) hg h12 hst he
    · exact PReadyFacts_p_poll_other hpre hX (tracked hpre hX) hg h12 hst he
  p_tensor := PReadyFacts_p_tensor hpre hX (tracked hpre hX)
  p_commit := PReadyFacts_p_commit hpre hX (tracked hpre hX)

theorem sfull : SFullFacts L X where
  s_arrive := SFullFacts_s_arrive hpre hX (tracked hpre hX)
  s_tensor := SFullFacts_s_tensor hpre hX (tracked hpre hX)
  s_poll := SFullFacts_s_poll hpre hX (tracked hpre hX)
  s_commit := SFullFacts_s_commit hpre hX (tracked hpre hX)

theorem ofull : OFullFacts L X where
  o_arrive := OFullFacts_o_arrive hpre hX (tracked hpre hX)
  o_tensor := OFullFacts_o_tensor hpre hX (tracked hpre hX)
  o_poll := by
    intro g i pc p c st ok acq sc hg hst he
    by_cases hw : 8 ≤ warpOf L g ∧ warpOf L g < 12
    · exact Facts.Corr.o_poll hpre hX (tracked hpre hX) hw.1 hw.2 hst he
    · exact OFullFacts_o_poll_other hpre hX (tracked hpre hX) hg hw hst he
  o_commit := OFullFacts_o_commit hpre hX (tracked hpre hX)

theorem p2 : P2Facts L X where
  p2_arrive := P2Facts_p2_arrive hpre hX (tracked hpre hX)
  p2_poll := by
    intro g i pc p c st ok acq sc hg hst he
    by_cases h12 : warpOf L g = 12
    · exact P2Facts_p2_poll_mma hpre hX (tracked hpre hX) hg h12 hst he
    · exact P2Facts_p2_poll_other hpre hX (tracked hpre hX) hg h12 hst he
  p2_tensor := P2Facts_p2_tensor hpre hX (tracked hpre hX)
  p2_commit := P2Facts_p2_commit hpre hX (tracked hpre hX)
  soft_warpBar := P2Facts_soft_warpBar hpre hX (tracked hpre hX)

theorem oacc : OAccFacts L X where
  corr_ld := OAccFacts_corr_ld hpre hX (tracked hpre hX)
  corr_st := OAccFacts_corr_st hpre hX (tracked hpre hX)
  corr_ld_st := OAccFacts_corr_ld_st hpre hX (tracked hpre hX)
  corr_st_one := OAccFacts_corr_st_one hpre hX (tracked hpre hX)

theorem floats : FloatFacts L X where
  mma_kind := FloatFacts_mma_kind hpre hX (tracked hpre hX)
  corr_rd := FloatFacts_corr_rd hpre hX (tracked hpre hX)
  soft_store_f32 := FloatFacts_soft_store_f32 hpre hX (tracked hpre hX)
  soft_store_one := FloatFacts_soft_store_one hpre hX (tracked hpre hX)
  soft_arrive_store := FloatFacts_soft_arrive_store hpre hX (tracked hpre hX)
  shfl_form := FloatFacts_shfl_form hpre hX (tracked hpre hX)
  shfl_uniform := FloatFacts_shfl_uniform hpre hX (tracked hpre hX)
  shfl_live := FloatFacts_shfl_live hpre hX (tracked hpre hX)

theorem tmemLife : TmemLifeFacts L X where
  bar2_warp := TmemLifeFacts_bar2_warp hpre hX (tracked hpre hX)
  bar2_alloc := TmemLifeFacts_bar2_alloc hpre hX (tracked hpre hX)
  exit_bar2 := TmemLifeFacts_exit_bar2 hpre hX (tracked hpre hX)
    (Cross.MmaExitBar2_mma hpre hX (tracked hpre hX))
  tc_sync := TmemLifeFacts_tc_sync hpre hX (tracked hpre hX)
  mma_sync := TmemLifeFacts_mma_sync hpre hX (tracked hpre hX)
  wait_bar2 := TmemLifeFacts_wait_bar2 hpre hX (tracked hpre hX)
  corr_items := TmemLifeFacts_corr_items hpre hX (tracked hpre hX)
  mma_item := TmemLifeFacts_mma_item hpre hX (tracked hpre hX)
  dealloc_sync := TmemLifeFacts_dealloc_sync hpre hX (tracked hpre hX)
  dealloc_wait := TmemLifeFacts_dealloc_wait hpre hX (tracked hpre hX)
  hs_release := by
    intro g y pc tx c cta rel sc hg he
    by_cases h12 : warpOf L g = 12
    · exact TmemLifeFacts_hs_release_mma hpre hX (tracked hpre hX) hg h12 he
    · exact TmemLifeFacts_hs_release_other hpre hX (tracked hpre hX) hg h12 he

theorem exit : ExitFacts P L X where
  bar2_warp := ExitFacts_bar2_warp hpre hX (tracked hpre hX)
  bar2_exit := ExitFacts_bar2_exit hpre hX (tracked hpre hX)
    (Cross.MmaExitBar2_mma hpre hX (tracked hpre hX))
  wait_own := ExitFacts_wait_own hpre hX (tracked hpre hX)
  peer_bar2 := ExitFacts_peer_bar2 hpre hX (tracked hpre hX) (Cross.peerBar2High hpre hX)
  hs_arrive := by
    intro g k pc tx cnt cta rel sc hg he
    by_cases h12 : warpOf L g = 12
    · exact ExitFacts_hs_arrive_mma hpre hX (tracked hpre hX) hg h12 he
    · exact ExitFacts_hs_arrive_other hpre hX (tracked hpre hX) hg h12 he
  hs_wait := by
    intro g k pc p cta acq sc hg he
    by_cases h12 : warpOf L g = 12
    · exact ExitFacts_hs_wait_mma hpre hX (tracked hpre hX) hg h12 he
    · exact ExitFacts_hs_wait_other hpre hX (tracked hpre hX) hg h12 he
  mma_exit := ExitFacts_mma_exit hpre hX (tracked hpre hX)
  mma_full := ExitFacts_mma_full hpre hX (tracked hpre hX)
  soft_exit := ExitFacts_soft_exit hpre hX (tracked hpre hX)
  corr_exit := ExitFacts_corr_exit hpre hX (tracked hpre hX)
  mma_ofull := ExitFacts_mma_ofull hpre hX (tracked hpre hX)
  sfull_commit := ExitFacts_sfull_commit hpre hX (tracked hpre hX)
  ofull_commit := ExitFacts_ofull_commit hpre hX (tracked hpre hX)
  commit_target := ExitFacts_commit_target hpre hX (tracked hpre hX)
  loader_q := ExitFacts_loader_q hpre hX (tracked hpre hX)
  q_next := ExitFacts_q_next hpre hX (tracked hpre hX)

/-- The base word's reads are ordered (`BaseWord.baseRead`, from the structures above). -/
theorem baseRead : TmemAlloc.BaseRead L X :=
  BaseWord.baseRead hpre hX (stats hpre hX) (tmem hpre hX) (tmemLife hpre hX)
    (async hpre hX) (older hpre hX) (rings hpre hX) (output hpre hX) (mmaReads hpre hX)
    (baseOrdered' hpre hX (rings hpre hX) (output hpre hX) (tmem hpre hX) (mmaReads hpre hX)
      (stats hpre hX) (tmemLife hpre hX) (async hpre hX) (older hpre hX))

end

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

theorem tc : TcFacts L X where
  commit_spec := TcFacts_commit_spec hpre hX (tracked hpre hX)
  init_done := TcFacts_init_done hpre hX (tracked hpre hX)
  mma_reads := TcFacts_mma_reads hpre hX (tracked hpre hX)
  mma_cell := TcFacts_mma_cell hpre hX (tracked hpre hX)
  qk_smem := TcFacts_qk_smem' hpre hX (tracked hpre hX)
  mma_shape := TcFacts_mma_shape hpre hX (tracked hpre hX)
  ub_stop := TcFacts_ub_stop hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)
  stop_cause := TcFacts_stop_cause hpre hX (tracked hpre hX)
    (Cross.nextStops hpre hX)

theorem warp : WarpSyncFacts L X where
  poll_round := WarpSyncFacts_poll_round hpre hX (tracked hpre hX)
    (Cross.pollAgree_of_rest hpre hX (tracked hpre hX) (Cross.pollAgreeRest hpre hX))
  poll_order := WarpSyncFacts_poll_order hpre hX (tracked hpre hX)
    (Cross.pollColl hpre hX (tracked hpre hX)) (Cross.pollRest hpre hX (statsGroup hpre hX))
  tc_seq := WarpSyncFacts_tc_seq hpre hX (tracked hpre hX)
    (Cross.tcAgree hpre hX (baseRead hpre hX))
  tc_count := WarpSyncFacts_tc_count hpre hX (tracked hpre hX)
    (Cross.tcExitAgree hpre hX) (Cross.tcExitAbove hpre hX)

/-- **`ThreadInputs`**: the thread layer's exports `safe_goal` takes. -/
theorem threadInputs : ThreadInputs P L X :=
  { cluster := cluster hpre hX
    tmem := tmem hpre hX
    stats := stats hpre hX
    output := output hpre hX
    rings := rings hpre hX
    score := score hpre hX
    reg := RegFacts_holds hpre hX (tracked hpre hX)
    async := async hpre hX
    ringCopies := ringCopies hpre hX
    init := initFacts' hpre hX
    oacc := oacc hpre hX
    tc := tc hpre hX
    thread := thread hpre hX
    route := route hpre hX
    pready := pready hpre hX
    p2 := p2 hpre hX
    sfull := sfull hpre hX
    ofull := ofull hpre hX
    floats := floats hpre hX
    tmemLife := tmemLife hpre hX
    tcmma := tcmma hpre hX
    warp := warp hpre hX
    exit := exit hpre hX
    older := older hpre hX
    store := store hpre hX
    cover := coverFacts hpre hX (tracked hpre hX)
    spare := SpareUnused_holds hpre hX (tracked hpre hX) (Cross.syncNamed hpre hX)
      (Cross.commitTargets hpre hX)
    noRelease := ProgressAsyncFacts_no_release hpre hX (tracked hpre hX)
    spin := spin hX
    bar2ArriveLast := Bar2.bar2ArriveLast hpre hX
    storeBoxes := Placed.storeBoxes hX (store hpre hX)
    sharedPlaced := Placed.sharedPlaced hpre hX (older hpre hX) (rings hpre hX) (async hpre hX)
      (tmem hpre hX) (output hpre hX) (mmaReads hpre hX)
    globalPlaced := Placed.globalPlaced hpre hX (store hpre hX) (older hpre hX) (rings hpre hX)
      (ringCopies hpre hX) (async hpre hX) (tmem hpre hX) (score hpre hX) (output hpre hX)
    globalWrites := Placed.globalWrites hpre hX (store hpre hX) (older hpre hX) (rings hpre hX)
      (tmem hpre hX)
    mmaReads := mmaReads hpre hX }

end

end FactsAll

end
end PTX.Kernels.FlashAttn4Fwd.Proof
