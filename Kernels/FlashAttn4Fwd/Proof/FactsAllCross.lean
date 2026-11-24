-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.FactsAllOpen
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrBars
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrCover
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOut
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrStep
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderPoll
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaExit
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaPollAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaReg
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftBarAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftCross
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftPoll
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftPollRest
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrPollRest
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrStops
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftRegs
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftTcAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreCross
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCommit
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderPollColl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTcAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftStops
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreCross
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaStop
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid3Stops
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid3Loader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedStep

@[expose] public section

/-! # The `Cross.*` premises, by role

Each `Cross.*` premise of the cross-warp theorems is a statement of every thread; the role
packages prove it for their warps. Here each premise is assembled by cases on the thread's warp
from the role parts. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- `Cross.LowAccessLow`: the softmax, correction and MMA parts. -/
theorem Cross.lowAccessLow : Cross.LowAccessLow L X := by
  intro g k a w l h13 ha hc
  have ht := tracked hpre hX
  by_cases h8 : warpOf L g < 8
  · exact Cross.lowAccessLow_soft hpre hX ht h8 ha hc
  by_cases h12 : warpOf L g < 12
  · exact Cross.lowAccessLow_corr hpre hX ht (by omega) h12 ha hc
  · exact Cross.LowAccessLow_mma hpre hX ht (by omega) ha hc

/-- `Cross.BaseFree`: the softmax and correction parts. -/
theorem Cross.baseFree : Cross.BaseFree L X := by
  intro g k a w l h12 ha hc h1 h2
  have ht := tracked hpre hX
  by_cases h8 : warpOf L g < 8
  · exact Cross.baseFree_soft hpre hX ht h8 ha hc h1 h2
  · exact Cross.baseFree_corr hpre hX ht (by omega) h12 ha hc h1 h2

/-- `Cross.NextStopsAtExitOrBadRead`: by the state's role. -/
theorem Cross.nextStops : Cross.NextStopsAtExitOrBadRead L X := by
  intro g i d e hg hσ he hn
  rcases d with p | r
  · exact .inl (Cross.NextStops_pro hpre hX hσ he hn)
  cases r with
  | softmax s => exact Cross.NextStops_soft hpre hX (tracked hpre hX) hσ he hn
  | mma s => exact Cross.NextStops_mma hpre hX hg hσ he hn
  | loader s => exact .inl (Cross.NextStops_loader hpre hX hσ he hn)
  | store s => exact .inl (Cross.NextStops_store hpre hX hσ he hn)
  | idle s => exact .inl (Cross.NextStops_idle hpre hX hσ he hn)
  | corr s => exact Cross.NextStops_corr hpre hX (tracked hpre hX) hg hσ he hn

/-- `Cross.CommitTargets`: the field `ExitFacts.commit_target` (MMA package). -/
theorem Cross.commitTargets : Cross.CommitTargets L X :=
  ExitFacts_commit_target hpre hX (tracked hpre hX)

/-- `Cross.CommitCluster`: the field `InitFacts.commit_cluster`. -/
theorem Cross.commitCluster : Cross.CommitCluster L X :=
  (initFacts' hpre hX).commit_cluster

/-- `Cross.SyncNamed`: by warp. -/
theorem Cross.syncNamed : Cross.SyncNamed L X := by
  intro g k pc m kd hg he hk
  have ht := tracked hpre hX
  by_cases h8 : warpOf L g < 8
  · exact Cross.syncNamed_soft hpre hX ht h8 he hk
  by_cases h12 : warpOf L g < 12
  · exact Cross.syncNamed_corr hpre hX ht (by omega) h12 he hk
  by_cases h12' : warpOf L g = 12
  · exact Cross.SyncNamed_mma hpre hX ht hg h12' he hk
  by_cases h14 : warpOf L g = 14
  · exact Cross.SyncNamed_loader hpre hX ht hg h14 he hk
  · exact Cross.SyncNamed_hi hpre hX ht hg (by have := warpOf_lt hpre g; omega) he hk

/-- `Cross.PeerBar2High`: by warp. -/
theorem Cross.peerBar2High : Cross.PeerBar2High L X := by
  intro g k ev hg h12 he hp
  have ht := tracked hpre hX
  by_cases h12' : warpOf L g = 12
  · exact Cross.PeerBar2High_mma hpre hX ht hg h12' he hp
  by_cases h14 : warpOf L g = 14
  · exact absurd hp (Cross.PeerBar2High_loader hpre hX ht hg h14 he)
  · exact absurd hp
      (Cross.PeerBar2High_hi hpre hX ht hg (by have := warpOf_lt hpre g; omega) he)

/-- `Cross.PollAgreeRest`: by warp (the idle warp has no poll). -/
theorem Cross.pollAgreeRest : Cross.PollAgreeRest L X := by
  intro g h k k' pc p p' m m' ok ok' acq acq' sc sc' d d' h12 h14 hw hσ hσ' he he' hr
  have ht := tracked hpre hX
  by_cases h8 : warpOf L g < 8
  · exact Cross.PollAgree_soft hpre hX ht h8 hw he he' hr
  by_cases h11 : warpOf L g < 12
  · exact Cross.pollAgree_corr hpre hX ht (by omega) h11 hw he he' hr
  by_cases h13 : warpOf L g = 13
  · exact Cross.pollAgree_store hpre hX ht h13 hw he he' hr
  · exact Cross.PollAgree_idle hpre hX ht (by have := warpOf_lt hpre g; omega) he

/-- `Cross.PollRest`: the softmax, correction, MMA, loader and idle parts and the store warp's
exempt polls. -/
theorem Cross.pollRest (hgrp : StatsGroup L X) : Cross.PollRest L X := by
  refine Cross.pollRest_of_rest hpre hX (tracked hpre hX) ?_
  intro g h k k' pc m m' p p' ok ok' acq acq' sc sc' h13 hg hh hne hw he he' hb hu hm hr
  by_cases h8 : warpOf L g < 8
  · exact Cross.PollRest_soft hpre hX (tracked hpre hX) hg hh h8 hw he he' hr
  by_cases h14 : warpOf L g = 14
  · exact absurd hr (Cross.PollRest_loader hpre hX (tracked hpre hX) h14 hw he' hu)
  by_cases h15 : warpOf L g = 15
  · exact absurd he (Cross.idle_no_wait hpre hX (tracked hpre hX) h15)
  by_cases h12 : warpOf L g < 12
  · exact Cross.PollRest_corr hpre hX (tracked hpre hX) hgrp (by dsimp only; omega) h12 hw he he'
      hr
  · exact absurd hr (Cross.PollRest_mma hpre hX (tracked hpre hX)
      (by have := warpOf_lt hpre g; omega) hw he' hb hu)

/-- `Cross.TcAgree`: by warp (the MMA part given the base word's reads). -/
theorem Cross.tcAgree (hbr : TmemAlloc.BaseRead L X) : Cross.TcAgree L X := by
  intro g h k k' pc pc' n kd kd' d d' hw hσ hσ' he he' hn hn'
  have ht := tracked hpre hX
  by_cases h8 : warpOf L g < 8
  · exact Cross.TcAgree_soft hpre hX ht h8 hw he he' hn hn'
  by_cases h11 : warpOf L g < 12
  · exact Cross.TcAgree_corr hpre hX ht (by omega) h11 hw he he' hn hn'
  by_cases h12 : warpOf L g = 12
  · exact Cross.TcAgree_mma hpre hX ht hbr hw h12 hσ hσ' he he' hn hn'
  by_cases h14 : warpOf L g = 14
  · exact Cross.TcAgree_loader hpre hX ht h14 hw hσ hσ' he he' hn hn'
  · exact Cross.TcAgree_hi hpre hX ht (by have := warpOf_lt hpre g; omega) he

/-- `Cross.TcExitAgree`: by warp. -/
theorem Cross.tcExitAgree : Cross.TcExitAgree L X := by
  intro g h k k' pc pc' d d' hw hσ hσ' he he'
  have ht := tracked hpre hX
  by_cases h8 : warpOf L g < 8
  · exact Cross.TcExitAgree_soft hpre hX ht h8 hw he he'
  by_cases h11 : warpOf L g < 12
  · exact Cross.TcExitAgree_corr hpre hX ht (by omega) h11 hw he he'
  by_cases h12 : warpOf L g = 12
  · exact Cross.TcExitAgree_mma hpre hX ht hw h12 hσ hσ' he he'
  by_cases h14 : warpOf L g = 14
  · exact Cross.TcExitAgree_loader hpre hX ht h14 hw hσ hσ' he he'
  · exact Cross.TcExitAgree_hi hpre hX ht (by have := warpOf_lt hpre g; omega) hw

/-- `Cross.TcExitAbove`: by warp. -/
theorem Cross.tcExitAbove : Cross.TcExitAbove L X := by
  intro g h k k' pc n d d' hw hσ hσ' he hn
  have ht := tracked hpre hX
  by_cases h8 : warpOf L g < 8
  · exact Cross.TcExitAbove_soft hpre hX ht h8 hw he hn
  by_cases h11 : warpOf L g < 12
  · exact Cross.TcExitAbove_corr hpre hX ht (by omega) h11 hw he hn
  by_cases h12 : warpOf L g = 12
  · exact Cross.TcExitAbove_mma hpre hX ht hw h12 hσ hσ' he hn
  by_cases h14 : warpOf L g = 14
  · exact Cross.TcExitAbove_loader hpre hX ht h14 hw hσ hσ' he hn
  · exact Cross.TcExitAbove_hi hpre hX ht (by have := warpOf_lt hpre g; omega) hn

/-- `Cross.BarAgree`: by warp. -/
theorem Cross.barAgree : Cross.BarAgree L X := by
  intro g h i j x y hw hx hy hbx hby hc
  have ht := tracked hpre hX
  by_cases h8 : warpOf L g < 8
  · exact Cross.BarAgree_soft hpre hX ht h8 hw hx hy hbx hby hc
  by_cases h11 : warpOf L g < 12
  · exact Cross.barAgree_corr hpre hX ht (by omega) h11 hw hx hy hbx hby hc
  by_cases h12 : warpOf L g = 12
  · exact Cross.BarAgree_mma hpre hX ht hw h12 hx hy hbx hby hc
  by_cases h14 : warpOf L g = 14
  · exact Cross.BarAgree_loader hpre hX ht h14 hw hx hy hbx hby hc
  · exact Cross.BarAgree_hi hpre hX ht (by omega) hx hbx

/-- `Cross.TcStepUp`: `Sched.tcStepUp`. -/
theorem Cross.tcStepUp : Cross.TcStepUp L X :=
  Sched.tcStepUp hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)

/-- `Cross.BarStepUp`: `Sched.barStepUp`. -/
theorem Cross.barStepUp : Cross.BarStepUp L X :=
  Sched.barStepUp hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
