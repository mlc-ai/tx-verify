-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.FactsAll
public import Kernels.FlashAttn4Fwd.Proof.ProgressWaitsGlue
public import Kernels.FlashAttn4Fwd.Proof.ValuesGlue
public import Lemmas.Flow.NotAsyncWait
public import Lemmas.Flow.NotBulk
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAllocNext
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsClusterWait
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTrip
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsFire
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLags
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsCredit
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsLoader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsMma
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsOutput
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsReady
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsRing
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsCorr
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsLoader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsMma
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsSoft
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsProgressAsync
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid2Async
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid2Loader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedNoExit
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpPos
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftValues
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaRingCommits
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarW
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedMma
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarpColl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpAll
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedCorrTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCollShape
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCollLast

@[expose] public section

/-! # The thread layer's interface structures (II): the progress, result and value inputs

The bundles `Progress.Remaining` takes (`NextFacts`, `ProgressPolls`, `PollInputs`,
`WarpCollFacts`, `WaitInputs`, `AsyncInputs`), `ResultInputs` and `ValueFacts`, for every
consistent execution, from their field theorems. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace FactsAll

theorem pollInputs (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) :
    PollInputs P L X where
  route := route hpre hX
  pready := pready hpre hX
  p2 := p2 hpre hX
  sfull := sfull hpre hX
  ofull := ofull hpre hX
  older := older hpre hX

/-- FA4's code has no `cp.async` group wait. -/
theorem kernel_noAsyncWait : kernel.code.all (fun ins => !Flow.asyncWaitOp ins.op) = true := by
  decide +kernel

/-- **FA4 makes no `cp.async` group wait.** -/
theorem no_asyncWait (hX : Consistent L kernel asms mem0 X) {i : EvId} {pc n : Nat} :
    X.get i ≠ some ⟨pc, .asyncWait n⟩ := fun he =>
  Flow.no_kind_of_code hX Flow.asyncWaitOp (fun k => ∃ n, k = .asyncWait n)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => Flow.fires_asyncWait_op hf hk)
    kernel_noAsyncWait he ⟨_, rfl⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

theorem next : NextFacts L X where
  fire := NextFacts_fire hpre
  alloc_next := NextFacts_alloc_next hpre hX
  alloc_result_event := Cross.alloc_result_event hpre hX (tracked hpre hX)
  reg_entry := NextFacts_reg_entry hpre hX noRegReentry_all

theorem polls : ProgressPolls L X where
  loader :=
    { poll := LoaderPollFacts_poll hpre hX (tracked hpre hX)
      started := LoaderPollFacts_started hpre hX (tracked hpre hX)
      lane := LoaderPollFacts_lane hpre hX (tracked hpre hX)
      lag := LoaderPollFacts_lag hpre hX (tracked hpre hX) }
  mmaRing :=
    { poll := MmaRingPollFacts_poll hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)
      commits := MmaRingPollFacts_commits hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)
      arrive := MmaRingPollFacts_arrive hpre hX (tracked hpre hX)
      copies := MmaRingPollFacts_copies hpre hX (tracked hpre hX) }
  pReady :=
    { poll := PReadyPollFacts_poll hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)
      lag_soft := PReadyPollFacts_lag_soft hpre hX (tracked hpre hX)
      lag_corr := PReadyPollFacts_lag_corr hpre hX (tracked hpre hX) }
  p2 :=
    { poll := P2PollFacts_poll hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)
      lag_soft := P2PollFacts_lag_soft hpre hX (tracked hpre hX) }
  handshake :=
    { poll := HandshakePollFacts_poll hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)
      lag := HandshakePollFacts_lag hpre hX (tracked hpre hX) }
  sFull :=
    { poll := SFullPollFacts_poll hpre hX (tracked hpre hX)
      lag := SFullPollFacts_lag hpre hX (tracked hpre hX) }
  credit :=
    { poll := CreditPollFacts_poll hpre hX (tracked hpre hX)
      lag := CreditPollFacts_lag hpre hX (tracked hpre hX) }
  oFull :=
    { poll := OFullPollFacts_poll hpre hX (tracked hpre hX)
      lag := OFullPollFacts_lag hpre hX (tracked hpre hX) }
  free :=
    { poll := FreePollFacts_poll hpre hX (tracked hpre hX)
      lag := FreePollFacts_lag hpre hX (tracked hpre hX) }
  staged :=
    { poll := StagedPollFacts_poll hpre hX (tracked hpre hX)
      lag := StagedPollFacts_lag hpre hX (tracked hpre hX) }

theorem warpColl : WarpCollFacts L X :=
  have ⟨_, hs⟩ := Sched.warpSched_all hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre)
  { shape := WarpCollFacts_shape hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre) hs
    last := WarpCollFacts_last hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre) hs
    exit := WarpCollFacts_exit
      (Sched.warpExitAgree_all hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre))
      (Sched.warpExitAbove_all hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre))
    lag := WarpCollFacts_lag hs (Sched.warpLagPos hpre hX (Cross.sitesTmplOk hpre)) }

theorem waits : Progress.WaitInputs L X :=
  { cluster := cluster hpre hX
    tmem := tmem hpre hX
    stats := stats hpre hX
    tmemLife := tmemLife hpre hX
    regMatch := regMatch_of (RegFacts_holds hpre hX (tracked hpre hX))
    regExit := regExit_of (RegFacts_holds hpre hX (tracked hpre hX))
    waits :=
      { reg :=
          { before := RegWaitFacts_before hpre hX (tracked hpre hX)
            after := RegWaitFacts_after hpre hX (tracked hpre hX) }
        tc := tcWaitFacts
          (Sched.tcSched_all hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre))
          (Cross.tcStepUp hpre hX)
        tmem := tmemWaitFacts (Sched.tmemSched hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre))
          fun hg he => ((tmem hpre hX).event hg he).1
        cluster :=
          { state_time := ClusterWaitFacts_state_time hpre hX (tracked hpre hX)
            end_time := ClusterWaitFacts_end_time hpre hX (tracked hpre hX)
            live := ClusterWaitFacts_live hpre hX (tracked hpre hX)
            arrive_pc := ClusterWaitFacts_arrive_pc hpre hX (tracked hpre hX)
            wait_pc := ClusterWaitFacts_wait_pc hpre hX (tracked hpre hX) }
        bar := barWaitFacts (Sched.barSched hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre))
          (Sched.barMember hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre))
          (Sched.barNoExit hpre hX (tracked hpre hX) (Cross.sitesTmplOk hpre))
          (Cross.barStepUp hpre hX) }
    no_asyncWait := no_asyncWait hX }

theorem asyncInputs {P' : Params} (hpre' : Pre P' L mem0) : AsyncInputs P' L X :=
  { cluster := cluster hpre hX
    init := initFacts' hpre hX
    tmem := tmem hpre hX
    rings := rings hpre hX
    ringCopies := ringCopies hpre' hX
    async := async hpre' hX
    output := output hpre hX
    store := store hpre' hX
    writes := writes hX
    score := score hpre hX
    tc := tc hpre hX
    tcmma := tcmma hpre hX
    progress :=
      { copy_route := ProgressAsyncFacts_copy_route hpre hX (tracked hpre hX)
        store_valid := ProgressAsyncFacts_store_valid hpre hX (tracked hpre hX)
        write_length := ProgressAsyncFacts_write_length hpre hX (tracked hpre hX)
        no_release := ProgressAsyncFacts_no_release hpre hX (tracked hpre hX)
        mma_reads := mmaReads hpre hX } }

/-- **`ResultInputs`**: the thread layer's exports `result_goal_of` takes. -/
theorem resultInputs : ResultInputs P L X :=
  { output := output hpre hX
    tmem := tmem hpre hX
    rings := rings hpre hX
    mmaReads := mmaReads hpre hX
    outputInit := InitFirst.outputInit hpre hX (cluster hpre hX) (tmem hpre hX)
      (initFacts' hpre hX) (output hpre hX)
    spin := spin hX
    store := store hpre hX
    writes := writes hX }

/-- **`ValueFacts`**: the threads' computations. -/
theorem values : ValueFacts P L X where
  soft := ValueFacts_soft hpre hX (tracked hpre hX)
  corr := ValueFacts_corr hpre hX (tracked hpre hX)

end

/-- **`Progress.Remaining`**, from the thread facts. -/
theorem progressRemaining (hpre : Pre P L mem0) :
    Progress.Remaining L mem0 where
  commit_mask X hX i sp := by
    rintro ⟨pc, he⟩
    obtain ⟨-, -, b, -, rfl⟩ := (tc hpre hX).commit_spec (Frame.lt_of_get hX he) he
    exact ⟨rfl, rfl⟩
  next X hX := next hpre hX
  polls X hX := polls hpre hX
  pollInputs _ X hpre' hX := pollInputs hpre' hX
  warpColl X hX := warpColl hpre hX
  waits X hX := waits hpre hX
  async _ X hpre' hX := asyncInputs hpre hX hpre'

end FactsAll

end
end PTX.Kernels.FlashAttn4Fwd.Proof
