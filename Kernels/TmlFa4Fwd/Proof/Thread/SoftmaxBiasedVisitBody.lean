-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedBiasRow
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasRendezvousProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasStageProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasReturnProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasArrivalRank
public import Kernels.TmlFa4Fwd.Proof.Thread.AffineCursor
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue Thread Correction

/-- A cursor of one maximal history is a cursor of another with the same traces when its
position is not the end of the trace or the other history releases the lane. -/
def OpeningTripCursor.transfer {l : Launch} {X Y : Execution} {g pc : Nat}
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g pc F) (hTrace : Y.tr = X.tr)
    (hReleased : c.pos = (X.tr g).length → Step.Released l Y g) :
    OpeningTripCursor l Y g pc F :=
  ⟨c.pos,c.before,c.ready,c.ending,c.positive,by simpa only [hTrace] using c.bounded,
    fun h => hReleased (by simpa only [hTrace] using h),c.checkpoint,
    by simpa only [hTrace] using c.recorded,by simpa only [hTrace] using c.remaining,
    c.localSteps⟩

theorem SoftmaxCounts.ofTrace {X Y : Execution} (hTrace : Y.tr = X.tr)
    {g i tc bars elects notices credits scores : Nat}
    (h : SoftmaxCounts X g i tc bars elects notices credits scores) :
    SoftmaxCounts Y g i tc bars elects notices credits scores := by
  unfold SoftmaxCounts warpBars elections at *
  rw [hTrace]
  exact h

/-- Events that are neither tensor collectives, warp barriers, elections nor statistics
notices keep all four counts. -/
theorem SoftmaxCounts.ofSilent {X : Execution}
    {g a n tc bars elects notices credits scores : Nat}
    (hSilent : ∀ k < n, ∃ e, X.get (g,a+k) = some e ∧ isTcColl e = false ∧
      Execution.isWarpBar e = false ∧ isElectEv e = false ∧ Scores.publishesStats e = false ∧
      Scores.creditAcquired e = false ∧ scoreAcquired e = false)
    (h : SoftmaxCounts X g a tc bars elects notices credits scores) :
    SoftmaxCounts X g (a+n) tc bars elects notices credits scores := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    obtain ⟨e,he,h1,h2,h3,h4,h5,h6⟩ := hSilent n (by omega)
    have prev := ih (fun k hk => hSilent k (by omega))
    unfold SoftmaxCounts warpBars elections at *
    rw [← Nat.add_assoc]
    exact ⟨(countP_take_succ_false he h1).trans prev.1,
      (countP_take_succ_false he h2).trans prev.2.1,
      (countP_take_succ_false he h3).trans prev.2.2.1,
      (countP_take_succ_false he h4).trans prev.2.2.2.1,
      (countP_take_succ_false he h5).trans prev.2.2.2.2.1,
      (countP_take_succ_false he h6).trans prev.2.2.2.2.2⟩

private theorem silentRead {X : Execution} {i : EvId} {pc : Nat} {a : Acc} {bs}
    (he : X.get i = some ⟨pc,.rd a bs⟩) :
    ∃ e, X.get i = some e ∧ isTcColl e = false ∧
      Execution.isWarpBar e = false ∧ isElectEv e = false ∧ Scores.publishesStats e = false ∧
      Scores.creditAcquired e = false ∧ scoreAcquired e = false :=
  ⟨_,he,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The whole Bias window of a lane keeps its counts. -/
private theorem biasWindowCounts {l : Launch} {X : Execution} {g pos : Nat} (warp : Fin 8)
    (words : Fin 16 → Nat → Value)
    (reads : ∀ i, BiasWordReads l X true i g (pos+4*i.val)
      (biasVectorBase l g (stageOf warp) true i) (words i))
    (fence : X.get (g,pos+64) = some
      ⟨biasFencePc true,.fenceProxy (.async (some (.shared .cta))) none⟩)
    (sync : X.get (g,pos+65) =
      some ⟨biasFencePc true+2,.bar (11+(stageOf warp).val) (some 128) .sync⟩)
    {tc bars elects notices credits scores : Nat}
    (h : SoftmaxCounts X g pos tc bars elects notices credits scores) :
    SoftmaxCounts X g (pos+66) tc bars elects notices credits scores := by
  apply SoftmaxCounts.ofSilent _ h
  intro k hk
  by_cases hv : k < 64
  · let i : Fin 16 := ⟨k/4,by omega⟩
    obtain ⟨bs,he,_⟩ := reads i (k%4) (Nat.mod_lt _ (by decide))
    have hk : pos+4*i.val+k%4 = pos+k := by dsimp only [i]; omega
    rw [hk] at he
    exact silentRead he
  · by_cases h64 : k = 64
    · subst h64; exact ⟨_,fence,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · have h65 : k = 65 := by omega
      subst h65; exact ⟨_,sync,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- A whole stage at its Bias acquires of the same repeated visit passes the rendezvous.
Each lane reaches the FMA body in one history with the same traces, keeps its counts and
reports the leader's Bias-empty arrival. -/
theorem stageBiasedBodiesOfRows {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFootprint : OutputFootprint p X) {cta : Nat} (hCta : cta < l.grid)
    (stage : Fin 2) (visit : Nat) (warp : Nat → Fin 8)
    (hWarp : ∀ lane < l.block, lane/32 ∈ biasParticipants stage →
      (warp lane).val = warpIndex l (cta*l.block+lane))
    (hStage : ∀ lane < l.block, lane/32 ∈ biasParticipants stage → stageOf (warp lane) = stage)
    (block floor counter bars elects : Nat → Nat) (maximum : Nat → Option ℝ) (sum : Nat → ℝ)
    (rows : ∀ lane < l.block, lane/32 ∈ biasParticipants stage →
      BiasedBiasRow p l X (cta*l.block+lane) (warp lane) visit (block lane) (floor lane)
        (counter lane) (bars lane) (elects lane) (maximum lane) (sum lane)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      Y.MemWrites = X.MemWrites ∧
      ∀ lane (hLane : lane < l.block) (hMember : lane/32 ∈ biasParticipants stage),
        let g := cta*l.block+lane
        let r := rows lane hLane hMember
        ∃ bias : Nat → Option ℝ,
          ∃ after : OpeningTripCursor l Y g (biasBodyStart true)
            (Scores.repeatedBiasFencePack p l g (warp lane) ++
              (repeatedBiasPackFrame r.scores.words ++
                biasedBiasFacts p l g visit (block lane) (maximum lane) (sum lane) (floor lane)
                  (counter lane))),
            after.ending = r.cursor.ending ∧
            after.pos = (if laneOf l g = 0 then r.cursor.pos+67 else r.cursor.pos+66) ∧
            (laneOf l g = 0 → Y.get (g,r.cursor.pos+66) = some ⟨5278,
              .arrive (signalLoc l g stage (biasReleaseSite true)) 0 1 true .cta⟩) ∧
            SoftmaxCounts Y g after.pos (11*visit+4) (bars lane) (elects lane) visit (visit+1)
              (visit+1) ∧
            ∀ i : Fin 16, BiasUnpacked true i after.ready (fun k =>
              biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1))) := by
  classical
  have hGuard := Progress.syncGuarded hp hMax.1 (hFootprint.metadataProtected hp).1
  have input (lane : Nat) (hLane : lane < l.block) (hMember : lane/32 ∈ biasParticipants stage) :
      Nonempty (RepeatedBiasAcquireLane l X (cta*l.block+lane) stage visit
        (Scores.repeatedBiasFencePack p l (cta*l.block+lane) (warp lane) ++
          (repeatedBiasPackFrame (rows lane hLane hMember).scores.words ++
            biasedBiasFacts p l (cta*l.block+lane) visit (block lane) (maximum lane) (sum lane)
              (floor lane) (counter lane)))) := by
    obtain ⟨a,_⟩ := (rows lane hLane hMember).vectorLane hp hMax.1 (hWarp lane hLane hMember)
      (hStage lane hLane hMember)
    exact ⟨a⟩
  have spec (lane : Nat) (hLane : lane < l.block) (hMember : lane/32 ∈ biasParticipants stage) :=
    (rows lane hLane hMember).vectorLane hp hMax.1 (hWarp lane hLane hMember)
      (hStage lane hLane hMember)
  choose a hAWarp hAPos hAEnd using spec
  have prepare (lane : Nat) (hLane : lane < l.block) (hMember : lane/32 ∈ biasParticipants stage) :=
    let c := a lane hLane hMember
    repeatedBiasArrivalOfMaximal hp hMax hGuard hFootprint (NamedBar.cta_thread_lt hCta hLane)
      c.warp c.cursor c.row c.stageOffset c.vectorBase c.addressKeeps c.vectorKeeps
      c.barrierKeeps c.fenceFrame
  choose bias arrived hPos hEnd hFence hSync hKeep hLive hData using prepare
  have hHere (lane : Nat) (hLane : lane < l.block)
      (hMember : lane/32 ∈ biasParticipants stage) :
      let c := a lane hLane hMember
      let i := (arrived lane hLane hMember).pos-1
      BarrierArrival X (cta*l.block+lane,i) (11+stage.val) (some 128) .sync ∧
        observedBarrierOrdinal X (cta*l.block+lane,i) (11+stage.val) = visit := by
    dsimp only
    let c := a lane hLane hMember
    rw [hPos lane hLane hMember,show c.cursor.pos+66-1 = c.cursor.pos+65 by omega]
    have hArrival := hSync lane hLane hMember
    rw [c.stageEq] at hArrival
    refine ⟨⟨_,hArrival,rfl⟩,?_⟩
    have hCount := repeatedBiasArrivalOrdinal c.warp
      (fun i k => biasLoadWord (bias lane hLane hMember (8*i.val+2*k))
        (bias lane hLane hMember (8*i.val+2*k+1)))
      (fun i => (hData lane hLane hMember i).1) (hFence lane hLane hMember)
    rw [c.stageEq] at hCount
    exact hCount.trans c.rank
  obtain ⟨Y,hY,hTrace,hObjects,hWrites,hRelease⟩ :=
    biasStageReleaseOfMaximal hp hMax hFootprint hCta stage visit
      (fun lane hl hm => ⟨_,hHere lane hl hm⟩)
  refine ⟨Y,hY,hTrace,hObjects,hWrites,?_⟩
  intro lane hLane hMember
  dsimp only
  let g := cta*l.block+lane
  let c := a lane hLane hMember
  let r := rows lane hLane hMember
  let cut := arrived lane hLane hMember
  have hg : g < l.threads := NamedBar.cta_thread_lt hCta hLane
  have hCta' : g/l.block = cta :=
    (NamedBar.lane_cta (c := cta) (NamedBar.block_pos_of_thread_lt hg) hLane).1
  have hReleased (hLast : cut.pos = (X.tr g).length) : Step.Released l Y g := by
    have hObserved := hHere lane hLane hMember
    change BarrierArrival X (g,cut.pos-1) (11+stage.val) (some 128) .sync ∧
      observedBarrierOrdinal X (g,cut.pos-1) (11+stage.val) = visit at hObserved
    rw [hLast] at hObserved
    exact hRelease g hg hCta' hObserved.1 hObserved.2
  let resumed := cut.resume hTrace hReleased
  let F := Scores.repeatedBiasFencePack p l g (warp lane) ++
    (repeatedBiasPackFrame r.scores.words ++
      biasedBiasFacts p l g visit (block lane) (maximum lane) (sum lane) (floor lane)
        (counter lane))
  let d : OpeningTripCursor l Y g (biasFencePc true+3) F :=
    ⟨resumed.pos,resumed.before,resumed.ready,resumed.ending,resumed.positive,resumed.bounded,
      resumed.released,resumed.checkpoint.mono (hLive lane hLane hMember),resumed.recorded,
      resumed.remaining,resumed.localSteps⟩
  obtain ⟨after,hEnding,hPosition,hCredit,hBias⟩ :=
    repeatedBiasReturnOfMaximal hp hY hg c.warp d (hKeep lane hLane hMember).2.2.2.2
      c.releaseKeeps (bias lane hLane hMember) (fun i => (hData lane hLane hMember i).2)
  have hcPos : c.cursor.pos = r.cursor.pos := hAPos lane hLane hMember
  have hcWarp : c.warp = warp lane := hAWarp lane hLane hMember
  have hcStage : stageOf c.warp = stage := c.stageEq
  have window : SoftmaxCounts X g (c.cursor.pos+66) (11*visit+4) (bars lane) (elects lane)
      visit (visit+1) (visit+1) := by
    have sync := hSync lane hLane hMember
    exact biasWindowCounts c.warp _ (fun i => (hData lane hLane hMember i).1)
      (hFence lane hLane hMember) sync (hcPos ▸ r.counts)
  have hdPos : d.pos = c.cursor.pos+66 := hPos lane hLane hMember
  refine ⟨bias lane hLane hMember,after,?_,?_,?_,?_,hBias⟩
  · exact hEnding.trans ((hEnd lane hLane hMember).trans (hAEnd lane hLane hMember))
  · rw [hPosition,hdPos,hcPos]
  · intro hLeader
    have he := hCredit hLeader
    rw [hcStage,hdPos,hcPos] at he
    exact he
  · have inY := SoftmaxCounts.ofTrace hTrace window
    rw [hPosition,hdPos]
    by_cases hLeader : laneOf l g = 0
    · rw [ite_eq_left hLeader]
      have he := hCredit hLeader
      rw [hdPos] at he
      exact SoftmaxCounts.ofSilent (n := 1) (fun k hk => by
        obtain rfl : k = 0 := by omega
        exact ⟨_,he,rfl,rfl,rfl,rfl,rfl,rfl⟩) inY
    · rw [ite_eq_right hLeader]
      exact inY

end PTX.Kernels.TmlFa4Fwd.Softmax
