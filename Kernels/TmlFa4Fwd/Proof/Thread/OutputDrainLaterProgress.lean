-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainScanProgress
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainLaterPrepare
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainFinish
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainGroup
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainRounds
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainTerminalProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

private def laterDrainSaved (p : Params) (first cta lane : Nat) : List (Nat × Value) :=
  [(7232,b32 (groupLaneTiles p first lane)),(7235,b32 first),(1210,b32 (cta+1)),
    (1201,b32 lane),(7147,b32 p.batch),(7506,b64 p.cuQBase),
    (7230,b32 (tilePrefix p first*p.heads)),(1072,b32 cta),(7138,b32 p.heads),(1062,b32 13)]

private theorem laterDrainSavedRegs (p : Params) (first cta lane : Nat) :
    ∀ item ∈ laterDrainSaved p first cta lane, item.1 ∈ drainRoundPersistent := by
  intro item h
  simp only [laterDrainSaved,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact of_decide_eq_true rfl

private def laterDrainReadFrame (p : Params) (l : Launch) (g first cta lane : Nat) :
    List (Nat × Value) :=
  [(1212,b32 (first+lane)),(318,.pred (decide (p.batch < first+lane))),(7231,b32 0)] ++
    drainLaterGroup p l (warpLane l g lane) first (tilePrefix p first*p.heads) (cta+1) cta

private def laterDrainReadDone (p : Params) (l : Launch) (g first cta lane : Nat) :
    List (Nat × Value) :=
  laterLaneFacts l (warpLane l g lane) first (b32 (drainCuQ p (first+lane))) ++
    drainLaterGroup p l (warpLane l g lane) first (tilePrefix p first*p.heads) (cta+1) cta

private theorem laterDrainReadReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first cta shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first+31 < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3032 (drainNextFacts p l g first cta) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 3040 (laterDrainReadFrame p l g (first+31) cta)
      shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  have hLane : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).2
  have hBound := hp.shape.2.2.2.2.2
  change p.qOffset p.batch + 256 * p.batch < 2 ^ 30 at hBound
  have hFit : first+31+laneOf l (warpLane l g lane) < 2^31 := by rw [hLane]; omega
  have ht := cur.checkpoint lane hl
  rw [drainNextFacts, Nat.min_eq_right hFirst.le] at ht
  rcases drainLaterReadRoute hp hFit ht with ⟨hNo,_⟩ | ⟨_,u,hLocal,hu⟩
  · omega
  · rw [hLane] at hu
    exact ⟨u,hLocal,hu⟩

private theorem laterDrainReadAndDown {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first cta shuffles votes : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3040 (laterDrainReadFrame p l g first cta)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 3046
      (fun lane => drainLaterWords p l (warpLane l g lane) first ++
        drainLaterGroup p l (warpLane l g lane) first (tilePrefix p first*p.heads) (cta+1) cta)
      (shuffles+1) votes ends) := by
  classical
  let thread := warpLane l g
  let pos := fun lane => if first+lane ≤ p.batch then cur.pos lane+1 else cur.pos lane
  let done := laterDrainReadDone p l g first cta
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).2
  have hEach (lane : Nat) (hl : lane < 32) : ∃ before state,
      At state 3044 (done lane) ∧
      0 < pos lane ∧ pos lane ≤ (X.tr (thread lane)).length ∧
      (pos lane = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      ((X.tr (thread lane)).take (pos lane)).countP Execution.isShfl = shuffles ∧
      ((X.tr (thread lane)).take (pos lane)).countP isFullWarpVote = votes ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take (pos lane))
        (some before) ∧
      Run kernel Assumptions.all l (thread lane) before ((X.tr (thread lane)).drop (pos lane))
        (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before state := by
    have ht := cur.checkpoint lane hl
    have ht' : At (cur.state lane) 3040 ([(1212,b32 (first+laneOf l (thread lane))),
        (318,.pred (decide (p.batch < first+laneOf l (thread lane)))),(7231,b32 0)] ++
      drainLaterGroup p l (thread lane) first (tilePrefix p first*p.heads) (cta+1) cta) := by
      rw [hLane lane hl]
      exact ht
    have h := laterDrainReadOfMaximal (g := warpLane l g lane) hp hMax
      (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.1 ht' (cur.localSteps lane hl)
      (cur.continuation lane hl) (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
      (cur.recorded lane hl) (cur.ordinals.shfl lane hl) (cur.ordinals.vote lane hl) hCuQ
    have hLane' : laneOf l (warpLane l g lane) = lane := hLane lane hl
    simpa only [hLane',pos,done,laterDrainReadDone] using h
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! before state hAt hPos hBound hRelease hSh hVote hRecorded hRun hLocal using hEach
  let rd : SchedulerWarpReached l X g 3044 done shuffles votes ends :=
    ⟨⟨pos,before,state,⟨hSh,hVote⟩,hRun,hLocal,hAt⟩,hPos,hBound,hRelease,hRecorded⟩
  let F := fun lane => (319,.pred (decide (lane = 31))) :: done lane
  obtain ⟨ready⟩ := rd.advanceLocal (pc' := 3045) (G := F) (by
    intro lane hl
    have ht := rd.checkpoint lane hl
    have ht' : At (rd.state lane) 3044
        (laterLaneFacts l (thread lane) first (b32 (drainCuQ p (first+laneOf l (thread lane)))) ++
          drainLaterGroup p l (thread lane) first (tilePrefix p first*p.heads) (cta+1) cta) := by
      rw [hLane lane hl]
      exact ht
    obtain ⟨u,hTau,hu,_⟩ := laterDrainDownLocal hp ht'
    rw [hLane lane hl] at hu
    exact ⟨u,hTau,hu⟩)
  obtain ⟨advanced⟩ := ready.consumeShuffle (dst := 2422) hp hMax hg .down
    (fun lane => b32 (drainCuQ p (first+lane))) (fun _ => 1) (fun _ => 31) (by
      intro lane _ item hm
      simp only [F,done,laterDrainReadDone,laterLaneFacts,drainLaterGroup,drainLaterCommon,
        List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact of_decide_eq_true rfl) (by
      intro lane hl
      have ht := ready.checkpoint lane hl
      have hModel : out kernel Assumptions.all l (thread lane) (ready.state lane) =
          out kernel [] l (thread lane) (ready.state lane) :=
        epilogue_out_all_eq_nil (.inl (by rw [ht.1]; decide))
      exact hModel.trans (drainLaterShuffle hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.2.2.1))
  apply advanced.advanceLocal
  intro lane hl
  have hu := advanced.checkpoint lane hl
  refine ⟨advanced.state lane,.refl,hu.mono ?_⟩
  have hf := ((holds_append ..).mp hu.2.2.2.2.2.2)
  unfold drainLaterWords drainLaterWordFacts
  rw [hLane lane hl]
  have hIdx := hf.1.1
  have hLane' : laneOf l (warpLane l g lane) = lane := hLane lane hl
  rw [hLane'] at hIdx
  exact ⟨hu.2.2.2.2.1,hf.1.2.1,hIdx,hu.2.2.2.2.2.1,hf.2⟩


private theorem laterDrainScanReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first cta shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3046
      (fun lane => drainLaterWords p l (warpLane l g lane) first ++
        drainLaterGroup p l (warpLane l g lane) first (tilePrefix p first*p.heads) (cta+1) cta)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (drainScanPc true 0)
      (fun lane => outputDrainUpFrame p first true 0 lane (laterDrainSaved p first cta lane))
      shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  let thread := warpLane l g lane
  have hLane : laneOf l thread = lane := (Step.sameWarp_lane (by rw [hp.block]) hg hl).2
  have hBound := hp.shape.2.2.2.2.2
  change p.qOffset p.batch + 256 * p.batch < 2 ^ 30 at hBound
  have hFit : first+laneOf l thread < 2^31 := by rw [hLane]; omega
  have ht := cur.checkpoint lane hl
  obtain ⟨_,u,hLocal,hu,hGuard,hFrame⟩ :=
    drainLaterPrepared hp thread _ (hLane.symm ▸ hl) hFit ht
  rw [hLane] at hu hGuard
  have hGuards : Holds u.regs (drainUpGuards true lane) :=
    ⟨hGuard 0,hGuard 1,hGuard 2,hGuard 3,hGuard 4,trivial⟩
  have hRaw := ((holds_append ..).mp ht.2.2.2.2).2
  have hSaved {r : Nat} {v : Value} (hr : r ∈ drainPersistent)
      (hm : (r,v) ∈ drainLaterGroup p l thread first (tilePrefix p first*p.heads) (cta+1) cta) :
      u.regs r = some v := (hFrame r hr).trans (holds_mem hRaw hm)
  have hFacts : Holds u.regs (laterDrainSaved p first cta lane) := by
    refine ⟨hu.2.2.2.2.1,hSaved (by decide) ?_,hSaved (by decide) ?_,hSaved (by decide) ?_,
      hSaved (by decide) ?_,hSaved (by decide) ?_,hSaved (by decide) ?_,hSaved (by decide) ?_,
      hSaved (by decide) ?_,hSaved (by decide) ?_,trivial⟩
    all_goals simp [drainLaterGroup,drainLaterCommon,hLane]
  refine ⟨u,run_rtg hLocal,hu.mono ⟨?_,(holds_append ..).mpr ⟨hGuards,hFacts⟩⟩⟩
  change u.regs 7232 = some (b32 (prefixWindow (groupLaneTiles p first) 1 lane))
  rw [prefixWindow_one]
  exact hu.2.2.2.2.1

set_option maxHeartbeats 4000000 in
/-- A later drain group progresses in a maximal trace and updates its selected interval. -/
theorem laterOutputDrainRouteOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first cta shuffles votes : Nat} (hg : g < l.threads) (hc : cta < l.grid)
    (hFirst : first+31 < p.batch) (hCuQ : DrainCuQProtected p X) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3032 (drainNextFacts p l g first cta) shuffles votes ends) :
    let next := first+31
    if cta < tilePrefix p (min p.batch (next+31))*p.heads then
      Nonempty (SchedulerWarpReached l X g 3086 (drainFinishFacts p next cta)
        (shuffles+7) votes ends)
    else Nonempty (SchedulerWarpReached l X g 3032 (drainNextFacts p l g next cta)
      (shuffles+7) votes ends) := by
  let next := first+31
  let limit := tilePrefix p (min p.batch (next+31))*p.heads
  let sum := fun lane => prefixWindow (groupLaneTiles p next) 32 lane
  let F := fun lane => (7233,b32 (sum lane)) ::
    (drainUpGuards true lane ++ laterDrainSaved p next cta lane)
  obtain ⟨rd⟩ := laterDrainReadReady hp hg hFirst cur
  obtain ⟨down⟩ := laterDrainReadAndDown hp hMax hg hCuQ rd
  obtain ⟨ready⟩ := laterDrainScanReady hp hg hFirst down
  obtain ⟨scan⟩ := drainUpsOfMaximal hp hMax hg hFirst.le true
    (fun lane _ => laterDrainSavedRegs p next cta lane) ready
  have hFresh (lane : Nat) (_ : lane < 32) (item : Nat × Value) (hm : item ∈ F lane) :
      item.1 ≠ 7234 := by
    rcases List.mem_cons.mp hm with rfl | h
    · exact of_decide_eq_true rfl
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨stage,rfl⟩ := List.mem_ofFn.mp h
        exact (by decide : ∀ stage : Fin 5, drainScanGuardReg true stage ≠ 7234) stage
      · have hm := laterDrainSavedRegs p next cta lane item h
        exact fun he => (of_decide_eq_true rfl : 7234 ∉ drainRoundPersistent) (he ▸ hm)
  obtain ⟨all⟩ := scan.consumeShuffle (dst := 7234) hp hMax hg .idx
    (fun lane => b32 (sum lane)) (fun _ => 31) (fun _ => 31) hFresh (by
      intro lane hl
      have ht := scan.checkpoint lane hl
      have hModel : out kernel Assumptions.all l (warpLane l g lane) (scan.state lane) =
          out kernel [] l (warpLane l g lane) (scan.state lane) :=
        epilogue_out_all_eq_nil (.inl (by rw [ht.1]; decide))
      exact hModel.trans (drainGroupTotalTemplate hp true _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1))
  have hCount : tilePrefix p next + drainPrefix p next 31 =
      tilePrefix p (min p.batch (next+31)) := groupTiles_eq p hFirst.le (by decide)
  have hGoto (lane : Nat) (hl : lane < 32) : ∃ u,
      At u (if limit ≤ cta then 3032 else 3086) [(7230,b32 limit),(7236,b32 limit)] ∧
      (∀ r ∉ [7236,330,7230], u.regs r = (all.state lane).regs r) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane))
        (all.state lane) u := by
    have ht := all.checkpoint lane hl
    have hSrc : sum (shflSource .idx lane 31 31).1 = drainPrefix p next 31 := by
      rw [shflSource_idx lane (by decide)]
      exact prefixWindow_warp _ (by decide)
    have hFixed : Holds (all.state lane).regs (laterDrainSaved p next cta lane) :=
      ((holds_append ..).mp ht.2.2.2.2.2.2.2).2
    exact drainLaterRouteLocal hp hc hCount (ht.mono
      ⟨hFixed.2.2.2.2.2.2.1,hSrc ▸ ht.2.2.2.2.1,hFixed.2.2.2.2.2.2.2.2.1,
        hFixed.2.2.2.2.2.2.2.1,trivial⟩)
  have saved (lane : Nat) (hl : lane < 32) {u : TState}
      (hFrame : ∀ r ∉ [7236,330,7230], u.regs r = (all.state lane).regs r)
      {r : Nat} {v : Value} (hNot : r ∉ [7236,330,7230])
      (hFact : (r,v) ∈ laterDrainSaved p next cta lane) :
      u.regs r = some v := by
    have ht := all.checkpoint lane hl
    exact (hFrame r hNot).trans (holds_mem ((holds_append ..).mp ht.2.2.2.2.2.2.2).2 hFact)
  change if cta < limit then _ else _
  by_cases hFound : cta < limit
  · rw [ite_eq_left hFound]
    apply all.advanceLocal (pc' := 3086) (G := drainFinishFacts p next cta)
    intro lane hl
    obtain ⟨u,hu,hFrame,hLocal⟩ := hGoto lane hl
    rw [ite_eq_right (Nat.not_le_of_gt hFound)] at hu
    have ht := all.checkpoint lane hl
    have hSum : sum lane = drainPrefix p next lane := prefixWindow_warp _ hl
    have hSrc : sum (shflSource .idx lane 31 31).1 = drainPrefix p next 31 := by
      rw [shflSource_idx lane (by decide)]
      exact prefixWindow_warp _ (by decide)
    refine ⟨u,hLocal,hu.mono ?_⟩
    unfold drainFinishFacts
    refine ⟨saved lane hl hFrame (by decide) ?_,saved lane hl hFrame (by decide) ?_,
      (hFrame 7234 (by decide)).trans (hSrc ▸ ht.2.2.2.2.1),
      saved lane hl hFrame (by decide) ?_,hu.2.2.2.2.2.1,
      (hFrame 7233 (by decide)).trans (hSum ▸ ht.2.2.2.2.2.1),
      saved lane hl hFrame (by decide) ?_,saved lane hl hFrame (by decide) ?_,
      saved lane hl hFrame (by decide) ?_,trivial⟩
    all_goals simp [laterDrainSaved]
  · rw [ite_eq_right hFound]
    apply all.advanceLocal (pc' := 3032) (G := drainNextFacts p l g next cta)
    intro lane hl
    obtain ⟨u,hu,hFrame,hLocal⟩ := hGoto lane hl
    rw [ite_eq_left (Nat.le_of_not_gt hFound)] at hu
    have hLane : laneOf l (warpLane l g lane) = lane :=
      (Step.sameWarp_lane (by rw [hp.block]) hg hl).2
    refine ⟨u,hLocal,hu.mono ?_⟩
    unfold drainNextFacts drainLaterEntry drainLaterCommon
    rw [hLane]
    refine ⟨saved lane hl hFrame (by decide) ?_,saved lane hl hFrame (by decide) ?_,
      saved lane hl hFrame (by decide) ?_,saved lane hl hFrame (by decide) ?_,
      saved lane hl hFrame (by decide) ?_,hu.2.2.2.2.1,
      saved lane hl hFrame (by decide) ?_,saved lane hl hFrame (by decide) ?_,
      saved lane hl hFrame (by decide) ?_,trivial⟩
    all_goals simp [laterDrainSaved]

/-- A backedge consumes 31 requests. A CTA still in the work interval must
reach the selected group and perform the terminal ballot and exit. -/
theorem outputDrainRestExits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g cta votes : Nat} (hg : g < l.threads) (hc : cta < l.grid)
    (hActive : cta < tilePrefix p p.batch * p.heads) (hCuQ : DrainCuQProtected p X)
    {ends : Nat → Option TState} (first shuffles : Nat)
    (hPast : tilePrefix p (min p.batch (first+31)) * p.heads ≤ cta)
    (cur : SchedulerWarpReached l X g 3032 (drainNextFacts p l g first cta) shuffles votes ends) :
    ∀ lane < 32, Thread.Exited X (warpLane l g lane) := by
  have hGroup : first+31 < p.batch := by
    by_contra! hNo
    rw [Nat.min_eq_left hNo] at hPast
    omega
  have hLow : tilePrefix p (first+31) * p.heads ≤ cta := by
    rwa [Nat.min_eq_right hGroup.le] at hPast
  have hNext := laterOutputDrainRouteOfMaximal hp hMax hg hc hGroup hCuQ cur
  by_cases hFound : cta < tilePrefix p (min p.batch (first+31+31)) * p.heads
  · rw [ite_eq_left hFound] at hNext
    obtain ⟨ready⟩ := hNext
    exact ready.selectedDrainGroupExits hp hMax hg hc hGroup hLow hFound
  · rw [ite_eq_right hFound] at hNext
    obtain ⟨again⟩ := hNext
    exact outputDrainRestExits hp hMax hg hc hActive hCuQ (first+31) (shuffles+7)
      (Nat.le_of_not_gt hFound) again
termination_by p.batch-first
decreasing_by omega

/-- The actual final drain and exit follow from both stages of output writeback. -/
theorem outputDrainExitsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    (hActive : g/l.block < tilePrefix p p.batch * p.heads)
    (hWriteback : OutputWritebackDrained p l X g) :
    Thread.Exited X g := by
  obtain ⟨shuffles,ends,hRoute⟩ := firstOutputDrainRouteOfMaximal hp hMax hg hCuQ hWriteback
  have hc := NamedBar.cta_lt hg
  have hExit : ∀ lane < 32, Thread.Exited X (warpLane l g lane) := by
    by_cases hFirst : g/l.block < tilePrefix p (min p.batch 31) * p.heads
    · rw [ite_eq_left hFirst] at hRoute
      obtain ⟨ready⟩ := hRoute
      have hLow : tilePrefix p 0 * p.heads ≤ g/l.block := by simp [tilePrefix]
      exact ready.selectedDrainGroupExits hp hMax hg hc hp.shape.1 hLow
        (by simpa only [Nat.zero_add] using hFirst)
    · rw [ite_eq_right hFirst] at hRoute
      obtain ⟨again⟩ := hRoute
      exact outputDrainRestExits hp hMax hg hc hActive hCuQ 0 (shuffles+7)
        (by simpa only [Nat.zero_add] using Nat.le_of_not_gt hFirst) again
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  exact hSelf ▸ hExit lane hl

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
