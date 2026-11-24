-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderStartupPrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderSchedule
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private def withShuffleCount {l : Launch} {X : Execution} {g pc old new votes : Nat}
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g pc F old votes ends) (h : old = new) :
    SchedulerWarpAt l X g pc F new votes ends :=
  ⟨cur.pos, cur.before, cur.state, h ▸ cur.ordinals, cur.continuation, cur.localSteps,
    cur.checkpoint⟩

private def LoaderPrefixFallbackChoice (p : Params) (l : Launch) (X : Execution)
    (g warp : Nat) (ends : Nat → Option TState) (src index : Nat) (target : Event) : Prop :=
  (tilePrefix p p.batch * p.heads ≤ g / l.block ∧
    ∃ shuffles, ∃ idle : SchedulerWarpAt l X g 1862 (fun _ => loaderIdleDrainFacts l warp)
      shuffles 0 ends, WarpFollowsEvent l X g idle.pos src index target) ∨
  ∃ group, 0 < group ∧ group < p.batch ∧ group % 31 = 0 ∧
    tilePrefix p group * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (min p.batch (group + 31)) * p.heads ∧
      ∃ chosen : SchedulerWarpAt l X g 288 (loaderLaterChoiceFacts p l g warp group)
        (10 + 7 * (group / 31)) 0 ends,
        WarpFollowsEvent l X g chosen.pos src index target

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Active fallback advances whole groups before a recorded downstream event.
The returned group number fixes how many fallback collectives have occurred. -/
private theorem loaderFallbackTo {g warp first src index : Nat} {target : Event}
    (hg : g < l.threads) (hPc : 283 < target.pc) (hf : first < p.batch) (hAligned : first % 31 = 0)
    (hPast : tilePrefix p (min p.batch (first + 31)) * p.heads ≤ g / l.block)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp first)
      (10 + 7 * (first / 31)) 0 ends) (hFollow : WarpFollowsEvent l X g cur.pos src index target) :
    LoaderPrefixFallbackChoice p l X g warp ends src index target := by
  suffices all : ∀ fuel first, p.batch - first = fuel → first < p.batch → first % 31 = 0 →
      tilePrefix p (min p.batch (first + 31)) * p.heads ≤ g / l.block →
      ∀ cur : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp first)
        (10 + 7 * (first / 31)) 0 ends,
      WarpFollowsEvent l X g cur.pos src index target →
      LoaderPrefixFallbackChoice p l X g warp ends src index target by
    exact all _ first rfl hf hAligned hPast cur hFollow
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first hfuel hf hAligned hPast cur hFollow
    have hAdvance := loaderFallbackAdvanceAt hp hf cur
    by_cases hClip : p.batch ≤ first + 31
    · rw [ite_eq_left hClip] at hAdvance
      obtain ⟨ready, hPos⟩ := hAdvance
      obtain ⟨endAt, hEnd⟩ := loaderFallbackExhaustedAt hp hg hClip ready
      obtain ⟨idle, hIdle⟩ := loaderIdleWarpAt endAt
      exact .inl ⟨by simpa only [Nat.min_eq_left hClip] using hPast, _, idle,
        hIdle.symm ▸ hEnd.symm ▸ hPos.symm ▸ hFollow⟩
    have hNext := Nat.lt_of_not_ge hClip
    rw [ite_eq_right (by omega : ¬ p.batch ≤ first + 31)] at hAdvance
    obtain ⟨ready, hPos⟩ := hAdvance
    have hReady : WarpFollowsEvent l X g ready.pos src index target := hPos.symm ▸ hFollow
    obtain ⟨down, hd⟩ := loaderLaterWarpCuQTo hp hX hg hNext ready (.inr hReady)
      (by omega) hProtected
    obtain ⟨scan, hs⟩ := loaderLaterScanTo hp hX hg hNext down (.inr (hd hReady)) (by omega)
    have hScan := hs (hd hReady)
    have hLo : tilePrefix p (first + 31) * p.heads ≤ g / l.block := by
      simpa only [Nat.min_eq_right hNext.le] using hPast
    have hMod : (first + 31) % 31 = 0 := by omega
    have hRank : 10 + 7 * (first / 31) + 1 + 5 + 1 = 10 + 7 * ((first + 31) / 31) := by omega
    rcases loaderLaterRouteTo hp hX hg hNext scan (.inr hScan) hPc with
      ⟨hPast', next, hStep⟩ | ⟨hFound, next, hStep⟩
    · have hFollow' := hStep hScan
      exact ih (p.batch - (first + 31)) (by omega) (first + 31) rfl hNext hMod hPast'
        (withShuffleCount next hRank) hFollow'
    · have hFollow' := hStep hScan
      exact .inr ⟨first + 31, by omega, hNext, hMod, hLo, hFound,
        withShuffleCount next hRank, hFollow'⟩

/-- Any active loader CTA chooses its actual batch before an observed downstream event. -/
theorem loaderActiveBatchOfEvent {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hSrc : src < 32)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hActive : g / l.block < tilePrefix p p.batch * p.heads) {target : Event}
    (he : X.get (warpLane l g src, j) = some target) (hPc : 297 < target.pc) :
    ∃ first batch, first = 31 * (batch / 31) ∧ first ≤ batch ∧ batch < first + 31 ∧
      batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ ending, ∃ cur : SchedulerWarpAt l X g 302
        (loaderChosenFacts p l g (warpIndex l g) first batch)
        (10 + 7 * (batch / 31)) 1 ending,
        WarpFollowsEvent l X g cur.pos src j target := by
  by_cases hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads
  · obtain ⟨batch, hIn, hLo, hHi, ending, cur, hFollows⟩ :=
      loaderFirstBatchOfEvent hp hX hg hw hSrc hProtected hFirst he hPc
    have hBound := hIn.trans_le (Nat.min_le_right ..)
    have hMajor : batch / 31 = 0 := Nat.div_eq_of_lt hBound
    refine ⟨0, batch, by simp [hMajor], Nat.zero_le _, hBound,
      hIn.trans_le (Nat.min_le_left ..), hLo, hHi, ending, ?_⟩
    rw [hMajor]
    exact ⟨cur, hFollows⟩
  have hRoute := loaderFirstScheduleOfEvent hp hX hg hw hSrc hProtected he (by omega)
  rw [ite_eq_right hFirst] at hRoute
  obtain ⟨ending, cur, hFollows⟩ := hRoute
  obtain ⟨start, hPos⟩ := loaderFallbackStartAt hp hg cur
  obtain ⟨group, _, hgBatch, hAlign, hLo, hHi, chosen, hChosen⟩ :=
    (loaderFallbackTo hp hX hg (by omega) hp.shape.1 (by decide)
      (Nat.le_of_not_gt hFirst) hProtected start (hPos.symm ▸ hFollows)).resolve_left
        (fun h => Nat.not_le_of_lt hActive h.1)
  have hAll := Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (Nat.min_le_left p.batch (group + 31)))
  obtain ⟨batch, ⟨hb, hBatchLo, hBatchHi⟩, _⟩ := tileBatch_existsUnique p (hHi.trans_le hAll)
  have hStart : group ≤ batch := by
    by_contra! h
    have hLe := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch + 1 ≤ group by omega))
    omega
  have hRange : batch < group + 31 := by
    by_contra! h
    have hMin : min p.batch (group + 31) ≤ batch := (Nat.min_le_right ..).trans h
    have hLe := Nat.mul_le_mul_right p.heads (tilePrefix_mono p hMin)
    omega
  have hMajor : group / 31 = batch / 31 := by omega
  have hGroup : group = 31 * (batch / 31) := by omega
  obtain ⟨ready, hReadyPos⟩ :=
    loaderGroupBallotReadyAt hp hg hStart hRange hb hBatchLo hBatchHi chosen
  have hReady : WarpFollowsEvent l X g ready.pos src j target := hReadyPos.symm ▸ hChosen
  obtain ⟨selected, hStep⟩ :=
    loaderSelectBatchTo hp hX hg hStart hRange hb ready (.inr hReady) hPc
  have hs := hStep hReady
  have hSelectedCount : 10 + 7 * (group / 31) = 10 + 7 * (batch / 31) := by rw [hMajor]
  exact ⟨group, batch, hGroup, hStart, hRange, hb, hBatchLo, hBatchHi, ending,
    withShuffleCount selected hSelectedCount, hs⟩

/-- Any actual event between work selection and the idle drain belongs to an active CTA. -/
theorem loaderPrefixEventRequiresActiveTile {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {target : Event}
    (he : X.get (warpLane l g src, j) = some target) (hLow : 297 < target.pc)
    (hHigh : target.pc < 1862) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  by_contra! hInactive
  have hFirst : ¬ g / l.block < tilePrefix p (min p.batch 31) * p.heads :=
    Nat.not_lt_of_ge ((Nat.mul_le_mul_right p.heads
      (tilePrefix_mono p (Nat.min_le_left p.batch 31))).trans hInactive)
  have hRoute := loaderFirstScheduleOfEvent hp hX hg hw hSrc hProtected he (by omega)
  rw [ite_eq_right hFirst] at hRoute
  obtain ⟨ending, cur, hFollows⟩ := hRoute
  obtain ⟨start, hPos⟩ := loaderFallbackStartAt hp hg cur
  have hFallback := loaderFallbackTo hp hX hg (by omega) hp.shape.1 (by decide)
    (Nat.le_of_not_gt hFirst) hProtected start (hPos.symm ▸ hFollows)
  rcases hFallback with ⟨_, shuffles, idle, hIdle⟩ | ⟨group, _, hGroup, _, _, hEnd, _⟩
  · have hAfter : ((X.tr (warpLane l g src)).drop (idle.pos src))[j - idle.pos src]? =
        some target := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hIdle.before]
      exact he
    have hEvent := List.mem_of_getElem? hAfter
    have hNonempty : (X.tr (warpLane l g src)).drop (idle.pos src) ≠ [] := by
      intro h
      rw [h] at hEvent
      cases hEvent
    obtain ⟨_, hWalk⟩ := Mma.walkFromRun ((idle.continuation src hSrc).after_local_nonempty
      (idle.localSteps src hSrc) hNonempty)
    let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
    have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
    have ht := idle.checkpoint src hSrc
    have hRegs : Holds (idle.state src).regs
        [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] := by
      rw [hWarp]
      exact ⟨holds_lookup ht.2.2.2.2 rfl, holds_lookup ht.2.2.2.2 rfl, trivial⟩
    have hBranches : ∀ branch, ((kernel.code.drop 1862).take (1901 - 1862)).all
        (fun ins => loaderPipelineCutOp 1862 1901 branch [2535, 1062] ins.op) = true := by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl
    have hPc := (Epilogue.loaderWalkEventRange warp (by decide) (by rw [ht.1]; decide)
      (ringShapeOfAt ht) hRegs hBranches hWalk target hEvent).1
    omega
  · have hBound := Nat.mul_le_mul_right p.heads
      (tilePrefix_mono p (Nat.min_le_left p.batch (group + 31)))
    omega

/-- Specialize the prefix result to an issuing lane's own trace. -/
theorem loaderOwnPrefixEventRequiresActiveTile {g j : Nat} (hw : 14 ≤ warpIndex l g)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {target : Event}
    (he : X.get (g, j) = some target) (hLow : 297 < target.pc) (hHigh : target.pc < 1862) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  let lane := laneOf l g
  have hSelf : warpLane l g lane = g := by
    unfold warpLane lane laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  exact loaderPrefixEventRequiresActiveTile hp hX (event_thread_lt hX he) hw hl hProtected
    (hSelf.symm ▸ he) hLow hHigh

end
end PTX.Kernels.TmlFa4Fwd.Loader
