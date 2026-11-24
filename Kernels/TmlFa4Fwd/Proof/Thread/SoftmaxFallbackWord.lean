-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackRoute
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxIdleProgress
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Proof.NoCancellation
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow Prologue Epilogue Softmax

/-- The softmax scheduler's optional lookup on entry to a later request group. -/
@[no_expose] def SoftmaxFallbackCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop := X.get i = some ⟨3169, .rd a bytes⟩

def SoftmaxFallbackAddresses (p : Params) (X : Execution) : Prop :=
  ∀ i a bytes, SoftmaxFallbackCuQRead X i a bytes →
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4}

private theorem noSoftmaxFallbackAfterSearch {l : Launch} {X : Execution} {g pos j : Nat}
    {s : TState} {ending : Option TState} (hPc : 3212 ≤ s.pc)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hj : pos ≤ j) {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some ⟨3169,.rd a bytes⟩) : False := by
  have hCode : (kernel.code.drop 3212).all (fun i => staysPastEvent 3212 i.op) = true := by
    decide +kernel
  have hSeg : Assumptions.swExp2Sites.all (fun site =>
      match PTX.Assumption.cuteExp2.matchAt kernel site with
      | some seg => decide (3212 ≤ seg.stop)
      | none => false) = true := by decide +kernel
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hr
  have hMem : (⟨3169,.rd a bytes⟩ : Event) ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := j-pos)
    rw [List.getElem?_drop,Nat.add_sub_of_le hj]
    exact he
  exact (by decide : ¬ 3212 ≤ 3169) (eventTailEvents hCode hSeg hWalk hPc _ hMem)

private theorem softmaxFallbackReadOfComplete {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hCuQ : DrainCuQProtected p X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    {src j : Nat} (hSrc : src < 32) {a : Acc} {bytes : List (Option Byte)}
    (he : SoftmaxFallbackCuQRead X (warpLane l g src,j) a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} := by
  let thread := warpLane l g src
  let warp : Fin 8 := ⟨warpIndex l g, hw⟩
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hGet : X.get (thread,j) = some ⟨3169,.rd a bytes⟩ := he
  obtain ⟨ends, entry, hFollow⟩ :=
    firstSchedulerRouteOfEvent hp hX hg hw hSrc hCuQ hGet (show 3150 < 3169 by decide)
  by_cases hFirst : g/l.block < tilePrefix p (min p.batch 31)*p.heads
  · have hs : 3212 ≤ (entry.state src).pc := by
      rw [(entry.checkpoint src hSrc).1, ite_eq_left hFirst]
    exact (noSoftmaxFallbackAfterSearch hs
      ((entry.continuation src hSrc).after_local_nonempty
        (entry.localSteps src hSrc) hFollow.nonempty)
      hFollow.before hGet).elim
  have hEnds (lane : Nat) (hl : lane < 32) : ends lane = none := by
    have hThread := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    obtain ⟨pc,hExit⟩ := (hDone.1 (warpLane l g lane) hThread).resolve_left (noCanceled hX)
    let index := (X.tr (warpLane l g lane)).length-1
    have hExitGet : X.get (warpLane l g lane,index) = some ⟨pc,.exit⟩ := by
      simpa only [List.getLast?_eq_getElem?,Execution.get,index] using hExit
    have hPos : entry.pos lane ≤ index := by
      by_contra! hLt
      exact hFollow.noExit lane hl index hLt pc hExitGet
    have hSuffix : ((X.tr (warpLane l g lane)).drop (entry.pos lane))[index-entry.pos lane]? =
        some ⟨pc,.exit⟩ := by
      rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
      exact hExitGet
    have hr := entry.continuation lane hl
    cases h : ends lane with
    | none => rfl
    | some out =>
      rw [h] at hr
      exact (hr.no_exit hSuffix).elim
  have hStart : ∃ initial : SchedulerWarpAt l X g 3158 (fun lane =>
      fallbackScanFacts p l (warpLane l g lane) warp 0
        (tilePrefix p (min p.batch (0+31))*p.heads)) 10 0 ends, initial.pos = entry.pos := by
    obtain ⟨r,hR⟩ := entry.advanceLocalAt (pc' := 3155) (G := firstRouteFacts p l g warp) (by
      intro lane hl
      refine ⟨entry.state lane, .refl, ?_⟩
      simpa only [ite_eq_right hFirst] using entry.checkpoint lane hl)
    obtain ⟨s,hS,_⟩ := warpFallbackStartPreserving hp hg r
    exact ⟨s,hS.trans hR⟩
  obtain ⟨initial,hInitial⟩ := hStart
  have hReadWords : CuQReadsFromLaunch p X :=
    fun index hi => cuQWordReadsFromLaunchOfProtected hp hX hi (hCuQ index hi)
  suffices all : ∀ fuel first shuffles, p.batch-first = fuel → first < p.batch →
      ∀ cur : SchedulerWarpAt l X g 3158 (fun lane =>
        fallbackScanFacts p l (warpLane l g lane) warp first
          (tilePrefix p (min p.batch (first+31))*p.heads)) shuffles 0 ends,
        cur.pos src ≤ j →
        ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} by
    exact all _ 0 10 rfl hp.shape.1 initial (hInitial.symm ▸ hFollow.before)
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first shuffles hFuel hBound cur hLo
    obtain ⟨ready,hPos,_⟩ := warpFallbackAdvancePreserving hp hBound cur
    by_cases hClip : p.batch ≤ first+31
    · obtain ⟨exhausted,hExhausted⟩ := ready.advanceLocalAt (pc' := 3209)
        (G := fun lane => fallbackAdvanceFacts p l (warpLane l g lane) warp first
          (tilePrefix p (min p.batch (first+31))*p.heads)) (by
            intro lane hl
            refine ⟨ready.state lane,.refl,?_⟩
            simpa only [ite_eq_left hClip] using ready.checkpoint lane hl)
      obtain ⟨idle,hIdle,_⟩ := idleTerminalAtFromExhausted hp hg hClip exhausted
      have hRun := (hEnds src hSrc ▸ idle.continuation src hSrc).after_local
        (idle.localSteps src hSrc)
      exact (noSoftmaxFallbackAfterSearch (by rw [(idle.checkpoint src hSrc).1]; decide)
        hRun (hIdle.symm ▸ hExhausted.symm ▸ hPos.symm ▸ hLo) hGet).elim
    have hMore : first+31 < p.batch := Nat.lt_of_not_ge hClip
    let cutoff := tilePrefix p (first+31)*p.heads
    obtain ⟨openGroup,hOpen⟩ := ready.advanceLocalAt (pc' := 3163)
      (G := fun lane => fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff) (by
        intro lane hl
        refine ⟨ready.state lane, .refl, ?_⟩
        simpa only [ite_eq_right hClip, Nat.min_eq_right hMore.le] using ready.checkpoint lane hl)
    obtain ⟨down,hDown,hRead,_⟩ :=
      warpFallbackDownRecorded hp hX hg hMore hReadWords openGroup
        (src := src) (eventIndex := j) (target := ⟨3212,.exit⟩) (.inl hEnds) (by decide)
    obtain ⟨tiles,hTiles,_⟩ := warpFallbackTilesPreserving hp hg hMore down
    obtain ⟨start,hStart,_⟩ := warpFallbackFoldStartPreserving tiles
    obtain ⟨folded,hFold,_⟩ := warpFallbackFoldRecorded hp hX hg hMore.le start
      (src := src) (index := j) (target := ⟨3212,.exit⟩) (.inl hEnds) (by decide)
    obtain ⟨next,hNext,hLen,_⟩ := warpFallbackRouteToRecorded hp hX hg hMore folded
      (src := src) (index := j) (target := ⟨3212,.exit⟩) (.inl hEnds) (by decide)
    by_cases hHi : j < next.pos src
    · let ix := first+31+src
      let base := openGroup.pos src
      let afterRead := if ix ≤ p.batch then base+1 else base
      have hBase : base ≤ j := by dsimp [base]; rwa [hOpen,hPos]
      have hLength : next.pos src = afterRead+7 := by
        rw [hNext,hFold,hStart,hTiles,hDown]
      have hKeep : ((X.tr thread).take afterRead).countP Execution.isShfl =
          ((X.tr thread).take base).countP Execution.isShfl := by
        by_cases hIndex : ix ≤ p.batch
        · simp only [afterRead,ite_eq_left hIndex,List.take_add_one]
          rw [show (X.tr thread)[base]? = _ from hRead src hSrc hIndex]
          simp [Execution.isShfl]
        · simp [afterRead,hIndex]
      by_cases hActual : j < afterRead
      · by_cases hIndex : ix ≤ p.batch
        · have hAt : j = base := by simp [afterRead,hIndex] at hActual; omega
          have h := hRead src hSrc hIndex
          have hActualGet := hAt ▸ hGet
          have hAcc := (Kind.rd.inj (congrArg Event.kind (Option.some.inj
            (hActualGet.symm.trans h)))).1
          exact ⟨ix,hIndex,hAcc⟩
        · simp [afterRead,hIndex] at hActual
          omega
      have hOld := (hKeep.trans (openGroup.ordinals.shfl src hSrc))
      have hNew := next.ordinals.shfl src hSrc
      change ((X.tr thread).take (next.pos src)).countP Execution.isShfl =
        shuffles+1+5+1 at hNew
      have hCounts : ((X.tr thread).take (next.pos src)).countP Execution.isShfl =
          ((X.tr thread).take afterRead).countP Execution.isShfl + (next.pos src-afterRead) := by
        omega
      cases getIsShuffleBetween (hLen src hSrc) (Nat.le_of_not_gt hActual) hHi hCounts hGet
    let bound := tilePrefix p (min p.batch (first+31+31))*p.heads
    by_cases hCut : tilePrefix p (min p.batch (first+31+31))*p.heads ≤ g/l.block
    · obtain ⟨again,hAgain⟩ := next.advanceLocalAt (pc' := 3158)
        (G := fun lane => fallbackScanFacts p l (warpLane l g lane) warp (first+31) bound) (by
          intro lane hl
          refine ⟨next.state lane, .refl, ?_⟩
          simpa only [ite_eq_left hCut] using next.checkpoint lane hl)
      exact ih (p.batch-(first+31)) (by omega) (first+31) _ rfl hMore again
        (hAgain.symm ▸ Nat.le_of_not_gt hHi)
    · have hs : 3212 ≤ (next.state src).pc := by
        rw [(next.checkpoint src hSrc).1, ite_eq_right hCut]
      have hRun := (hEnds src hSrc ▸ next.continuation src hSrc).after_local
        (next.localSteps src hSrc)
      exact (noSoftmaxFallbackAfterSearch hs hRun (Nat.le_of_not_gt hHi) hGet).elim

/-- The softmax fallback reads an in-range launch word, including in incomplete prefixes. -/
theorem softmaxFallbackAddressesOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hProtected : ∀ Y, Consistent l kernel Assumptions.all m Y → DrainCuQProtected p Y)
    (hComplete : ∀ Y, Maximal l kernel Assumptions.all m Y → Complete l Y) :
    SoftmaxFallbackAddresses p X := by
  intro i a bytes hRead
  obtain ⟨g,j⟩ := i
  have he : X.get (g,j) = some ⟨3169,.rd a bytes⟩ := hRead
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < 3169 by decide)
    (show 3169 ∉ registerHintSites by decide)
  have hw : warpIndex l g < 8 := by
    change roleBodyPc (warpIndex l g) 3169 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨Y,hXY,hMax⟩ := maximalExtension hp hX
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  exact softmaxFallbackReadOfComplete hp hMax.1 (hComplete Y hMax) (hProtected Y hMax.1)
    hg hw hl (hLane.symm ▸ Execution.le_get hXY he)

end PTX.Kernels.TmlFa4Fwd.Thread
