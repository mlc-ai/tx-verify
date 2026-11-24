-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputFallbackCuQReadClass
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.EpilogueSearchWarp
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.LoaderStartupPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderSchedule
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
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
import Kernels.TmlFa4Fwd.Proof.NoCancellation
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (loaderFirstScheduleOfEvent loaderFallbackStartAt loaderFallbackAdvanceAt
    loaderFallbackExhaustedAt loaderIdleWarpAt loaderLaterWarpCuQRecorded
    loaderLaterScanWithLength loaderLaterRouteWithLength loaderFallbackFacts)

@[no_expose] def LoaderFallbackCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨245,.rd a bytes⟩

def LoaderFallbackAddresses (p : Params) (X : Execution) : Prop :=
  ∀ i a bytes, LoaderFallbackCuQRead X i a bytes →
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4*index), size := 4}

private theorem noLoaderFallbackAfterSelection {l : Launch} {X : Execution} {g pos j : Nat}
    {s : TState} (hPc : 288 ≤ s.pc)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) none)
    (hj : pos ≤ j) {a : Acc} {bytes : List (Option Byte)}
    (he : LoaderFallbackCuQRead X (g,j) a bytes) : False := by
  have hCode : (kernel.code.drop 288).all (fun i => staysPastEvent 288 i.op) = true := by
    decide +kernel
  have hSeg : Assumptions.swExp2Sites.all (fun site =>
      match PTX.Assumption.cuteExp2.matchAt kernel site with
      | some seg => decide (288 ≤ seg.stop)
      | none => false) = true := by decide +kernel
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hr
  have hMem : (⟨245,.rd a bytes⟩ : Event) ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := j-pos)
    rw [List.getElem?_drop,Nat.add_sub_of_le hj]
    exact he
  have hFloor := eventTailEventsOfSegmentFloor hCode (fun site _ hm seg hMatch => by
    have h := List.all_eq_true.mp hSeg site hm
    rw [hMatch] at h
    exact of_decide_eq_true h) hWalk hPc _ hMem
  exact (by decide : ¬ 288 ≤ 245) hFloor

private theorem loaderFallbackReadOfComplete {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hCuQ : DrainCuQProtected p X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    {src j : Nat} (hSrc : src < 32) {a : Acc} {bytes : List (Option Byte)}
    (he : LoaderFallbackCuQRead X (warpLane l g src,j) a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4*index), size := 4} := by
  let thread := warpLane l g src
  let warp := warpIndex l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hGet : X.get (thread,j) = some ⟨245,.rd a bytes⟩ := he
  have hEarly := loaderFirstScheduleOfEvent hp hX hg hw hSrc hCuQ hGet (show 226 < 245 by decide)
  let cta := g/l.block
  by_cases hFirst : cta < tilePrefix p (min p.batch 31)*p.heads
  · rw [ite_eq_left hFirst] at hEarly
    obtain ⟨ends,found,hFollow⟩ := hEarly
    have hr := (found.continuation src hSrc).after_local_nonempty
      (found.localSteps src hSrc) hFollow.nonempty
    have hDoneRun : ends src = none := by
      have hThread := (Step.sameWarp_lane hBlock hg hSrc).1.1.2.1
      obtain ⟨pc,hExit⟩ := (hDone.1 thread hThread).resolve_left (noCanceled hX)
      let index := (X.tr thread).length-1
      have hExitGet : X.get (thread,index) = some ⟨pc,.exit⟩ := by
        simpa only [List.getLast?_eq_getElem?,Execution.get,index] using hExit
      have hPos : found.pos src ≤ index := by
        by_contra! hLt
        exact hFollow.noExit src hSrc index hLt pc hExitGet
      have hSuffix : ((X.tr thread).drop (found.pos src))[index-found.pos src]? =
          some ⟨pc,.exit⟩ := by
        rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
        exact hExitGet
      cases h : ends src with
      | none => rfl
      | some out =>
        rw [h] at hr
        exact (hr.no_exit hSuffix).elim
    exact (noLoaderFallbackAfterSelection (found.checkpoint src hSrc).1.ge
      (hDoneRun ▸ hr) hFollow.before he).elim
  rw [ite_eq_right hFirst] at hEarly
  obtain ⟨ends,entry,hFollow⟩ := hEarly
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
  have runAt {pc shuffles votes : Nat} {facts : Nat → List (Nat × Value)}
      (cur : SchedulerWarpAt l X g pc facts shuffles votes ends) :=
    (show Run kernel Assumptions.all l thread (cur.before src)
      ((X.tr thread).drop (cur.pos src)) none from
        hEnds src hSrc ▸ cur.continuation src hSrc).after_local (cur.localSteps src hSrc)
  have posBound {pc shuffles votes : Nat} {facts : Nat → List (Nat × Value)}
      (cur : SchedulerWarpAt l X g pc facts shuffles votes ends) :
      cur.pos src ≤ (X.tr thread).length := by
    by_contra! h
    have hr := runAt cur
    rw [List.drop_eq_nil_iff.mpr h.le] at hr
    cases hr
  obtain ⟨initial,hInitial⟩ := loaderFallbackStartAt hp hg entry
  suffices all : ∀ fuel first shuffles, p.batch-first = fuel → first < p.batch →
      ∀ cur : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp first) shuffles 0 ends,
        cur.pos src ≤ j →
        ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4*index), size := 4} by
    exact all _ 0 10 rfl hp.shape.1 initial (hInitial.symm ▸ hFollow.before)
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first shuffles hFuel hBound cur hLo
    have hAdvance := loaderFallbackAdvanceAt hp hBound cur
    by_cases hClip : p.batch ≤ first+31
    · rw [ite_eq_left hClip] at hAdvance
      obtain ⟨ready,hPos⟩ := hAdvance
      obtain ⟨last,hLast⟩ := loaderFallbackExhaustedAt hp hg hClip ready
      obtain ⟨idle,hIdle⟩ := loaderIdleWarpAt last
      exact (noLoaderFallbackAfterSelection (by rw [(idle.checkpoint src hSrc).1]; decide)
        (runAt idle) (hIdle.symm ▸ hLast.symm ▸ hPos.symm ▸ hLo) he).elim
    have hMore : first+31 < p.batch := Nat.lt_of_not_ge hClip
    rw [ite_eq_right hClip] at hAdvance
    obtain ⟨ready,hPos⟩ := hAdvance
    obtain ⟨down,hDown,hRead,_⟩ := loaderLaterWarpCuQRecorded hp hX hg hMore ready
      (src := src) (index := j) (target := ⟨284,.exit⟩) (.inl hEnds) (by decide) hCuQ
    obtain ⟨scan,hScan,_⟩ := loaderLaterScanWithLength hp hX hg hMore down
      (src := src) (index := j) (target := ⟨284,.exit⟩) (.inl hEnds) (by decide)
    let ix := first+31+src
    let start := (if ix ≤ p.batch then ready.pos src+1 else ready.pos src)
    have hDownLen : down.pos src = start+1 := congrFun hDown src
    have hScanLen : scan.pos src = down.pos src+5 := congrFun hScan src
    have inGroup {pc : Nat} {facts : Nat → List (Nat × Value)}
        (next : SchedulerWarpAt l X g pc facts (shuffles+1+5+1) 0 ends)
        (hNext : next.pos = fun lane => scan.pos lane+1) (hHi : j < next.pos src) :
        ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4*index), size := 4} := by
      have hReadyLo : ready.pos src ≤ j := hPos.symm ▸ hLo
      have hNextLen : next.pos src = scan.pos src+1 := congrFun hNext src
      have hShift (mark : Event → Bool) (hNot : ∀ a bytes, mark ⟨245,.rd a bytes⟩ = false) :
          ((X.tr thread).take start).countP mark =
            ((X.tr thread).take (ready.pos src)).countP mark := by
        by_cases hReadIndex : ix ≤ p.batch
        · simp only [start,ite_eq_left hReadIndex,List.take_add_one]
          rw [show (X.tr thread)[ready.pos src]? = _ from hRead src hSrc hReadIndex]
          simp [hNot]
        · simp [start,hReadIndex]
      by_cases hReadAt : j < start
      · by_cases hIndex : ix ≤ p.batch
        · have hLt : j = ready.pos src := by simp [start,hIndex] at hReadAt; omega
          have hEvent := hRead src hSrc hIndex
          rw [hLt] at hGet
          have hShape := congrArg Event.kind (Option.some.inj (hEvent.symm.trans hGet))
          exact ⟨ix,hIndex,(Kind.rd.inj hShape).1.symm⟩
        · simp [start,hIndex] at hReadAt
          omega
      have hRank := next.ordinals.shfl src hSrc
      change ((X.tr thread).take (next.pos src)).countP Execution.isShfl =
        shuffles+1+5+1 at hRank
      have hStartRank := (hShift Execution.isShfl (fun _ _ => rfl)).trans
        (ready.ordinals.shfl src hSrc)
      change ((X.tr thread).take start).countP Execution.isShfl = shuffles at hStartRank
      have hCounts : ((X.tr thread).take (next.pos src)).countP Execution.isShfl =
          ((X.tr thread).take start).countP Execution.isShfl + (next.pos src-start) := by omega
      have hKind := getIsShuffleBetween (posBound next) (Nat.le_of_not_gt hReadAt) hHi
        hCounts hGet
      cases hKind
    rcases loaderLaterRouteWithLength hp hX hg hMore scan
        (src := src) (index := j) (target := ⟨284,.exit⟩) (.inl hEnds) (by decide) with
      ⟨_,next,hNext,_⟩ | ⟨_,next,hNext,_⟩
    · by_cases hHi : j < next.pos src
      · exact inGroup next hNext hHi
      · exact ih (p.batch-(first+31)) (by omega) (first+31) (shuffles+1+5+1)
          rfl hMore next (Nat.le_of_not_gt hHi)
    · by_cases hHi : j < next.pos src
      · exact inGroup next hNext hHi
      · exact (noLoaderFallbackAfterSelection (next.checkpoint src hSrc).1.ge
          (runAt next) (Nat.le_of_not_gt hHi) he).elim

/-- The cache loader's repeated scheduler lookups address the launch CuQ array. -/
theorem loaderFallbackAddressesOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hProtected : ∀ Y, Consistent l kernel Assumptions.all m Y → DrainCuQProtected p Y)
    (hComplete : ∀ Y, Maximal l kernel Assumptions.all m Y → Complete l Y) :
    LoaderFallbackAddresses p X := by
  intro i a bytes hRead
  obtain ⟨g,j⟩ := i
  have he : X.get (g,j) = some ⟨245,.rd a bytes⟩ := hRead
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < 245 by decide)
    (show 245 ∉ registerHintSites by decide)
  have hw : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) 245 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨Y,hXY,hMax⟩ := maximalExtension hp hX
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hy : LoaderFallbackCuQRead Y (warpLane l g lane,j) a bytes := by
    rw [hLane]
    exact Execution.le_get hXY he
  exact loaderFallbackReadOfComplete hp hMax.1 (hComplete Y hMax) (hProtected Y hMax.1)
    hg hw hl hy

end PTX.Kernels.TmlFa4Fwd.Thread
