-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActiveDrain
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderIdleProgress
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound
import Lemmas.Tmem.PairProtocol
import Kernels.TmlFa4Fwd.Proof.LoaderIdleDrain
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.LoaderTransparency
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Proof.NoCancellation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader (drainWaitSite kvUseStage idleRelease loaderIdleKvDrained
  idleDrainForBatchesOfMaximal prefixStableCutFromInteriorWithReach loaderPipelineCutOp
  loaderOutCore HasWarmTile reuseArrival)

noncomputable section

/-- The three cache waits at the end of each loader lane's scheduler. -/
def drainCacheSite (slot : Fin 3) : Nat := (drainWaitSite ⟨slot.val, by omega⟩).pc

private theorem drainSiteBounds (slot : Fin 3) :
    1864 ≤ drainCacheSite slot ∧ drainCacheSite slot < 1891 := by decide +revert

private theorem drainSiteInj : Function.Injective drainCacheSite := by decide

private theorem aboveDrainEntry {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hs : 1864 ≤ s.pc) (h : WStep kernel Assumptions.all l g s e u) :
    1864 ≤ u.pc :=
  eventTailStepOfAudit (by decide +kernel) (by decide +kernel) hs h

private theorem drainEntryPrecedesPoll {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (hRun : TraceReach kernel Assumptions.all l g s events u)
    (hu : u.pc < 1864) :
    ∀ e ∈ events, e.pc < 1864 := by
  have keepsFloor {a b : TState} {xs : List Event}
      (h : TraceReach kernel Assumptions.all l g a xs b) (ha : 1864 ≤ a.pc) :
      1864 ≤ b.pc := by
    induction h with
    | refl => exact ha
    | tau h _ ih => exact ih (aboveDrainEntry ha (.inl ⟨rfl,h⟩))
    | event h _ ih => exact ih (aboveDrainEntry ha (.inr ⟨_,rfl,h⟩))
  induction hRun with
  | refl => simp
  | tau _ _ ih => exact ih hu
  | event h hTail ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | hMem
    · by_contra! hPc
      have hSource := estep_source_pc h
      have hNext := aboveDrainEntry (hSource.symm ▸ hPc) (.inr ⟨_,rfl,h⟩)
      exact (Nat.not_le_of_gt hu) (keepsFloor hTail hNext)
    · exact ih hu e hMem

private theorem returningRunReach {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (hr : Run kernel Assumptions.all l g s events (some u)) :
    TraceReach kernel Assumptions.all l g s events u := by
  generalize hEnd : (some u : Option TState) = result at hr
  induction hr with
  | nil => cases hEnd; exact .refl _
  | step hLocal he _ ih =>
    exact (TraceReach.of_local hLocal).append (.event he (ih hEnd))
  | last => cases hEnd

private theorem afterDrainRange {l : Launch} {g : Nat} {s : TState} {events : List Event}
    (hs : s.pc = 1891) (hr : Run kernel Assumptions.all l g s events none) :
    ∀ e ∈ events, 1891 ≤ e.pc := by
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  exact eventTailEvents (by decide +kernel) (by decide +kernel) hWalk hs.ge

private theorem blockKind {wait : Fin 3 → Bool → Event}
    {runs : Fin 3 → Nat} {rest : List Event} (step : Fin 3)
    (hPc : ∀ j ok, (wait j ok).pc = drainCacheSite j)
    (hTail : ∀ e ∈ rest, 1891 ≤ e.pc)
    {e : Event} (he : e.pc = drainCacheSite step)
    (hMem : e ∈
      (List.replicate (runs 0) (wait 0 false) ++ [wait 0 true]) ++
      (List.replicate (runs 1) (wait 1 false) ++ [wait 1 true]) ++
      (List.replicate (runs 2) (wait 2 false) ++ [wait 2 true]) ++ rest) :
    ∃ ok, e = wait step ok := by
  have one (slot : Fin 3)
      (hBlock : e ∈ List.replicate (runs slot) (wait slot false) ++ [wait slot true]) :
      ∃ ok, e = wait step ok := by
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hBlock
    obtain ⟨ok, hEq⟩ : ∃ ok, e = wait slot ok := by
      rcases hBlock with ⟨_, hEq⟩ | hEq
      · exact ⟨false,hEq⟩
      · exact ⟨true,hEq⟩
    have hSlot := drainSiteInj ((hPc slot ok).symm.trans ((congrArg Event.pc hEq).symm.trans he))
    exact ⟨ok,hSlot ▸ hEq⟩
  rcases List.mem_append.mp hMem with hMem | hRest
  · rcases List.mem_append.mp hMem with hMem | hTwo
    · rcases List.mem_append.mp hMem with hZero | hOne
      · exact one 0 hZero
      · exact one 1 hOne
    · exact one 2 hTwo
  · exact (Nat.not_le_of_gt (drainSiteBounds step).2 (he ▸ hTail e hRest)).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An actual idle cache drain wait uses the initialized slot for its drain position. -/
theorem idleDrainPollObject (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hComplete : Complete l X) {g lane i : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block)
    (hl : lane < 32) (slot : Fin 3) {loc : Loc} {parity : Nat} {ok acq : Bool} {scope : MbarScope}
    (hGet : X.get (warpLane l g lane,i) = some ⟨drainCacheSite slot,.wait loc parity ok acq scope⟩)
    :
    loc = emptyObject l (warpLane l g lane) slot := by
  obtain ⟨shuffles,ends,⟨cur⟩⟩ := idleDrainForBatchesOfMaximal hp hMax hg hw hCuQ hIdle
  let thread := warpLane l g lane
  let pos := cur.pos lane
  let e : Event := ⟨drainCacheSite slot,.wait loc parity ok acq scope⟩
  have hLocal := cur.localSteps lane hl
  have hState := cur.checkpoint lane hl
  have hBefore := (returningRunReach (cur.recorded lane hl)).append
    (TraceReach.of_local hLocal)
  simp only [List.append_nil] at hBefore
  have hPos : pos ≤ i := by
    by_contra! hLt
    have hMem : e ∈ (X.tr thread).take pos := by
      apply List.mem_of_getElem? (i := i)
      rw [List.getElem?_take]
      simp only [hLt, ↓reduceIte]
      exact hGet
    have hLow := drainEntryPrecedesPoll hBefore (by rw [hState.1]; decide) e hMem
    exact Nat.not_lt_of_ge (drainSiteBounds slot).1 hLow
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hThread := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  have hRun := (cur.continuation lane hl)
  have hEnd : ends lane = none := by
    obtain ⟨exitPc,hExit⟩ := (hComplete.1 thread hThread).resolve_left (noCanceled hMax.1)
    obtain ⟨tail, hTail⟩ := List.mem_iff_getElem?.mp (List.mem_of_getLast? hExit)
    have hLate : i < tail := by
      have hLength : i < (X.tr thread).length := (List.getElem?_eq_some_iff.mp hGet).1
      have hLast : tail + 1 = (X.tr thread).length := by
        obtain ⟨_,hWhole⟩ := hMax.1.thr thread hThread
        exact hWhole.exit_last hTail
      by_contra! hOrder
      have hEq : i = tail := by omega
      have hConflict := congrArg Event.kind (Option.some.inj (hGet.symm.trans (hEq ▸ hTail)))
      cases hConflict
    have hMem : ((X.tr thread).drop pos)[tail-pos]? = some ⟨exitPc,.exit⟩ := by
      rw [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
      exact hTail
    cases h : ends lane with
    | none => rfl
    | some => exact ((h ▸ hRun).no_exit hMem).elim
  obtain ⟨runs,u,rest,hEvents,hu,hRest⟩ :=
    loaderIdleKvDrained hp (warpIndex_lt hp g) hState ((hEnd ▸ hRun).after_local hLocal)
  have hMem : e ∈ (X.tr thread).drop pos := by
    apply List.mem_of_getElem? (i := i-pos)
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact hGet
  rw [hEvents] at hMem
  obtain ⟨_,hEq⟩ := blockKind slot (wait := idleRelease l thread)
    (fun _ _ => rfl) (afterDrainRange hu.1 hRest) rfl hMem
  have hKind := congrArg Event.kind hEq
  cases hKind
  simp only [emptyObject, PTX.Kernels.TmlFa4Fwd.Loader.emptySlot_address]
  congr 1
  omega


private theorem activeDrainCut {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g start finish use : Nat}
    {s : TState} (hs : At s 1744 (drainCarry l use))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop start) none)
    (hStart : start ≤ finish) (hExit : X.get (g,finish) = some ⟨9205,.exit⟩)
    {obs : Event} {i : Nat} (he : X.get (g,i) = some obs) (hPc : 1864 ≤ obs.pc) :
    ∃ pos ≤ i, ∃ t, At t 1863 (drainCarry l use) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) none := by
  let F := drainCarry l use
  have auditFirst (branch : Nat) : ((kernel.code.drop 1744).take (1751 - 1744)).all
      (fun ins => loaderPipelineCutOp 1744 1751 branch (F.map Prod.fst) ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have auditSecond (branch : Nat) : ((kernel.code.drop 1744).take (1863 - 1744)).all
      (fun ins => loaderPipelineCutOp 1744 1863 branch (F.map Prod.fst) ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSafe : ∀ f, (Event.kind ⟨9205,.exit⟩) ≠ .ub f := by intro f h; cases h
  obtain ⟨a,first,r,_,ha,haRun,_,haIndex,_⟩ :=
    prefixStableCutFromInteriorWithReach (show 174 ≤ 1744 ∧ 1744 ≤ 1751 ∧ 1751 ≤ 1901 by decide)
      auditFirst (by rw [hs.1]; decide) ⟨rfl,hs.2⟩ hr hExit hStart hSafe
      (fun _ => 0) (fun _ => false) (.inl (by decide)) (by intros; rfl) (by intros; rfl)
      (by intros; simp)
  obtain ⟨t,front,ending,hsplit,ht,hRun,_,hIndex,hFront⟩ :=
    prefixStableCutFromInteriorWithReach (show 174 ≤ 1744 ∧ 1744 ≤ 1863 ∧ 1863 ≤ 1901 by decide)
      auditSecond (by rw [ha.1]; decide) ⟨rfl,ha.2⟩ haRun hExit haIndex hSafe
      (fun _ => 0) (fun _ => false) (.inl (by decide)) (by intros; rfl) (by intros; rfl)
      (by intros; simp)
  let pos := start + first.length + front.length
  have hMore : front ≠ [] := by
    intro hNil
    rw [hNil] at hFront
    cases hFront with
    | refl => have hc := ht.1; rw [ha.1] at hc; contradiction
    | @tau _ next _ _ hTau _ =>
      have hCore : Tau kernel [] l g a next := by
        unfold Tau at *
        rwa [← loaderOutCore (by rw [ha.1]; decide) (by rw [ha.1]; decide)]
      have hCode := Flow.code_1751
      rw [← ha.1] at hCode
      exact tau_core_not_event hCode rfl hCore
  have hFrontLen := List.length_pos_iff.mpr hMore
  let last := front[front.length-1]'(by omega)
  have hBefore : X.get (g,pos-1) = some last := by
    change (X.tr g)[pos-1]? = some last
    have hAt : front[front.length-1]? = some last := List.getElem?_eq_getElem (by omega)
    rw [← show start + first.length + (front.length-1) = pos-1 by dsimp [pos]; omega,
      ← List.getElem?_drop, hsplit, List.getElem?_append_left (by omega)]
    exact hAt
  have hLow := drainEntryPrecedesPoll hFront (by rw [ht.1]; decide)
    last (List.getElem_mem (by omega))
  have hOrder := traceOrderOfPcFloor hX (by decide +kernel) (by decide +kernel) hBefore he hLow hPc
  have hTarget : ((X.tr g).drop pos)[finish-pos]? = some ⟨9205,.exit⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hIndex]
    exact hExit
  have hDone : ending = none := by
    cases ending with
    | none => rfl
    | some => exact (hRun.no_exit hTarget).elim
  exact ⟨pos,by omega,t,ht,hDone ▸ hRun⟩

/-- An actual active cache drain wait uses the final logical ring position plus its step. -/
theorem activeDrainPollObject (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g seed use finish i : Nat} {s : TState} (hs : At s 1744 (drainCarry l use))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop seed) none) (hStart : seed ≤ finish)
    (hExit : X.get (g,finish) = some ⟨9205,.exit⟩) (step : Fin 3) {loc : Loc} {parity : Nat}
    {ok acq : Bool} {scope : MbarScope}
    (hGet : X.get (g,i) = some ⟨drainCacheSite step,.wait loc parity ok acq scope⟩) :
    loc = emptyObject l g (kvUseStage (use + step.val)) := by
  obtain ⟨pos,hPos,t,ht,hRun⟩ := activeDrainCut hX hs hr hStart hExit hGet (drainSiteBounds step).1
  obtain ⟨n0,n1,n2,u,rest,hEvents,hu,_,hRest⟩ := ringDrainTrace hp ht hRun
  let e : Event := ⟨drainCacheSite step,.wait loc parity ok acq scope⟩
  have hMem : e ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := i-pos)
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact hGet
  rw [hEvents] at hMem
  let wait := fun j ok => drainPoll l g j (use+j.val) ok
  let runs : Fin 3 → Nat := ![n0,n1,n2]
  have hBlocks : e ∈
      (List.replicate (runs 0) (wait 0 false) ++ [wait 0 true]) ++
      (List.replicate (runs 1) (wait 1 false) ++ [wait 1 true]) ++
      (List.replicate (runs 2) (wait 2 false) ++ [wait 2 true]) ++ rest := by
    simpa [runs, wait] using hMem
  obtain ⟨_,hEq⟩ := blockKind step (wait := wait)
    (fun _ _ => rfl) (afterDrainRange hu hRest) rfl hBlocks
  exact (Kind.wait.inj (congrArg Event.kind hEq)).1

private theorem markSite {e : Event} (hMark : recurringPublicationMark e = true) :
    (917 ≤ e.pc ∧ e.pc < 1348) ∨ (1396 ≤ e.pc ∧ e.pc < 1741) := by
  obtain ⟨site,_,rfl⟩ := (recurringPublicationMark_iff e).mp hMark
  exact (by decide : ∀ site : Fin 4,
    (917 ≤ reuseArrival site ∧ reuseArrival site < 1348) ∨
    (1396 ≤ reuseArrival site ∧ reuseArrival site < 1741)) site

private theorem nonFaultMark {e : Event} (hMark : recurringPublicationMark e = true) :
    ∀ f, e.kind ≠ .ub f := by
  obtain ⟨_,_,rfl⟩ := (recurringPublicationMark_iff e).mp hMark
  intro f h
  cases h

private theorem exactDrainUse (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g lane batch i : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : lane < 32) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads) {e : Event}
    (he : X.get (warpLane l g lane,i) = some e) (hLate : 1864 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    :
    2 + (X.tr (warpLane l g lane)).countP recurringPublicationMark =
      2 * Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 := by
  let thread := warpLane l g lane
  let trips := Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1
  let total := 2 + (X.tr thread).countP recurringPublicationMark
  change total = 2 * trips
  have hCTA : g / l.block < tilePrefix p p.batch * p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨selected,hSelected,hUnique⟩ := tileBatch_existsUnique p hCTA
  have hBatchEq (b : Nat) (hb' : b < p.batch)
      (hLo' : tilePrefix p b * p.heads ≤ g / l.block)
      (hHi' : g / l.block < tilePrefix p (b+1) * p.heads) : b = batch :=
    (hUnique b ⟨hb',hLo',hHi'⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  have hPositive : 0 < trips := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).1
  have hUpper : total ≤ 2 * trips := by
    by_contra! hTooMany
    have hMore : 2*trips-2 < ((X.tr thread).take (X.tr thread).length).countP
        recurringPublicationMark := by rw [List.take_length]; dsimp [total] at hTooMany; omega
    obtain ⟨j,_,hj,hMark,hRank⟩ := Tmem.Pair.countP_take_occ recurringPublicationMark
      (X.tr thread) (X.tr thread).length (2*trips-2) hMore
    let pub := (X.tr thread)[j]
    have hPub : X.get (thread,j) = some pub := List.getElem?_eq_getElem hj
    have hUse : recurringUseBefore X (thread,j) = 2*trips := by
      change 2 + ((X.tr thread).take j).countP recurringPublicationMark = _
      omega
    rcases markSite hMark with hWarm | hSteady
    · obtain ⟨b,hb',hLo',hHi',hBound⟩ :=
        actualWarmCacheUseBound hp hX hg hw hl (fun _ _ _ _ => loaderOutputWrites hFrame)
          hCTA hPub (.inr hMark) hWarm
      cases hBatchEq b hb' hLo' hHi'
      rw [hUse] at hBound
      have hMin := Nat.min_le_left (trips-1) 9
      change 2*trips < 2*(min (trips-1) 9+1) at hBound
      omega
    · obtain ⟨b,hb',hLo',hHi',round,_,hRound,hBound,_⟩ :=
        actualSteadyCacheProjection hp hX hg hw hl (fun _ _ _ _ => loaderOutputWrites hFrame)
          hCTA hPub hSteady (nonFaultMark hMark)
      cases hBatchEq b hb' hLo' hHi'
      rw [hUse] at hBound
      change round < trips-1 at hRound
      change 2*trips + cacheRoundRemaining true pub.pc = 2*(round+2) at hBound
      have hRemaining := cacheRoundArrivalRemainingPositive true hMark hSteady.1 hSteady.2
      change 0 < cacheRoundRemaining true pub.pc at hRemaining
      have hEnough : round + 2 ≤ trips := by omega
      exact (Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 hEnough)) (by omega)
  refine Nat.le_antisymm hUpper ?_
  by_cases hMany : 11 ≤ trips
  · obtain ⟨b,hb',hLo',hHi',hRank⟩ :=
      actualSteadyCacheProjectionOrAfter hp hX hg hw hl
        (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA he (by omega)
        (.inr ⟨batch,hb,hLo,hHi,hMany⟩) hSafe
    cases hBatchEq b hb' hLo' hHi'
    rcases hRank with ⟨⟨_,hBad⟩,_⟩ | ⟨_,pos,_,_,_,_,_,hReady⟩
    · omega
    · change recurringUseBefore X (thread,pos) = 2 * trips at hReady
      have hCount := (List.take_sublist pos (X.tr thread)).countP_le (p := recurringPublicationMark)
      calc
        _ = 2 + ((X.tr thread).take pos).countP recurringPublicationMark := hReady.symm
        _ ≤ total := Nat.add_le_add_left hCount 2
  · by_cases hWarm : 2 ≤ trips
    · obtain ⟨b,hb',hLo',hHi',hRank⟩ :=
        actualWarmCacheProjectionOrAfter hp hX hg hw hl
          (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA he (by omega)
          (.inr ⟨batch,hb,hLo,hHi,hWarm⟩) hSafe
      cases hBatchEq b hb' hLo' hHi'
      rcases hRank with ⟨⟨_,hBad⟩,_⟩ | ⟨_,pos,_,hReady,_⟩
      · omega
      · change recurringUseBefore X (thread,pos) = 2*(min (trips-1) 9+1) at hReady
        rw [Nat.min_eq_left (by omega : trips - 1 ≤ 9)] at hReady
        have hCount :=
          (List.take_sublist pos (X.tr thread)).countP_le (p := recurringPublicationMark)
        rw [show trips - 1 + 1 = trips by omega] at hReady
        calc
          _ = 2 + ((X.tr thread).take pos).countP recurringPublicationMark := hReady.symm
          _ ≤ total := Nat.add_le_add_left hCount 2
    · dsimp [total]; omega

private theorem packetsUseCount {l : Launch} {g use final : Nat} {packets : List Event}
    (hPackets : PacketsBeforeDrain l g use final packets) :
    use + packets.countP recurringPublicationMark = final := by
  induction hPackets with
  | done => simp
  | @gap _ _ pre _ hQuiet _ ih =>
    have hNo : pre.countP recurringPublicationMark = 0 :=
      List.countP_eq_zero.mpr fun e he h =>
      (hQuiet e he).1 ((recurringPublicationMark_iff e).mp h)
    rw [List.countP_append,hNo,Nat.zero_add]
    exact ih
  | @packet use final n site mid tail hQuiet hNext ih =>
    have hNo : mid.countP recurringPublicationMark = 0 :=
      List.countP_eq_zero.mpr fun e he h => (hQuiet e he).1 ((recurringPublicationMark_iff e).mp h)
    have hPub : recurringPublicationMark (cursorArrival l g use site) = true :=
      (recurringPublicationMark_iff _).mpr ⟨site,_,rfl⟩
    have hPoll (ok : Bool) : recurringPublicationMark (cursorPoll l g use site ok) = false := rfl
    simp only [List.countP_append,List.countP_replicate,List.countP_cons,hPub,hPoll,hNo,
      Bool.false_eq_true, ↓reduceIte,Nat.zero_add,Nat.add_zero]
    omega

private theorem activeDrainFrontierOfFirstPublication (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {loc : Loc}
    (hPub : X.AsyncArrive (g,index) loc true) (hExit : Thread.Exited X g) :
    ∃ start finish t, start ≤ finish ∧ X.get (g,finish) = some ⟨9205,.exit⟩ ∧
      At t 1744 (drainCarry l (2 + (X.tr g).countP recurringPublicationMark)) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop start) none := by
  have derive {index : Nat} {loc : Loc} (hPub : X.AsyncArrive (g,index) loc true)
      (hSeed : ∀ seed,
        (∀ e, X.get (g,index) = some e → recurringPublicationEvent e → seed ≤ index) →
        ((X.tr g).take seed).countP recurringPublicationMark = 0) :
      ∃ start finish t, start ≤ finish ∧ X.get (g,finish) = some ⟨9205,.exit⟩ ∧
        At t 1744 (drainCarry l (2 + (X.tr g).countP recurringPublicationMark)) ∧
        Run kernel Assumptions.all l g t ((X.tr g).drop start) none := by
    obtain ⟨seed,final,finish,t,front,hSplit,hPackets,hStart,he,ht,hr,hSelected,hQuiet⟩ :=
      actualDrainFrontierOfPublication hp hX hPub hExit
    have hZero : ((X.tr g).drop (seed + front.length)).countP recurringPublicationMark = 0 :=
      List.countP_eq_zero.mpr fun e he h => hQuiet e he ((recurringPublicationMark_iff e).mp h)
    have hTotal :
        (X.tr g).countP recurringPublicationMark = front.countP recurringPublicationMark := by
      have hWhole := congrArg (List.countP recurringPublicationMark)
        (List.take_append_drop seed (X.tr g))
      rw [hSplit,List.countP_append,List.countP_append,hSeed seed hSelected,hZero] at hWhole
      simpa using hWhole.symm
    rw [← packetsUseCount hPackets] at ht
    rw [hTotal]
    exact ⟨seed + front.length,finish,t,hStart,he,ht,hr⟩
  by_cases hNone : (X.tr g).countP recurringPublicationMark = 0
  · refine derive hPub fun seed _ => ?_
    exact Nat.eq_zero_of_le_zero (hNone ▸ (List.take_sublist seed (X.tr g)).countP_le)
  · have hMore : 0 < ((X.tr g).take (X.tr g).length).countP recurringPublicationMark := by
      rw [List.take_length]
      exact Nat.pos_of_ne_zero hNone
    obtain ⟨i,_,hi,hMarked,hFirst⟩ := Tmem.Pair.countP_take_occ recurringPublicationMark
      (X.tr g) (X.tr g).length 0 hMore
    let e := (X.tr g)[i]
    have hGet : X.get (g,i) = some e := List.getElem?_eq_getElem hi
    have hr := (recurringPublicationMark_iff e).mp hMarked
    have hArrive : ∃ loc, X.AsyncArrive (g,i) loc true := by
      obtain ⟨site,loc,hEq⟩ := hr
      exact ⟨loc,_,hEq ▸ hGet⟩
    obtain ⟨loc,hArrive⟩ := hArrive
    refine derive hArrive fun seed hSeed => ?_
    exact Nat.eq_zero_of_le_zero (hFirst ▸
      Flow.countP_take_mono recurringPublicationMark (X.tr g) (hSeed e hGet hr))

/-- The actual cache drain of a selected CTA starts at twice its exact trip count. -/
theorem selectedDrainPollObject (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g lane batch i q : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : lane < 32) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads) {ready : Loc}
    (hPub : X.AsyncArrive (warpLane l g lane,q) ready true)
    (hExit : Thread.Exited X (warpLane l g lane)) (step : Fin 3) {loc : Loc} {parity : Nat}
    {ok acq : Bool} {scope : MbarScope}
    (hGet : X.get (warpLane l g lane,i) = some ⟨drainCacheSite step,.wait loc parity ok acq scope⟩)
    :
    let trips := Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1
    loc = emptyObject l (warpLane l g lane) (kvUseStage (2 * trips + step.val)) := by
  obtain ⟨start,finish,t,hStart,he,ht,hr⟩ := activeDrainFrontierOfFirstPublication hp hX hPub hExit
  have hCount := exactDrainUse hp hX hFrame hg hw hl hb hLo hHi hGet
    (drainSiteBounds step).1 (by intro f h; cases h)
  rw [hCount] at ht
  exact activeDrainPollObject hp hX ht hr hStart he step hGet

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
