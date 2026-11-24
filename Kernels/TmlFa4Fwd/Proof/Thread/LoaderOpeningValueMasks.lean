-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValueAbi
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValueReload
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixMasks
import Lemmas.Flow.RecordedCheckpointPath
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Epilogue

private inductive LoaderVMaskCut
  | addressDone | keyWaitDone | keyMaskStart | valueWaitDone | valuePrep | afterReload | reloadDone

private def LoaderVMaskCut.floor : LoaderVMaskCut → Nat
  | .addressDone => 416
  | .keyWaitDone => 520
  | .keyMaskStart => 539
  | .valueWaitDone => 785
  | .valuePrep => 786
  | .afterReload => 806
  | .reloadDone => 805

set_option maxRecDepth 15000 in
private theorem maskTailCode (cut : LoaderVMaskCut) :
    (kernel.code.drop cut.floor).all (fun i => Thread.staysPastEvent cut.floor i.op) = true := by
  cases cut <;> kernel_rfl

private theorem maskTailSegments806 :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (806 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem maskTailSegments (cut : LoaderVMaskCut) :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (cut.floor ≤ seg.stop)
      | none => false) = true := by
  apply List.all_eq_true.mpr
  intro site hm
  have hKnown := List.all_eq_true.mp maskTailSegments806 site hm
  cases hseg : cuteExp2.matchAt kernel site with
  | none => simp [hseg] at hKnown
  | some seg =>
    simp only [hseg,decide_eq_true_eq] at hKnown ⊢
    have hFloor : cut.floor ≤ 806 := by cases cut <;> decide
    exact hFloor.trans hKnown

private theorem maskTraceCannotReturn {l : Launch} {g : Nat} {s u : TState}
    (cut : LoaderVMaskCut) (hs : cut.floor ≤ s.pc) (hu : u.pc < cut.floor)
    (es : List Event) : ¬ TraceReach kernel Assumptions.all l g s es u := by
  intro h
  exact (Nat.not_lt_of_ge
    (Thread.Loader.traceRetainsFloor (maskTailCode cut) (maskTailSegments cut) h hs)) hu

private theorem keepMaskFrameUntilCut {l : Launch} {g low : Nat} {s u : TState}
    {events : List Event} {F : List (Nat × Value)} (cut : LoaderVMaskCut)
    (hLow : 174 ≤ low) (hHigh : cut.floor ≤ 1901)
    (hCode : ((kernel.code.drop low).take (cut.floor-low)).all
      (fun ins => loaderPipelineCutOp low cut.floor cut.floor (F.map Prod.fst) ins.op) = true)
    (hTrace : TraceReach kernel Assumptions.all l g s events u)
    (hs : low ≤ s.pc) (hu : u.pc < cut.floor)
    (hShape : RingShape s) (hF : Holds s.regs F) : Holds u.regs F := by
  have below {t : TState} {es : List Event}
      (h : TraceReach kernel Assumptions.all l g t es u) : t.pc < cut.floor := by
    by_contra! hBad
    exact maskTraceCannotReturn cut hBad hu es h
  induction hTrace with
  | refl => exact hF
  | tau ht hTail ih =>
    obtain ⟨hNext,_,hRing,hKeep⟩ := pipelineCutStep hLow hHigh ⟨hs,below (.tau ht hTail)⟩
      hCode (.inl ⟨rfl,ht⟩) hShape hF
    exact ih hNext hu hRing hKeep below
  | event he hTail ih =>
    obtain ⟨hNext,_,hRing,hKeep⟩ := pipelineCutStep hLow hHigh ⟨hs,below (.event he hTail)⟩
      hCode (.inr ⟨_,rfl,he⟩) hShape hF
    exact ih hNext hu hRing hKeep below

set_option maxRecDepth 100000 in
private theorem keyMaskAbiCode (p : Params) (l : Launch) (batch head tile : Nat) :
    ((kernel.code.drop 488).take (539-488)).all (fun ins => loaderPipelineCutOp 488 539 539
      ((primingVAdmissionCarry p l batch head tile).map Prod.fst) ins.op) = true := by kernel_rfl

private theorem valueAdmissionAtMaskEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch shStart shPacked votesStart votesPacked : Nat}
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    {endStart endPacked : Nat → Option TState}
    (start : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      shStart votesStart endStart)
    (packed : SchedulerWarpReached l X g 538
      (primingKMaskInputs p l batch
        (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
        (warpIndex l g)) shPacked votesPacked endPacked) :
    ∀ lane < 32,
      let co := assignedCoordinates p batch (g/l.block)
      Holds (packed.state lane).regs (primingVAdmissionCarry p l batch co.2 co.1) := by
  intro lane hl
  let thread := warpLane l g lane
  let co := assignedCoordinates p batch (g/l.block)
  have hs := start.checkpoint lane hl
  have ht := packed.checkpoint lane hl
  obtain ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  obtain ⟨_,u,hu,hU⟩ := primingVAdmissionWithTripsLane hp (g := thread) hb
    (hHead.trans hp.heads_signed) hTile hl (hs.mono ((holds_append ..).mp hs.2.2.2.2).1)
  obtain ⟨_,hReach⟩ := recordedCheckpointsPath (start.bounded lane hl) (packed.bounded lane hl)
    (start.recorded lane hl) (start.localSteps lane hl)
    (packed.recorded lane hl) (packed.localSteps lane hl)
    (maskTraceCannotReturn .addressDone
      (show 416 ≤ (packed.state lane).pc by rw [ht.1]; decide)
      (show (start.state lane).pc < 416 by rw [hs.1]; decide))
  have hNo : ¬ Relation.ReflTransGen (Tau kernel Assumptions.all l thread)
      (packed.state lane) u := by
    intro h
    exact maskTraceCannotReturn .keyWaitDone
      (show 520 ≤ (packed.state lane).pc by rw [ht.1]; decide)
      (show u.pc < 520 by rw [hU.1]; decide) [] (TraceReach.of_local h)
  have hAbi := ((holds_append ..).mp ((holds_append ..).mp hU.2.2.2.2).1).2
  exact keepMaskFrameUntilCut .keyMaskStart (by decide) (by decide)
    (keyMaskAbiCode p l batch co.2 co.1) (hReach.afterLocalOfNoBack hu hNo)
    (by rw [hU.1]) (by rw [ht.1]; decide) (ringShapeOfAt hU) hAbi

set_option maxRecDepth 100000 in
private theorem copyMaskCarryCode (p : Params) (l : Launch) (batch h q t w lane : Nat) :
    ((kernel.code.drop 673).take (786-673)).all (fun ins => loaderPipelineCutOp 673 786 786
      ((primingMaskFrame p l batch h q t w lane 16).map Prod.fst) ins.op) = true := by kernel_rfl

/-- All tail masks produced by the opening K packet remain live at the actual V acquire.
The reconstructed K cursor keeps its recorded prefix, so the masks refer to those real lanes. -/
theorem openingValueMaskFrameOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch shStart shPacked shDone votesStart votesPacked votesDone : Nat}
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTile : 128*(Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)+127 < 2^31)
    {endStart endPacked endDone : Nat → Option TState}
    (start : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      shStart votesStart endStart)
    (packed : SchedulerWarpReached l X g 538
      (primingKMaskInputs p l batch
        (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
        (warpIndex l g)) shPacked votesPacked endPacked)
    (done : OpeningValueAcquired l X g shDone votesDone endDone)
    (hWait : ∀ lane < 32, ∃ j, j+1 = done.pos lane ∧
      OpeningValueWaitAt l X (warpLane l g lane) j) :
    ∀ lane < 32,
      let co := assignedCoordinates p batch (g/l.block)
      let tile := Mma.trips p batch co.1-1
      Holds (done.state lane).regs (vPacketFrame p l batch tile (warpIndex l g) lane
        (fun _ => vPrimingResidual p batch co.1)) := by
  intro lane hl
  let thread := warpLane l g lane
  let co := assignedCoordinates p batch (g/l.block)
  let tile := Mma.trips p batch co.1-1
  let warp := warpIndex l g
  have hAbi := valueAdmissionAtMaskEntry hp hb hLo hHi start packed lane hl
  have hAt := packed.checkpoint lane hl
  have hSeed : At (packed.state lane) 538
      (primingKMaskInputs p l batch tile warp lane ++ primingVAdmissionCarry p l batch co.2 co.1) :=
    hAt.mono ((holds_append ..).mpr ⟨hAt.2.2.2.2,hAbi⟩)
  obtain ⟨j,hJ,hWait⟩ := hWait lane hl
  have hGet : X.get (thread,j) = some (primingVWaitEvent l thread true) := hWait
  have hBefore : packed.pos lane ≤ j := by
    by_contra! hPast
    have hRead : ((X.tr thread).take (packed.pos lane))[j]? =
        some (primingVWaitEvent l thread true) := by
      rw [List.getElem?_take_of_lt hPast]
      exact hGet
    have hReach := (packed.recorded lane hl).returning_reach.append
      (TraceReach.of_local (packed.localSteps lane hl))
    simp only [List.append_nil] at hReach
    have hBad := Thread.Loader.noEventAboveFinalFloor (maskTailCode .keyMaskStart)
      (maskTailSegments .keyMaskStart) hReach (by rw [hAt.1]; decide) (List.mem_of_getElem? hRead)
    exact (by decide : ¬ 782 < 539) hBad
  have hRun := (packed.continuation lane hl).after_local_nonempty (packed.localSteps lane hl)
    (traceAfterObservedEvent hGet hBefore)
  have hLen : p.kLength batch < 2^31 := by have := (hp.lengths batch hb).2.2; omega
  have hRow : kvCopyRow tile (32*warp+lane) 0 < 2^31 := by
    change 128*tile+127 < 2^31 at hTile
    have := Nat.mod_lt ((32*warp+lane)/8) (by decide : 0 < 8)
    simp only [kvCopyRow,Nat.mul_zero,Nat.add_zero]
    omega
  obtain ⟨k,pos,_,hOrder,hK,_,_,hStart,hReach⟩ :=
    primingVMasksAtKCommitInPrefixWithReach hLen hRow hSeed hRun hGet hBefore
      (show 672 < 782 by decide) (by intro f hf; cases hf)
  have hPackedReach := (packed.recorded lane hl).returning_reach.append
    (TraceReach.of_local (packed.localSteps lane hl))
  have hFull := hPackedReach.append hReach
  have hIndexed : TraceReach kernel Assumptions.all l thread {} ((X.tr thread).take pos) k := by
    rw [← Nat.add_sub_of_le hStart,List.take_add]
    simpa only [List.append_nil] using hFull
  obtain ⟨before,hRecord,hLocal⟩ := hIndexed.returnedPrefix
  have ht := done.checkpoint lane hl
  have hDoneBound : done.pos lane ≤ (X.tr thread).length := done.bounded lane hl
  have hBound : pos ≤ (X.tr thread).length := by omega
  obtain ⟨_,hPath⟩ := recordedCheckpointsPath hBound (done.bounded lane hl)
    hRecord hLocal (done.recorded lane hl) (done.localSteps lane hl)
    (maskTraceCannotReturn .valueWaitDone (show 785 ≤ (done.state lane).pc by rw [ht.1])
      (show k.pc < 785 by rw [hK.1]; decide))
  have hKeep := keepMaskFrameUntilCut (low := 673) .valuePrep (by decide) (by decide)
    (copyMaskCarryCode p l batch co.2 co.1 tile warp lane) hPath
    (by rw [hK.1]) (by rw [ht.1]; decide) (ringShapeOfAt hK) hK.2.2.2.2
  have hFrame := vFrameAfterMasks p l g batch co.2 co.1 tile lane hKeep
  exact ((holds_append ..).mp hFrame).2

set_option maxRecDepth 100000 in
private theorem valueMaskAfterReloadCode (p : Params) (l : Launch)
    (batch tile warp lane word : Nat) :
    ((kernel.code.drop 785).take (806-785)).all (fun ins => loaderPipelineCutOp 785 806 806
      ((vPacketFrame p l batch tile warp lane (fun _ => word)).map Prod.fst) ins.op) = true := by
  kernel_rfl

/-- The first opening V broadcast sees both reloaded pointer words and the K-tail masks. -/
abbrev OpeningValueBroadcastReached (p : Params) (l : Launch) (X : Execution)
    (g batch shuffles votes : Nat) (ends : Nat → Option TState) :=
  let co := assignedCoordinates p batch (g/l.block)
  let tile := Mma.trips p batch co.1-1
  let warp := warpIndex l g
  SchedulerWarpReached l X g 805 (fun lane =>
    primingVReloadWords 0 (primingVRowPointer p batch (co.2/6)
      (primingLaneRow tile (32*warp+lane))) ++
    vPacketFrame p l batch tile warp lane (fun _ => vPrimingResidual p batch co.1))
    shuffles votes ends

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch shuffles votes : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (done : OpeningValueAcquired l X g shuffles votes ends)
    (hMasks : ∀ lane < 32,
      let co := assignedCoordinates p batch (g/l.block)
      let tile := Mma.trips p batch co.1-1
      Holds (done.state lane).regs (vPacketFrame p l batch tile (warpIndex l g) lane
        (fun _ => vPrimingResidual p batch co.1)))
    (hStored : ∀ lane < 32,
      let co := assignedCoordinates p batch (g/l.block)
      let tile := Mma.trips p batch co.1-1
      let row := primingLaneRow tile (32*warpIndex l g+lane)
      OpeningValuePointersStoredLane p l X (warpLane l g lane) (done.pos lane)
        batch (co.2/6) row (primingVAdmissionCarry p l batch co.2 co.1) (ends lane))
include hp hMax hg hb hLo hHi done hMasks hStored

/-- The two V scratch saves and first pointer reload preserve their warp's collectives
and the actual byte masks, so the next full-warp broadcast has a live cursor. -/
theorem openingValueBroadcastWithReadsOfMaximal :
    ∃ ready : OpeningValueBroadcastReached p l X g batch shuffles votes ends,
      ready.pos = (fun lane => done.pos lane+8) ∧
      ∀ lane < 32,
        let co := assignedCoordinates p batch (g/l.block)
        let tile := Mma.trips p batch co.1-1
        let row := primingLaneRow tile (32*warpIndex l g+lane)
        OpeningValueFirstPointerReloadedAt p l X (warpLane l g lane) (done.pos lane+6)
          batch (co.2/6) row := by
  classical
  let co := assignedCoordinates p batch (g/l.block)
  let tile := Mma.trips p batch co.1-1
  let warp := warpIndex l g
  let thread := warpLane l g
  let row := fun lane => primingLaneRow tile (32*warp+lane)
  let base := fun lane => primingVRowPointer p batch (co.2/6) (row lane)
  let F := fun lane =>
    vPacketFrame p l batch tile warp lane (fun _ => vPrimingResidual p batch co.1)
  let before := done.pos
  let pos := fun lane => before lane + 8
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2/6 < p.kvHeads := by
    unfold Params.heads at hHead
    change co.2 < 6*p.kvHeads at hHead
    omega
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : ∃ t,
      At t 805 (primingVReloadWords 0 (base lane) ++ F lane) ∧
      Run kernel Assumptions.all l (thread lane) {}
        ((X.tr (thread lane)).take (pos lane)) (some t) ∧
      Run kernel Assumptions.all l (thread lane) t
        ((X.tr (thread lane)).drop (pos lane)) (ends lane) ∧
      pos lane ≤ (X.tr (thread lane)).length ∧
      (pos lane = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      ((X.tr (thread lane)).take (pos lane)).countP Execution.isShfl = shuffles ∧
      ((X.tr (thread lane)).take (pos lane)).countP isFullWarpVote = votes ∧
      OpeningValueFirstPointerReloadedAt p l X (thread lane) (before lane+6)
        batch (co.2/6) (row lane) := by
    have hG : thread lane < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    have hStore : OpeningValuePointersStoredLane p l X (thread lane) (before lane)
        batch (co.2/6) (row lane) (primingVAdmissionCarry p l batch co.2 co.1) (ends lane) :=
      hStored lane hl
    have hR := openingValuePointerReloadWithFrameOfMaximal hp hMax hG hb hh hStore
    obtain ⟨t,ht,hPast,hTail⟩ := hR.continuation
    have hNext : ∀ word : Fin 2, let site := primingVPointerReload 0
        X.get (thread lane,before lane+6+word.val) = some
          ⟨site.pc,.rd (site.word (thread lane) l.localBase word)
            (pointerReadBytes (base lane) word)⟩ := hR.reloaded
    have hLow := hNext 0
    have hHigh := hNext 1
    simp only [Fin.val_zero,Nat.add_zero] at hLow
    simp only [Fin.val_one] at hHigh
    have hArithmetic : pos lane = (before lane+6+1)+1 := by simp [pos,Nat.add_assoc]
    have hBound : pos lane ≤ (X.tr (thread lane)).length := by
      rw [hArithmetic]
      exact len_of_get hHigh
    have hReleased : pos lane = (X.tr (thread lane)).length → Step.Released l X (thread lane) := by
      rw [hArithmetic]
      exact releasedIfLast hHigh (by intro h; cases h)
    have hAtV := done.checkpoint lane hl
    obtain ⟨_,hPath⟩ := recordedCheckpointsPath (done.bounded lane hl) hBound
      (done.recorded lane hl) (done.localSteps lane hl) hPast .refl
      (maskTraceCannotReturn .reloadDone (show 805 ≤ t.pc by rw [ht.1])
        (show (done.state lane).pc < 805 by rw [hAtV.1]; decide))
    have hKeep := keepMaskFrameUntilCut (low := 785) .afterReload (by decide) (by decide)
      (valueMaskAfterReloadCode p l batch tile warp lane _) hPath (by rw [hAtV.1])
      (by rw [ht.1]; decide) (ringShapeOfAt hAtV) (hMasks lane hl)
    let first := primingVPackEvents p l (thread lane) batch (co.2/6) (row lane) 0
    let second := primingVPackEvents p l (thread lane) batch (co.2/6) (row lane+64) 1
    let reload := primingVReloadEvents l (thread lane) (base lane) 0
    let events := first++second++reload
    have hLoad : (X.tr (thread lane)).drop (before lane+6) =
        reload ++ (X.tr (thread lane)).drop (pos lane) := by
      have he₀ := List.getElem?_eq_some_iff.mp hLow
      have he₁ := List.getElem?_eq_some_iff.mp hHigh
      rw [List.drop_eq_getElem_cons he₀.1,he₀.2,List.drop_eq_getElem_cons he₁.1,he₁.2,hArithmetic]
      rfl
    have hSplit : (X.tr (thread lane)).drop (before lane) =
        events ++ (X.tr (thread lane)).drop (pos lane) := by
      simpa only [events,List.append_assoc] using
        hStore.recorded.trans (congrArg (first++second++·) hLoad)
    have hExtend : pos lane = before lane+events.length := rfl
    have hTaken : (X.tr (thread lane)).take (pos lane) =
        (X.tr (thread lane)).take (before lane) ++ events := by
      rw [hExtend,List.take_add,hSplit,List.take_append_length]
    refine ⟨t,ht.mono ((holds_append ..).mpr ⟨((holds_append ..).mp ht.2.2.2.2).1,hKeep⟩),
      hPast,hTail,hBound,hReleased,?_,?_,hR.reloaded⟩
    · have hZero : events.countP Execution.isShfl = 0 := rfl
      rw [hTaken,List.countP_append,hZero,Nat.add_zero]
      exact done.ordinals.shfl lane hl
    · have hZero : events.countP isFullWarpVote = 0 := rfl
      rw [hTaken,List.countP_append,hZero,Nat.add_zero]
      exact done.ordinals.vote lane hl
  let _ : Inhabited TState := ⟨{}⟩
  choose! t hAt hPast hTail hBound hReleased hSh hVote hReload using hLane
  exact ⟨⟨⟨pos,t,t,⟨hSh,hVote⟩,hTail,fun _ _ => .refl,hAt⟩,
    fun _ _ => by dsimp [pos]; omega,hBound,hReleased,hPast⟩,rfl,hReload⟩

end PTX.Kernels.TmlFa4Fwd.Loader
