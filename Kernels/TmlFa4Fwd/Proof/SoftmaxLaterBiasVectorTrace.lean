-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasObservation
import Kernels.TmlFa4Fwd.Proof.Thread.BiasBarrierProgress
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
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
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRecordedEntry
import Lemmas.Step.ExitLast
import Lemmas.Flow.CountTake
import Lemmas.Flow.Widen

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Epilogue Thread Thread.Scores

/-- The two logical Bias elements consumed by one vector word on a repeated visit. -/
noncomputable def laterBiasWord (p : Params) (batch tile row head visit : Nat)
    (i : Fin 16) (word : Nat) : Value :=
  let col := 8*i.val+2*word
  biasLoadWord (visitBiasElement p batch tile row head visit col)
    (visitBiasElement p batch tile row head visit (col+1))

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X) (warp : Fin 8) {g start batch visit : Nat} {t : TState}
    (hWarp : warp.val = warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (hVisit : 0 < visit)
    (hCursor : observedBarrierOrdinal X (g,start) (11+(stageOf warp).val) = visit)
include hp hX hFrame hCuQ warp hWarp hb hLo hHi hVisit hCursor

/-- The repeated Bias vector run consumes all 128 decoded BF16 operands from its
own positive hardware phase and reaches the actual proxy fence on the same trace. -/
theorem laterBiasVectorsPath (ht : At t (biasReadPc true 0) [])
    (hBases : ∀ i, t.regs (biasReadSite true i).base =
      some (b32 (biasVectorBase l g (stageOf warp) true i)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop start) none) :
    let stage := stageOf warp
    let co := assignedCoordinates p batch (g/l.block)
    let row := 256*co.1+128*stage.val+(g%l.block)%128
    let words := laterBiasWord p batch co.1 row co.2 visit
    ∃ u, At u (biasFencePc true) [] ∧
      (∀ i, BiasWordReads l X true i g (start+4*i.val)
          (biasVectorBase l g stage true i) (words i) ∧
        BiasUnpacked true i u (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps true i r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+64)) none ∧
      observedBarrierOrdinal X (g,start+64) (11+stage.val) = visit ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop start).take 64) u := by
  let stage := stageOf warp
  let co := assignedCoordinates p batch (g/l.block)
  let row := 256*co.1+128*stage.val+(g%l.block)%128
  let words := laterBiasWord p batch co.1 row co.2 visit
  let base := fun i => biasVectorBase l g stage true i
  let cursor := fun j => observedBarrierOrdinal X (g,j) (11+stage.val) = visit
  have hShape (i : Fin 16) (k : Nat) (_ : k < 4) : BiasWordShape (words i k) :=
    biasLoadWordShape _ _
  have hBounds (i : Fin 16) :=
    biasVectorAddressBounds hp g stage i
  have hAddr (i : Fin 16) : base i + (biasReadSite true i).offset < 2^32 := by
    rw [show base i = biasVectorBase l g stage true i from rfl,biasVectorBase_add]
    exact (hBounds i).1
  have hAlign (i : Fin 16) : (base i + (biasReadSite true i).offset)%16 = 0 := by
    rw [show base i = biasVectorBase l g stage true i from rfl,biasVectorBase_add]
    exact (hBounds i).2
  have hAdvance (i : Fin 16) (k : Nat) (_ : k < 4) (bytes : List (Option Byte))
      (he : X.get (g,start+4*i.val+k) = some
        ⟨biasReadPc true i,.rd (biasReadAcc l g (base i) true i k) bytes⟩)
      (hPrev : cursor (start+4*i.val+k)) : cursor (start+4*i.val+k+1) := by
    unfold cursor observedBarrierOrdinal at *
    rw [countP_take_succ_false (p := Execution.isBarId (11+stage.val)) he rfl]
    exact hPrev
  have hValue (i : Fin 16) (k : Nat) (hk : k < 4) (hOrdinal : cursor (start+4*i.val+k))
      (bytes : List (Option Byte))
      (he : X.get (g,start+4*i.val+k) = some
        ⟨biasReadPc true i,.rd (biasReadAcc l g (base i) true i k) bytes⟩) :
      rebuild 3 bytes = .ok (words i k) := by
    have hRead : BiasVectorRead X (g,start+4*i.val+k) true i
        (biasReadAcc l g (base i) true i k) bytes := he
    obtain ⟨other,word,hOther,hWord,hValues⟩ := observedLaterBiasWord hp hX hFrame hCuQ hRead
    have hw : other = warp := Fin.ext (hOther.trans hWarp.symm)
    subst other
    have hWordIdx : k = word.val := congrArg Acc.elem hWord
    have hPos : 0 < observedBarrierOrdinal X (g,start+4*i.val+k) (11+(stageOf warp).val) :=
      hOrdinal.symm ▸ hVisit
    obtain ⟨chosen,hChosen,hChosenLo,hChosenHi,_,hValues⟩ := hValues hPos
    have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
      hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
    obtain ⟨owner,_,hOwner⟩ := tileBatch_existsUnique p hActive
    have hBatch := (hOwner chosen ⟨hChosen,hChosenLo,hChosenHi⟩).trans
      (hOwner batch ⟨hb,hLo,hHi⟩).symm
    subst chosen
    change observedBarrierOrdinal X (g,start+4*i.val+k) (11+(stageOf warp).val) = visit at hOrdinal
    rw [hOrdinal,← hWordIdx] at hValues
    exact hValues
  obtain ⟨u,hAt,hReads,hKeep,hTail,hCursorEnd,hPath⟩ :=
    biasVectorsTraceWithPathGuarded (g := g) (j := start) true base words hShape ht hBases
      hAddr hAlign
      (cursor := cursor)
      hCursor hValue hAdvance hRun (fun _ _ _ _ => .inl rfl)
  exact ⟨u,hAt,hReads,hKeep,hTail,hCursorEnd,hPath⟩

variable (ht : At t (biasReadPc true 0) (biasFenceFacts l g warp true))
    (hBases : ∀ i, t.regs (biasReadSite true i).base =
      some (b32 (biasVectorBase l g (stageOf warp) true i)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop start) none)
include ht hBases hRun

/-- The actual repeated Bias rendezvous preserves its 128 BF16 operands,
advances the Bias ordinal once, and reaches the affine-score instructions. -/
private theorem laterBiasVectorsThroughReleasePathWithRank :
    let stage := stageOf warp
    let co := assignedCoordinates p batch (g/l.block)
    let row := 256*co.1+128*stage.val+(g%l.block)%128
    let words := laterBiasWord p batch co.1 row co.2 visit
    let pos := if laneOf l g = 0 then start+64+3 else start+64+2
    ∃ u, At u (biasBodyStart true) (biasJoinFacts l warp) ∧
      (∀ i, BiasWordReads l X true i g (start+4*i.val)
          (biasVectorBase l g stage true i) (words i) ∧
        BiasUnpacked true i u (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps true i r) → r ∉ biasFenceWritten true → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) none ∧
      observedBarrierOrdinal X (g,pos) (11+stage.val) = visit+1 ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop start).take (pos-start)) u ∧
      ((X.tr g).take pos).countP earlyProbabilityMark =
        ((X.tr g).take start).countP earlyProbabilityMark := by
  let stage := stageOf warp
  obtain ⟨f,hAt,hReads,hRegs,hFF,hCount,hPath⟩ :=
    laterBiasVectorsPath hp hX hFrame hCuQ warp hWarp hb hLo hHi hVisit hCursor
      (ht.mono trivial) hBases hRun
  have hKeep (r v) (hr : (r,v) ∈ biasFenceFacts l g warp true) (i : Fin 16) :
      biasVectorKeeps true i r := by
    simp only [biasFenceFacts,biasStageReg,biasKeep,ite_true,List.mem_cons,List.not_mem_nil,
      or_false,Prod.mk.injEq] at hr
    rcases hr with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;>
      unfold biasVectorKeeps <;> fin_cases i <;> decide
  have hF : At f (biasFencePc true) (biasFenceFacts l g warp true) := hAt.mono
    (holdsSchedulerFrame ht.2.2.2.2 (fun r hR => hRegs r (fun i => by
      obtain ⟨⟨rr,v⟩,hr,heq⟩ := List.mem_map.mp hR
      exact heq ▸ hKeep rr v hr i)) (fun _ h => List.mem_map_of_mem h))
  obtain ⟨u,hFence,hBar,hRelease,hU,hTail,hStable,_,hReleasePath⟩ :=
    biasFinishTraceWithPathGuarded hp warp true hF hFF (cursor := fun _ => True)
      trivial (fun _ _ => .inl rfl) (fun _ _ _ _ h => h)
  have hUnpacked (i : Fin 16) (k : Nat) (hk : k < 4) :
      (biasUnpackRegs true i k).1 ∉ biasFenceWritten true ∧
        (biasUnpackRegs true i k).2 ∉ biasFenceWritten true := by
    fin_cases i <;> interval_cases k <;> decide
  refine ⟨u,hU,(fun i => ⟨(hReads i).1,?_⟩),(fun r hV hR =>
    (hStable r hR).trans (hRegs r hV)),hTail,?_,?_,?_⟩
  · intro k hk
    have hU := (hReads i).2 k hk
    have hR := hUnpacked i k hk
    exact ⟨(hStable _ hR.1).trans hU.1,(hStable _ hR.2).trans hU.2⟩
  · let key := 11+stage.val
    have hKeepFence := countP_take_succ_false (p := Execution.isBarId key) hFence rfl
    have hGrowBar := countP_take_succ (p := Execution.isBarId key) hBar
      (by simp [Execution.isBarId,key,stage])
    change observedBarrierOrdinal X (g,start+64+1) key =
      observedBarrierOrdinal X (g,start+64) key at hKeepFence
    change observedBarrierOrdinal X (g,start+64+1+1) key =
      observedBarrierOrdinal X (g,start+64+1) key + 1 at hGrowBar
    change observedBarrierOrdinal X
      (g, if laneOf l g = 0 then start+64+3 else start+64+2) key = visit+1
    by_cases hLane : laneOf l g = 0
    · rw [ite_eq_left hLane]
      have hKeepRelease := countP_take_succ_false (p := Execution.isBarId key) (hRelease hLane) rfl
      change observedBarrierOrdinal X (g,start+64+2+1) key =
        observedBarrierOrdinal X (g,start+64+2) key at hKeepRelease
      exact hKeepRelease.trans (hGrowBar.trans (congrArg (·+1) (hKeepFence.trans hCount)))
    · rw [ite_eq_right hLane]
      exact hGrowBar.trans (congrArg (·+1) (hKeepFence.trans hCount))

  · by_cases hLane : laneOf l g = 0
    · simp only [hLane,ite_true] at hReleasePath ⊢
      rw [show start+64+3-start = 64+3 by omega,List.take_add,List.drop_drop]
      exact hPath.append hReleasePath
    · simp only [hLane,ite_false] at hReleasePath ⊢
      rw [show start+64+2-start = 64+2 by omega,List.take_add,List.drop_drop]
      exact hPath.append hReleasePath

  · have hNone : (((X.tr g).drop start).take 64).countP earlyProbabilityMark = 0 := by
      apply List.countP_eq_zero.mpr
      intro e he
      obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp he
      have hK : k < 64 := (List.getElem?_eq_some_iff.mp hk).1.trans_le (by simp)
      rw [List.getElem?_take_of_lt hK,List.getElem?_drop] at hk
      let i : Fin 16 := ⟨k/4,by omega⟩
      obtain ⟨bytes,hGet,_⟩ := (hReads i).1 (k%4) (Nat.mod_lt _ (by decide))
      have hAt : start+4*i.val+k%4 = start+k := by dsimp [i]; omega
      rw [hAt] at hGet
      change X.get (g,start+k) = some e at hk
      obtain rfl := Option.some.inj (hk.symm.trans hGet)
      change ¬ ([4847,6532,7437] : List Nat).contains (biasReadPc true i) = true
      exact (by decide : ∀ i : Fin 16,
        ¬ ([4847,6532,7437] : List Nat).contains (biasReadPc true i) = true) i
    have hBase : ((X.tr g).take (start+64)).countP earlyProbabilityMark =
        ((X.tr g).take start).countP earlyProbabilityMark := by
      rw [List.take_add,List.countP_append,hNone,Nat.add_zero]
    have hF := countP_take_succ_false (p := earlyProbabilityMark) hFence rfl
    have hB := countP_take_succ_false (p := earlyProbabilityMark) hBar rfl
    change ((X.tr g).take (start+64+1)).countP earlyProbabilityMark =
      ((X.tr g).take (start+64)).countP earlyProbabilityMark at hF
    change ((X.tr g).take (start+64+2)).countP earlyProbabilityMark =
      ((X.tr g).take (start+64+1)).countP earlyProbabilityMark at hB
    change ((X.tr g).take (if laneOf l g = 0 then start+64+3 else start+64+2)).countP
      earlyProbabilityMark = _
    by_cases hLane : laneOf l g = 0
    · rw [ite_eq_left hLane]
      have hR := countP_take_succ_false (p := earlyProbabilityMark) (hRelease hLane) rfl
      exact hR.trans (hB.trans (hF.trans hBase))
    · rw [ite_eq_right hLane]
      exact hB.trans (hF.trans hBase)

end

private theorem repeatedBiasAfterFirstRendezvous {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j wait id phase : Nat}
    {obj : Loc} {acq : Bool} {scope : MbarScope}
    (hBar : X.get (g,j) = some ⟨3583,.bar id (some 128) .sync⟩)
    (hWait : X.get (g,wait) = some ⟨5181,.wait obj phase true acq scope⟩) : j < wait := by
  have hFloor : (kernel.code.drop 3584).all (fun i => staysPastEvent 3584 i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSeg : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (3584 ≤ seg.stop)
      | none => false) = true := by set_option maxRecDepth 100000 in kernel_rfl
  exact traceOrderOfPcFloor (floor := 3584) hX hFloor hSeg hBar hWait
    (show 3583 < 3584 by decide) (show 3584 ≤ 5181 by decide)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X) {g entry wait last pc phase batch : Nat} (warp : Fin 8)
    (hw : warp.val = warpIndex l g) {s : TState} {ending : Option TState}
    (hEntry : At s 3103 [(1062,b32 warp.val),(2535,b32 l.sharedBase)])
    (hEntryRun : Run kernel Assumptions.all l g s ((X.tr g).drop entry) ending)
    (hPos : entry ≤ wait) {obj : Loc} {acq : Bool} {scope : MbarScope}
    (he : X.get (g,wait) = some ⟨5181,.wait obj phase true acq scope⟩)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLater : wait < last) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hX hFrame hCuQ warp hw hEntry hEntryRun hPos he hExit hLater hb hLo hHi

/-- An actual successful repeated Bias acquire supplies all logical Bias operands and preserves the
64 packed QK pairs through the affine-score entry. -/
private theorem laterBiasThroughAcquireFromEntryWithRank :
    let stage := stageOf warp
      let visit := observedBarrierOrdinal X (g,wait) (11+stage.val)
      let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*stage.val+(g%l.block)%128
      let words := laterBiasWord p batch co.1 row co.2 visit
      let pos := if laneOf l g = 0 then wait+1+64+3 else wait+1+64+2
      0 < visit ∧ visit < Mma.trips p batch co.1 ∧
      visit < Mma.trips p batch co.1-stageGeometryBlocks p batch co.1 stage+10 ∧
      ∃ pre u, pre.pc = 5181 ∧
        Run kernel Assumptions.all l g pre ((X.tr g).drop wait) none ∧
        (∀ pair < 64, u.regs (7367+pair) = pre.regs (7367+pair)) ∧
        At u (biasBodyStart true) (biasJoinFacts l warp) ∧
        readERealPair l g u (.reg 7896) =
          some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))) ∧
        (∀ i, BiasWordReads l X true i g (wait+1+4*i.val)
            (biasVectorBase l g stage true i) (words i) ∧
          BiasUnpacked true i u (words i)) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop pos) none ∧
        observedBarrierOrdinal X (g,pos) (11+stage.val) = visit+1 ∧
        TraceReach kernel Assumptions.all l g s (((X.tr g).drop entry).take (wait-entry)) pre ∧
        Stops kernel Assumptions.all l g pre ∧
        TraceReach kernel Assumptions.all l g pre (((X.tr g).drop wait).take (pos-wait)) u ∧
        (∀ r, r ∉ [9755,4166,4167,4168,4169,4170] →
          (∀ i, biasVectorKeeps true i r) → r ∉ biasFenceWritten true →
          u.regs r = pre.regs r) ∧
        ((X.tr g).take pos).countP earlyProbabilityMark =
          ((X.tr g).take wait).countP earlyProbabilityMark := by
  have hExitIn : ((X.tr g).drop entry)[last-entry]? = some ⟨pc,.exit⟩ := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
  have hEnding : ending = none := by
    cases ending with
    | none => rfl
    | some u => exact (hEntryRun.no_exit hExitIn).elim
  subst ending
  have hMore : (X.tr g).drop (wait+1) ≠ [] := by
    intro hEmpty
    have hLength := len_of_get hExit
    have hBound := List.drop_eq_nil_iff.mp hEmpty
    change last < (X.tr g).length at hLength
    omega
  obtain ⟨pre,t,hPre,hPreRun,hDots,ht,hScale,hBases,hRun,hReach,hStop,hKeeps,hToRead⟩ :=
    repeatedBiasVectorStartWithPath hp warp hEntry hEntryRun hPos he hMore
  dsimp only
  let stage := stageOf warp
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  have hWarp : warpIndex l g < 8 := hw ▸ warp.isLt
  obtain ⟨j,hBar⟩ := firstBiasDecodedArrivalOfActiveExit hp hX hCuQ hActive hWarp
    (⟨last,_,hExit,rfl⟩ : Exited X g)
  have hStage : stage.val = warpIndex l g/4 := by
    rw [← hw]
    fin_cases warp <;> rfl
  rw [← hStage] at hBar
  have hj := repeatedBiasAfterFirstRendezvous hX hBar he
  have hVisit : 0 < observedBarrierOrdinal X (g,wait) (11+stage.val) := by
    by_contra! hBad
    have hZero : observedBarrierOrdinal X (g,wait) (11+stage.val) = 0 := by omega
    unfold observedBarrierOrdinal at hZero
    have hm : ⟨3583,.bar (11+stage.val) (some 128) .sync⟩ ∈ (X.tr g).take wait := by
      apply List.mem_of_getElem? (i := j)
      rw [List.getElem?_take_of_lt hj]
      exact hBar
    have hWrong := List.countP_eq_zero.mp hZero _ hm
    simp [Execution.isBarId] at hWrong
  have hOrdinal := countP_take_succ_false (p := Execution.isBarId (11+stage.val)) he rfl
  obtain ⟨u,hu,hReads,hKeep,hTail,hEnd,hToBody,hQuiet⟩ :=
    laterBiasVectorsThroughReleasePathWithRank hp hX hFrame hCuQ warp
    hw hb hLo hHi hVisit hOrdinal ht hBases hRun
  have hReadFirst := (hReads 0).1 0 (by decide)
  dsimp only [Fin.val_zero] at hReadFirst
  simp only [Nat.mul_zero,Nat.add_zero] at hReadFirst
  obtain ⟨bytes,hRead,_⟩ := hReadFirst
  obtain ⟨peer,_,hPeer,_,hBounds⟩ := observedLaterBiasWordInRange hp hX hFrame hCuQ
    (show BiasVectorRead X (g,wait+1) true 0
      (biasReadAcc l g (biasVectorBase l g stage true 0) true 0 0) bytes from hRead)
  have hEq : peer = warp := Fin.ext (hPeer.trans hw.symm)
  subst peer
  change observedBarrierOrdinal X (g,wait+1) (11+stage.val) =
    observedBarrierOrdinal X (g,wait) (11+stage.val) at hOrdinal
  obtain ⟨owner,ho,hOwnerLo,hOwnerHi,hTrips,hBiased,_⟩ := hBounds (hOrdinal.symm ▸ hVisit)
  obtain ⟨chosen,_,hUnique⟩ := tileBatch_existsUnique p hActive
  have hSame := (hUnique owner ⟨ho,hOwnerLo,hOwnerHi⟩).trans
    (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst owner
  rw [hOrdinal] at hTrips hBiased
  obtain ⟨_,inv,_,hInv,_,_⟩ := hp.scales
  have hBits := (hp.values (14,p.invScaleBits) (by simp [Params.scalarWords])).1
  have hRead := valFloat_b32 (by omega) hInv
  have hSplit : splitValue 64 (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)) =
      (b32 p.invScaleBits,b32 p.invScaleBits) :=
    split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact hBits)
  have hSafe (i : Fin 16) : biasVectorKeeps true i 7896 := by
    unfold biasVectorKeeps
    fin_cases i <;> decide
  have hPacked : u.regs 7896 = some (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)) :=
    (hKeep 7896 hSafe (by decide)).trans hScale
  have hDecoded := readERealPair_reg (L := l) (g := g) hPacked
    (by rw [hSplit]; exact hRead) (by rw [hSplit]; exact hRead)
  have hAbi : abiFloat p.invScaleBits = (inv : ℝ) := by simp [abiFloat,hInv]
  refine ⟨hVisit,hTrips,hBiased,pre,u,hPre,hPreRun,?_,hu,?_,hReads,hTail,hEnd,hReach,hStop,?_,?_,?_⟩
  · intro pair hPair
    have hVector (i : Fin 16) : biasVectorKeeps true i (7367+pair) := by
      have hRead := (by decide : ∀ k : Fin 16,
        (biasReadRegs true k).all (fun r => decide (r < 7367)) = true) i
      have hUnpack := (by decide : ∀ k : Fin 16, (biasUnpackRegs true k 0).1 < 7367) i
      exact ⟨fun hMem => by
        have hBound := of_decide_eq_true (List.all_eq_true.mp hRead _ hMem)
        omega,Or.inr (by omega)⟩
    have hSignal : 7367+pair ∉ biasFenceWritten true := by
      intro hMem
      have hWritten :
          (biasFenceWritten true).all (fun r => decide (r < 7367 ∨ 7431 ≤ r)) = true := by decide
      have hBound := of_decide_eq_true (List.all_eq_true.mp hWritten _ hMem)
      omega
    exact (hKeep _ hVector hSignal).trans (hDots _ (by omega) (by omega))
  · rw [hAbi]
    exact hDecoded

  · by_cases hLane : laneOf l g = 0
    · simp only [hLane,ite_true] at hToBody ⊢
      have hLen : wait+1+64+3-wait = 1+(wait+1+64+3-(wait+1)) := by omega
      rw [hLen,List.take_add,List.drop_drop]
      exact hToRead.append hToBody
    · simp only [hLane,ite_false] at hToBody ⊢
      have hLen : wait+1+64+2-wait = 1+(wait+1+64+2-(wait+1)) := by omega
      rw [hLen,List.take_add,List.drop_drop]
      exact hToRead.append hToBody
  · intro r hPre hRead hFence
    exact (hKeep r hRead hFence).trans (hKeeps r hPre)
  · have hKeepWait := countP_take_succ_false (p := earlyProbabilityMark) he rfl
    change ((X.tr g).take (wait+1)).countP earlyProbabilityMark =
      ((X.tr g).take wait).countP earlyProbabilityMark at hKeepWait
    exact hQuiet.trans hKeepWait

theorem laterBiasThroughAcquireFromEntryWithPath :
    let stage := stageOf warp
      let visit := observedBarrierOrdinal X (g,wait) (11+stage.val)
      let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*stage.val+(g%l.block)%128
      let words := laterBiasWord p batch co.1 row co.2 visit
      let pos := if laneOf l g = 0 then wait+1+64+3 else wait+1+64+2
      0 < visit ∧ visit < Mma.trips p batch co.1 ∧
      visit < Mma.trips p batch co.1-stageGeometryBlocks p batch co.1 stage+10 ∧
      ∃ pre u, pre.pc = 5181 ∧
        Run kernel Assumptions.all l g pre ((X.tr g).drop wait) none ∧
        (∀ pair < 64, u.regs (7367+pair) = pre.regs (7367+pair)) ∧
        At u (biasBodyStart true) (biasJoinFacts l warp) ∧
        readERealPair l g u (.reg 7896) =
          some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))) ∧
        (∀ i, BiasWordReads l X true i g (wait+1+4*i.val)
            (biasVectorBase l g stage true i) (words i) ∧
          BiasUnpacked true i u (words i)) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop pos) none ∧
        observedBarrierOrdinal X (g,pos) (11+stage.val) = visit+1 ∧
        TraceReach kernel Assumptions.all l g s (((X.tr g).drop entry).take (wait-entry)) pre ∧
        Stops kernel Assumptions.all l g pre ∧
        TraceReach kernel Assumptions.all l g pre (((X.tr g).drop wait).take (pos-wait)) u ∧
        ∀ r, r ∉ [9755,4166,4167,4168,4169,4170] →
          (∀ i, biasVectorKeeps true i r) → r ∉ biasFenceWritten true →
          u.regs r = pre.regs r := by
  obtain ⟨hVisit,hTrips,hBudget,pre,u,hPre,hPreRun,hDots,hu,hScale,hReads,hTail,
    hEnd,hReach,hStop,hPath,hKeep,_⟩ :=
    laterBiasThroughAcquireFromEntryWithRank hp hX hFrame hCuQ warp hw hEntry
      hEntryRun hPos he hExit hLater hb hLo hHi
  exact ⟨hVisit,hTrips,hBudget,pre,u,hPre,hPreRun,hDots,hu,hScale,hReads,hTail,
    hEnd,hReach,hStop,hPath,hKeep⟩

omit hp hX hFrame hCuQ warp hw hEntry hEntryRun hPos he hExit hLater hb hLo hHi in
/-- From the successful Bias acquire to the affine-score body, the recorded vector reads,
rendezvous and release issue no early probability packet. -/
theorem repeatedBiasAffineEarlyRank {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g wait last pc batch phase : Nat}
    {obj : Loc} {acq : Bool} {scope : MbarScope}
    (he : X.get (g,wait) = some ⟨5181,.wait obj phase true acq scope⟩)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLater : wait < last)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let pos := if laneOf l g = 0 then wait+1+64+3 else wait+1+64+2
    ((X.tr g).take pos).countP earlyProbabilityMark =
      ((X.tr g).take wait).countP earlyProbabilityMark := by
  obtain ⟨other,hOther,_⟩ :=
    softmaxBodySuffix hp hX he (show 3420 ≤ 5181 by decide) (show 5181 < 7742 by decide)
  obtain ⟨warp,hWarp,entry,s,ending,hStart,hEntry,_,hEntryRun⟩ :=
    softmaxRoleEntryRecorded hp hX he (by decide : 173 < 5181)
      (by decide : 5181 ≠ 3102) (hOther ▸ other.isLt)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hRank⟩ :=
    laterBiasThroughAcquireFromEntryWithRank hp hX hFrame (hFrame.metadataProtected hp).1
      warp hWarp hEntry hEntryRun hStart he hExit hLater hb hLo hHi
  exact hRank

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X) {g wait last pc phase batch : Nat} {obj : Loc} {acq : Bool}
    {scope : MbarScope} (he : X.get (g,wait) = some ⟨5181,.wait obj phase true acq scope⟩)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLater : wait < last) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hX hFrame hCuQ he hExit hLater hb hLo

end PTX.Kernels.TmlFa4Fwd.Softmax
