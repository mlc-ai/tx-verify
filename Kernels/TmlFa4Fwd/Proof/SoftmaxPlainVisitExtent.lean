-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedPlainScore
public import Kernels.TmlFa4Fwd.Proof.SoftmaxCounterEntry
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
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue Thread Thread.Scores

private theorem plainAfterFirstRoundAudit :
    (kernel.code.drop 5006).all (fun i => Thread.staysPastEvent 5006 i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem plainAfterFirstSegmentAudit :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (5006 ≤ seg.stop)
      | none => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A plain score load can only occur after the completed biased probability
publications of its selected request and stage. -/
theorem plainScoreVisitLower (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {g pos last pc addr : Nat} {values : List Value} {shape : TcShape} (hw : warpIndex l g < 8)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) (q : Fin 4)
    (he : X.get (g,pos) = some ⟨scorePc .unbiased q,.tc (.ld addr values shape)⟩)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let stage := stageOf ⟨warpIndex l g,hw⟩
      let tile := (assignedCoordinates p batch (g/l.block)).1
      let blocks := Mma.trips p batch tile
      let cap := blocks-stageGeometryBlocks p batch tile stage+10
      1+firstBiasedRepeats blocks cap ≤ probabilityOrdinal l X (g/l.block) stage 0 (g,pos) := by
  let stage := stageOf ⟨warpIndex l g,hw⟩
  let src := laneOf l g
  let target : Event := ⟨scorePc .unbiased q,.tc (.ld addr values shape)⟩
  have hLane : warpLane l g src = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  obtain ⟨batch,hb,hLo,hHi,j,s,waits,before,rest,trail,_,hList,hReturn,hFirst,hCounters,
      hWalk,hSites⟩ :=
    activeCountersOfExit hp hX (event_thread_lt hX he) hw
      (show src < 32 from Nat.mod_lt _ (by decide)) hWork hCuQ hUsedK (hLane.symm ▸ hExit)
  rw [hLane] at hList hWalk
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  let cap := blocks-stageGeometryBlocks p batch tile stage+10
  let past := p.kLength batch-p.qLength batch+256*tile
  have hCounters' : At s 5006 (firstLoopGeometry blocks cap past) := hCounters
  have hBounds := firstGeometryBounds hp stage hb (assignedCoordinates_valid hp hLo hHi).1
    (lane := 0) (by decide)
  have hBlocks : 0 < blocks := hBounds.1
  have hB32 : blocks < 2^31 := hBounds.2.1
  have hC : 0 < cap := hBounds.2.2.1
  have hC32 : cap < 2^31 := hBounds.2.2.2.1
  let front := (X.tr g).take (j+3) ++ waits
  have hTrace : X.tr g = front ++ (before ++ rest) := by
    dsimp only [front]
    conv_lhs => rw [← List.take_append_drop (j+3) (X.tr g)]
    rw [hList]
    simp only [List.append_assoc]
  have hFirstMark : 0 < before.countP (barrierMark 4397) := by omega
  obtain ⟨first,hMem,hMark⟩ := List.countP_pos_iff.mp hFirstMark
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hMem
  have hI := (List.getElem?_eq_some_iff.mp hi).1
  have hFirstGet : X.get (g,front.length+i) = some first := by
    change (X.tr g)[front.length+i]? = some first
    rw [hTrace,List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left,List.getElem?_append_left hI]
    exact hi
  have hTarget : target = ⟨scorePc .unbiased q,.tc (.ld addr values shape)⟩ := rfl
  have hTargetPc : 6654 ≤ target.pc := by
    change 6654 ≤ scorePc .unbiased q
    fin_cases q <;> decide
  have hAfter := Thread.traceOrderOfPcFloor hX plainAfterFirstRoundAudit plainAfterFirstSegmentAudit
    hFirstGet he (hSites first hMem) (show 5006 ≤ target.pc by omega)
  have hAfterPrefix : front.length ≤ pos := by omega
  have hAfterFirst : front.length+before.length ≤ pos := by
    by_contra! h
    have hIn : pos-front.length < before.length := by omega
    have hGet : before[pos-front.length]? = some target := by
      have hh : (X.tr g)[pos]? = some target := he
      rwa [hTrace,List.getElem?_append_right hAfterPrefix,List.getElem?_append_left hIn] at hh
    have hEarlier := hSites target (List.mem_of_getElem? hGet)
    omega
  have hRest : target ∈ rest := by
    apply List.mem_of_getElem? (i := pos-front.length-before.length)
    have hh : (X.tr g)[pos]? = some target := he
    rwa [hTrace,List.getElem?_append_right hAfterPrefix,
      List.getElem?_append_right (by omega : before.length ≤ pos-front.length)] at hh
  refine ⟨batch,hb,hLo,hHi,?_⟩
  change 1+firstBiasedRepeats blocks cap ≤ probabilityOrdinal l X (g/l.block) stage 0 (g,pos)
  have hFirstCredit := firstCreditBeforeRepeatedScore hX .unbiased (by decide) q he
  rw [← earlyProbabilityCount hp hX stage hw rfl (len_of_get he),
    earlyProbabilityMarkCount]
  dsimp only
  let split := firstPlainSplit blocks cap
  let biased := firstBiasedRepeats blocks cap
  change 1+biased ≤ _
  by_cases hNone : biased = 0
  · omega
  obtain ⟨a,_,ha,hLaneWalk⟩ := firstCountEntryWalk
    hBlocks hB32 hC hC32 hCounters' hWalk hReturn
  have hAt : At a 5032 ((7248,b32 (2^32-(blocks-split))) :: repeatCountLimits blocks split) := by
    simpa only [show firstBiasedRepeats blocks cap ≠ 0 from hNone,ite_false] using ha
  have hMore : split+1 < blocks := by
    unfold biased firstBiasedRepeats at hNone
    omega
  have hWord : a.regs 7248 = some (b32 (2^32-(blocks-split))) := hAt.2.2.2.2.1
  obtain ⟨_,early,late,_,hParts,_,_,hCount,_,_,_,_,_,hEarly⟩ :=
    loopProbabilityCountBounds .biased hLaneWalk hAt.1 (hAt.2.1 ▸ Nat.zero_le _)
      hWord (by omega) hRest hTargetPc
  change early.countP (barrierMark 6532) = _ at hCount
  rw [initialBiasedDistance hB32 hMore] at hCount
  have hTrace' : X.tr g = (front ++ before) ++ (early ++ late) := by
    rw [hTrace,hParts,← List.append_assoc]
  have hAfterBiased : (front ++ before).length+early.length ≤ pos := by
    by_contra! h
    have ha : (front ++ before).length ≤ pos := by simpa only [List.length_append]
    have hIn : pos-(front ++ before).length < early.length := by omega
    have hGet : early[pos-(front ++ before).length]? = some target := by
      have hh : (X.tr g)[pos]? = some target := he
      rwa [hTrace',List.getElem?_append_right ha,List.getElem?_append_left hIn] at hh
    have h := (hEarly target (List.mem_of_getElem? hGet)).2
    change target.pc < 6650 at h
    omega
  have hTake : (X.tr g).take ((front ++ before).length+early.length) =
      (front ++ before) ++ early := by
    rw [hTrace',← List.append_assoc,← List.length_append,List.take_append_length]
  have hMon := countP_take_mono (barrierMark 6532) (X.tr g) hAfterBiased
  rw [hTake,List.countP_append,hCount] at hMon
  change (front ++ before).countP (barrierMark 6532)+(blocks-1-split) ≤
    ((X.tr g).take pos).countP (barrierMark 6532) at hMon
  change 1+(blocks-1-split) ≤ _
  omega

/-- A plain load's observed score generation is inside the non-Bias portion
of the selected launch request. The chosen key packet bounds its upper extent. -/
theorem plainScoreVisitBounds (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    {g pos last pc batch : Nat} {values : List Value} {stage : Fin 2} (hw : warpIndex l g < 8)
    (hs : warpIndex l g/4 = stage.val) (q : Fin 4)
    (he : X.get (g,pos) =
      some ⟨scorePc .unbiased q,.tc (.ld (scoreAddress l g stage q) values .s32x32b)⟩)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let tile := (assignedCoordinates p batch (g/l.block)).1
    let trips := Mma.trips p batch tile
    let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,pos)
    trips-stageGeometryBlocks p batch tile stage+10 ≤ visit ∧ visit < trips := by
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  have hUsedK := (hFrame.metadataProtected hp).2
  obtain ⟨actual,hActual,hLower,hUpper,hBound⟩ := plainScoreVisitLower hp hX hCuQ hUsedK
    hw hWork q he hExit
  obtain ⟨other,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hBatch := (hUnique actual ⟨hActual,hLower,hUpper⟩).trans
    (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst actual
  have hStage : stageOf (⟨warpIndex l g,hw⟩ : Fin 8) = stage := Fin.ext hs
  simp only [hStage] at hBound
  obtain ⟨_,_,_,hLength,_⟩ := scoreLoadAddress hp hX .unbiased q he
  obtain ⟨observed,hCell⟩ := ScoreLoadCell.ofDecoded hp hX .unbiased q he
    (show 0 < values.length by rw [hLength]; decide)
    (show tcDataCell l g .s32x32b (scoreAddress l g stage q) 0 = _ from rfl)
  obtain ⟨_,_,hActualStage,_,_⟩ := hCell.acquire hp hX
  have hEqual : observed = stage := Fin.ext (hActualStage.symm.trans hs)
  subst observed
  obtain ⟨bank⟩ := observedScoreQkBank hp hX hCuQ hCell
  have hPositive : 0 < scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit := by
    rw [bank.seen.generation]
    exact repeatedScoreHasEarlierVisit hp hX stage hw hs .unbiased (by decide) q he
  have hLimit := bank.recurringVisitBound hp hX hFrame hPositive hb hLo hHi
  rw [bank.seen.generation] at hLimit
  refine ⟨?_,hLimit⟩
  dsimp only at hBound hLimit ⊢
  unfold firstBiasedRepeats firstPlainSplit at hBound
  omega

end PTX.Kernels.TmlFa4Fwd.Softmax
