-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleVoteProjection
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionInitialTensorCoverage
import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleSlots
import Lemmas.Flow.PollRounds
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

private theorem dataColl {e : Event} (h : isTcData e = true) : isTcColl e = true := by
  rcases e with ⟨pos,kind⟩
  cases kind <;> try cases h
  rename_i tc
  cases tc <;> first | rfl | cases h

private theorem correctionEventClass {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i : Nat} (hRole : warpIndex l g < 12) {e : Event}
    (hGet : X.get (g,i) = some e) : isTcColl e = isTcData e := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨arithmeticTensorCollectiveIsData hp hX hRole hGet, dataColl⟩

set_option maxRecDepth 100000 in
private theorem correctionBeforeRescaleFloor :
    (kernel.code.drop 7989).all (fun i => staysPastEvent 7989 i.op) = true := by kernel_rfl

private theorem correctionPrefixNoTensor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g q : Nat} (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hInit : X.get (g,q) = some ⟨7988,.bar (statsBarrierId l g 1) (some 64) .sync⟩) :
    correctionTensorLabels ((X.tr g).take (q+1)) = [] := by
  apply correctionTensorLabelsNone
  intro e hMem
  obtain ⟨r,hr⟩ := List.mem_iff_getElem?.mp hMem
  have hR : r < q+1 := ((List.getElem?_eq_some_iff.mp hr).1).trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hR] at hr
  by_cases hColl : isTcData e = true
  · have hBand := correctionCollectiveBand hp hX hLo hHi hr (dataColl hColl)
    have hOrder := traceOrderOfSegmentFloor (floor := 7989) hX correctionBeforeRescaleFloor
      (fun site hSite hm => by
        simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hm
        omega) hInit hr (show 7988 < 7989 by decide) (by omega)
    omega
  · exact Bool.eq_false_iff.mpr hColl

private def correctionFinalSchedule : List (Nat × Fin 4) :=
  correctionFinalStageSchedule 0 ++ correctionFinalStageSchedule 1

private structure CorrectionSchedule (p : Params) (l : Launch) (X : Execution) (g : Nat) where
  batch : Nat
  batchValid : batch < p.batch
  assignedLo : tilePrefix p batch * p.heads ≤ g/l.block
  assignedHi : g/l.block < tilePrefix p (batch+1) * p.heads
  base : Nat
  final : Bool
  bound : (rescaleVoteLabels (X.tr g)).length ≤
    2*(Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
  full : final = true → (rescaleVoteLabels (X.tr g)).length =
    2*(Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
  labels : List.IsPrefix (correctionTensorLabels (X.tr g))
    (rescaleVoteSchedule (rescaleVoteLabels (X.tr g)) ++
      if final then correctionFinalSchedule else [])
  vote {n : Nat} {stage : Fin 2} {word : BitVec 32} :
    (rescaleVoteLabels (X.tr g))[n]? = some (stage,word) →
    ∃ j site bit, X.get (g,j) = some ⟨site,.vote (2^32-1) bit word⟩ ∧
      site = (if stage = 0 then 8009 else 8228) ∧ X.MaskK voteClass (g,j) (2^32-1) (base+n) ∧
      (rescaleVoteLabels ((X.tr g).take j)).length = n
  peerFirst {h j ordinal site : Nat} {bit : Bool} {word : BitVec 32} :
    SameWarp l g h → X.get (h,j) = some ⟨site,.vote (2^32-1) bit word⟩ →
    (site = 8009 ∨ site = 8228) → (rescaleVoteLabels ((X.tr h).take j)).length = 0 →
    X.MaskK voteClass (h,j) (2^32-1) ordinal → base ≤ ordinal → base = ordinal

private theorem noBallotsAfterRescale {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (h : 8447 ≤ s.pc)
    (hw : Walk kernel Assumptions.all l g s events visits) : rescaleVoteLabels events = [] := by
  apply rescaleVoteLabelsNone
  intro e he
  have hMark (stage : Fin 2) := List.countP_eq_zero.mp (correctionRescaleVoteNone stage h hw) e he
  constructor
  · have h0 := hMark 0
    simpa [isRescaleStageVote, correctionRescaleMarkPc, barrierMark] using h0
  · have h1 := hMark 1
    simpa [isRescaleStageVote, correctionRescaleMarkPc, barrierMark] using h1

private theorem tensorSuffixPlan {l : Launch} {g steps : Nat} {s : TState}
    {F : List (Nat × Value)}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hAt : At s (if steps < 2 then 8447 else 8006) F)
    (hSeed : 2 ≤ steps → s.regs 7278 = some (b32 (2^32-steps)))
    (hBound : steps ≤ 2^32)
    (hData : ∀ e ∈ events, 9044 ≤ e.pc → isTcData e = false) :
    ∃ final : Bool, (rescaleVoteLabels events).length ≤ 2*(steps-1) ∧
      (final = true → (rescaleVoteLabels events).length = 2*(steps-1)) ∧
      List.IsPrefix (correctionTensorLabels events)
        (rescaleVoteSchedule (rescaleVoteLabels events) ++
          if final then correctionFinalSchedule else []) := by
  by_cases hSkip : steps < 2
  · have hp : s.pc = 8447 := hAt.1.trans (ite_eq_left hSkip)
    have hNoVote := noBallotsAfterRescale hp.ge hw
    have hN : steps-1 = 0 := by omega
    refine ⟨true,?_,?_,?_⟩
    · simp [hNoVote,hN]
    · intro _
      simp [hNoVote,hN]
    · simpa [hNoVote,rescaleScheduleNil,correctionFinalSchedule] using
        correctionFinalizationTraceLabels hw hp hData
  have hp : s.pc = 8006 := hAt.1.trans (ite_eq_right hSkip)
  have hLo : 2 ≤ steps := by omega
  have hFrame : CorrectionRescaleFrame s (b32 (2^32-steps)) := ⟨hAt.2.1,hAt.2.2.1,hSeed hLo⟩
  rcases correctionRescaleTraceDecompose hw hp hFrame hLo hBound with ⟨hPrefix,hLen⟩ |
    ⟨u,pre,tail,rest,hSplit,hU,hLab,hVotes,hWalk⟩
  · exact ⟨false,hLen,fun h => Bool.noConfusion h,
      by simpa only [Bool.false_eq_true,↓reduceIte,List.append_nil] using hPrefix⟩
  have hTailVotes := noBallotsAfterRescale hU.ge hWalk
  have hLen : (rescaleVoteLabels events).length = 2*(steps-1) := by
    rw [hSplit,rescaleVoteLabelsAppend,hTailVotes,List.append_nil,hVotes]
  have hTailData (e : Event) (he : e ∈ tail) (hLate : 9044 ≤ e.pc) : isTcData e = false := by
    apply hData e _ hLate
    rw [hSplit]
    exact List.mem_append_right _ he
  have hPrefix := correctionFinalizationTraceLabels hWalk hU hTailData
  refine ⟨true,hLen.le,fun _ => hLen,?_⟩
  rw [hSplit,correctionTensorLabelsAppend,rescaleVoteLabelsAppend,hLab,hTailVotes,List.append_nil]
  exact (List.prefix_append_right_inj _).2 hPrefix

private theorem actualCorrectionSchedule {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hUsedK : ∀ b < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*b)).at k))
    {g i k : Nat} (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hk : X.TcK (g,i) k) : Nonempty (CorrectionSchedule p l X g) := by
  have hWork := correctionTensorCollectiveRequiresWork hp hX hLo hHi hk
  obtain ⟨⟨target,hGet,hColl⟩,_⟩ := hk
  have hBand := correctionCollectiveBand hp hX hLo hHi hGet hColl
  have hg := event_thread_lt hX hGet
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨batch,hb,hCtaLo,hCtaHi,ends,shuffles,votes,cur,hFollow⟩ :=
    correctionActiveTileOfEvent hp hX hg hLo hHi hl hWork (by omega) (hSelf.symm ▸ hGet)
  have hRun := (cur.continuation lane hl).after_local_nonempty
    (cur.localSteps lane hl) hFollow.nonempty
  obtain ⟨t,hAt,hPos,_,_,hInit,hRest⟩ := correctionLaneBeforeRescaleOfEvent hp hX hb hCtaLo hCtaHi
    (cur.checkpoint lane hl) hRun hUsedK hFollow.before (by omega) hFollow.get
  have hMarks (stage : Fin 2) := noRescaleMarkerBeforeInitial hX hInit stage
  have hZero (stage : Fin 2) :
      ((X.tr (warpLane l g lane)).take (cur.pos lane)).countP (isRescaleStageVote stage) = 0 := by
    have hLe := countP_take_mono (isRescaleStageVote stage) (X.tr (warpLane l g lane))
      (show cur.pos lane ≤ cur.pos lane+5+1 by omega)
    have hZ := hMarks stage
    change ((X.tr (warpLane l g lane)).take (cur.pos lane+5+1)).countP
      (isRescaleStageVote stage) = 0 at hZ
    omega
  obtain ⟨_,u,hu,hU⟩ := correctionLaneRescaleSetup hp hb hCtaLo hCtaHi hAt
  let position := cur.pos lane+6
  let steps := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have hSeed (h : 2 ≤ steps) : u.regs 7278 = some (b32 (2^32-steps)) := by
    have hh := hU.2.2.2.2
    unfold correctionRescaleSetupFacts at hh
    rw [ite_eq_right (show ¬steps < 2 by omega)] at hh
    exact hh.1
  have hBound : steps ≤ 2^32 := by
    have hTrips := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hCtaLo hCtaHi).1).2.1
    have hK := (hp.lengths batch hb).2.2
    change steps ≤ _ at hTrips
    omega
  have hSuffix : (X.tr g).drop position ≠ [] := by
    intro hn
    have hLen := List.drop_eq_nil_iff.mp hn
    have hI : i < (X.tr g).length := len_of_get hGet
    change position ≤ i at hPos
    omega
  rw [hSelf] at hInit hRest hu
  have hW := hRest.after_local_nonempty (run_rtg hu) hSuffix
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hW
  have hNoData (e : Event) (hMem : e ∈ (X.tr g).drop position) (hLate : 9044 ≤ e.pc) :
      isTcData e = false := by
    obtain ⟨r,hr⟩ := List.mem_iff_getElem?.mp hMem
    rw [List.getElem?_drop] at hr
    by_cases hColl : isTcData e = true
    · have h := correctionCollectiveBand hp hX hLo hHi hr (dataColl hColl)
      omega
    · exact Bool.eq_false_iff.mpr hColl
  obtain ⟨final,hSize,hFull,hPlan⟩ := tensorSuffixPlan hWalk hU hSeed hBound hNoData
  have hStartData := correctionPrefixNoTensor hp hX hLo hHi hInit
  have hStartVote : rescaleVoteLabels ((X.tr g).take position) = [] := by
    apply rescaleVoteLabelsNone
    intro e he
    have h (stage : Fin 2) := hMarks stage
    have h0 := h 0
    have h1 := h 1
    rw [hSelf] at h0 h1
    have h0' := List.countP_eq_zero.mp h0 e he
    have h1' := List.countP_eq_zero.mp h1 e he
    simp [isRescaleStageVote,correctionRescaleMarkPc,barrierMark] at h0' h1'
    exact ⟨h0',h1'⟩
  have hTrace : (X.tr g).take position ++ (X.tr g).drop position = X.tr g :=
    List.take_append_drop ..
  have hVoteTrace : rescaleVoteLabels (X.tr g) = rescaleVoteLabels ((X.tr g).drop position) := by
    conv_lhs => rw [← hTrace,rescaleVoteLabelsAppend,hStartVote,List.nil_append]
  have hDataTrace : correctionTensorLabels (X.tr g) =
      correctionTensorLabels ((X.tr g).drop position) := by
    conv_lhs => rw [← hTrace,correctionTensorLabelsAppend,hStartData,List.nil_append]
  refine ⟨⟨batch,hb,hCtaLo,hCtaHi,votes,final,?_,?_,?_,?_,?_⟩⟩
  · rw [hVoteTrace]
    exact hSize
  · rw [hVoteTrace]
    exact hFull
  · rw [hDataTrace,hVoteTrace]
    exact hPlan
  · intro n stage word hEntry
    have hEntry' : (rescaleVoteLabels (X.tr (warpLane l g lane)))[n]? = some (stage,word) := by
      simpa only [hSelf] using hEntry
    simpa only [hSelf] using
      correctionProjectedBallotOrdinal hX cur hl hFollow.noExit hZero hEntry'
  · intro h j ordinal site bit word hWarp hGet' hSite hFirst hOrd hBase
    let lane' := laneOf l h
    have hLane : lane' < 32 := Nat.mod_lt _ (by decide)
    have hPeer : warpLane l g lane' = h := Step.warpLane_of_sameWarp hWarp
    exact correctionPeerFirstBallotAtBase hX cur hLane hFollow.noExit
      (hPeer.symm ▸ hGet') hSite (hPeer.symm ▸ hFirst) (hPeer.symm ▸ hOrd) hBase

private theorem correctionCommonVoteBase {l : Launch} {X : Execution} {g h : Nat}
    {p : Params} (hWarp : SameWarp l g h) (a : CorrectionSchedule p l X g)
    (b : CorrectionSchedule p l X h) (ha : 0 < (rescaleVoteLabels (X.tr g)).length)
    (hb : 0 < (rescaleVoteLabels (X.tr h)).length) : a.base = b.base := by
  let left := (rescaleVoteLabels (X.tr g))[0]
  let right := (rescaleVoteLabels (X.tr h))[0]
  have hEntryL : (rescaleVoteLabels (X.tr g))[0]? = some (left.1,left.2) :=
    List.getElem?_eq_getElem ha
  have hEntryR : (rescaleVoteLabels (X.tr h))[0]? = some (right.1,right.2) :=
    List.getElem?_eq_getElem hb
  obtain ⟨i,site,x,hL,hSite,hOrdL,hFirstL⟩ := a.vote hEntryL
  obtain ⟨j,site',y,hR,hSite',hOrdR,hFirstR⟩ := b.vote hEntryR
  have hSites : site = 8009 ∨ site = 8228 := by rw [hSite]; split <;> simp
  have hSites' : site' = 8009 ∨ site' = 8228 := by rw [hSite']; split <;> simp
  rcases le_total a.base b.base with hl | hr
  · exact a.peerFirst hWarp hR hSites' hFirstR hOrdR hl
  · exact (b.peerFirst hWarp.symm hL hSites hFirstL hOrdL hr).symm

private theorem correctionProjectedVotesPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hUsedK : ∀ b < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*b)).at k))
    {g h : Nat} (hWarp : SameWarp l g h) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (a : CorrectionSchedule p l X g) (b : CorrectionSchedule p l X h)
    (hLen : (rescaleVoteLabels (X.tr g)).length ≤ (rescaleVoteLabels (X.tr h)).length) :
    List.IsPrefix (rescaleVoteLabels (X.tr g)) (rescaleVoteLabels (X.tr h)) := by
  apply List.prefix_iff_getElem?.mpr
  intro n hn
  have hn' := hn.trans_le hLen
  have hBase := correctionCommonVoteBase hWarp a b (by omega) (by omega)
  let x := (rescaleVoteLabels (X.tr g))[n]
  let y := (rescaleVoteLabels (X.tr h))[n]
  have hx : (rescaleVoteLabels (X.tr g))[n]? = some (x.1,x.2) := List.getElem?_eq_getElem hn
  have hy : (rescaleVoteLabels (X.tr h))[n]? = some (y.1,y.2) := List.getElem?_eq_getElem hn'
  obtain ⟨i,site,bit,he,hSite,hOrd,_⟩ := a.vote hx
  obtain ⟨j,site',bit',hf,hSite',hOrd',_⟩ := b.vote hy
  have hSites : site = 8009 ∨ site = 8228 := by rw [hSite]; split <;> simp
  have hSites' : site' = 8009 ∨ site' = 8228 := by rw [hSite']; split <;> simp
  rw [hBase] at hOrd
  obtain ⟨hSiteAgree,hWordAgree⟩ := correctionRescaleBallotPeersAgree hp hX hWarp hLo hHi hUsedK he
      hf hSites hSites' hOrd hOrd'
  have hStage : x.1 = y.1 := by
    rw [hSite,hSite'] at hSiteAgree
    by_cases hx : x.1 = 0 <;> by_cases hy : y.1 = 0
    · exact hx.trans hy.symm
    · simp [hx,hy] at hSiteAgree
    · simp [hx,hy] at hSiteAgree
    · apply Fin.ext
      have hX0 := x.1.isLt
      have hY0 := y.1.isLt
      have hOneX : x.1.val ≠ 0 := fun h => hx (Fin.ext h)
      have hOneY : y.1.val ≠ 0 := fun h => hy (Fin.ext h)
      omega
  rw [hy]
  exact congrArg some (Prod.ext hStage.symm hWordAgree.symm)

private theorem correctionScheduleBudget {p : Params} {l : Launch} {X : Execution} {g h : Nat}
    (hWarp : SameWarp l g h) (a : CorrectionSchedule p l X g) (b : CorrectionSchedule p l X h) :
    2*(Mma.trips p a.batch (assignedCoordinates p a.batch (g/l.block)).1-1) =
      2*(Mma.trips p b.batch (assignedCoordinates p b.batch (h/l.block)).1-1) := by
  have hCTA : g/l.block = h/l.block := hWarp.1.2.2
  have hNext : a.batch + 1 ≤ p.batch := a.batchValid
  have hWork : g/l.block < tilePrefix p p.batch * p.heads :=
    a.assignedHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hNext))
  have hLo := b.assignedLo
  have hHi := b.assignedHi
  rw [← hCTA] at hLo hHi
  have hBatch := ExistsUnique.unique (tileBatch_existsUnique p hWork)
    ⟨a.batchValid,a.assignedLo,a.assignedHi⟩ ⟨b.batchValid,hLo,hHi⟩
  rw [hCTA,hBatch]

private theorem correctionScheduleCommonPrefix {p : Params} {l : Launch} {X : Execution} {g h : Nat}
    (hWarp : SameWarp l g h) (a : CorrectionSchedule p l X g) (b : CorrectionSchedule p l X h)
    (hPrefix : List.IsPrefix (rescaleVoteLabels (X.tr g)) (rescaleVoteLabels (X.tr h))) :
    ∃ common, List.IsPrefix (correctionTensorLabels (X.tr g)) common ∧
      List.IsPrefix (correctionTensorLabels (X.tr h)) common := by
  let left := rescaleVoteSchedule (rescaleVoteLabels (X.tr g))
  let right := rescaleVoteSchedule (rescaleVoteLabels (X.tr h))
  have hPlan : List.IsPrefix left right := by
    obtain ⟨extra,hE⟩ := hPrefix
    refine ⟨rescaleVoteSchedule extra,?_⟩
    exact (rescaleVoteScheduleAppend ..).symm.trans (congrArg rescaleVoteSchedule hE)
  have hL : List.IsPrefix (correctionTensorLabels (X.tr g))
      (left ++ if a.final then correctionFinalSchedule else []) := a.labels
  have hR : List.IsPrefix (correctionTensorLabels (X.tr h))
      (right ++ if b.final then correctionFinalSchedule else []) := b.labels
  by_cases hFinal : a.final = true
  · have hBudget := correctionScheduleBudget hWarp a b
    have hBound := b.bound
    have hLen := a.full hFinal
    have hSame : rescaleVoteLabels (X.tr g) = rescaleVoteLabels (X.tr h) :=
      hPrefix.eq_of_length_le (by omega)
    have hEq : left = right := congrArg rescaleVoteSchedule hSame
    refine ⟨right ++ correctionFinalSchedule,?_,?_⟩
    · simpa [hFinal,hEq] using hL
    · by_cases hFinal' : b.final = true
      · simpa [hFinal'] using hR
      · have hNo : List.IsPrefix (correctionTensorLabels (X.tr h)) right :=
          by simpa [hFinal'] using hR
        exact hNo.trans (List.prefix_append ..)
  · have hNo : List.IsPrefix (correctionTensorLabels (X.tr g)) left :=
      by simpa [hFinal] using hL
    exact ⟨_, hNo.trans (List.prefix_append_of_prefix hPlan), hR⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g j batch : Nat}
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) (hb : batch < p.batch)
    (hBatchLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hBatchHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
include hp hX hFrame hLo hHi hb hBatchLo hBatchHi hSingle

/-- A single-visit correction lane has no rescale collectives. Its final
load or wait ordinal is the index of that operation in the fixed finalization list. -/
private theorem correctionSingleVisitFinalOrdinal {e : Event} (he : X.get (g,j) = some e)
    (hColl : isTcColl e = true) {op : Fin 4} (hOp : correctionTensorOperation e.kind = some op)
    {rank : Nat} (hPlan : correctionFinalSchedule[rank]? = some (e.pc,op)) :
    X.TcK (g,j) rank := by
  let n := ((X.tr g).take j).countP isTcColl
  have hK : X.TcK (g,j) n := ⟨⟨_,he,hColl⟩,rfl⟩
  obtain ⟨hCuQ,hUsedK⟩ := hFrame.metadataProtected hp
  obtain ⟨a⟩ := actualCorrectionSchedule hp hX hUsedK hLo hHi hK
  have hWork : g/l.block < tilePrefix p p.batch*p.heads :=
    hBatchHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hb))
  have hBatch : a.batch = batch := ExistsUnique.unique (tileBatch_existsUnique p hWork)
    ⟨a.batchValid,a.assignedLo,a.assignedHi⟩ ⟨hb,hBatchLo,hBatchHi⟩
  have hBound := a.bound
  rw [hBatch,hSingle] at hBound
  have hNil : rescaleVoteLabels (X.tr g) = [] :=
    List.length_eq_zero_iff.mp (by omega)
  obtain ⟨op',hOp',hLabel⟩ := correctionTensorLabelAt (fun x hx => by
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hx
    exact correctionEventClass hp hX hHi (show X.get (g,i) = some x from hi))
    he hColl (show _ = n from rfl)
  have hSame : op' = op := Option.some.inj (hOp'.symm.trans hOp)
  subst op'
  have hPrefix : List.IsPrefix (correctionTensorLabels (X.tr g)) correctionFinalSchedule := by
    have hPrefix := a.labels
    rw [hNil,rescaleScheduleNil,List.nil_append] at hPrefix
    by_cases hFinal : a.final = true
    · simpa only [hFinal,↓reduceIte] using hPrefix
    · exact (by simpa [hFinal] using hPrefix :
        List.IsPrefix (correctionTensorLabels (X.tr g)) []).trans List.nil_prefix
  obtain ⟨hIndex,hGet⟩ := List.getElem?_eq_some_iff.mp hLabel
  have hPlan' := List.prefix_iff_getElem?.mp hPrefix n hIndex
  rw [hGet] at hPlan'
  have hNodup : correctionFinalSchedule.Nodup := by decide +kernel
  have hEqual : n = rank :=
    (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp hPlan').1 hNodup).mp
      (hPlan'.trans hPlan.symm)
  exact hEqual ▸ hK

omit hp hX hFrame hLo hHi hb hBatchLo hBatchHi hSingle in
private theorem finalScheduleLoadAt (stage : Fin 2) (chunk : Fin 16) :
    correctionFinalSchedule[32*stage.val+2*chunk.val]? = some (finalizeLoadPc stage chunk,0) := by
  fin_cases stage <;> fin_cases chunk <;> decide +kernel

/-- The first accumulator load is the first Tensor Memory collective of each
correction lane in a single-visit CTA. -/
theorem correctionFirstOutputLoadOrdinal {addr : Nat} {words : List Value}
    (he : X.get (g,j) = some ⟨finalizeLoadPc 0 0,.tc (.ld addr words .s32x32b)⟩) :
    X.TcK (g,j) 0 :=
  correctionSingleVisitFinalOrdinal hp hX hFrame hLo hHi hb hBatchLo hBatchHi hSingle
    he rfl (op := 0) rfl (by
      change correctionFinalSchedule[0]? = some (finalizeLoadPc 0 0,0)
      decide +kernel)

/-- The first explicit wait follows only the first load in the single-visit schedule. -/
theorem correctionFirstOutputWaitOrdinal
    (he : X.get (g,j) = some ⟨finalizeLoadPc 0 0+5,.tc .waitLd⟩) :
    X.TcK (g,j) 1 :=
  correctionSingleVisitFinalOrdinal hp hX hFrame hLo hHi hb hBatchLo hBatchHi hSingle
    he rfl (op := 1) rfl (by
      change correctionFinalSchedule[1]? = some (finalizeLoadPc 0 0+5,1)
      decide +kernel)
end

/-- The correction lanes of a warp agree on the site and operation of every shared
Tensor Memory ordinal in every consistent prefix. -/
theorem correctionTensorSlotAlignment {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hUsedK : ∀ b < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*b)).at k)) :
    CorrectionTensorSlotAlignment l X := by
  apply CorrectionTensorSlotAlignment.of_agreement
  intro g h i j k e f hLo hHi hWarp he hf hk hk'
  have hRole : warpIndex l g = warpIndex l h := hWarp.2
  have hLo' : 8 ≤ warpIndex l h := hRole ▸ hLo
  have hHi' : warpIndex l h < 12 := hRole ▸ hHi
  obtain ⟨a⟩ := actualCorrectionSchedule hp hX hUsedK hLo hHi hk
  obtain ⟨b⟩ := actualCorrectionSchedule hp hX hUsedK hLo' hHi' hk'
  have hAt {q z ord : Nat} {ev : Event} (hQ : warpIndex l q < 12)
      (hGet : X.get (q,z) = some ev) (hK : X.TcK (q,z) ord) :
      ∃ op, correctionTensorOperation ev.kind = some op ∧
        (correctionTensorLabels (X.tr q))[ord]? = some (ev.pc,op) := by
    obtain ⟨⟨other,hOther,hColl⟩,hCount⟩ := hK
    obtain rfl := Option.some.inj (hGet.symm.trans hOther)
    exact correctionTensorLabelAt (fun x hx => by
      obtain ⟨r,hr⟩ := List.mem_iff_getElem?.mp hx
      exact correctionEventClass hp hX hQ hr) hGet hColl hCount
  obtain ⟨op,ho,hLeft⟩ := hAt hHi he hk
  obtain ⟨op',ho',hRight⟩ := hAt hHi' hf hk'
  have hEqual {q r : Nat} {x y : Nat × Fin 4}
      (hx : (correctionTensorLabels (X.tr q))[k]? = some x)
      (hy : (correctionTensorLabels (X.tr r))[k]? = some y)
      (hC : ∃ common, List.IsPrefix (correctionTensorLabels (X.tr q)) common ∧
          List.IsPrefix (correctionTensorLabels (X.tr r)) common) : x = y := by
    obtain ⟨common,hP,hQ⟩ := hC
    have hXBound := (List.getElem?_eq_some_iff.mp hx).1
    have hYBound := (List.getElem?_eq_some_iff.mp hy).1
    have hX' := List.prefix_iff_getElem?.mp hP k hXBound
    have hY' := List.prefix_iff_getElem?.mp hQ k hYBound
    have hElemX := (List.getElem?_eq_some_iff.mp hx).2
    have hElemY := (List.getElem?_eq_some_iff.mp hy).2
    rw [hElemX] at hX'
    rw [hElemY] at hY'
    exact Option.some.inj (hX'.symm.trans hY')
  have hPair : (e.pc,op) = (f.pc,op') := by
    rcases le_total (rescaleVoteLabels (X.tr g)).length (rescaleVoteLabels (X.tr h)).length with
      hLeftLen | hRightLen
    · have hP := correctionProjectedVotesPrefix hp hX hUsedK hWarp hLo hHi a b hLeftLen
      exact hEqual hLeft hRight (correctionScheduleCommonPrefix hWarp a b hP)
    · have hP := correctionProjectedVotesPrefix hp hX hUsedK hWarp.symm hLo' hHi' b a hRightLen
      exact (hEqual hRight hLeft (correctionScheduleCommonPrefix hWarp.symm b a hP)).symm
  have hOp : some op = some op' := congrArg some (congrArg Prod.snd hPair)
  exact ⟨congrArg Prod.fst hPair,ho.trans (hOp.trans ho'.symm)⟩

end PTX.Kernels.TmlFa4Fwd.Thread
