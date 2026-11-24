-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTensorWindow
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTensorOperands
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstVisitGeometry
import Kernels.TmlFa4Fwd.Proof.SoftmaxExitPublications
import Kernels.TmlFa4Fwd.Proof.SoftmaxCounterEntry
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Flow.Final
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open _root_.PTX.Kernels.TmlFa4Fwd.Softmax Epilogue Prologue

private def copies (n : Nat) (loop : ScoreLoop) : List (Nat × Fin 4) :=
  (List.replicate n (softmaxVisitTokens (softmaxLoopRound loop))).flatten

/-- The Tensor Memory sequence of the selected softmax role, including every repeat. -/
@[no_expose] def softmaxTensorPlan (blocks cap : Nat) : List (Nat × Fin 4) :=
  softmaxVisitTokens .first ++
    (copies (firstBiasedRepeats blocks cap) .biased ++
      copies (firstPlainSplit blocks cap) .plain)

private def exitEvent : Event := ⟨9205,.exit⟩

private theorem plainTokensThroughBody {l : Launch} {g blocks split : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hs : At s 6654 (repeatCountLimits blocks split))
    (hb : blocks < 2^31) (hSplit : split < blocks)
    (hw : Walk kernel Assumptions.all l g s es vs) (hExit : exitEvent ∈ es) :
    ∃ u pre tail path, es = pre ++ tail ∧ 7605 ≤ u.pc ∧
      softmaxTraceTokens pre = copies split .plain ∧
      Walk kernel Assumptions.all l g u tail path := by
  obtain ⟨t,ht,hT⟩ := (plainCountDecisionWithLimits l g blocks split hb hSplit).apply hs
  have hAt : At t 6656 [(1491, b32 split)] := hT.mono hT.2.2.2.2.2
  obtain ⟨a,ha,hA⟩ := run_bra (A := Assumptions.all) (L := l) (g := g)
    Flow.code_6656 (decide (split=0)) hAt hT.2.2.2.2.1
    (fun a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (maxSeg (by decide))
  rcases Mma.advanceWalkLocals (run_comp ht ha) hw with rfl | ⟨_,_,_,hWalk⟩
  · cases hExit
  by_cases hz : split = 0
  · have hPc : a.pc = 7605 := by simpa [hz] using hA.1
    exact ⟨a,[],es,_,rfl,hPc.ge,by
      simpa [hz,copies] using (softmaxTraceTokensNone (events := []) (by simp)),hWalk⟩
  have hA' : At a 6657 [(1491,b32 split)] := by
    simpa only [decide_eq_false hz,Bool.false_eq_true,ite_false] using hA
  obtain ⟨u,_,hInit,hUWalk⟩ := scoreRunToHeadBefore .plain hWalk
    (by rw [hA'.1]; decide) (by rw [hA'.1]; decide) (by intro _ h; cases h) hExit (by decide)
  rw [hA'.1] at hInit
  have hPos := Nat.pos_of_ne_zero hz
  have hSub : a.sub ≤ 3 := hA'.2.1.symm ▸ Nat.zero_le _
  obtain ⟨hPc,_,hWord⟩ := plainLoopInitializedCount hA'.1 hSub hA'.2.2.2.2.1
    hPos (by omega) hInit
  have hScratch := softmaxScratchAtLoopHead .plain hPc
    (softmaxScratchAcrossSilent (run_rtg hInit) (scratchStateOfClear ⟨hA'.2.1,hA'.2.2.1⟩))
  have hHealthy := softmaxHealthyBeforeLaterTarget hUWalk hExit
    (by rw [hPc]; decide : u.pc < exitEvent.pc)
  obtain ⟨v,pre,rest,path,hSplit,hV,_,_,_,_,hTokens,_,hVW⟩ :=
    softmaxRepeatedTensorTrace .plain hUWalk hPc hScratch hHealthy hWord
      (by omega) hExit (by decide)
  rw [initialPlainDistance hPos (by omega)] at hTokens
  exact ⟨v,pre,rest,path,hSplit,hV.symm ▸ (by decide : 7605 ≤ (scoreLoopSite .plain).increment+4),
    hTokens,hVW⟩

private theorem remainingTokensThroughBody {l : Launch} {g blocks cap past : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hs : At s 5006 (firstLoopGeometry blocks cap past))
    (hBlocks : 0 < blocks) (hb : blocks < 2^31) (hCap : 0 < cap) (hc : cap < 2^31)
    (hw : Walk kernel Assumptions.all l g s es vs) (hExit : exitEvent ∈ es) :
    ∃ u pre tail path, es = pre ++ tail ∧ 7605 ≤ u.pc ∧
      softmaxTraceTokens pre =
        copies (firstBiasedRepeats blocks cap) .biased ++
        copies (firstPlainSplit blocks cap) .plain ∧
      Walk kernel Assumptions.all l g u tail path := by
  obtain ⟨a,_,hA,hAW⟩ := firstCountEntryWalk hBlocks hb hCap hc hs hw hExit
  let split := firstPlainSplit blocks cap
  let biased := firstBiasedRepeats blocks cap
  have hSplit : split < blocks := by unfold split firstPlainSplit; omega
  change (if biased = 0 then At a 6654 (repeatCountLimits blocks split)
    else At a 5032 ((7248,b32 (2^32-(blocks-split))) :: repeatCountLimits blocks split)) at hA
  by_cases hz : biased = 0
  · rw [ite_eq_left hz] at hA
    obtain ⟨u,pre,tail,path,hSplit,hU,hTokens,hWalk⟩ :=
      plainTokensThroughBody hA hb hSplit hAW hExit
    exact ⟨u,pre,tail,path,hSplit,hU,by simpa [show firstBiasedRepeats blocks cap = 0 from hz,
      copies,split] using hTokens,hWalk⟩
  rw [ite_eq_right hz] at hA
  have hMore : split+1 < blocks := by
    unfold biased firstBiasedRepeats at hz
    change blocks-1-split ≠ 0 at hz
    omega
  obtain ⟨u,pre,tail,path,hTrace,hU,hS,hAcc,hF,hRegs,hTokens,hMem,hW⟩ :=
    softmaxRepeatedTensorTrace .biased hAW hA.1 ⟨hA.2.1,hA.2.2.1⟩ hA.2.2.2.1
      hA.2.2.2.2.1 (by omega) hExit (by decide)
  have hLimits : Holds a.regs (repeatCountLimits blocks split) := hA.2.2.2.2.2
  have hFrame : At u 6654 (repeatCountLimits blocks split) :=
    ⟨hU,hS,hAcc,hF,(hRegs _ (by decide)).trans hLimits.1,
      (hRegs _ (by decide)).trans hLimits.2.1,trivial⟩
  obtain ⟨v,mid,rest,last,hTail,hV,hMid,hVW⟩ := plainTokensThroughBody hFrame hb hSplit hW hMem
  rw [initialBiasedDistance hb hMore] at hTokens
  refine ⟨v,pre++mid,rest,last,by rw [hTrace,hTail,List.append_assoc],hV,?_,hVW⟩
  rw [softmaxTraceTokensAppend,hTokens,hMid]
  rfl

set_option maxRecDepth 100000 in
private theorem firstTensorFloor :
    (kernel.code.drop 3425).all (fun i => staysPastEvent 3425 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstTensorSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (3425 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterTensorFloor :
    (kernel.code.drop 7605).all (fun i => staysPastEvent 7605 i.op) = true := by kernel_rfl

private theorem afterTensorSegments :
    ∀ site, 7605 ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → 7605 ≤ seg.stop := by
  intro site hLo hm _ _
  have ha : Assumptions.swExp2Sites.all (fun i => decide (i < 7605)) = true := by decide +kernel
  exact (Nat.not_lt_of_ge hLo (of_decide_eq_true (List.all_eq_true.mp ha site hm))).elim

theorem softmaxTensorEventClass {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i : Nat} {e : Event} (hWarp : warpIndex l g < 8) (he : X.get (g,i) = some e) :
    isTcColl e = isTcData e := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨arithmeticTensorCollectiveIsData hp hX (by omega) he,?_⟩
  intro h
  rcases e with ⟨pos,kind⟩
  cases kind <;> try cases h
  rename_i tc
  cases tc <;> first | rfl | cases h

private theorem softmaxNoTensorBeforeFirstAck {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g q : Nat} {ack : Event} (hWarp : warpIndex l g < 8)
    (hAck : X.get (g,q) = some ack) (hSite : ack.pc = 3420) :
    softmaxTraceTokens ((X.tr g).take (q+1)) = [] := by
  apply softmaxTraceTokensNone
  intro e hm
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hm
  have hI := ((List.getElem?_eq_some_iff.mp hi).1).trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hI] at hi
  rw [← softmaxTensorEventClass hp hX hWarp hi]
  by_cases hData : isTcColl e = true
  · have hBand := softmaxTensorCollectiveBand hp hX hWarp hi hData
    have hOrd := traceOrderOfPcFloor hX firstTensorFloor firstTensorSegments
      hAck hi (by omega) hBand.1
    omega
  · exact Bool.eq_false_iff.mpr hData

/-- The full trace of each actual selected softmax lane has the same Tensor Memory projection
for its stage and request geometry. -/
theorem softmaxTensorTraceOfComplete {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads) (hWarp : warpIndex l g < 8)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let stage := stageOf ⟨warpIndex l g,hWarp⟩
    let tile := (assignedCoordinates p batch (g/l.block)).1
    let blocks := Mma.trips p batch tile
    let cap := blocks - stageGeometryBlocks p batch tile stage + 10
    softmaxTraceTokens (X.tr g) = softmaxTensorPlan blocks cap := by
  dsimp only
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  let stage := stageOf warp
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  let cap := blocks - stageGeometryBlocks p batch tile stage + 10
  let past := p.kLength batch - p.qLength batch + 256*tile
  let ack : Event := ⟨3420,.wait (waitLoc l g stage 0) 1 true true .cta⟩
  obtain ⟨pos,fails,s,_,hSuffix,hs,hRun⟩ :=
    firstVisitGeometryTraceOfComplete hp hX hDone hFootprint hg hWarp hb hLo hHi
  let q := pos+3+fails
  have hAck : X.get (g,q) = some ack := by
    change (X.tr g)[q]? = some ack
    have hAt : ((X.tr g).drop (pos+3))[fails]? = some ack := by
      rw [hSuffix,List.getElem?_append_right (by simp),List.length_replicate,Nat.sub_self]
      rfl
    rw [List.getElem?_drop] at hAt
    exact hAt
  have hNone := softmaxNoTensorBeforeFirstAck hp hX hWarp hAck rfl
  obtain ⟨finish,⟨site,kind⟩,hExit,hKind⟩ := exitedOfComplete hX hDone hg
  change kind = .exit at hKind
  subst kind
  obtain rfl := actualExitPc hX hExit
  obtain ⟨e,hEnds,_⟩ := PTX.Flow.Run.ended_last hRun
  have hLen := Execution.exit_last hX hg hExit
  have hNonempty : 0 < ((X.tr g).drop (q+1)).length := by
    cases hEs : (X.tr g).drop (q+1) with
    | nil => simp [q,hEs] at hEnds
    | cons => simp
  rw [List.length_drop] at hNonempty
  have hMem : exitEvent ∈ (X.tr g).drop (q+1) := by
    apply List.mem_of_getElem? (i := finish-(q+1))
    rw [List.getElem?_drop,Nat.add_sub_of_le (show q+1 ≤ finish by omega)]
    exact hExit
  obtain ⟨_,hw⟩ := Mma.walkFromRun hRun
  have hpast : p.kLength batch-p.qLength batch + 256*(tile+1) = past+256 := by
    dsimp [past]
    omega
  have hs' : At s 3425 (firstLoopGeometry blocks cap past) := by
    refine hs.mono ⟨?_,?_,?_,hs.2.2.2.2.1,trivial⟩
    · rw [← hpast]
      exact holds_mem hs.2.2.2.2 (by simp [firstGeometryAckFacts,firstGeometryFacts,tile])
    · exact holds_mem hs.2.2.2.2 (by simp [firstGeometryAckFacts,firstGeometryFacts,blocks,tile])
    · exact holds_mem hs.2.2.2.2 (by simp [firstGeometryAckFacts,firstGeometryFacts,cap,blocks,tile,
        stage,warp])
  obtain ⟨v,first,tail,path,hSplit,hV,hFirst,hTail,hWalk⟩ :=
    softmaxFirstTensorTrace hs' hw hMem (by decide)
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hBounds := firstGeometryBounds hp stage hb hTile (lane := 0) (by decide)
  obtain ⟨u,repeated,last,out,hTailEq,hU,hRepeat,hUW⟩ :=
    remainingTokensThroughBody hV hBounds.1 hBounds.2.1 hBounds.2.2.1
      hBounds.2.2.2.1 hWalk hTail
  have hBand := eventTailEventsOfSegmentFloor afterTensorFloor afterTensorSegments hUW hU
  have hLast : softmaxTraceTokens last = [] := by
    apply softmaxTraceTokensNone
    intro e he
    have hIn : e ∈ X.tr g := by
      apply List.mem_of_mem_drop (i := q+1)
      rw [hSplit,hTailEq]
      exact List.mem_append_right _ (List.mem_append_right _ he)
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hIn
    rw [← softmaxTensorEventClass hp hX hWarp hj]
    by_cases hColl : isTcColl e = true
    · have hBad := softmaxTensorCollectiveBand hp hX hWarp hj hColl
      have := hBand _ he
      omega
    · exact Bool.eq_false_iff.mpr hColl
  rw [← List.take_append_drop (q+1) (X.tr g),softmaxTraceTokensAppend,hNone,List.nil_append]
  rw [hSplit,softmaxTraceTokensAppend,hFirst,hTailEq,softmaxTraceTokensAppend,hRepeat,hLast,
    List.append_nil]
  rfl

end PTX.Kernels.TmlFa4Fwd.Thread
