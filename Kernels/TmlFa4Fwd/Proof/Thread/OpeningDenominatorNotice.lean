-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxLaneRegister
import all Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningStatistics
import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.NthEv
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame Prologue
open Thread.Scores

set_option maxRecDepth 100000 in
private theorem openingDenominatorFloor :
    (kernel.code.drop 5006).all (fun ins => Thread.staysPastEvent 5006 ins.op) = true := by
  decide +kernel

private theorem openingDenominatorSegmentAudit :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => !decide (5006 ≤ site) || decide (5006 ≤ seg.stop)
      | none => false) = true := by decide +kernel

private theorem openingDenominatorSegmentFloor (site : Nat) (hFloor : 5006 ≤ site)
    (hSite : site ∈ Assumptions.swExp2Sites) (seg : SegMatch CuteSlot)
    (hMatch : cuteExp2.matchAt kernel site = some seg) : 5006 ≤ seg.stop := by
  have h := List.all_eq_true.mp openingDenominatorSegmentAudit site hSite
  rw [hMatch,decide_eq_true hFloor] at h
  exact of_decide_eq_true h

private theorem beforeOpeningDenominatorEvent {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events t)
    (ht : t.pc = 5006) {e : Event} (he : e ∈ events) : e.pc < 5007 := by
  induction h with
  | refl => cases he
  | tau _ _ ih => exact ih ht he
  | event hStep hRest ih =>
    rcases List.mem_cons.mp he with rfl | hMem
    · by_contra! hp
      have hCode : (kernel.code.drop 5007).all
          (fun ins => Thread.staysPastEvent 5007 ins.op) = true := by
        set_option maxRecDepth 100000 in decide +kernel
      have hSeg (site : Nat) (hSite : 5007 ≤ site) (hm : site ∈ Assumptions.swExp2Sites)
          (seg : SegMatch CuteSlot) (hMatch : cuteExp2.matchAt kernel site = some seg) :
          5007 ≤ seg.stop := by
        have hAll : Assumptions.swExp2Sites.all (fun site =>
            match cuteExp2.matchAt kernel site with
            | some x => !decide (5007 ≤ site) || decide (5007 ≤ x.stop)
            | none => false) = true := by decide +kernel
        have h := List.all_eq_true.mp hAll site hm
        rw [hMatch,decide_eq_true hSite] at h
        exact of_decide_eq_true h
      have hStart := (estep_source_pc hStep).symm ▸ hp
      have hEnd := traceKeepsFloor hRest hCode hSeg
        (Thread.eventTailStep hCode hSeg hStart (.inr ⟨_,rfl,hStep⟩))
      omega
    · exact ih ht hMem

/-- At the real first denominator the statistics ledger contains precisely the
opening publication. This holds even when the current prefix stops there. -/
theorem OpeningDenominatorCursor.noticesOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch blocks cap past : Nat} (hg : g < l.threads)
    (stage : Fin 2) (hRole : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (c : OpeningDenominatorCursor p l X g blocks cap past) :
    (Thread.Scores.before X (g,c.cursor.pos)).notices = 1 := by
  let w : Fin 8 := ⟨warpIndex l g,by have := stage.isLt; omega⟩
  have hw : warpIndex l g < 8 := w.isLt
  obtain ⟨early⟩ := Progress.openingStatisticsCursorOfMaximal hp hMax hFrame hg stage
    hRole hb hLo hHi
  have hEarly : early.state.pc = 4398 := early.ready.1
  have ht : c.cursor.ready.pc = 5006 := c.cursor.checkpoint.1
  have hNoBack es : ¬ TraceReach kernel Assumptions.all l g c.cursor.ready es early.state := by
    intro h
    have hFloor := traceKeepsFloor h openingDenominatorFloor openingDenominatorSegmentFloor ht.ge
    omega
  obtain ⟨e,he,hE⟩ := early.published
  obtain ⟨hOrder,_⟩ := recordedCheckpointsPath (len_of_get he) c.cursor.bounded early.recorded .refl
    c.cursor.recorded c.cursor.localSteps hNoBack
  let pMark := Thread.Scores.publishesStats
  have hSeen : pMark e = true := by simp [pMark,Thread.Scores.publishesStats,hE]
  have hStep : ((X.tr g).take (early.index+1)).countP pMark =
      ((X.tr g).take early.index).countP pMark + 1 := countP_take_succ he hSeen
  have hMon : ((X.tr g).take (early.index+1)).countP pMark ≤
      ((X.tr g).take c.cursor.pos).countP pMark := countP_take_mono pMark (X.tr g) hOrder
  rw [beforeNotices]
  have hLower : 1 ≤ ((X.tr g).take c.cursor.pos).countP pMark := by omega
  refine Nat.le_antisymm ?_ hLower
  by_contra! hTooMany
  obtain ⟨j,hj,f,hGet,hMark,hCount⟩ := exists_nth pMark (X.tr g) hTooMany
  have hMem : f ∈ (X.tr g).take c.cursor.pos := by
    apply List.mem_of_getElem? (i := j)
    rwa [List.getElem?_take_of_lt hj]
  have hTrace : TraceReach kernel Assumptions.all l g {}
      ((X.tr g).take c.cursor.pos) c.cursor.ready := by
    simpa only [List.append_nil] using c.cursor.recorded.returning_reach.append
      (TraceReach.of_local c.cursor.localSteps)
  have hPc := beforeOpeningDenominatorEvent hTrace ht hMem
  obtain ⟨round,hNotice⟩ := Option.isSome_iff_exists.mp hMark
  have hSite := publicationSiteOfNotice hNotice
  have hFirst : round = .first := by
    cases round <;> simp [publicationSite] at hSite ⊢ <;> omega
  subst round
  have hFact : Thread.Scores.Publishes X (g,j) .first := ⟨f,hGet,hNotice⟩
  have hOrdinal := firstOrdinal hp hMax.1 hFact (statsBarrierSources hp hMax.1 w)
  rw [← notificationOrdinal hp hMax.1 hw, beforeNotices] at hOrdinal
  change ((X.tr g).take j).countP pMark = 0 at hOrdinal
  omega

/-- The two terminal stores leave the opening statistics rank unchanged. -/
theorem OpeningDenominatorCursor.singleVisitPublicationOrdinal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {g cap past : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) (hCap : 0 < cap) (hCapSigned : cap < 2^31)
    (hPast : past+256 < 2^31) (c : OpeningDenominatorCursor p l X g 1 cap past)
    (hNotice : (Thread.Scores.before X (g,c.cursor.pos)).notices = 1) :
    (Thread.Scores.before X (g,c.cursor.pos+2)).notices = 1 := by
  obtain ⟨_,⟨_,hs⟩,⟨_,hm⟩⟩ := c.publishSingleVisitAtCursor hp hMax hCuQ hg hw
    hCap hCapSigned hPast
  rw [beforeNotices] at hNotice ⊢
  rw [show c.cursor.pos+2 = c.cursor.pos+1+1 from rfl, countP_take_succ_false hm rfl,
    countP_take_succ_false hs rfl]
  exact hNotice

end PTX.Kernels.TmlFa4Fwd.Softmax
