-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionTerminalWords
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalStats
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
import all Kernels.TmlFa4Fwd.Proof.CorrectionFinalStats
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.Object
import Lemmas.Flow.EventCont
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy Prologue

/-- A reached unit release arrival records its object update and actual
continuation. The acknowledgement destination is outside the carried frame. -/
theorem unitArrivalOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g pc dst : Nat} {mb : Loc}
    (hg : g < l.threads) {F : List (Nat × Value)} (c : OpeningTripCursor l X g pc F)
    (hOut : out kernel Assumptions.all l g c.ready =
      .ev (.arrive mb 0 (next (mbarStateDest c.ready (some dst))) 1 true .cta))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ dst) :
    X.get (g,c.pos) = some ⟨pc,.arrive mb 0 1 true .cta⟩ ∧
      ∃ d : OpeningTripCursor l X g (pc+1) F, d.pos = c.pos+1 := by
  let u := next (mbarStateDest c.ready (some dst))
  let event : Event := ⟨c.ready.pc,.arrive mb 0 1 true .cta⟩
  have hStep : EStep kernel Assumptions.all l g c.ready event (some u) := ⟨_,hOut,rfl,rfl⟩
  have hLt : c.pos < (X.tr g).length := by
    by_contra! hShort
    have hLen := Nat.le_antisymm c.bounded hShort
    have hStarted : X.tr g ≠ [] := List.ne_nil_of_length_pos (hLen ▸ c.positive)
    have hr := c.recorded
    rw [List.take_of_length_le hShort] at hr
    apply hMax.not_grows
    refine Step.object_counted_extension_silent hMax.1 (by trivial) hg (.inl hStarted)
      (c.released hLen) hr c.localSteps hStep ⟨trivial,fun _ h => by cases h⟩ (by trivial)
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rfl (mb := mb) (act := .arrive 1 0)
      (fun _ _ h => by cases h) ?_ ?_
    · intro loc
      by_cases h : loc = mb
      · subst loc
        simp [objectAction,snoc_get_new,event]
      · simp [objectAction,snoc_get_new,event,h,Ne.symm h]
    · intro rec
      exact Assumptions.wfStep.quiet hMax.1
        (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  have hn := Next.mk c.localSteps hOut
  obtain ⟨_,_,he,⟨rfl,hReturn⟩,hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,hBad⟩; cases hBad) c.remaining
    (fun h => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hReturn
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some u) := by
    rw [List.take_add_one,show (X.tr g)[c.pos]? = some event from he]
    exact c.recorded.snoc c.localSteps hStep
  have hAt := At.clear_state c.checkpoint hFresh
  refine ⟨?_,⟨c.pos+1,u,u,c.ending,Nat.succ_pos _,len_of_get he,
    releasedIfLast he (by simp [Kind.resume]),hAt,hPast,hTail,.refl⟩,rfl⟩
  simpa only [c.checkpoint.1] using he

private theorem terminalCreditOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (stage : Fin 2) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (reciprocalPc stage-1) F)
    (hBase : (rescaleReuseReg (1-stage),b32 (rescaleReuseLoc l g (1-stage)).addr) ∈ F)
    (hCount : (6498,b32 1) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ finalStatsReleaseDst stage) :
    X.get (g,c.pos) = some ⟨reciprocalPc stage-1,
      .arrive (rescaleReuseLoc l g (1-stage)) 0 1 true .cta⟩ ∧
      ∃ nextC : OpeningTripCursor l X g (reciprocalPc stage) F, nextC.pos = c.pos+1 := by
  let mb := rescaleReuseLoc l g (1-stage)
  let result := finalStatsReleaseDst stage
  let u := next (mbarStateDest c.ready (some result))
  have hCode := finalStatsReleaseCode stage
  have hModel : out kernel Assumptions.all l g c.ready = out kernel [] l g c.ready := by
    apply Assumptions.out_all_eq_nil _ _ _ (c.checkpoint.1.symm ▸ hCode) rfl
    all_goals rw [c.checkpoint.1]; fin_cases stage <;> decide
  have hAddr : mb.addr+0 < 2^32 := by
    have := hp.shared.2.1
    fin_cases stage <;> simp only [mb,rescaleReuseLoc] <;> omega
  have hAlign : (mb.addr+0)%8 = 0 := by
    have := hp.shared.1
    fin_cases stage <;> simp only [mb,rescaleReuseLoc] <;> omega
  have hOut : out kernel Assumptions.all l g c.ready = .ev (.arrive mb 0 u 1 true .cta) := by
    simpa only [Nat.add_zero,mb,rescaleReuseLoc,u,result] using
      correctionReleaseOut c.checkpoint hModel hCode (holds_mem c.checkpoint.2.2.2.2 hBase)
        (holds_mem c.checkpoint.2.2.2.2 hCount) hAddr hAlign
  have hPc : reciprocalPc stage-1+1 = reciprocalPc stage := by
    unfold reciprocalPc
    omega
  obtain ⟨he,d,hPos⟩ := unitArrivalOfMaximal hMax hg c hOut hFresh
  exact ⟨he,⟨d.pos,d.before,d.ready,d.ending,d.positive,d.bounded,d.released,
    ⟨d.checkpoint.1.trans hPc,d.checkpoint.2⟩,d.recorded,d.remaining,d.localSteps⟩,hPos⟩

/-- The terminal row words release the first statistics slot in the actual trace,
retaining the state for the normalization instructions. -/
theorem FirstTerminalWordsReady.creditOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads)
    (c : FirstTerminalWordsReady p l X g batch lane) :
    X.get (warpLane l g lane,c.cursor.pos) = some ⟨8468,
      .arrive (statsCreditLoc l (warpLane l g lane/l.block) 0) 0 1 true .cta⟩ ∧
      ∃ nextC : OpeningTripCursor l X (warpLane l g lane) (reciprocalPc 0)
        ((6513,Softmax.scoreValue c.maximum)::(6512,fl c.sum)::
          finalizeLayoutFacts l (warpLane l g lane) ++
          (7134,b32 p.scaleLog2Bits)::correctionBeforeRescale p l g batch lane),
        nextC.pos = c.cursor.pos+1 := by
  apply terminalCreditOfMaximal hp hMax hg 0 c.cursor
  · simp [rescaleReuseReg,rescaleReuseLoc,correctionBeforeRescale,tileSetupFrame,
      correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,entryFacts,
      nonzeroBarrierFacts]
  · simp [finalizeLayoutFacts]
  · intro pair hm hEq
    have hReg := List.mem_map_of_mem (f := Prod.fst) hm
    rw [hEq] at hReg
    exact (of_decide_eq_true rfl : finalStatsReleaseDst 0 ∉ _) hReg

/-- The first terminal credit has exactly the ordinal of the named wait that supplied
its two row words. -/
theorem FirstTerminalWordsReady.creditObservationOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane blocks : Nat} (hg : warpLane l g lane < l.threads)
    (hw : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12)
    (c : FirstTerminalWordsReady p l X g batch lane)
    (hOrdinal : (Thread.correctionBefore X (warpLane l g lane,c.waitIndex)).barrier
      (statsBarrierId l (warpLane l g lane) 0) = blocks) :
    ∃ e, X.get (warpLane l g lane,c.cursor.pos) = some e ∧
      Thread.correctionAction e = some (.statsCredit 0) ∧
      (Thread.correctionBefore X (warpLane l g lane,c.cursor.pos)).count (.statsCredit 0) =
        blocks := by
  let g' := warpLane l g lane
  let credit := (g',c.cursor.pos)
  let e := Event.mk 8468 (.arrive (statsCreditLoc l (g'/l.block) 0) 0 1 true .cta)
  obtain ⟨he,_⟩ := c.creditOfMaximal hp hMax hg
  have hCredit : Thread.correctionAction e = some (.statsCredit 0) :=
    (Thread.correctionStatsCreditObservation 0 (show e.kind = _ from rfl)).mpr
      (by change (8468 : Nat) ∈ [7987,8443,8468]; decide)
  refine ⟨e,he,hCredit,?_⟩
  obtain ⟨wait,hWait,hAction⟩ := c.waited
  have hMarked : correctionStatsWaitMark 0 wait = true := by
    apply (correctionStatsWaitMark_iff 0 wait).mpr
    rw [Thread.correctionTerminalWaitSite hAction]
    decide
  have hReadMark (word : Fin 2) (kind : Kind) :
      correctionStatsWaitMark 0 ⟨statsPc 0 (finalStatsKind word),kind⟩ = false := by
    apply Bool.eq_false_iff.mpr
    intro hm
    have hSite := (correctionStatsWaitMark_iff 0 _).mp hm
    change statsPc 0 (finalStatsKind word) ∈ correctionStatsSites 0 at hSite
    have hAbsent : ∀ q : Fin 2, statsPc 0 (finalStatsKind q) ∉ correctionStatsSites 0 := by decide
    exact hAbsent word hSite
  have hWaits : ((X.tr g').take c.cursor.pos).countP (correctionStatsWaitMark 0) = blocks+1 := by
    rw [Thread.correctionBarrierOrdinal,← correctionWaitPrefixCount hp hMax.1 0
      (len_of_get hWait) hw] at hOrdinal
    rw [c.position,show c.waitIndex+3 = c.waitIndex+2+1 from rfl,
      countP_take_succ_false c.maximumRead (hReadMark 1 _),
      countP_take_succ_false c.sumRead (hReadMark 0 _),
      countP_take_succ hWait hMarked]
    exact congrArg (·+1) hOrdinal
  have hMark : correctionStatsCreditMark 0 e = true := by
    apply (correctionStatsCreditMark_iff 0 e).mpr
    change (8468 : Nat) ∈ [7987,8443,8468]
    decide
  have hBalance := correctionCreditRequiresWait hMax.1 0 (i := credit) he hMark
  change ((X.tr g').take c.cursor.pos).countP (correctionStatsWaitMark 0) =
      ((X.tr g').take c.cursor.pos).countP (correctionStatsCreditMark 0)+1 at hBalance
  have hMarkers : ((X.tr g').take c.cursor.pos).countP (correctionStatsCreditMark 0) =
      blocks := by omega
  rw [Thread.correctionBefore_count,← hMarkers]
  apply List.countP_congr
  intro record hMember
  obtain ⟨i,hGet⟩ := List.mem_iff_getElem?.mp hMember
  have hi := (List.getElem?_eq_some_iff.mp hGet).1
  rw [List.length_take] at hi
  have hiPos : i < c.cursor.pos := by omega
  rw [List.getElem?_take_of_lt hiPos] at hGet
  refine ⟨fun h => ?_,fun h => ?_⟩
  · have hCredit := of_decide_eq_true h
    obtain ⟨_,_,hKind⟩ := Thread.correctionStatsCreditKind hCredit
    exact (correctionStatsCreditMark_iff 0 record).mpr
      ((Thread.correctionStatsCreditObservation 0 hKind).mp hCredit)
  · have hLen : c.cursor.pos < (X.tr g').length := len_of_get he
    change X.get (g',i) = some record at hGet
    exact decide_eq_true (creditObservationOfMark hp hMax.1 0 hGet (by omega) h)

end PTX.Kernels.TmlFa4Fwd.Correction
