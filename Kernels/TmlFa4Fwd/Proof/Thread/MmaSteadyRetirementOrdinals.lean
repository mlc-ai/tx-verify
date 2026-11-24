-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseMatch
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTailValueProgress
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.CountTake
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow Prologue
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (readyObject)

noncomputable section

private theorem taggedKeyCount {l : Launch} {g use : Nat} {es : List (Nat × (Loc × Nat))}
    (h : TaggedReadySequence l g use es) :
    es.countP (fun e => e.1 == readyHead 2) = (use+es.length-1)/2-(use-1)/2 := by
  induction h with
  | nil => simp
  | @next use pc es hSite _ ih =>
    have hFlag : (pc == readyHead 2) = decide (0 < use ∧ use%2 = 0) := by
      rcases hSite with ⟨rfl,rfl⟩ | ⟨rfl,hu,hm⟩ | ⟨hs,hm⟩
      · rfl
      · simp [hu,hm]
      · rcases hs with rfl | rfl <;> simp [hm,readyHead]
    simp only [List.countP_cons,hFlag,decide_eq_true_eq,List.length_cons,ih]
    split <;> omega

private theorem readyHeadProjection (es : List Event) (gate : Fin 4) :
    (es.filterMap readyEventTagged).countP (fun e => e.1 == readyHead gate) =
      es.countP (readyAtSite gate) := by
  rw [List.countP_filterMap]
  have hEq (ev : Event) :
      ((readyEventTagged ev).map (fun e => e.1 == readyHead gate)).getD false =
        readyAtSite gate ev := by
    have hs : (slotWait gate).pc = readyHead gate := by fin_cases gate <;> rfl
    obtain ⟨pc,kind⟩ := ev
    cases kind <;> try rfl
    case wait loc phase ok acquire scope =>
      cases ok
      · rfl
      · by_cases hPc : pc = readyHead gate
        · subst pc
          have hTag : (List.finRange 4).any (fun i => readyHead i == readyHead gate) = true :=
            List.any_eq_true.mpr ⟨gate,by simp,by simp⟩
          simp [readyEventTagged,readyEvent,readyAtSite,hs,hTag]
        · simp only [readyEventTagged,readyEvent]
          split <;> simp [readyAtSite,hs,hPc]
  rw [funext hEq]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The number of completed recurring K acquires is determined by the total on
the role's ready ring. The priming K acquire contributes only to that total. -/
theorem loopKeyOccurrenceFromReadyCount {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (index : Nat) :
    readyOccurrence X g index .loopKey =
      ((((X.tr g).take index).filterMap readyEvent).length-1)/2 := by
  let pre := (X.tr g).take index
  let tags := pre.filterMap readyEventTagged
  have hCut : ((X.tr g).filterMap readyEventTagged).take tags.length = tags := by
    obtain ⟨tail,hSplit⟩ := List.take_prefix index (X.tr g)
    rw [←hSplit,List.filterMap_append]
    simp [tags,pre]
  have hTags : TaggedReadySequence l g 0 tags :=
    hCut ▸ taggedPrefix (rawTaggedReadySequence hp hX hg hw) tags.length
  have hCount := taggedKeyCount hTags
  rw [Nat.zero_add,show (0-1)/2 = 0 by decide,Nat.sub_zero] at hCount
  change (pre.filterMap readyEventTagged).countP _ = _ at hCount
  rw [readyHeadProjection pre 2] at hCount
  change pre.countP (readyAtSite 2) = ((pre.filterMap readyEvent).length-1)/2
  simpa only [tags,← taggedProjectionErase pre,List.length_map] using hCount

private theorem releaseReadyBalanceAtIssue {g index : Nat} {form : ReleaseForm}
    {spec : TcCommit.Spec} (he : ReleaseIssue X g index form spec) :
    readyOccurrence X g index form = 1+releaseOccurrence X g index form := by
  obtain ⟨hPos,inst,leader,hE⟩ := readyReleaseElection hp hX (releaseIndex form) he
  have hCount := releaseElectionBalance hp hX (releaseIndex form)
    (show X.Elect (g,index-1) (slotElect (releaseIndex form)).pc (2^32-1) inst leader from hE)
  have hSame := countP_take_succ_false (p := readyAtSite (releaseIndex form)) hE rfl
  have hIndex : index-1+1 = index := by omega
  rw [hIndex] at hSame
  exact hSame.trans hCount

omit hp hX in
private theorem noTailCountBeforeLoopValue {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {spec : TcCommit.Spec} (he : ReleaseIssue X g index .loopValue spec) :
    ((X.tr g).take index).countP (readyAtSite 3) = 0 := by
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨before,_,hPrefix,hStep⟩ := hRun.before_event he
  have hPc : before.pc = 2462 := (PTX.EventFrame.estep_source_pc hStep).symm
  apply List.countP_eq_zero.mpr
  intro ev hm hMark
  have hLate : 2534 ≤ ev.pc := by
    obtain ⟨pc,kind⟩ := ev
    cases kind <;> try cases hMark
    case wait loc phase ok acquire scope =>
      cases ok <;> try cases hMark
      have hTag : pc = (slotWait 3).pc := beq_iff_eq.mp hMark
      rw [hTag]
      change 2534 ≤ (slotWait 3).pc
      decide
  have hFloor := eventReachesFloor (by decide : 2534 ∈ [2285,2534]) hPrefix ⟨ev,hm,hLate⟩
  omega

/-- At the retirement after a completed recurring visit, the observed ready ring
determines the logical occurrence of the K release. -/
theorem loopKeyRetirementOrdinalOfReadyCount {g index visit : Nat} {spec : TcCommit.Spec}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (he : ReleaseIssue X g index .loopKey spec)
    (hUses : (((X.tr g).take index).filterMap readyEvent).length = 2*visit+3) :
    releaseOccurrence X g index .loopKey = visit := by
  have h := (loopKeyOccurrenceFromReadyCount hp hX hg hw index).symm.trans
    (releaseReadyBalanceAtIssue hp hX he)
  rw [hUses] at h
  omega

/-- At the retirement after a completed recurring visit, the observed ready ring
determines the logical occurrence of the V release. -/
theorem loopValueRetirementOrdinalOfReadyCount {g index visit : Nat} {spec : TcCommit.Spec}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (he : ReleaseIssue X g index .loopValue spec)
    (hUses : (((X.tr g).take index).filterMap readyEvent).length = 2*visit+3) :
    releaseOccurrence X g index .loopValue = visit := by
  have h := readyValueCountAtPrefix hp hX hg hw index
  change readyOccurrence X g index .loopValue +
    ((X.tr g).take index).countP (readyAtSite 3) =
      (((X.tr g).take index).filterMap readyEvent).length/2 at h
  rw [noTailCountBeforeLoopValue hX he,hUses,releaseReadyBalanceAtIssue hp hX he] at h
  omega

private theorem ReleaseMatch.useSite {g index : Nat} {form : ReleaseForm} {target : Loc}
    (hw : warpIndex l g = 12) (a : ReleaseMatch l X g index form target) :
    ReadyUseSite ((((X.tr g).take a.wait).filterMap readyEvent).length)
      (slotWait (releaseIndex form)).pc := by
  obtain ⟨pc,hEvent,hSite⟩ := a.ready.useSite hp hX hw
  have hRaw : X.get (g,a.wait) = some ⟨(slotWait (releaseIndex form)).pc,
      .wait (readyObject l g a.slot) a.parity true true .cta⟩ := a.readyForm
  have he := congrArg Event.pc (Option.some.inj (hEvent.symm.trans hRaw))
  change pc = (slotWait (releaseIndex form)).pc at he
  rwa [he] at hSite

private theorem ReleaseMatch.operandsOfUse {g index use : Nat} {form : ReleaseForm} {target : Loc}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (a : ReleaseMatch l X g index form target)
    (hUses : (((X.tr g).take a.wait).filterMap readyEvent).length = use) :
    a.slot = readyStage use ∧ (atPrefix l X g a.wait).kvAcquires a.slot = use/3 ∧
      a.parity = readyWord use := by
  have hCount := readyUsesAtPrefix hp hX hg hw a.wait
  have hOp := a.ready.exactOccurrence hp hX hw
  change a.slot.val = _ ∧ (atPrefix l X g a.wait).kvAcquires a.slot = _ ∧ a.parity = _ at hOp
  rw [← hCount,hUses] at hOp
  exact ⟨Fin.ext hOp.1,hOp.2.1,hOp.2.2⟩

/-- At exact logical visit `visit`, the matching K return retires physical slot
generation `(2*visit+2)/3`. -/
theorem ReleaseMatch.loopKeyOperandsOfVisit {g index visit : Nat} {target : Loc}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (a : ReleaseMatch l X g index .loopKey target)
    (hRank : releaseOccurrence X g index .loopKey = visit) :
    a.slot = readyStage (2*visit+2) ∧
      (atPrefix l X g a.wait).kvAcquires a.slot = (2*visit+2)/3 ∧
      a.parity = readyWord (2*visit+2) := by
  let use := (((X.tr g).take a.wait).filterMap readyEvent).length
  have hs : ReadyUseSite use (readyHead 2) := a.useSite hp hX hw
  have hShape : 0 < use ∧ use%2 = 0 := by
    rcases hs with ⟨he,_⟩ | ⟨_,h⟩ | ⟨he,_⟩
    · exact (by decide : readyHead 2 ≠ readyHead 0) he |>.elim
    · exact h
    · rcases he with he | he
      · exact (by decide : readyHead 2 ≠ readyHead 1) he |>.elim
      · exact (by decide : readyHead 2 ≠ readyHead 3) he |>.elim
  have hCount := loopKeyOccurrenceFromReadyCount hp hX hg hw a.wait
  rw [a.ordinal,hRank] at hCount
  change visit = (use-1)/2 at hCount
  exact a.operandsOfUse hp hX hg hw (show use = 2*visit+2 by omega)

/-- At exact logical visit `visit`, the matching V return retires physical slot
generation `(2*visit+1)/3`. -/
theorem ReleaseMatch.loopValueOperandsOfVisit {g index visit : Nat} {target : Loc}
    {spec : TcCommit.Spec} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hIssue : ReleaseIssue X g index .loopValue spec)
    (a : ReleaseMatch l X g index .loopValue target)
    (hRank : releaseOccurrence X g index .loopValue = visit) :
    a.slot = readyStage (2*visit+1) ∧
      (atPrefix l X g a.wait).kvAcquires a.slot = (2*visit+1)/3 ∧
      a.parity = readyWord (2*visit+1) := by
  let use := (((X.tr g).take a.wait).filterMap readyEvent).length
  have hs : ReadyUseSite use (readyHead 1) := a.useSite hp hX hw
  have hShape : use%2 = 1 := by
    rcases hs with ⟨he,_⟩ | ⟨he,_⟩ | ⟨_,h⟩
    · exact (by decide : readyHead 1 ≠ readyHead 0) he |>.elim
    · exact (by decide : readyHead 1 ≠ readyHead 2) he |>.elim
    · exact h
  have hTail := countP_take_mono (readyAtSite 3) (X.tr g) a.earlier.le
  rw [noTailCountBeforeLoopValue hX hIssue] at hTail
  have hCount := readyValueCountAtPrefix hp hX hg hw a.wait
  change readyOccurrence X g a.wait .loopValue +
    ((X.tr g).take a.wait).countP (readyAtSite 3) = use/2 at hCount
  rw [a.ordinal,hRank,Nat.eq_zero_of_le_zero hTail,Nat.add_zero] at hCount
  exact a.operandsOfUse hp hX hg hw (show use = 2*visit+1 by omega)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
