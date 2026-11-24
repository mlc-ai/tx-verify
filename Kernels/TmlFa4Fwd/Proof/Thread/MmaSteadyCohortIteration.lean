-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyKeyCohort
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyBodyEnd
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaScoreRounds
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyRetirementOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread.Mma (ReleaseIssue releaseOccurrence atPrefix kvAcquireCount readyUsesAtPrefix
  loopKeyRetirementOrdinalOfReadyCount loopValueRetirementOrdinalOfReadyCount)
open Thread.Scores (probabilityObject ScoreCommit scoreCommitOrdinal)

noncomputable section

/-- Credits published for a single recurring consumer visit. -/
structure SteadyVisitCohorts (l : Launch) (X : Execution) (g visit : Nat) : Prop where
  value : Protocol.LoaderReady.DeliveredCohort l X g
    (readyStage (2*visit+1)) ((2*visit+1)/3)
  key : Protocol.LoaderReady.DeliveredCohort l X g
    (readyStage (2*visit+2)) ((2*visit+2)/3)
  probability : ∀ stage packet : Fin 2,
    Protocol.Scores.ProbabilityCohort l X (g/l.block) stage packet visit

def cacheLoc (l : Launch) (cta : Nat) (slot : Fin 3) : Loc :=
  ⟨.shared,cta,l.sharedBase+(8*slot.val+32)⟩

/-- The consumer prefix counts once per earlier probability visit and once per
earlier logical use of each rotating cache slot. -/
structure SteadyVisitLedger (l : Launch) (X : Execution) (g visit : Nat)
    (pos : Nat → Nat) : Prop where
  cache : ∀ lane < 32, ∀ slot : Fin 3, okPolls (cacheLoc l (g/l.block) slot)
    ((X.tr (warpLane l g lane)).take (pos lane)) = (2*visit+1+(2-slot.val))/3
  probability : ∀ lane < 32, ∀ stage packet : Fin 2,
    okPolls (probabilityObject l (g/l.block) stage packet)
      ((X.tr (warpLane l g lane)).take (pos lane)) = visit

private theorem cacheLocInj (l : Launch) (cta : Nat) :
    Function.Injective (cacheLoc l cta) := by
  intro a b h
  apply Fin.ext
  have ha := congrArg Loc.addr h
  change l.sharedBase+(8*a.val+32) = l.sharedBase+(8*b.val+32) at ha
  omega

private theorem cacheLocNeProbability (l : Launch) (cta : Nat)
    (slot : Fin 3) (stage packet : Fin 2) :
    cacheLoc l cta slot ≠ probabilityObject l cta stage packet := by
  intro he
  have hs := slot.isLt
  have hq := congrArg Loc.addr he
  change l.sharedBase+(8*slot.val+32) = l.sharedBase+(96+8*stage.val+16*packet.val) at hq
  omega

private theorem probabilityEq (l : Launch) (cta : Nat) (s p s' p' : Fin 2) :
    probabilityObject l cta s p = probabilityObject l cta s' p' ↔ s = s' ∧ p = p' := by
  constructor
  · intro he
    have h := congrArg Loc.addr he
    change l.sharedBase+(96+8*s.val+16*p.val) = l.sharedBase+(96+8*s'.val+16*p'.val) at h
    have hs := s.isLt
    have ht := s'.isLt
    refine ⟨Fin.ext ?_,Fin.ext ?_⟩ <;> omega
  · rintro ⟨rfl,rfl⟩
    rfl

private theorem cacheCountUse (use : Nat) (slot : Fin 3) :
    (use+(2-slot.val))/3 + (if slot = readyStage use then 1 else 0) =
      (use+1+(2-slot.val))/3 := by
  have hLt := slot.isLt
  have hVal : (readyStage use).val = use%3 := rfl
  by_cases h : slot = readyStage use
  · have hSlot := (congrArg Fin.val h).trans hVal
    rw [ite_eq_left h]
    omega
  · have hSlot : slot.val ≠ use%3 := fun he => h (Fin.ext (he.trans hVal.symm))
    rw [ite_eq_right h]
    omega

private theorem cacheCountStep (visit : Nat) (slot : Fin 3) :
    (2*visit+1+(2-slot.val))/3 + (if slot = readyStage (2*visit+1) then 1 else 0) +
      (if slot = readyStage (2*visit+2) then 1 else 0) =
      (2*(visit+1)+1+(2-slot.val))/3 := by
  have h := (congrArg (· + if slot = readyStage (2*visit+2) then 1 else 0)
    (cacheCountUse (2*visit+1) slot)).trans (cacheCountUse (2*visit+2) slot)
  have he : 2*visit+2+1 = 2*(visit+1)+1 := by omega
  rw [he] at h
  exact h

private theorem cacheCountSum (uses : Nat) :
    (uses+2)/3 + (uses+1)/3 + uses/3 = uses := by
  have hA : (uses+1)%3 = (uses%3+1)%3 := by omega
  have hB : (uses+2)%3 = (uses%3+2)%3 := by omega
  have hRem : uses%3 + (uses+1)%3 + (uses+2)%3 = 3 := by
    rw [hA,hB]
    have h := Nat.mod_lt uses (by decide : 0 < 3)
    generalize uses%3 = r at h ⊢
    interval_cases r <;> decide
  have ha := Nat.mod_add_div uses 3
  have hb := Nat.mod_add_div (uses+1) 3
  have hc := Nat.mod_add_div (uses+2) 3
  omega

private theorem cacheNextValueOrdinal (visit : Nat) :
    (2*visit+1+(2-(readyStage (2*visit+1)).val))/3 = (2*visit+1)/3 := by
  change (2*visit+1+(2-(2*visit+1)%3))/3 = _
  omega

private theorem cacheNextKeyOrdinal (visit : Nat) :
    (2*visit+1+(2-(readyStage (2*visit+2)).val))/3 = (2*visit+2)/3 := by
  change (2*visit+1+(2-(2*visit+2)%3))/3 = _
  omega

private theorem cacheKeyNeValue (l : Launch) (cta visit : Nat) :
    cacheLoc l cta (readyStage (2*visit+2)) ≠ cacheLoc l cta (readyStage (2*visit+1)) := by
  intro h
  have he := congrArg Fin.val (cacheLocInj l cta h)
  change (2*visit+2)%3 = (2*visit+1)%3 at he
  omega

/-- The recorded cache retirement issues and the score generations they publish. -/
structure SteadyRetirementAges (l : Launch) (X : Execution) (g visit : Nat) : Prop where
  value : ∃ issuer idx, SameWarp l g issuer ∧ ReleaseIssue X issuer idx .loopValue
    (commitSpec l issuer (l.sharedBase+8*(readyStage (2*visit+1)).val+56)) ∧
    releaseOccurrence X issuer idx .loopValue = visit
  keyAndScores : ∃ issuer idx, SameWarp l g issuer ∧ ReleaseIssue X issuer idx .loopKey
    (commitSpec l issuer (l.sharedBase+8*(readyStage (2*visit+2)).val+56)) ∧
    releaseOccurrence X issuer idx .loopKey = visit ∧
    ∀ stage : Fin 2, ∃ score spec,
      ScoreCommit l X (issuer,score) (issuer/l.block) stage spec 0 ∧
      scoreCommitOrdinal l X (issuer/l.block) stage (issuer,score) = visit+1 ∧
      TraceBefore X (issuer,score) (issuer,idx)

/-- The actual release issue matches the ready generation for this cache use. -/
def RetiredCacheUse (l : Launch) (X : Execution) (g use : Nat)
    (form : Thread.Mma.ReleaseForm) : Prop :=
  ∃ issuer idx,
    SameWarp l g issuer ∧ ReleaseIssue X issuer idx form
      (commitSpec l issuer (l.sharedBase+8*(readyStage use).val+56)) ∧
    ∃ a : Thread.Mma.ReleaseMatch l X issuer idx form
      (Thread.Mma.Observation.emptyObject l issuer (readyStage use)),
      a.slot = readyStage use ∧ (atPrefix l X issuer a.wait).kvAcquires a.slot = use/3

private theorem recurringRetirementTarget (l : Launch) (issuer use : Nat) :
    TcCommit.target (commitSpec l issuer (l.sharedBase+8*(readyStage use).val+56)) 0 =
      some (Thread.Mma.Observation.emptyObject l issuer (readyStage use)) := by
  simp [TcCommit.target,commitSpec,Thread.Mma.Observation.emptyObject,Loader.emptySlot_address]

/-- The recurring value release returns the exact earlier V cohort generation. -/
theorem SteadyRetirementAges.valueReturnsUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g visit : Nat} (hw : warpIndex l g = 12) (hAges : SteadyRetirementAges l X g visit) :
    RetiredCacheUse l X g (2*visit+1) .loopValue := by
  obtain ⟨issuer,idx,hWarp,hIssue,hRank⟩ := hAges.value
  obtain ⟨a⟩ := hIssue.matchReady hp hX (recurringRetirementTarget l issuer (2*visit+1))
  have hOperands := a.loopValueOperandsOfVisit hp hX hWarp.1.2.1 (hWarp.2.symm.trans hw)
    hIssue hRank
  exact ⟨issuer,idx,hWarp,hIssue,a,hOperands.1,hOperands.2.1⟩

/-- The recurring key release returns the exact earlier K cohort generation. -/
theorem SteadyRetirementAges.keyReturnsUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g visit : Nat} (hw : warpIndex l g = 12) (hAges : SteadyRetirementAges l X g visit) :
    RetiredCacheUse l X g (2*visit+2) .loopKey := by
  obtain ⟨issuer,idx,hWarp,hIssue,hRank,_⟩ := hAges.keyAndScores
  obtain ⟨a⟩ := hIssue.matchReady hp hX (recurringRetirementTarget l issuer (2*visit+2))
  have hOperands := a.loopKeyOperandsOfVisit hp hX hWarp.1.2.1 (hWarp.2.symm.trans hw) hRank
  exact ⟨issuer,idx,hWarp,hIssue,a,hOperands.1,hOperands.2.1⟩

/-- A reached visit with its publication cohorts consumes exactly its six
credits and issues both accumulator packets, both score and both retirement
notifications, advancing the complete consumer ledger to the successor. -/
theorem steadyIterationOfCohorts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : Protocol.Scores.CorrectionJointGuards l X)
    {g visit remaining shuffles votes : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 12)
    {ends : Nat → Option TState} (hRemaining : 2 ≤ remaining) (hBound : remaining < 2^32)
    (cur : SteadyIterationCursor l X g visit remaining shuffles votes ends)
    (hLedger : SteadyVisitLedger l X g visit cur.pos)
    (hCohorts : SteadyVisitCohorts l X g visit) :
    ∃ lastEnds, ∃ next : SchedulerWarpReached l X g (if 2 < remaining then 2291 else 2534)
      (fun _ => steadyFrame l (visit+1) (remaining-1) ++ steadyIterationRoots l)
      (shuffles+3+1+2) votes lastEnds,
      SteadyVisitLedger l X g (visit+1) next.pos ∧ SteadyIterationIssues l X g visit ∧
      (∀ lane < 32, cur.pos lane < next.pos lane) ∧ SteadyRetirementAges l X g visit
    := by
  let cta := g/l.block
  let key := cacheLoc l cta (readyStage (2*visit+2))
  let value := cacheLoc l cta (readyStage (2*visit+1))
  let prob := probabilityObject l cta
  obtain ⟨_,pv0,hPv0,hFirst⟩ := steadyVisitFirstProductOfCohorts hp hMax hGuard hg hWarp cur
    hCohorts.value (hCohorts.probability 0)
    (fun lane hl => (hLedger.cache lane hl _).trans (cacheNextValueOrdinal visit))
    (fun packet lane hl => hLedger.probability lane hl 0 packet)
  obtain ⟨k,hKey⟩ := steadyKeyPollOfDelivered hp hMax hg hWarp pv0 hCohorts.key (fun lane hl => by
    change okPolls key _ = _
    rw [(hFirst lane hl).2 key]
    change _ + (if key = value then 1 else 0) + (if key = prob 0 0 then 1 else 0) +
      (if key = prob 0 1 then 1 else 0) = _
    rw [ite_eq_right (cacheKeyNeValue l cta visit),
      ite_eq_right (cacheLocNeProbability l cta _ 0 0),
      ite_eq_right (cacheLocNeProbability l cta _ 0 1)]
    simpa only [Nat.add_zero,cacheNextKeyOrdinal] using
      hLedger.cache lane hl (readyStage (2*visit+2)))
  obtain ⟨score,hScore,si,sj,hWarpScore,hScoreIssue,_⟩ :=
    steadyFirstQkScoreWithPollCounts hp hMax hg k
  obtain ⟨prePv,hPre⟩ := score.advanceLocalWithPosition (pc' := 2419)
    (G := fun _ => steadySecondPvFrame l visit remaining) (by
    intro lane hl
    have ht := score.checkpoint lane hl
    have hh := (holds_append ..).mp ht.2.2.2.2
    have hx := (holds_append ..).mp hh.1.2
    refine ⟨_,.refl,ht.mono ⟨hx.2.1,?_⟩⟩
    exact (holds_append ..).mpr ⟨⟨hh.1.1,(holds_append ..).mpr ⟨hx.1,trivial⟩⟩,hh.2⟩)
  have hProb (packet : Fin 2) (lane : Nat) (hl : lane < 32) :
      okPolls (prob 1 packet) ((X.tr (warpLane l g lane)).take (prePv.pos lane)) = visit := by
    rw [hPre,(hScore lane hl).2,(hKey lane hl).2.2.1,(hFirst lane hl).2]
    change _ + (if prob 1 packet = value then 1 else 0) +
      (if prob 1 packet = prob 0 0 then 1 else 0) +
      (if prob 1 packet = prob 0 1 then 1 else 0) + (if prob 1 packet = key then 1 else 0) = _
    rw [ite_eq_right (Ne.symm (cacheLocNeProbability l cta _ 1 packet)),
      ite_eq_right (Ne.symm (cacheLocNeProbability l cta _ 1 packet))]
    simpa only [prob,probabilityEq,show (1 : Fin 2) ≠ 0 by decide,false_and,ite_false,
      Nat.add_zero] using hLedger.probability lane hl 1 packet
  obtain ⟨p1,hMain⟩ := steadySecondMainOfCohort hp hMax hGuard hg hWarp prePv
    (hProb 0) (hCohorts.probability 1 0)
  obtain ⟨lastEnds,_,pv1,hPv1,hSecond⟩ :=
    steadySecondPvPacketWithPollCounts hp hMax hg p1 (fun lane hl => .inr (by
      have hPeer := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
      have hc : (warpLane l g lane)/l.block = cta := hPeer.1.2.2.symm
      have hw : warpIndex l (warpLane l g lane) = 12 := hPeer.2.symm.trans hWarp
      change okPolls (probabilityObject l ((warpLane l g lane)/l.block) 1 1)
          (X.tr (warpLane l g lane)) =
        okPolls (probabilityObject l ((warpLane l g lane)/l.block) 1 1)
          ((X.tr (warpLane l g lane)).take (p1.pos lane)) → _
      rw [hc]
      have hAddr : prob 1 1 ≠ prob 1 0 := by
        change probabilityObject l cta 1 1 ≠ probabilityObject l cta 1 0
        rw [ne_eq,probabilityEq]
        decide
      have hCount := (hMain lane hl).2.2.1 (prob 1 1)
      change _ = _ + (if prob 1 1 = prob 1 0 then 1 else 0) at hCount
      simp only [ite_eq_right hAddr,Nat.add_zero,hProb 1 lane hl] at hCount
      rw [hCount]
      intro hTotal
      have hReady := Protocol.Scores.probabilityReadyOfUnconsumedCohort hp hMax.1 hGuard
        (g := warpLane l g lane) (gen := visit) hPeer.1.2.1 hw 1 1
        (by rw [hc]; exact hCohorts.probability 1 1) (by rwa [hc])
      rw [hc] at hReady
      exact hReady))
  obtain ⟨done,hEnd,⟨vi,vj,hVr,hVe,hVLower,hVUpper⟩,⟨si',sj',hSr,hSe,_⟩,ki,kj,hKr,hKe,hKPos⟩ :=
    steadyBodyEndWithPollCounts hp hMax hg hRemaining hBound pv1 (fun lane hl =>
      (hSecond lane hl).2.1)
  have hDelta (lane : Nat) (hl : lane < 32) (object : Loc) :
      okPolls object ((X.tr (warpLane l g lane)).take (done.pos lane)) =
        okPolls object ((X.tr (warpLane l g lane)).take (cur.pos lane)) +
        (if object = value then 1 else 0) + (if object = prob 0 0 then 1 else 0) +
        (if object = prob 0 1 then 1 else 0) + (if object = key then 1 else 0) +
        (if object = prob 1 0 then 1 else 0) + (if object = prob 1 1 then 1 else 0) := by
    rw [(hEnd lane hl).2 object,(hSecond lane hl).2.2 object,(hMain lane hl).2.2.1 object,
      hPre,(hScore lane hl).2 object,(hKey lane hl).2.2.1 object,(hFirst lane hl).2 object]
    simp [value,key,prob,cta,cacheLoc,readyAddr,probabilityObject]
    rfl
  have hNextLedger : SteadyVisitLedger l X g (visit+1) done.pos := by
    refine ⟨?_,?_⟩
    · intro lane hl slot
      change okPolls (cacheLoc l cta slot) ((X.tr _).take (done.pos lane)) = _
      rw [hDelta lane hl (cacheLoc l cta slot),hLedger.cache lane hl slot]
      have hc0 := cacheLocNeProbability l cta slot 0 0
      have hc1 := cacheLocNeProbability l cta slot 0 1
      have hc2 := cacheLocNeProbability l cta slot 1 0
      have hc3 := cacheLocNeProbability l cta slot 1 1
      change cacheLoc l cta slot ≠ prob 0 0 at hc0
      change cacheLoc l cta slot ≠ prob 0 1 at hc1
      change cacheLoc l cta slot ≠ prob 1 0 at hc2
      change cacheLoc l cta slot ≠ prob 1 1 at hc3
      rw [ite_eq_right hc0,ite_eq_right hc1,ite_eq_right hc2,ite_eq_right hc3]
      simpa only [value,key,(cacheLocInj l cta).eq_iff,Nat.add_zero] using cacheCountStep visit slot
    · intro lane hl stage packet
      change okPolls (prob stage packet) ((X.tr _).take (done.pos lane)) = _
      rw [hDelta lane hl (prob stage packet),hLedger.probability lane hl stage packet]
      have hv : prob stage packet ≠ value := (cacheLocNeProbability l cta _ _ _).symm
      have hk : prob stage packet ≠ key := (cacheLocNeProbability l cta _ _ _).symm
      rw [ite_eq_right hv,ite_eq_right hk]
      fin_cases stage <;> fin_cases packet <;> simp [prob,probabilityEq]
  have hUses {issuer idx : Nat} (hs : SameWarp l g issuer)
      (hEarly : pv1.pos (laneOf l issuer) ≤ idx) (hLate : idx ≤ done.pos (laneOf l issuer)) :
      (((X.tr issuer).take idx).filterMap readyEvent).length = 2*visit+3 := by
    let lane := laneOf l issuer
    have hl : lane < 32 := Nat.mod_lt _ (by decide)
    have hThread : warpLane l g lane = issuer := Step.warpLane_of_sameWarp hs
    have hBlock : issuer/l.block = cta := hs.1.2.2.symm
    have hw : warpIndex l issuer = 12 := hs.2.symm.trans hWarp
    rw [readyUsesAtPrefix hp hMax.1 hs.1.2.1 hw]
    have hSlot (slot : Fin 3) : (atPrefix l X issuer idx).kvAcquires slot =
        (2*(visit+1)+1+(2-slot.val))/3 := by
      rw [atPrefix,kvAcquireCount,Loader.readySlot_address,hBlock,Nat.add_assoc]
      change okPolls (cacheLoc l cta slot) ((X.tr issuer).take idx) = _
      rw [← hThread]
      have hBefore := MbarRing.Poll.okPolls_mono (cacheLoc l cta slot) (X.tr (warpLane l g lane))
        (show pv1.pos lane ≤ idx from hEarly)
      have hAfter := MbarRing.Poll.okPolls_mono (cacheLoc l cta slot) (X.tr (warpLane l g lane))
        (show idx ≤ done.pos lane from hLate)
      rw [← (hEnd lane hl).2 (cacheLoc l cta slot),hNextLedger.cache lane hl slot] at hBefore
      rw [hNextLedger.cache lane hl slot] at hAfter
      omega
    rw [hSlot 0,hSlot 1,hSlot 2]
    change (2*(visit+1)+1+2)/3 + (2*(visit+1)+1+1)/3 + (2*(visit+1)+1)/3 = _
    rw [cacheCountSum]
    omega
  have hVAge := loopValueRetirementOrdinalOfReadyCount hp hMax.1 hVr.1.2.1
    (hVr.2.symm.trans hWarp) hVe (hUses hVr hVLower hVUpper.le)
  have hKAge : releaseOccurrence X ki kj .loopKey = visit := by
    have hl : laneOf l ki < 32 := Nat.mod_lt _ (by decide)
    have hAfter := (hEnd (laneOf l ki) hl).1
    rw [← hKPos] at hAfter
    exact loopKeyRetirementOrdinalOfReadyCount hp hMax.1 hKr.1.2.1
      (hKr.2.symm.trans hWarp) hKe (hUses hKr (by omega) (by omega))
  refine ⟨lastEnds,done,hNextLedger,⟨?_,?_,⟨vi,vj,hVr,hVe⟩,ki,kj,hKr,hKe⟩,?_,
    ⟨⟨vi,vj,hVr,hVe,hVAge⟩,ki,kj,hKr,hKe,hKAge,?_⟩⟩
  · intro stage
    fin_cases stage
    · exact hPv0
    · exact hPv1
  · intro stage
    fin_cases stage
    · exact ⟨si,sj,hWarpScore,hScoreIssue⟩
    · simpa only [Nat.add_assoc] using (show ∃ g i, SameWarp l _ g ∧
          X.Commit (g,i) (commitSpec l g (l.sharedBase+88)) from ⟨si',sj',hSr,hSe⟩)
  · intro lane hl
    have hScorePast := (hScore lane hl).1
    have hMainPast := (hMain lane hl).1
    rw [hPre] at hMainPast
    exact (hFirst lane hl).1.trans ((hKey lane hl).1.trans
      (hScorePast.trans (hMainPast.trans ((hSecond lane hl).1.trans (hEnd lane hl).1))))
  · intro stage
    obtain ⟨idx,spec,hScore',hAge,hBefore⟩ :=
      Thread.Scores.recurringScoreOfKeyRelease hp hMax.1 hKe stage
    exact ⟨idx,spec,hScore',by rw [hAge,hKAge,Nat.add_comm],hBefore⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
