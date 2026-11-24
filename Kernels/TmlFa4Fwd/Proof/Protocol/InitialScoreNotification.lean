-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityScoreOrder
public import Lemmas.Protocol.MbarRingRound
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.TmemInitialScoreStore
import Kernels.TmlFa4Fwd.Proof.Protocol.TailProbabilityObservations
import Lemmas.Protocol.PollPhase
import Lemmas.Protocol.MbarRingBlocker
import Lemmas.Protocol.MbarUnitTx
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.Protocol.ScoreReadyFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Proof PTX.AsyncCopy PTX.MBarrier Thread.Scores

private theorem observedUnit {K : Kernel} {A : List Assumption} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l K A m X)
    {loc : Loc} {n : Nat}
    (hInit : PairTmaRing.InitFirst X loc n) (hPos : 0 < n)
    (hNo : NoInval (X.objects loc))
    (hUnit : ∀ r ∈ X.objects loc, CounterUpdate r.action → r.action = .arrive 1 0)
    {i phase : Nat} {poll : Record Ref}
    (hi : (X.objects loc)[i]? = some poll) (hPoll : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects loc) i = some phase) :
    ∃ r ∈ X.objects loc, CounterUpdate r.action ∧ r.fault = none ∧
      MbarObserved X r.id poll.id ∧ MBarrier.Before (X.objects loc) r.id poll.id := by
  classical
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hInc
    have h := hUnit r hr (by rw [hInc]; trivial)
    rw [hInc] at h
    cases h
  obtain ⟨st, hState, hOrdinal⟩ := hChecked.observed_phase hi hPoll hPhase
  have hCard := hChecked.card_unit_arrivals_phase hNo (q := phase)
    (fun _ r count tx hr _ ha => by
      have hu := hUnit r (List.mem_of_getElem? hr) (by rw [ha]; trivial)
      exact (Action.arrive.inj (ha.symm.trans hu)).1)
    (fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hNo h) hIncr
    (List.getElem?_eq_some_iff.mp hi).1.le hState (by omega)
  rw [← hCard] at hPos
  obtain ⟨k,hk⟩ := Finset.card_pos.mp hPos
  obtain ⟨_, r, tx, hr, ha, hClean, hPhaseR⟩ := Finset.mem_filter.mp hk
  have hUpdate : CounterUpdate r.action := by rw [ha]; trivial
  have hPrior := hChecked.phase_before_observation hNo
    (List.getElem?_eq_some_iff.mp hr).1.le hPhaseR hi hPoll hPhase
  exact ⟨r, List.mem_of_getElem? hr, hUpdate, hClean,
    hX.observed_of_phase hNo hr hClean hUpdate hi hPoll hPhaseR hPhase,
    k,i,r,poll,hr,rfl,hi,rfl,hPrior⟩

private def scoreHistoryDep (l : Launch) (X : Execution) (loc : Loc)
    (a b : Ref × Bool) : Prop :=
  DepStep l kernel X a b ∨ ObjectOrder l X (.mbar loc) a b

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem earlierScoreNotification {cta : Nat} (stage : Fin 2) {e : EvId}
    {spec : TcCommit.Spec} {rank : Fin 16} (hCommit : ScoreCommit l X e cta stage spec rank)
    (hPos : 0 < scoreCommitOrdinal l X cta stage e)
    (hPresent : X.RefPresent (.async e (.tcNotify rank))) :
    ∃ earlier ∈ X.objects (scoreReadyObject l cta stage), CounterUpdate earlier.action ∧
      Relation.TransGen (DepStep l kernel X) (earlier.id,false)
        (.async e (.tcNotify rank),false) ∧
      Relation.TransGen (scoreHistoryDep l X (scoreReadyObject l cta stage)) (earlier.id,true)
        (.async e (.tcNotify rank),true) ∧
      ∃ observed ∈ X.objects (scoreReadyObject l cta stage), observed.reply.waited = some true := by
  let packet : Fin 2 := 1
  let prob := probabilityObject l cta stage packet
  let score := scoreReadyObject l cta stage
  obtain ⟨wait, i, phase, w, hi, hid, hOk, hResume, hPhase, _⟩ :=
    probabilityObservedBeforeScore hp hX hCommit packet hPos
  have hProbMem : w ∈ X.objects prob := List.mem_of_getElem? hi
  have hProbInit := probabilityInitialized hp hX stage packet hProbMem
  have hProbNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) prob
  have hProbUnit (r : Record Ref) (hr : r ∈ X.objects prob) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_, _, _, _, ha⟩ := probabilityUpdate hp hX stage packet hr hu
    exact ha
  obtain ⟨r, hr, hUpdate, _, hObserved, _⟩ :=
    observedUnit hX hProbInit (by decide) hProbNo hProbUnit hi hOk hPhase
  obtain ⟨credit, hId, hCredit, _, _⟩ := probabilityUpdate hp hX stage packet hr hUpdate
  rw [hId, hid] at hObserved
  have hWarp : Prologue.warpIndex l credit.1 < 8 := by
    rcases (probabilityCreditRole hp hX stage packet hCredit).2 with h | h
    · exact h.1
    · exact (by decide : (1 : Fin 2).val ≠ 0) h.1 |>.elim
  obtain ⟨prior, k, generation, s, hk, sid, hSOk, hCreditResumes, hSPhase, _⟩ :=
    scoreObservedBeforeSoftmaxCredit hp hX stage packet hWarp hCredit
  have hScoreMem : s ∈ X.objects score := List.mem_of_getElem? hk
  have hScoreInit := scoreReadyInitialized hp hX stage hScoreMem
  have hScoreNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) score
  have hScoreUnit (r : Record Ref) (hr : r ∈ X.objects score) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_, _, _, _, _, _, _, ha⟩ := scoreReadyUpdate hp hX stage hr hu
    exact ha
  obtain ⟨beforeScore, hBefore, hSUpdate, _, hPreceding, hHistory⟩ :=
    observedUnit hX hScoreInit (by decide) hScoreNo hScoreUnit hk hSOk hSPhase
  rw [sid] at hPreceding
  obtain ⟨_, hGet⟩ := hCommit.1
  have hIssue : DepStep l kernel X (.thread e,false) (.async e (.tcNotify rank),false) :=
    DepStep.issue ⟨_, hGet⟩ hPresent (by intro t h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
  have hPrev : DepStep l kernel X (beforeScore.id,false) (.thread (credit.1,prior),true) :=
    DepStep.of_witness l (Witness.of_mbarObserved hPreceding)
  have hTrace := (((Relation.TransGen.single (DepStep.of_resumes l hCreditResumes)).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hObserved))).tail
    (DepStep.of_resumes l hResume)).tail hIssue
  have hMix : Relation.TransGen (scoreHistoryDep l X score)
      (.thread (credit.1,prior),true) (.async e (.tcNotify rank),true) :=
    Relation.TransGen.mono (fun _ _ step => Or.inl step) _ _
      (hTrace.tail (DepStep.node hPresent))
  rw [sid] at hHistory
  exact ⟨beforeScore,hBefore,hSUpdate,.head hPrev hTrace,
    .head (.inr ⟨rfl,rfl,hHistory⟩) hMix, s, hScoreMem, hSOk⟩

private theorem initialScoreAncestorPaths {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (scoreReadyObject l cta stage)) (hUpdate : CounterUpdate r.action) :
    ∃ first ∈ X.objects (scoreReadyObject l cta stage),
      ∃ issue spec rank, first.id = .async issue (.tcNotify rank) ∧
        ScoreCommit l X issue cta stage spec rank ∧ scoreCommitOrdinal l X cta stage issue = 0 ∧
        Relation.ReflTransGen (DepStep l kernel X) (first.id,false) (r.id,false) ∧
        Relation.ReflTransGen (scoreHistoryDep l X (scoreReadyObject l cta stage))
          (first.id,true) (r.id,true) := by
  classical
  let log := X.objects (scoreReadyObject l cta stage)
  let nodes : Finset (Ref × Bool) := (log.map (fun d => (d.id,false))).toFinset
  let Q (node : Ref × Bool) : Prop :=
    ∀ d ∈ log, (d.id,false) = node → CounterUpdate d.action →
      ∃ first ∈ log, ∃ issue spec rank, first.id = .async issue (.tcNotify rank) ∧
        ScoreCommit l X issue cta stage spec rank ∧ scoreCommitOrdinal l X cta stage issue = 0 ∧
        Relation.ReflTransGen (DepStep l kernel X) (first.id,false) (d.id,false) ∧
        Relation.ReflTransGen (scoreHistoryDep l X (scoreReadyObject l cta stage))
          (first.id,true) (d.id,true)
  have hNode {d : Record Ref} (hd : d ∈ log) : (d.id,false) ∈ nodes :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨d,hd,rfl⟩)
  apply induction_of_acyclic hX.depAcyclic nodes Q ?_ (r.id,false) (hNode hr) r hr rfl hUpdate
  intro node _ ih d hd hEq hAct
  subst node
  obtain ⟨issue, spec, rank, hId, hCommit, hTarget, _, _⟩ := scoreReadyUpdate hp hX stage hd hAct
  have hShape : ScoreCommit l X issue cta stage spec rank := ⟨hCommit,hTarget⟩
  rcases Nat.eq_zero_or_pos (scoreCommitOrdinal l X cta stage issue) with hZero | hPositive
  · exact ⟨d,hd,issue,spec,rank,hId,hShape,hZero,.refl,.refl⟩
  · have hPresent := object_record_present hX.tma hd
    rw [hId] at hPresent
    obtain ⟨earlier, hs, hUpd, hPath, hHist, _⟩ :=
      earlierScoreNotification hp hX stage hShape hPositive hPresent
    rw [← hId] at hPath hHist
    obtain ⟨first, hf, e, s, r, hFirst, hInit, hZero, hAncestor, hHistory⟩ :=
      ih _ (hNode hs) hPath earlier hs rfl hUpd
    exact ⟨first,hf,e,s,r,hFirst,hInit,hZero,hAncestor.trans hPath.to_reflTransGen,
      hHistory.trans hHist.to_reflTransGen⟩

/-- Any actual recurring notification follows the initial issue in the score object's history. -/
theorem recurringScoreNotificationAfterInitial {cta : Nat} (stage : Fin 2) {r : Record Ref}
    {issue : EvId} {rank : Fin 16} (hr : r ∈ X.objects (scoreReadyObject l cta stage))
    (hAct : CounterUpdate r.action) (hId : r.id = .async issue (.tcNotify rank))
    (hRecurring : 0 < scoreCommitOrdinal l X cta stage issue) :
    ∃ first ∈ X.objects (scoreReadyObject l cta stage),
      ∃ initial spec initialRank, first.id = .async initial (.tcNotify initialRank) ∧
        ScoreCommit l X initial cta stage spec initialRank ∧
        scoreCommitOrdinal l X cta stage initial = 0 ∧
        MBarrier.Before (X.objects (scoreReadyObject l cta stage)) first.id r.id := by
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  obtain ⟨first, hf, initial, spec, initialRank, hFirst, hCommit, hZero, _, hPath⟩ :=
    initialScoreAncestorPaths hp hX stage hr hAct
  have hNe : first.id ≠ r.id := by
    intro hEqual
    rw [hFirst, hId] at hEqual
    have h := (Ref.async.inj hEqual).1
    exact (Nat.ne_of_gt hRecurring) (h ▸ hZero)
  have hDep : Relation.TransGen (scoreHistoryDep l X loc) (first.id,true) (r.id,true) := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hPath with h | h
    · exact (hNe (congrArg Prod.fst h.symm)).elim
    · exact h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  have hij : i < j := by
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · exact h
    · exact (hNe (congrArg Record.id (Option.some.inj (hi.symm.trans hj)))).elim
    · have hBack : MBarrier.Before log r.id first.id := ⟨j,i,r,first,hj,rfl,hi,rfl,h⟩
      exact (hX.dependency.acyclic (.mbar loc) trivial _
        (hDep.tail (.inr ⟨rfl,rfl,hBack⟩))).elim
  exact ⟨first,hf,initial,spec,initialRank,hFirst,hCommit,hZero,⟨i,j,first,r,hi,rfl,hj,rfl,hij⟩⟩

/-- The initial score issue is the first counter update in its physical object history. -/
theorem initialScoreNotificationNoEarlierUpdate {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    {issue : EvId} {spec : TcCommit.Spec} {rank : Fin 16}
    (hi : (X.objects (scoreReadyObject l cta stage))[i]? = some r)
    (hId : r.id = .async issue (.tcNotify rank))
    (hIssue : ScoreCommit l X issue cta stage spec rank)
    (hZero : scoreCommitOrdinal l X cta stage issue = 0) :
    ∀ k < i, ∀ d, (X.objects (scoreReadyObject l cta stage))[k]? = some d →
      ¬ CounterUpdate d.action := by
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have unique {e s rk} (h : ScoreCommit l X e cta stage s rk)
      (hZ : scoreCommitOrdinal l X cta stage e = 0) :
      Ref.async e (.tcNotify rk) = r.id := by
    obtain ⟨rfl,rfl⟩ := scoreCommitOrdinalInjective hp hX h hIssue (hZ.trans hZero.symm)
    exact hId.symm
  intro k hk d hd hUpdate
  obtain ⟨e,s,rk,hed,he,ht,_,_⟩ :=
    scoreReadyUpdate hp hX stage (List.mem_of_getElem? hd) hUpdate
  have hCommit : ScoreCommit l X e cta stage s rk := ⟨he,ht⟩
  rcases Nat.eq_zero_or_pos (scoreCommitOrdinal l X cta stage e) with hz | hpos
  · have hSame := ObjectInit.checked_record_index_eq hChecked hd hi
      (hed.trans (unique hCommit hz))
    omega
  · obtain ⟨first, _, initial, initialSpec, initialRank, hFirst, hInit, hInitial, hOrder⟩ :=
      recurringScoreNotificationAfterInitial hp hX stage
        (List.mem_of_getElem? hd) hUpdate hed hpos
    obtain ⟨a,b,q,w,hA,hQa,hB,hWb,hab⟩ := hOrder
    have ha := ObjectInit.checked_record_index_eq hChecked hA hi
      (hQa.trans (hFirst.trans (unique hInit hInitial)))
    have hb := ObjectInit.checked_record_index_eq hChecked hB hd hWb
    omega

/-- The actual first score notification can never report a barrier fault. -/
theorem initialScoreNotificationClean {cta i : Nat} (stage : Fin 2) {r : Record Ref} {issue : EvId}
    {spec : TcCommit.Spec} {rank : Fin 16}
    (hi : (X.objects (scoreReadyObject l cta stage))[i]? = some r)
    (hId : r.id = .async issue (.tcNotify rank))
    (hIssue : ScoreCommit l X issue cta stage spec rank)
    (hZero : scoreCommitOrdinal l X cta stage issue = 0) :
    r.fault = none := by
  let log := X.objects (scoreReadyObject l cta stage)
  have hNone := initialScoreNotificationNoEarlierUpdate hp hX stage hi hId hIssue hZero
  apply scoreReadyInitialPhaseClean hp hX stage hi
  have hBound : i < log.length := (List.getElem?_eq_some_iff.mp hi).1
  have empty (k : Nat) (hk : k ≤ i) : unitsBefore log k = 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hK : k < log.length := by omega
      let d := log[k]
      have hd : log[k]? = some d := List.getElem?_eq_getElem hK
      rw [unitsBefore_succ log hd, ih (by omega)]
      have hNo := hNone k (by omega) d hd
      cases he : d.action <;> simp [he, arrivalUnits, CounterUpdate] at hNo ⊢
  exact empty i le_rfl

private theorem initialScorePhaseOfNoRecurringUpdate {cta n : Nat} (stage : Fin 2) {r : Record Ref}
    {issue : EvId} {spec : TcCommit.Spec} {rank : Fin 16}
    (hr : (X.objects (scoreReadyObject l cta stage))[n]? = some r)
    (hId : r.id = .async issue (.tcNotify rank)) (hAction : r.action = .arrive 1 0)
    (hIssue : ScoreCommit l X issue cta stage spec rank)
    (hOrdinal : scoreCommitOrdinal l X cta stage issue = 0)
    (hNoRecurring : ∀ j sp rank, ScoreCommit l X j cta stage sp rank →
      0 < scoreCommitOrdinal l X cta stage j →
      X.RefPresent (.async j (.tcNotify rank)) → False) :
    let log := X.objects (scoreReadyObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  classical
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  have hMem : r ∈ log := List.mem_of_getElem? hr
  have hInit := scoreReadyInitialized hp hX stage hMem
  have hCheck := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨initial, hi, hCount, hClean, _⟩ := hInit r hMem
  have hLength : 0 < log.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨st, hs, hExpected⟩ := ObjectInit.checked_expected_after_init
    hCheck hNo hi hCount hClean hLength (Nat.le_refl _)
  have hShape {q : Record Ref} (hq : q ∈ log) (hUpdate : CounterUpdate q.action) :
      q.action = .arrive 1 0 := by
    obtain ⟨_, _, _, _, _, _, _, hAct⟩ := scoreReadyUpdate hp hX stage hq hUpdate
    exact hAct
  have hOnly {q : Record Ref} (hq : q ∈ log) (hUpdate : CounterUpdate q.action) :
      q.id = r.id := by
    obtain ⟨j, sp, rk, hQ, hCommit, hTarget, _, _⟩ := scoreReadyUpdate hp hX stage hq hUpdate
    have hScore : ScoreCommit l X j cta stage sp rk := ⟨hCommit, hTarget⟩
    rcases Nat.eq_zero_or_pos (scoreCommitOrdinal l X cta stage j) with hz | hPos
    · obtain ⟨rfl, rfl⟩ := scoreCommitOrdinalInjective hp hX hScore hIssue (hz.trans hOrdinal.symm)
      exact hQ.trans hId.symm
    · have hPresent := object_record_present hX.tma hq
      rw [hQ] at hPresent
      exact (hNoRecurring j sp rk hScore hPos hPresent).elim
  have hUnit : UnitTx log 0 := by
    refine ⟨?_, ?_, fun _ _ h => PairTmaRing.expected_of_init hX hInit hNo h⟩
    · intro q hq _ c tx hAct
      exact Action.arrive.inj (hAct.symm.trans (hShape hq (by rw [hAct]; trivial)))
    · intro q hq _ tx hAct
      have h := hShape hq (by rw [hAct]; trivial)
      rw [hAct] at h
      cases h
  have hTx : st.tx = 0 := by
    simpa using hUnit.tx hCheck hNo (Nat.le_refl _) hs
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro q hq hAct
    have h := hShape hq (by rw [hAct]; trivial)
    rw [hAct] at h
    cases h
  have hUpper : unitsBefore log log.length ≤ 1 := by
    simpa using hCheck.unitsBefore_le_card {r.id}
      (fun _ q c tx hq hFault hAct => (hUnit.arrive q (List.mem_of_getElem? hq) hFault c tx hAct).1)
      (fun _ _ q _ _ hq _ hAct =>
        Finset.mem_singleton.mpr (hOnly (List.mem_of_getElem? hq) (by rw [hAct]; trivial)))
  have hFault := initialScoreNotificationClean hp hX stage hr hId hIssue hOrdinal
  have hUnits : arrivalUnits log = 1 := by
    have hLow : 1 ≤ arrivalUnits log := by
      rw [arrivalUnits_eq_length (fun q hq c tx hf ha => (hUnit.arrive q hq hf c tx ha).1)]
      exact List.length_pos_of_mem (List.mem_filter.mpr
        ⟨hMem, countedArrive_iff.mpr ⟨hFault, 1, 0, hAction⟩⟩)
    rw [unitsBefore, List.take_length] at hUpper
    omega
  have hPhase := MbarRing.Blocker.units_eq_phase hCheck hNo hs hTx hExpected hIncr
  exact ⟨st, hs, hPhase.symm.trans hUnits⟩

/-- The opening score is still available to a lane that has not acquired it.
A recurring score requires the full participation of that lane's warp. -/
theorem initialScoreReadyPhaseForPendingLane {g n : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hStage : Prologue.warpIndex l g / 4 = stage.val) {r : Record Ref} {issue : EvId}
    {spec : TcCommit.Spec} {rank : Fin 16}
    (hr : (X.objects (scoreReadyObject l (g/l.block) stage))[n]? = some r)
    (hId : r.id = .async issue (.tcNotify rank)) (hAction : r.action = .arrive 1 0)
    (hIssue : ScoreCommit l X issue (g/l.block) stage spec rank)
    (hOrdinal : scoreCommitOrdinal l X (g/l.block) stage issue = 0)
    (hMissing : ¬ ∃ j, FirstScoreAcquire l X (g,j) stage) :
    let log := X.objects (scoreReadyObject l (g/l.block) stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  apply initialScorePhaseOfNoRecurringUpdate hp hX stage hr hId hAction hIssue hOrdinal
  intro issue' spec' rank' hLater hPositive _
  obtain ⟨wait, n, phase, actual, hRecord, _, hSuccess, _, hPhase, _⟩ :=
    probabilityObservedBeforeScore hp hX hLater 1 hPositive
  let warp : Fin 4 := ⟨Prologue.warpIndex l g % 4, Nat.mod_lt _ (by decide)⟩
  obtain ⟨credit, hCredit, hWarp, _, _⟩ :=
    tailCreditOfObservedWarpExact hp hX stage warp hRecord hSuccess hPhase
  have hCta := (probabilityCreditRole hp hX stage 1 hCredit).1
  have hSource := hCredit
  obtain ⟨_, hCreditEvent⟩ := hSource
  have hWarpIndex : Prologue.warpIndex l g = Prologue.warpIndex l credit.1 := by
    change Prologue.warpIndex l credit.1 = 4 * stage.val + Prologue.warpIndex l g % 4 at hWarp
    omega
  have hSame : SameWarp l g credit.1 :=
    ⟨⟨hg, event_thread_lt hX hCreditEvent, hCta.symm⟩, hWarpIndex⟩
  exact hMissing (Thread.firstScoreAcquireOfTailPeer hp hX hSame hStage hCredit)

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
