-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityScoreOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailIssuer
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.MbarRingRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy Thread.Scores
open PTX.MBarrier hiding okPolls
open PTX.Kernels.TmlFa4Fwd.Prologue (warpIndex)

/-- A tail credit is indexed by its stage-local warp and its ordinal on that warp. -/
def tailLabel (l : Launch) (X : Execution) (cta : Nat) (s : Fin 2) :
    Ref → Fin 4 × Nat
  | .thread e =>
      (⟨warpIndex l e.1 % 4, Nat.mod_lt _ (by decide)⟩, probabilityOrdinal l X cta s 1 e)
  | _ => (0,0)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Tail credits of a given warp and local ordinal identify one actual event. -/
theorem tailLabelInj {cta : Nat} {stage : Fin 2} {a b : EvId}
    (ha : ProbabilityCredit l X a cta stage 1) (hb : ProbabilityCredit l X b cta stage 1)
    (hEq : tailLabel l X cta stage (.thread a) = tailLabel l X cta stage (.thread b)) :
    a = b := by
  have role {x : EvId} (h : ProbabilityCredit l X x cta stage 1) :
      x.1 / l.block = cta ∧ warpIndex l x.1 / 4 = stage.val := by
    rcases probabilityCreditRole hp hX stage 1 h with ⟨hCta,h | h⟩
    · exact ⟨hCta,h.2⟩
    · have hn : (1 : Fin 2).val ≠ 0 := by decide
      exact (hn h.1).elim
  have hR : warpIndex l a.1 % 4 = warpIndex l b.1 % 4 :=
    congrArg (fun x => x.1.val) hEq
  have hC := role ha
  have hD := role hb
  have hMode : warpIndex l a.1 = warpIndex l b.1 := by omega
  obtain ⟨_, hGetA⟩ := show ProbabilityCredit l X a cta stage 1 from ha
  obtain ⟨_, hGetB⟩ := show ProbabilityCredit l X b cta stage 1 from hb
  have hw : SameWarp l a.1 b.1 := ⟨⟨PTX.Proof.event_thread_lt hX hGetA,
    PTX.Proof.event_thread_lt hX hGetB, hC.1.trans hD.1.symm⟩, hMode⟩
  exact probabilityOrdinalInjective ha hb (tailProbabilityCreditSameIssuer hp hX hw ha hb)
    (congrArg Prod.snd hEq)

private theorem scoreGuardForConsumedTail {cta atScore : Nat} (stage : Fin 2) {score : Record Ref}
    {e : EvId} {rank : Fin 16} {spec : TcCommit.Spec}
    (hScore : (X.objects (scoreReadyObject l cta stage))[atScore]? = some score)
    (hScoreId : score.id = .async e (.tcNotify rank))
    (hCommit : ScoreCommit l X e cta stage spec rank) {i g phase : Nat} {w : Record Ref}
    (hWait : (X.objects (probabilityObject l cta stage 1))[i]? = some w)
    (hWaitId : w.id = .thread (e.1,g)) (hWaitOk : w.reply.waited = some true)
    (hWaitPhase : observedAt (X.objects (probabilityObject l cta stage 1)) i = some phase)
    (hWaitResumes : Resumes kernel X (e.1,g) e) {creditIndex : Nat}
    (hCredit : UnitArrivalIn (X.objects (probabilityObject l cta stage 1)) phase creditIndex) :
    let log := X.objects (scoreReadyObject l cta stage)
    let credit := ((X.objects (probabilityObject l cta stage 1))[creditIndex]?).getD w
    ∃ k < atScore, ∃ guard st, log[k]? = some guard ∧ guard.reply.waited = some true ∧
      stateBefore log k = some st ∧ (tailLabel l X cta stage credit.id).2 + 1 ≤ st.phase := by
  let loc := scoreReadyObject l cta stage
  let prob := probabilityObject l cta stage 1
  let log := X.objects loc
  obtain ⟨row, bytes, hr, ha, hClean, hPhase⟩ := hCredit
  have hUpdate : CounterUpdate row.action := by rw [ha]; trivial
  obtain ⟨a, hA, hIssue, _, _⟩ := probabilityUpdate hp hX stage 1 (List.mem_of_getElem? hr) hUpdate
  have hw : warpIndex l a.1 < 8 := by
    rcases (probabilityCreditRole hp hX stage 1 hIssue).2 with h | h
    · exact h.1
    · have hn : (1 : Fin 2).val ≠ 0 := by decide
      exact (hn h.1).elim
  have hProbNI := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) prob
  have hUse := hX.observed_of_phase hProbNI hr hClean hUpdate hWait hWaitOk hPhase hWaitPhase
  rw [hA, hWaitId] at hUse
  obtain ⟨k, j, q, guard, hGuard, hGuardId, hGuardOk, hGuardResume, hSeen, hLower⟩ :=
    scoreObservedBeforeSoftmaxCredit hp hX stage 1 hw hIssue
  obtain ⟨state, hState, hCurrent⟩ :=
    (X.objects_checked hX loc).observed_phase hGuard hGuardOk hSeen
  have hPresent := object_record_present hX.tma (List.mem_of_getElem? hScore)
  rw [hScoreId] at hPresent
  obtain ⟨_, hGet⟩ := hCommit.1
  have hDo : DepStep l kernel X (.thread e,false) (.async e (.tcNotify rank),false) :=
    DepStep.issue ⟨_, hGet⟩ hPresent (by intro x h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
  have hChain := (((Relation.TransGen.single (DepStep.of_resumes l hGuardResume)).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hUse))).tail
    (DepStep.of_resumes l hWaitResumes)).tail hDo
  rw [← hGuardId, ← hScoreId] at hChain
  have hNot := MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hChain
  have hj : j < atScore := by
    rcases Nat.lt_trichotomy j atScore with h | rfl | h
    · exact h
    · obtain rfl := Option.some.inj (hGuard.symm.trans hScore)
      rw [hScoreId] at hGuardId
      cases hGuardId
    · exact (hNot ⟨atScore,j,score,guard,hScore,rfl,hGuard,rfl,h⟩).elim
  refine ⟨j,hj,guard,state,hGuard,hGuardOk,hState,?_⟩
  change (tailLabel l X cta stage (((X.objects prob)[creditIndex]?).getD w).id).2 + 1 ≤
    state.phase
  rw [hr, Option.getD_some, hA]
  change probabilityOrdinal l X cta stage 1 a + 1 ≤ state.phase
  omega

/-- A recurring score update has already observed at least its preceding score generation.
The four tail credits per earlier probability poll form distinct (warp, local ordinal) pairs. -/
theorem recurringScoreUpdateGuard {cta atScore : Nat} (stage : Fin 2) {r : Record Ref} {e : EvId}
    {rank : Fin 16} {spec : TcCommit.Spec}
    (hScore : (X.objects (scoreReadyObject l cta stage))[atScore]? = some r)
    (hScoreId : r.id = .async e (.tcNotify rank)) (hCommit : ScoreCommit l X e cta stage spec rank)
    (hPositive : 0 < scoreCommitOrdinal l X cta stage e) :
    let log := X.objects (scoreReadyObject l cta stage)
    ∃ k < atScore, ∃ guard st, log[k]? = some guard ∧ guard.reply.waited = some true ∧
      stateBefore log k = some st ∧ scoreCommitOrdinal l X cta stage e ≤ st.phase := by
  classical
  let score := scoreReadyObject l cta stage
  let prob := probabilityObject l cta stage 1
  let log := X.objects prob
  let n := scoreCommitOrdinal l X cta stage e
  have hPick (a : Fin n) : ∃ (k i phase : Nat) (w : Record Ref), log[i]? = some w ∧
      w.id = .thread (e.1,k) ∧ w.reply.waited = some true ∧ Resumes kernel X (e.1,k) e ∧
      observedAt log i = some phase ∧
      k = MbarRing.Poll.nth X prob e.1 a ∧ a.val < PTX.Flow.okPolls prob (X.tr e.1) := by
    obtain ⟨k,i,phase,w,hI,hId,hOk,hRes,hPhase,_,hK,hNth⟩ :=
      probabilityObservedBeforeScoreOrdinal hp hX hCommit 1 a.isLt
    exact ⟨k,i,phase,w,hI,hId,hOk,hRes,hPhase,hK,hNth⟩
  choose event row phase poll hGet hId hWait hRes hPhase hEvent hBound using hPick
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) prob
  have hClean : ∀ r ∈ log, (∃ p ok, r.action = .pollParity p ok) → r.fault = none :=
    fun _ hr hP => actualInitOrPollClean hp hX hr (.inr hP)
  have hUnit (r : Record Ref) (hr : r ∈ log) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,ha⟩ := probabilityUpdate hp hX stage 1 hr hu
    exact ha
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr ha
    have h := hUnit r hr (by rw [ha]; trivial)
    rw [ha] at h
    cases h
  have hDistinct {a b : Fin n} (hab : a < b) : phase a < phase b := by
    have hMono := MbarRing.Poll.observed_lt hX (m := prob) (g := e.1) (δ := 0)
      (by decide) hClean hNo (probabilitySelectedAlternates hp hX stage 1)
      (by omega : 0 ≤ a.val) hab (hBound b)
    rw [← hEvent a, ← hEvent b, ← hId a, ← hId b,
      MbarRing.Poll.observedOf_eq hX (hGet a) (hPhase a),
      MbarRing.Poll.observedOf_eq hX (hGet b) (hPhase b)] at hMono
    exact hMono
  let members (a : Fin n) := (Finset.range log.length).filter (UnitArrivalIn log (phase a))
  have hCard (a : Fin n) : (members a).card = 4 := by
    have hInit := probabilityInitialized hp hX stage 1 (List.mem_of_getElem? (hGet a))
    obtain ⟨st, hSt, hOrd⟩ :=
      (X.objects_checked hX prob).observed_phase (hGet a) (hWait a) (hPhase a)
    exact (X.objects_checked hX prob).card_unit_arrivals_phase hNo
      (fun _ r c tx hr _ ha =>
        (Action.arrive.inj (ha.symm.trans (hUnit r (List.mem_of_getElem? hr)
          (by rw [ha]; trivial)))).1)
      (fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hNo h) hIncr
      (List.getElem?_eq_some_iff.mp (hGet a)).1.le hSt (by omega)
  let credits := (Finset.univ : Finset (Fin n)).biUnion members
  have hCredits : credits.card = n * 4 := by
    rw [Finset.card_biUnion (by
      intro a _ b _ hab
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨_,p,_,hp,_,_,hP⟩ := Finset.mem_filter.mp hx
      obtain ⟨_,q,_,hq,_,_,hQ⟩ := Finset.mem_filter.mp hy
      rw [hP] at hQ
      have hEq := Option.some.inj hQ
      rcases lt_or_gt_of_ne hab with h | h
      · exact (Nat.ne_of_lt (hDistinct h)) hEq
      · exact (Nat.ne_of_gt (hDistinct h)) hEq)]
    simp [hCard]
  let label (index : Nat) := tailLabel l X cta stage (log[index]?.getD r).id
  have hLabelInj : Set.InjOn label (credits : Set Nat) := by
    intro a ha b hb hEq
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp ha)
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hb)
    obtain ⟨_,ra,txA,hA,haAct,_,_⟩ := Finset.mem_filter.mp hi
    obtain ⟨_,rb,txB,hB,hbAct,_,_⟩ := Finset.mem_filter.mp hj
    obtain ⟨ea,hEA,hSourceA,_,_⟩ :=
      probabilityUpdate hp hX stage 1 (List.mem_of_getElem? hA) (by rw [haAct]; trivial)
    obtain ⟨eb,hEB,hSourceB,_,_⟩ :=
      probabilityUpdate hp hX stage 1 (List.mem_of_getElem? hB) (by rw [hbAct]; trivial)
    change tailLabel l X cta stage ((log[a]?).getD r).id =
      tailLabel l X cta stage ((log[b]?).getD r).id at hEq
    rw [hA,hB,Option.getD_some,Option.getD_some,hEA,hEB] at hEq
    have hIndex := tailLabelInj hp hX hSourceA hSourceB hEq
    exact ObjectInit.checked_record_index_eq (X.objects_checked hX prob) hA hB
      (hEA.trans (congrArg Ref.thread hIndex) |>.trans hEB.symm)
  by_contra hGate
  have hSmall (a : Nat) (ha : a ∈ credits) :
      label a ∈ (Finset.univ : Finset (Fin 4)) ×ˢ Finset.range (n-1) := by
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨_,hUnit⟩ := Finset.mem_filter.mp hi
    obtain ⟨j,hj,guard,st,hG,hW,hS,hLower⟩ :=
      scoreGuardForConsumedTail hp hX stage hScore hScoreId hCommit (hGet i) (hId i)
        (hWait i) (hPhase i) (hRes i) hUnit
    have hn : st.phase < n := by
      apply Nat.lt_of_not_ge
      exact fun hn => hGate ⟨j,hj,guard,st,hG,hW,hS,hn⟩
    obtain ⟨credit,_,hc,_,_,_⟩ := hUnit
    change (tailLabel l X cta stage (log[a]?.getD (poll i)).id).2 + 1 ≤ st.phase at hLower
    rw [hc, Option.getD_some] at hLower
    have hLab : (label a).2 = (tailLabel l X cta stage credit.id).2 := by
      simp [label, hc]
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr (by omega)⟩
  have hFit := Finset.card_le_card_of_injOn label hSmall hLabelInj
  rw [hCredits, Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_range] at hFit
  change 0 < n at hPositive
  omega

omit hp hX in
private def notifyLabel (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2) :
    Ref → Fin 1 × Nat
  | .async e (.tcNotify _) => (0,scoreCommitOrdinal l X cta stage e)
  | _ => (0,0)

private theorem scoreUpdateAligned {cta i c tx : Nat} (stage : Fin 2) {r : Record Ref}
    (hi : (X.objects (scoreReadyObject l cta stage))[i]? = some r) (ha : r.action = .arrive c tx) :
    r.fault = none ∧ phaseAt (X.objects (scoreReadyObject l cta stage)) i =
      some (notifyLabel l X cta stage r.id).2 := by
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  let labels := notifyLabel l X cta stage
  have hInit := scoreReadyInitialized hp hX stage (List.mem_of_getElem? hi)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have unit {d : Record Ref} (hd : d ∈ log) (h : CounterUpdate d.action) :
      d.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,_,_,_,ha⟩ := scoreReadyUpdate hp hX stage hd h
    exact ha
  have source {i c tx : Nat} {d : Record Ref} (hd : log[i]? = some d)
      (ha : d.action = .arrive c tx) :
      ∃ issue spec rank, d.id = .async issue (.tcNotify rank) ∧
        ScoreCommit l X issue cta stage spec rank ∧
        (labels d.id).2 = scoreCommitOrdinal l X cta stage issue := by
    obtain ⟨e,s,rank,hId,hCommit,hTarget,_,_⟩ :=
      scoreReadyUpdate hp hX stage (List.mem_of_getElem? hd) (by rw [ha]; trivial)
    exact ⟨e,s,rank,hId,⟨hCommit,hTarget⟩,by rw [hId]; rfl⟩
  have hInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro d hd h
    have ha := unit hd (by rw [h]; trivial)
    rw [h] at ha
    cases ha
  have hCh := X.objects_checked hX loc
  apply hCh.gated_arrive hNo (Finset.univ : Finset (Fin 1)) labels _ _ _ _ _ hInc i r c tx hi ha
  · intro k s hk hs
    have hExpected := PairTmaRing.expected_of_init hX hInit hNo hs
    have hZero := MbarRing.tx_zero_of hX hNo
      (fun d hd c tx h => (Action.arrive.inj (h.symm.trans (unit hd (by rw [h]; trivial)))).2)
      (fun d hd n h => by
        have ha := unit hd (by rw [h]; trivial)
        rw [h] at ha
        cases ha) hk hs
    exact ⟨by simpa using hExpected,hZero⟩
  · intro index d c tx hd hArrive
    obtain ⟨_,st,hState,_⟩ := PairTmaRing.state_of_init hX hInit hNo hd
      (by intro n; rw [hArrive]; simp)
    exact ⟨st,hState⟩
  · intro index d c tx hd hArrive
    have h := Action.arrive.inj
      (hArrive.symm.trans (unit (List.mem_of_getElem? hd) (by rw [hArrive]; trivial)))
    exact ⟨h.1,h.2,Finset.mem_univ _⟩
  · intro j k d f cd td cf tf hd hf had haf heq
    obtain ⟨ed,sd,rd,hId,hD,hOrd⟩ := source hd had
    obtain ⟨ef,sf,rf,hIF,hF,hOR⟩ := source hf haf
    have hSame : scoreCommitOrdinal l X cta stage ed = scoreCommitOrdinal l X cta stage ef :=
      hOrd.symm.trans ((congrArg Prod.snd heq).trans hOR)
    obtain ⟨rfl,rfl⟩ := scoreCommitOrdinalInjective hp hX hD hF hSame
    exact ObjectInit.checked_record_index_eq hCh hd hf (hId.trans hIF.symm)
  · intro j d c tx hd hArrive hPos
    obtain ⟨e,s,rank,hId,hCommit,hOrd⟩ := source hd hArrive
    rw [hOrd] at hPos ⊢
    obtain ⟨kw,hk,w,sw,hw,hDone,hState,hPhase⟩ :=
      recurringScoreUpdateGuard hp hX stage hd hId hCommit hPos
    exact ⟨kw,w,sw,hk,hw,hDone,hState,hPhase⟩

/-- Every actual score notification is clean and carries its lane's score generation. -/
theorem scoreNotificationPhaseExact {cta i : Nat} (stage : Fin 2) {e : EvId} {rank : Fin 16}
    {r : Record Ref} (hi : (X.objects (scoreReadyObject l cta stage))[i]? = some r)
    (ha : CounterUpdate r.action) (hId : r.id = .async e (.tcNotify rank)) :
    r.fault = none ∧ phaseAt (X.objects (scoreReadyObject l cta stage)) i =
      some (scoreCommitOrdinal l X cta stage e) := by
  obtain ⟨_,_,_,_,_,_,_,hAct⟩ := scoreReadyUpdate hp hX stage (List.mem_of_getElem? hi) ha
  have h := scoreUpdateAligned hp hX stage hi hAct
  rw [hId] at h
  exact h

/-- Both score-ready barrier histories are fault-free in every consistent prefix. -/
theorem scoreReadyHistoryNoFault {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (scoreReadyObject l cta stage)) : r.fault = none := by
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX)
    (scoreReadyObject l cta stage)
  cases ha : r.action with
  | init n => exact actualInitOrPollClean hp hX hr (.inl ⟨n,ha⟩)
  | pollParity q ok => exact actualInitOrPollClean hp hX hr (.inr ⟨q,ok,ha⟩)
  | inval => exact (hNo _ hr ha).elim
  | arrive | completeTx | increment =>
    have hUpdate : CounterUpdate r.action := by rw [ha]; trivial
    obtain ⟨_,_,_,hId,_,_,_,_⟩ := scoreReadyUpdate hp hX stage hr hUpdate
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hr
    exact (scoreNotificationPhaseExact hp hX stage hi hUpdate hId).1

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
