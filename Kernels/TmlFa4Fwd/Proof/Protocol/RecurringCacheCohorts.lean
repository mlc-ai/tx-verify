-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReadyFaults
import Lemmas.Protocol.GatedFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier Prologue
open Thread.Loader (producer readyObject)

/-- Each lane of a cache-ready cohort records a delivered publication at the
same producer generation. -/
def DeliveredCohort (l : Launch) (X : Execution) (owner : Nat) (slot : Fin 3)
    (gen : Nat) : Prop :=
  ∀ lane : Fin 64, ∃ issue, issue.1 = producer l (owner/l.block) lane ∧
    X.AsyncArrive issue (readyObject l owner slot) true ∧
    X.async.arrived issue = true ∧ generation l X issue slot = gen

/-- A recorded recurring publication implies that the previous packets were
delivered. Its empty guard requires an actual MMA release of the preceding
generation, whose successful ready acquire covers those packets. -/
theorem earlierCohortsOfPublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner : Nat} {slot : Fin 3} {pub : EvId}
    (hPub : X.AsyncArrive pub (readyObject l owner slot) true)
    {gen : Nat} (hGen : generation l X pub slot = gen+1) :
    ∀ prior ≤ gen, DeliveredCohort l X owner slot prior := by
  obtain ⟨guard,g,k,release,hOrdinal,_⟩ :=
    actualReleaseForNextPublicationExact hp hX hPub hGen
  have hReady := release.matched.ready
  rw [release.matchedSlot] at hReady
  obtain ⟨ready⟩ := actualCompletedForIssuer hp hX release.issue hReady
  unfold Thread.Mma.EmptyReleaseAt.ordinal at hOrdinal
  rw [release.matchedSlot] at hOrdinal
  rw [hOrdinal] at ready
  have hCta : owner/l.block = g/l.block := by
    rw [publicationCta hp hX hPub,← guard.issuer,release.issuerCta hp hX]
  intro prior hPrior lane
  let obj := (ready.acquire.record hp hX).1
  have hCap (q : Nat) (_ : q ≤ gen) :=
    (phaseAlignment hp hX (actualEmptyGuardLower hp hX g slot) q).1
  obtain ⟨i,entry,issue,_,hAt,_,hAction,_,hId,hLane,hArrive,hGeneration⟩ :=
    Thread.Loader.readyCoverageByOrdinal hp hX obj ready.record ready.success ready.observed
      hCap prior hPrior lane
  obtain ⟨_,_,actual,hActual,_,hDone⟩ := obj.arrive_source hAt hAction
  have hSame := (Ref.async.inj (hActual.symm.trans hId)).1
  subst actual
  refine ⟨issue,by simpa only [hCta] using hLane,?_,hDone,hGeneration⟩
  unfold readyObject at hArrive ⊢
  rwa [hCta]

/-- At a delivered cohort its earlier producer generations are delivered too. -/
theorem DeliveredCohort.prefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner gen : Nat} {slot : Fin 3} (h : DeliveredCohort l X owner slot gen)
    {prior : Nat} (hPrior : prior ≤ gen) : DeliveredCohort l X owner slot prior := by
  rcases Nat.eq_or_lt_of_le hPrior with rfl | hLess
  · exact h
  · obtain ⟨issue,_,hPub,_,hGen⟩ := h 0
    exact earlierCohortsOfPublication hp hX hPub (show generation l X issue slot = gen-1+1 by
      omega) prior (by omega)

/-- All delivered records through a cohort's generation complete that ready
phase. Distinct producer lanes and generations give distinct unit records. -/
theorem readyPhaseOfDeliveredCohort {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner gen : Nat} {slot : Fin 3} (hDelivered : DeliveredCohort l X owner slot gen) :
    let log := X.objects (readyObject l owner slot)
    ∃ st, stateBefore log log.length = some st ∧ gen < st.phase := by
  classical
  let loc := readyObject l owner slot
  let log := X.objects loc
  let index := Fin (gen+1) × Fin 64
  have hEvents (q : index) : ∃ issue, issue.1 = producer l (owner/l.block) q.2 ∧
      X.AsyncArrive issue loc true ∧ X.async.arrived issue = true ∧
      generation l X issue slot = q.1.val :=
    hDelivered.prefix hp hX (Nat.le_of_lt_succ q.1.isLt) q.2
  choose issue hLane hArrive hDone hGen using hEvents
  let id (q : index) : Ref := .async (issue q) .arriveOn
  have hRecord (q : index) : ∃ r ∈ log, r.id = id q ∧ r.action = .arrive 1 0 := by
    have ha := objectAction_noinc_arriveOn (hArrive q) (hDone q)
    obtain ⟨r,hr,hId⟩ := (hX.tma.2.2.1 loc).2.2 _ _ ha
    have hAction := ((hX.tma.2.2.1 loc).2.1 r hr).1
    rw [hId,ha] at hAction
    exact ⟨r,hr,hId,(Option.some.inj hAction).symm⟩
  obtain ⟨r0,hr0,-,-⟩ := hRecord (⟨0,by omega⟩,0)
  have hObj := Loader.actualReadyHistoryObject hp hX slot hr0
  have hChecked := X.objects_checked hX loc
  obtain ⟨init,hInit,hAction,hClean,_⟩ := hObj.init r0 hr0
  obtain ⟨st,hState,hExpected⟩ := ObjectInit.checked_expected_after_init hChecked hObj.noInval
    hInit hAction hClean (List.getElem?_eq_some_iff.mp hInit).1 (Nat.le_refl _)
  have hUnits : (gen+1)*64 ≤ unitsBefore log log.length := by
    have hInj : Function.Injective id := by
      intro a b hEq
      have hIssue := (Ref.async.inj hEq).1
      apply Prod.ext
      · apply Fin.ext
        rw [← hGen a,← hGen b,hIssue]
      · have h := congrArg Prod.fst hIssue
        rw [hLane,hLane] at h
        apply Fin.ext
        unfold producer Loader.readyProducer at h
        omega
    have hCard : (Finset.univ.image id).card = (gen+1)*64 := by
      rw [Finset.card_image_of_injective _ hInj,Finset.card_univ,Fintype.card_prod,
        Fintype.card_fin,Fintype.card_fin]
    have hSubset : Finset.univ.image id ⊆ ((log.filter countedArrive).map Record.id).toFinset := by
      intro d hd
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨r,hr,hId,hAct⟩ := hRecord j
      have hFault := (readyHistoryClean hp hX owner slot hr).1
      exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨r,List.mem_filter.mpr ⟨hr,countedArrive_iff.mpr ⟨hFault,1,0,hAct⟩⟩,hId⟩)
    have hCount := (Finset.card_le_card hSubset).trans (List.toFinset_card_le _)
    rw [hCard,List.length_map] at hCount
    unfold unitsBefore
    rw [List.take_length,arrivalUnits_eq_length
      (fun r hr c tx _ ha => by
        obtain ⟨k,hk⟩ := List.getElem?_of_mem hr
        exact (hObj.arrive_source hk ha).1)]
    exact hCount
  have hTx : st.tx = 0 := MbarRing.tx_zero_of hX hObj.noInval
    (fun r hr c tx ha => by
      obtain ⟨k,hk⟩ := List.getElem?_of_mem hr
      exact (hObj.arrive_source hk ha).2.1)
    (fun r hr n ha => by
      cases hObj.source r hr with
      | init h | poll h | arriveOn _ _ _ h => rw [ha] at h; cases h)
    (Nat.le_refl _) hState
  have hPending := stateBefore_pending_pos hChecked hState hTx
  have hBalance := ((hChecked.accounted hObj.noInval (Nat.le_refl _)).2 st hState).2
  have hZero : incrementsBefore log log.length = 0 := hObj.noIncrement
  rw [hExpected,hZero] at hBalance
  change unitsBefore log log.length+st.pending = 64*(st.phase+1)+0 at hBalance
  exact ⟨st,hState,by omega⟩

/-- If the ready history advances beyond one generation, it contains an
actual later producer publication. -/
theorem laterPublicationOfReadyPhase {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g gen : Nat} (slot : Fin 3) {s : State}
    (hs : let log := X.objects (readyObject l g slot); stateBefore log log.length = some s)
    (hPhase : gen+1 < s.phase) :
    ∃ issue, X.AsyncArrive issue (readyObject l g slot) true ∧
      gen < generation l X issue slot := by
  let loc := readyObject l g slot
  let log := X.objects loc
  change stateBefore log log.length = some s at hs
  have hNonempty : log ≠ [] := by
    intro h
    rw [h] at hs
    cases hs
  obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil log hNonempty
  have hObj := Loader.actualReadyHistoryObject hp hX slot hr
  have hChecked := X.objects_checked hX loc
  obtain ⟨i,hInit,hAction,hClean,_⟩ := hObj.init r hr
  have hIn := (List.getElem?_eq_some_iff.mp hInit).1
  have hE := ObjectInit.checked_expected_after_init hChecked hObj.noInval
    hInit hAction hClean hIn (Nat.le_refl _)
  obtain ⟨current,hCurrent,hExpected⟩ := hE
  change stateBefore log log.length = some current at hCurrent
  rw [hs] at hCurrent
  obtain rfl := Option.some.inj hCurrent
  have hBalance := ((hChecked.accounted hObj.noInval (Nat.le_refl _)).2 s hs).2
  have hNoIncrement : incrementsBefore log log.length = 0 := hObj.noIncrement
  rw [hExpected,hNoIncrement] at hBalance
  change unitsBefore log log.length + s.pending = 64 * (s.phase+1)+0 at hBalance
  have hPending := ((hChecked.accounted hObj.noInval (Nat.le_refl _)).2 s hs).1
  rw [hExpected,hNoIncrement] at hPending
  by_contra! hNo
  have hUnits : unitsBefore log log.length ≤ 64 * (gen+1) := by
    apply Loader.readyUnitsBefore hp hX slot hObj
    dsimp only
    intro k hk r' issue hAt _ ha hId
    obtain ⟨_,_,actual,hActual,hPub,_⟩ := hObj.arrive_source hAt ha
    have hIdEq := (Ref.async.inj (hActual.symm.trans hId)).1
    subst actual
    change Loader.readyOrdinal X (readyObject l g slot) issue ≤ gen
    rw [← Thread.Loader.publicationOrdinalAtObject hp hX hPub]
    exact hNo issue hPub
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
