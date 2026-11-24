-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.JointProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityBeforeScore
import Kernels.TmlFa4Fwd.Proof.Thread.InitialProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarOneShot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.MBarrier PTX.AsyncCopy PTX.Flow Thread.Scores
open Prologue (warpIndex)

/-- A lane that has supplied enough physical unit arrivals has an actual
probability credit at every covered ordinal. -/
theorem probabilityCreditOfExtent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g cta gen : Nat}
    (stage packet : Fin 2)
    (hPos : gen+1 ≤ (X.tr g).countP (arrivesOn (probabilityObject l cta stage packet))) :
    ∃ i, ProbabilityCredit l X (g,i) cta stage packet ∧
      probabilityOrdinal l X cta stage packet (g,i) = gen := by
  let loc := probabilityObject l cta stage packet
  obtain ⟨i,e,he,hMark,hPrior⟩ := MbarRing.Slot.exists_nth_countP (arrivesOn loc) hPos
  obtain ⟨source,kind⟩ := e
  cases kind <;> try cases hMark
  case arrive other tx n rel scope =>
    have hLoc : other = loc := of_decide_eq_true hMark
    subst other
    have hAction : objectAction X X.async loc (.thread (g,i)) = some (.arrive n tx) := by
      have hGet : X.get (g,i) = some ⟨source,.arrive loc tx n rel scope⟩ := he
      simp [objectAction,hGet]
    obtain ⟨_,r,hr,hId,hAct⟩ := MbarOneShot.Hist.record_of_action hX hAction
    have hUpdate : CounterUpdate r.action := by rw [hAct]; trivial
    obtain ⟨actual,hActual,hCredit,_,_⟩ :=
      probabilityUpdate hp hX stage packet (List.mem_of_getElem? hr) hUpdate
    obtain rfl := Ref.thread.inj (hActual.symm.trans hId)
    exact ⟨i,hCredit,hPrior⟩

/-- An actual cohort of the main or tail P object is the full number of
distinct credits of one local generation. The joint main packet includes its
correction credits. -/
def ProbabilityCohort (l : Launch) (X : Execution) (cta : Nat)
    (stage packet : Fin 2) (gen : Nat) : Prop :=
  ∃ credits : Fin (probabilityCredits packet) → EvId, Function.Injective credits ∧
    ∀ a, ProbabilityCredit l X (credits a) cta stage packet ∧
      probabilityOrdinal l X cta stage packet (credits a) = gen

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hGuard : CorrectionJointGuards l X)
include hp hX hGuard

private theorem probabilityCreditAligned {cta i : Nat} (stage packet : Fin 2) {e : EvId}
    {r : Record Ref} (hr : (X.objects (probabilityObject l cta stage packet))[i]? = some r)
    (ha : CounterUpdate r.action) (hId : r.id = .thread e) :
    r.fault = none ∧ phaseAt (X.objects (probabilityObject l cta stage packet)) i =
      some (probabilityOrdinal l X cta stage packet e) := by
  fin_cases packet
  · exact jointProbabilityCreditPhaseExact hp hX hGuard stage hr ha hId
  · exact tailProbabilityCreditPhaseExact hp hX stage hr ha hId

/-- The current cohort completes its generation. Actual position and exact
phase of its earliest credit account for all earlier completed generations. -/
theorem probabilityAdvancedOfCohort {cta gen : Nat} (stage packet : Fin 2)
    (hCohort : ProbabilityCohort l X cta stage packet gen) :
    let log := X.objects (probabilityObject l cta stage packet)
    ∃ s, stateBefore log log.length = some s ∧ gen < s.phase := by
  classical
  obtain ⟨credits,hDistinct,hCredit⟩ := hCohort
  let loc := probabilityObject l cta stage packet
  let log := X.objects loc
  let N := probabilityCredits packet
  have hPos : 0 < N := by dsimp [N]; fin_cases packet <;> decide
  have hRecords (a : Fin N) : ∃ i r, log[i]? = some r ∧ r.id = .thread (credits a) ∧
      r.action = .arrive 1 0 ∧ r.fault = none ∧ phaseAt log i = some gen := by
    obtain ⟨k,r,hAt,hId,hUpdate⟩ := probabilityCreditRecord hX (hCredit a).1
    have hShape := probabilityUpdate hp hX stage packet (List.mem_of_getElem? hAt) hUpdate
    have hClean := probabilityCreditAligned hp hX hGuard stage packet hAt hUpdate hId
    rw [(hCredit a).2] at hClean
    exact ⟨k,r,hAt,hId,hShape.choose_spec.2.2.2,hClean⟩
  choose pos rec hAt hId hAct hClean hPhase using hRecords
  let indices := (Finset.univ : Finset (Fin N)).image pos
  have hNonempty : indices.Nonempty := ⟨pos ⟨0,hPos⟩,Finset.mem_image.mpr ⟨_,by simp,rfl⟩⟩
  let first := indices.min' hNonempty
  obtain ⟨a,_,hFirst⟩ := Finset.mem_image.mp (indices.min'_mem hNonempty)
  change pos a = first at hFirst
  have hEarliest (a : Fin N) : first ≤ pos a :=
    indices.min'_le _ (Finset.mem_image.mpr ⟨a,by simp,rfl⟩)
  obtain ⟨start,hState,hGen⟩ := Option.map_eq_some_iff.mp (hPhase a)
  rw [hFirst] at hState
  have ha := List.mem_of_getElem? (hAt a)
  have hInit := probabilityInitialized hp hX stage packet ha
  have hChecked := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hShape {r : Record Ref} (hr : r ∈ log) (hUpdate : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,h⟩ := probabilityUpdate hp hX stage packet hr hUpdate
    exact h
  have hNotInc (r : Record Ref) (hr : r ∈ log) (h : r.action = .increment) : False := by
    have h' := hShape hr (by rw [h]; trivial)
    rw [h] at h'
    cases h'
  have hNoinc : incrementsBefore log log.length = 0 :=
    incrementsBefore_length_of log hNotInc
  obtain ⟨init,hInitial,hInitAct,hInitClean,_⟩ := hInit (rec a) ha
  obtain ⟨final,hFinal,hFinalExpected⟩ := ObjectInit.checked_expected_after_init hChecked hNo
    hInitial hInitAct hInitClean (List.getElem?_eq_some_iff.mp hInitial).1 le_rfl
  have hFirstLe : first ≤ log.length := hFirst ▸ (List.getElem?_eq_some_iff.mp (hAt a)).1.le
  have hUnitsStart : N*gen ≤ unitsBefore log first := by
    obtain ⟨hPending,hBal⟩ := (hChecked.accounted hNo hFirstLe).2 start hState
    change unitsBefore log first + start.pending = _ at hBal
    have hExpected := PairTmaRing.expected_of_init hX hInit hNo hState
    change start.expected = N at hExpected
    rw [hExpected, hGen, incrementsBefore_eq_zero log hNoinc first,
      Nat.mul_succ, Nat.add_zero] at hBal
    rw [hExpected, incrementsBefore_eq_zero log hNoinc first, Nat.add_zero] at hPending
    omega
  let rest := log.drop first
  have hUnitsRest : N ≤ arrivalUnits rest := by
    rw [arrivalUnits_eq_length]
    · let ids := ((rest.filter countedArrive).map Record.id).toFinset
      have hMem (w : Fin N) : rec w ∈ rest := by
        apply List.mem_of_getElem? (i := pos w-first)
        rw [List.getElem?_drop, Nat.add_sub_of_le (hEarliest w)]
        exact hAt w
      have hSub : (Finset.univ.image fun w => Ref.thread (credits w)) ⊆ ids := by
        intro x hx
        obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hx
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rec w,List.mem_filter.mpr
          ⟨hMem w,countedArrive_iff.mpr ⟨hClean w,1,0,hAct w⟩⟩,hId w⟩)
      have hLe := (Finset.card_le_card hSub).trans (List.toFinset_card_le _)
      rw [Finset.card_image_of_injective _ (fun _ _ h => hDistinct (Ref.thread.inj h)),
        Finset.card_univ,Fintype.card_fin,List.length_map] at hLe
      exact hLe
    · intro r hr count tx _ hArrive
      exact (Action.arrive.inj (hArrive.symm.trans
        (hShape (List.mem_of_mem_drop hr) (by rw [hArrive]; trivial)))).1
  have hTotal : N*gen+N ≤ arrivalUnits log := by
    have hApp := arrivalUnits_append (log.take first) rest
    rw [List.take_append_drop] at hApp
    change N*gen ≤ arrivalUnits (log.take first) at hUnitsStart
    omega
  have hNoTx : final.tx = 0 := MbarRing.tx_zero_of hX hNo
    (fun _ hr _ _ ha => (Action.arrive.inj (ha.symm.trans
      (hShape hr (by rw [ha]; trivial)))).2)
    (fun _ hr _ h => by
      have hUnit := hShape hr (by rw [h]; trivial)
      rw [h] at hUnit
      cases hUnit) le_rfl hFinal
  have hPending := stateBefore_pending_pos hChecked hFinal hNoTx
  have hBalance := ((hChecked.accounted hNo le_rfl).2 final hFinal).2
  change final.expected = N at hFinalExpected
  rw [hFinalExpected,hNoinc,Nat.add_zero] at hBalance
  change arrivalUnits (log.take log.length) + final.pending = _ at hBalance
  rw [List.take_length] at hBalance
  refine ⟨final,hFinal,?_⟩
  by_contra! hCap
  have hFinalLe := Nat.mul_le_mul_left N (show final.phase+1 ≤ gen+1 by omega)
  rw [Nat.mul_succ N gen] at hFinalLe
  omega

/-- A completed later P generation requires a real softmax credit of that
generation, for both the joint main packet and the elected tail packet. -/
theorem softmaxCreditOfCompletedProbabilityPhase {cta gen : Nat} (stage packet : Fin 2) {s : State}
    (hFinal : let log := X.objects (probabilityObject l cta stage packet)
      stateBefore log log.length = some s) (hPhase : gen < s.phase) :
    ∃ i, ProbabilityCredit l X i cta stage packet ∧ warpIndex l i.1 < 8 ∧
      probabilityOrdinal l X cta stage packet i = gen := by
  classical
  let log := X.objects (probabilityObject l cta stage packet)
  have hNonempty : log ≠ [] := by
    intro h
    change stateBefore log log.length = some s at hFinal
    rw [h] at hFinal
    cases hFinal
  obtain ⟨sample,hInLog⟩ := List.exists_mem_of_ne_nil log hNonempty
  have hSample : sample ∈ X.objects (probabilityObject l cta stage packet) := hInLog
  clear hNonempty hInLog log
  fin_cases packet
  · let lane := cta*l.block+128*stage.val
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    have hBound : 128*stage.val < l.block := by rw [hp.block]; have := stage.isLt; omega
    obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hBlock hBound
    have hRole : warpIndex l lane < 8 ∧ warpIndex l lane/4 = stage.val := by
      unfold warpIndex
      rw [show lane%l.block = 128*stage.val from hLocal]
      have := stage.isLt
      omega
    obtain ⟨_,_,credit,_,_,_,_,_,hCredit,hLane,hOrdinal⟩ :=
      jointPhaseProducerRecord hp hX hGuard stage (g := lane) (phase := gen)
        hOwner (.inl hRole) hSample le_rfl hFinal hPhase
    exact ⟨credit,hCredit,hLane.symm ▸ hRole.1,hOrdinal⟩
  · let loc := probabilityObject l cta stage 1
    let log := X.objects loc
    have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
    have hInit := probabilityInitialized hp hX stage 1 hSample
    have hUnit {r : Record Ref} (hr : r ∈ log) (ha : CounterUpdate r.action) :
        r.action = .arrive 1 0 := by
      obtain ⟨_,_,_,_,hAction⟩ := probabilityUpdate hp hX stage 1 hr ha
      exact hAction
    have hIncr : incrementsBefore log log.length = 0 := by
      apply incrementsBefore_length_of
      intro r hr hi
      have h := hUnit hr (by rw [hi]; trivial)
      rw [hi] at h
      cases h
    have hCard := (X.objects_checked hX loc).card_unit_arrivals_phase hNo (n := 4) (q := gen)
      (fun _ _ _ _ hr _ ha =>
        (Action.arrive.inj (ha.symm.trans (hUnit (List.mem_of_getElem? hr)
          (by rw [ha]; trivial)))).1)
      (fun _ _ _ hs => by
        simpa [probabilityCredits] using PairTmaRing.expected_of_init hX hInit hNo hs)
      hIncr le_rfl hFinal hPhase
    have hSome : ((Finset.range log.length).filter (UnitArrivalIn log gen)).Nonempty :=
      Finset.card_pos.mp (by rw [hCard]; decide)
    obtain ⟨_,hk⟩ := hSome
    obtain ⟨_,r,_,hr,hArrive,_,hAt⟩ := Finset.mem_filter.mp hk
    have hUpdate : CounterUpdate r.action := by rw [hArrive]; trivial
    obtain ⟨credit,hId,hCredit,_,_⟩ :=
      probabilityUpdate hp hX stage 1 (List.mem_of_getElem? hr) hUpdate
    have hWarp : warpIndex l credit.1 < 8 := by
      rcases (probabilityCreditRole hp hX stage 1 hCredit).2 with h | h
      · exact h.1
      · exact (by decide : (1 : Fin 2).val ≠ 0) h.1 |>.elim
    have hExact := (tailProbabilityCreditPhaseExact hp hX stage hr hUpdate hId).2
    exact ⟨credit,hCredit,hWarp,Option.some.inj (hExact.symm.trans hAt)⟩

/-- The actual dispatched cohorts make the P wait ready at the exact generation
the MMA lane has yet to consume. A later completed generation would require a
later score commit, and its matching MMA election would require this lane's
successful acquire already to be present in its trace. -/
theorem probabilityPhaseOfUnconsumedCohort {g gen : Nat} (hg : g < l.threads)
    (hWarp : warpIndex l g = 12) (stage packet : Fin 2)
    (hCohort : ProbabilityCohort l X (g/l.block) stage packet gen)
    (hCursor : okPolls (probabilityObject l (g/l.block) stage packet) (X.tr g) = gen) :
    let log := X.objects (probabilityObject l (g/l.block) stage packet)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = gen+1 := by
  obtain ⟨s,hState,hLower⟩ := probabilityAdvancedOfCohort hp hX hGuard stage packet hCohort
  refine ⟨s,hState,?_⟩
  by_contra! hNot
  have hLater : gen+1 < s.phase := by omega
  obtain ⟨credit,hCredit,hSoftmax,hOrdinal⟩ :=
    softmaxCreditOfCompletedProbabilityPhase hp hX hGuard stage packet hState hLater
  obtain ⟨_,_,phase,_,hScorePoll,_,hSuccess,_,hObserved,hBound⟩ :=
    scoreObservedBeforeSoftmaxCredit hp hX stage packet hSoftmax hCredit
  obtain ⟨_,spec,rank,hScore,hRank,_⟩ :=
    scoreCommitOfObservation hp hX stage hScorePoll hSuccess hObserved
  have hPeer := scoreOrdinalLePeerProbabilityCount hp hX hScore packet hg rfl hWarp
  omega

omit hp hX hGuard in
/-- The actual credits of the mapped softmax and correction lanes form the
joint main cohort. -/
theorem mainProbabilityCohortOfProducers {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {cta gen : Nat} (stage : Fin 2)
    (hCredit : ∀ g, g/l.block = cta → JointProbabilityProducer l stage g →
      ∃ j, ProbabilityCredit l X (g,j) cta stage 0 ∧
        probabilityOrdinal l X cta stage 0 (g,j) = gen) :
    ProbabilityCohort l X cta stage 0 gen := by
  let localLane (a : Fin 256) :=
    if a.val < 128 then 128*stage.val+a.val else 128+a.val
  let thread (a : Fin 256) := cta*l.block+localLane a
  have hActual (a : Fin 256) : ∃ j, ProbabilityCredit l X (thread a,j) cta stage 0 ∧
      probabilityOrdinal l X cta stage 0 (thread a,j) = gen := by
    have hStage := stage.isLt
    have hIndex := a.isLt
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    have hBound : localLane a < l.block := by
      rw [hp.block]
      dsimp only [localLane]
      split <;> omega
    obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hBlock hBound
    refine hCredit (thread a) hOwner ?_
    change thread a % l.block = localLane a at hLocal
    unfold JointProbabilityProducer warpIndex
    rw [hLocal]
    dsimp only [localLane]
    split <;> omega
  choose j hAct using hActual
  have hCount : probabilityCredits 0 = 256 := rfl
  unfold ProbabilityCohort
  rw [hCount]
  refine ⟨fun a => (thread a,j a),?_,hAct⟩
  intro a b hEq
  have hThread := congrArg (fun e : EvId => e.1) hEq
  have hLocal : localLane a = localLane b := Nat.add_left_cancel hThread
  have hA := a.isLt
  have hB := b.isLt
  have hStage := stage.isLt
  apply Fin.ext
  dsimp only [localLane] at hLocal
  split at hLocal <;> split at hLocal <;> omega

omit hp hX hGuard in
/-- The actual elected arrivals, one from each of the four stage-local warps,
form the tail cohort. -/
theorem tailProbabilityCohortOfWarps {l : Launch} {X : Execution} {cta gen : Nat}
    (stage : Fin 2)
    (hCredit : ∀ a : Fin 4, ∃ i, ProbabilityCredit l X i cta stage 1 ∧
      probabilityOrdinal l X cta stage 1 i = gen ∧ warpIndex l i.1 % 4 = a.val) :
    ProbabilityCohort l X cta stage 1 gen := by
  choose ids hIssued using hCredit
  refine ⟨ids,?_,fun a => ⟨(hIssued a).1,(hIssued a).2.1⟩⟩
  intro a b hEq
  apply Fin.ext
  exact ((hIssued a).2.2.symm.trans
    (congrArg (fun i : EvId => warpIndex l i.1 % 4) hEq)).trans (hIssued b).2.2

/-- The exact phase makes the frontier poll at parity determined by the
consumer's current generation successful. -/
theorem probabilityReadyOfUnconsumedCohort {g gen : Nat} (hg : g < l.threads)
    (hWarp : warpIndex l g = 12) (stage packet : Fin 2)
    (hCohort : ProbabilityCohort l X (g/l.block) stage packet gen)
    (hCursor : okPolls (probabilityObject l (g/l.block) stage packet) (X.tr g) = gen) :
    let log := X.objects (probabilityObject l (g/l.block) stage packet)
    ∃ s, stateBefore log log.length = some s ∧ s.phase%2 ≠ (gen%2)%2 := by
  obtain ⟨s,hState,hPhase⟩ :=
    probabilityPhaseOfUnconsumedCohort hp hX hGuard hg hWarp stage packet hCohort hCursor
  exact ⟨s,hState,by omega⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
