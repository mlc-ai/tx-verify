-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SoftmaxProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.GatedFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Scores
open PTX.Kernels.TmlFa4Fwd.Prologue (warpIndex)

/-- Each recurring correction credit follows a successful joint probability observation
of at least its preceding generation. -/
def CorrectionJointGuards (l : Launch) (X : Execution) : Prop :=
  ∀ {cta i : Nat} {r : Record Ref} {e : EvId} (stage : Fin 2),
    let log := X.objects (probabilityObject l cta stage 0)
    log[i]? = some r → r.id = .thread e → ProbabilityCredit l X e cta stage 0 →
    8 ≤ warpIndex l e.1 → 0 < probabilityOrdinal l X cta stage 0 e →
    ∃ k w st, k < i ∧ log[k]? = some w ∧ w.reply.waited = some true ∧
      stateBefore log k = some st ∧ probabilityOrdinal l X cta stage 0 e ≤ st.phase

private def jointIssuerIndex (l : Launch) (stage : Fin 2) (g : Nat) : Nat :=
  if warpIndex l g < 8 then g % l.block - 128 * stage.val else g % l.block - 128

private def jointLabel (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2) :
    Ref → Nat × Nat
  | .thread e => (jointIssuerIndex l stage e.1, probabilityOrdinal l X cta stage 0 e)
  | .async .. => (0,0)

private theorem jointIndexRange {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta : Nat} {stage : Fin 2} (hIssue : ProbabilityCredit l X e cta stage 0) :
    (warpIndex l e.1 < 8 ∧ 128 * stage.val ≤ e.1 % l.block ∧
      e.1 % l.block < 128 * stage.val + 128) ∨
    (¬ warpIndex l e.1 < 8 ∧ 256 ≤ e.1 % l.block ∧ e.1 % l.block < 384) := by
  rcases (probabilityCreditRole hp hX stage 0 hIssue).2 with h | h
  · left
    refine ⟨h.1,?_⟩
    rw [warpIndex,Nat.div_div_eq_div_mul] at h
    simp only [Nat.reduceMul] at h
    omega
  · right
    have hW := h.2
    unfold warpIndex at hW
    refine ⟨by omega,?_⟩
    omega

private theorem jointLabelBound {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta : Nat} {stage : Fin 2} (hIssue : ProbabilityCredit l X e cta stage 0) :
    (jointLabel l X cta stage (.thread e)).1 < 256 := by
  rcases jointIndexRange hp hX hIssue with h | h
  · simpa only [jointLabel,jointIssuerIndex,ite_eq_left h.1] using
      (show e.1 % l.block - 128 * stage.val < 256 by omega)
  · simpa only [jointLabel,jointIssuerIndex,ite_eq_right h.1] using
      (show e.1 % l.block - 128 < 256 by omega)

private theorem jointLabelInj {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e f : EvId} {cta : Nat} {stage : Fin 2}
    (he : ProbabilityCredit l X e cta stage 0) (hf : ProbabilityCredit l X f cta stage 0)
    (hEq : jointLabel l X cta stage (.thread e) = jointLabel l X cta stage (.thread f)) :
    e = f := by
  have hIndex := congrArg Prod.fst hEq
  change jointIssuerIndex l stage e.1 = jointIssuerIndex l stage f.1 at hIndex
  have hMod : e.1 % l.block = f.1 % l.block := by
    rcases jointIndexRange hp hX he with hE | hE <;>
      rcases jointIndexRange hp hX hf with hF | hF <;>
      simp only [jointIssuerIndex,hE.1,hF.1,↓reduceIte] at hIndex <;> omega
  have hCta := ((probabilityCreditRole hp hX stage 0 he).1).trans
    (probabilityCreditRole hp hX stage 0 hf).1.symm
  have hLane : e.1 = f.1 := by
    rw [← Nat.mod_add_div e.1 l.block, hMod,hCta,Nat.mod_add_div]
  exact probabilityOrdinalInjective he hf hLane (congrArg Prod.snd hEq)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hGuard : CorrectionJointGuards l X)
include hp hX hGuard

private theorem jointUpdateAligned {cta i c tx : Nat} (stage : Fin 2) {r : Record Ref}
    (hi : (X.objects (probabilityObject l cta stage 0))[i]? = some r) (ha : r.action = .arrive c tx)
    :
    r.fault = none ∧ phaseAt (X.objects (probabilityObject l cta stage 0)) i =
      some (jointLabel l X cta stage r.id).2 := by
  let loc := probabilityObject l cta stage 0
  let log := X.objects loc
  let labels := jointLabel l X cta stage
  have hInit := probabilityInitialized hp hX stage 0 (List.mem_of_getElem? hi)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have unit {d : Record Ref} (hd : d ∈ log) (h : CounterUpdate d.action) :
      d.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,ha⟩ := probabilityUpdate hp hX stage 0 hd h
    exact ha
  have source {i c tx : Nat} {d : Record Ref} (hd : log[i]? = some d)
      (ha : d.action = .arrive c tx) :
      ∃ issue, d.id = .thread issue ∧ ProbabilityCredit l X issue cta stage 0 ∧
        (labels d.id).2 = probabilityOrdinal l X cta stage 0 issue := by
    obtain ⟨e,hId,hCredit,_,_⟩ :=
      probabilityUpdate hp hX stage 0 (List.mem_of_getElem? hd) (by rw [ha]; trivial)
    exact ⟨e,hId,hCredit,by rw [hId]; rfl⟩
  have hInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro d hd h
    have ha := unit hd (by rw [h]; trivial)
    rw [h] at ha
    cases ha
  have hCh := X.objects_checked hX loc
  apply hCh.gated_arrive hNo (Finset.range 256) labels _ _ _ _ _ hInc i r c tx hi ha
  · intro k s hk hs
    have hExpected := PairTmaRing.expected_of_init hX hInit hNo hs
    have hZero := MbarRing.tx_zero_of hX hNo
      (fun d hd c tx h => (Action.arrive.inj (h.symm.trans (unit hd (by rw [h]; trivial)))).2)
      (fun d hd n h => by
        have ha := unit hd (by rw [h]; trivial)
        rw [h] at ha
        cases ha) hk hs
    exact ⟨by simpa [Finset.card_range,probabilityCredits] using hExpected,hZero⟩
  · intro index d c tx hd hArrive
    obtain ⟨_,st,hState,_⟩ := PairTmaRing.state_of_init hX hInit hNo hd
      (by intro n; rw [hArrive]; simp)
    exact ⟨st,hState⟩
  · intro index d c tx hd hArrive
    obtain ⟨e,hId,hCredit,_⟩ := source hd hArrive
    have h := Action.arrive.inj
      (hArrive.symm.trans (unit (List.mem_of_getElem? hd) (by rw [hArrive]; trivial)))
    rw [hId]
    exact ⟨h.1,h.2,Finset.mem_range.mpr (jointLabelBound hp hX hCredit)⟩
  · intro j k d f cd td cf tf hd hf had haf heq
    obtain ⟨ed,hId,hD,_⟩ := source hd had
    obtain ⟨ef,hIF,hF,_⟩ := source hf haf
    rw [hId,hIF] at heq
    obtain rfl := jointLabelInj hp hX hD hF heq
    exact ObjectInit.checked_record_index_eq hCh hd hf (hId.trans hIF.symm)
  · intro j d c tx hd hArrive hPos
    obtain ⟨e,hId,hCredit,hOrd⟩ := source hd hArrive
    rw [hOrd] at hPos ⊢
    by_cases hw : warpIndex l e.1 < 8
    · exact softmaxCreditProbabilityGuard hp hX stage 0 hd hId hCredit hw hPos
    · exact hGuard stage hd hId hCredit (by omega) hPos

/-- A guarded joint probability notification is clean and has its local generation. -/
theorem jointProbabilityCreditPhaseExact {cta i : Nat} (stage : Fin 2) {e : EvId} {r : Record Ref}
    (hi : (X.objects (probabilityObject l cta stage 0))[i]? = some r) (ha : CounterUpdate r.action)
    (hId : r.id = .thread e) :
    r.fault = none ∧ phaseAt (X.objects (probabilityObject l cta stage 0)) i =
      some (probabilityOrdinal l X cta stage 0 e) := by
  obtain ⟨_,_,_,_,hAct⟩ := probabilityUpdate hp hX stage 0 (List.mem_of_getElem? hi) ha
  have h := jointUpdateAligned hp hX hGuard stage hi hAct
  rw [hId] at h
  exact h

/-- Joint probability histories are clean when every recurring correction credit is gated. -/
theorem jointProbabilityHistoryNoFault {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (probabilityObject l cta stage 0)) : r.fault = none := by
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX)
    (probabilityObject l cta stage 0)
  cases ha : r.action with
  | init n => exact actualInitOrPollClean hp hX hr (.inl ⟨n,ha⟩)
  | pollParity q ok => exact actualInitOrPollClean hp hX hr (.inr ⟨q,ok,ha⟩)
  | inval => exact (hNo _ hr ha).elim
  | arrive | completeTx | increment =>
    have hUpdate : CounterUpdate r.action := by rw [ha]; trivial
    obtain ⟨_,hId,_,_,_⟩ := probabilityUpdate hp hX stage 0 hr hUpdate
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hr
    exact (jointProbabilityCreditPhaseExact hp hX hGuard stage hi hUpdate hId).1

omit hp hX hGuard in
/-- Each mapped softmax or correction lane contributes a unit to the joint probability packet. -/
def JointProbabilityProducer (l : Launch) (stage : Fin 2) (g : Nat) : Prop :=
  (warpIndex l g < 8 ∧ warpIndex l g / 4 = stage.val) ∨
    (8 ≤ warpIndex l g ∧ warpIndex l g < 12)

omit hp hX hGuard in
private theorem jointProducerIndexRange {l : Launch} {stage : Fin 2} {g : Nat}
    (h : JointProbabilityProducer l stage g) :
    (warpIndex l g < 8 ∧ 128*stage.val ≤ g%l.block ∧ g%l.block < 128*stage.val+128) ∨
      (¬ warpIndex l g < 8 ∧ 256 ≤ g%l.block ∧ g%l.block < 384) := by
  rcases h with ⟨hw,hStage⟩ | h
  · left
    refine ⟨hw,?_⟩
    unfold warpIndex at hStage
    omega
  · right
    refine ⟨by omega,?_⟩
    unfold warpIndex at h
    omega

/-- A completed joint probability phase contains the exact credit of every mapped producer. -/
theorem jointPhaseProducerRecord {cta index phase : Nat} (stage : Fin 2) {g : Nat}
    (hOwner : g/l.block = cta) (hRole : JointProbabilityProducer l stage g) {sample : Record Ref}
    (hSample : sample ∈ X.objects (probabilityObject l cta stage 0)) {st : State}
    (hBound : index ≤ (X.objects (probabilityObject l cta stage 0)).length)
    (hState : stateBefore (X.objects (probabilityObject l cta stage 0)) index = some st)
    (hPhase : phase < st.phase) :
    let log := X.objects (probabilityObject l cta stage 0)
    ∃ j r credit, log[j]? = some r ∧ r.fault = none ∧ CounterUpdate r.action ∧
      phaseAt log j = some phase ∧ r.id = .thread credit ∧
      ProbabilityCredit l X credit cta stage 0 ∧ credit.1 = g ∧
      probabilityOrdinal l X cta stage 0 credit = phase := by
  classical
  let loc := probabilityObject l cta stage 0
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hInit := probabilityInitialized hp hX stage 0 hSample
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have source {j : Nat} (h : UnitArrivalIn log phase j) :
      ∃ r credit, log[j]? = some r ∧ CounterUpdate r.action ∧ r.fault = none ∧
        phaseAt log j = some phase ∧ r.id = .thread credit ∧
        ProbabilityCredit l X credit cta stage 0 ∧ probabilityOrdinal l X cta stage 0 credit = phase
      := by
    obtain ⟨r, _, hr, hArrive, hClean, hAt⟩ := h
    have hUpdate : CounterUpdate r.action := by rw [hArrive]; trivial
    obtain ⟨credit, hId, hCredit, _, _⟩ :=
      probabilityUpdate hp hX stage 0 (List.mem_of_getElem? hr) hUpdate
    have hExact := (jointProbabilityCreditPhaseExact hp hX hGuard stage hr hUpdate hId).2
    exact ⟨r, credit, hr, hUpdate, hClean, hAt, hId, hCredit,
      Option.some.inj (hExact.symm.trans hAt)⟩
  have unit {r : Record Ref} (hr : r ∈ log) (h : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,ha⟩ := probabilityUpdate hp hX stage 0 hr h
    exact ha
  have hInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hInc
    have h := unit hr (by rw [hInc]; trivial)
    rw [hInc] at h
    cases h
  have hCard := hChecked.card_unit_arrivals_phase hNo (n := 256) (q := phase)
    (fun _ r c tx hr _ ha => (Action.arrive.inj
      (ha.symm.trans (unit (List.mem_of_getElem? hr) (by rw [ha]; trivial)))).1)
    (fun _ _ _ hs => by
      simpa [probabilityCredits] using PairTmaRing.expected_of_init hX hInit hNo hs)
    hInc hBound hState hPhase
  let items := (Finset.range log.length).filter (UnitArrivalIn log phase)
  let label (j : Nat) : Nat := (jointLabel l X cta stage (log[j]?.getD sample).id).1
  have labelOf {j : Nat} {r : Record Ref} {credit : EvId}
      (hr : log[j]? = some r) (hId : r.id = .thread credit) :
      label j = jointIssuerIndex l stage credit.1 := by
    simp only [label,hr,Option.getD_some,hId,jointLabel]
  have hRange : items.image label ⊆ Finset.range 256 := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r,credit,hr,_,_,_,hId,he,_⟩ := source (Finset.mem_filter.mp hj).2
    rw [labelOf hr hId]
    exact Finset.mem_range.mpr (jointLabelBound hp hX he)
  have hInj : Set.InjOn label items := by
    intro j hj k hk hSame
    obtain ⟨r,e,hr,_,_,_,hId,he,hOrd⟩ := source (Finset.mem_filter.mp hj).2
    obtain ⟨s,f,hs,_,_,_,hF,hf,hOrd'⟩ := source (Finset.mem_filter.mp hk).2
    have hEq : jointLabel l X cta stage (.thread e) = jointLabel l X cta stage (.thread f) :=
      Prod.ext ((labelOf hr hId).symm.trans (hSame.trans (labelOf hs hF))) (hOrd.trans hOrd'.symm)
    have hCredit := jointLabelInj hp hX he hf hEq
    exact ObjectInit.checked_record_index_eq hChecked hr hs (hId.trans (hCredit ▸ hF.symm))
  have hLabels : items.image label = Finset.range 256 := by
    apply Finset.eq_of_subset_of_card_le hRange
    rw [Finset.card_image_of_injOn hInj,Finset.card_range]
    exact hCard.ge
  have hRoleRange := jointProducerIndexRange hRole
  have hLabel : jointIssuerIndex l stage g < 256 := by
    rcases hRoleRange with h | h
    · simp only [jointIssuerIndex,h.1,↓reduceIte]
      omega
    · simp only [jointIssuerIndex,h.1,↓reduceIte]
      omega
  have hTarget : jointIssuerIndex l stage g ∈ items.image label :=
    hLabels ▸ Finset.mem_range.mpr hLabel
  obtain ⟨j,hj,hJ⟩ := Finset.mem_image.mp hTarget
  obtain ⟨r,e,hr,hUpdate,hClean,hAt,hId,he,hOrd⟩ := source (Finset.mem_filter.mp hj).2
  have hSame := (labelOf hr hId).symm.trans hJ
  have hMod : e.1%l.block = g%l.block := by
    rcases jointIndexRange hp hX he with hE | hE <;> rcases hRoleRange with h | h <;>
      simp only [jointIssuerIndex,hE.1,h.1,↓reduceIte] at hSame <;> omega
  have hCta := (probabilityCreditRole hp hX stage 0 he).1
  have hLane : e.1 = g := by
    rw [← Nat.mod_add_div e.1 l.block,hMod,hCta,← hOwner,Nat.mod_add_div]
  exact ⟨j,r,e,hr,hClean,hUpdate,hAt,hId,he,hLane,hOrd⟩

/-- A returning joint wait observes the credit of every mapped softmax and correction lane. -/
theorem jointPollObservesProducer {cta index phase : Nat} (stage : Fin 2) {g : Nat}
    (hOwner : g/l.block = cta) (hRole : JointProbabilityProducer l stage g) {poll : Record Ref}
    (hPoll : (X.objects (probabilityObject l cta stage 0))[index]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (probabilityObject l cta stage 0)) index = some phase) :
    ∃ credit, ProbabilityCredit l X credit cta stage 0 ∧ credit.1 = g ∧
      probabilityOrdinal l X cta stage 0 credit = phase ∧
      MbarObserved X (.thread credit) poll.id := by
  let loc := probabilityObject l cta stage 0
  have hChecked := X.objects_checked hX loc
  obtain ⟨st,hSt,hLower⟩ := hChecked.observed_phase hPoll hSuccess hPhase
  have hPhaseLt : phase < st.phase := by omega
  obtain ⟨j,r,e,hr,hClean,hUpdate,hAt,hId,he,hLane,hOrd⟩ :=
    jointPhaseProducerRecord hp hX hGuard stage hOwner hRole (List.mem_of_getElem? hPoll)
      (List.getElem?_eq_some_iff.mp hPoll).1.le hSt hPhaseLt
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hObserved := hX.observed_of_phase hNo hr hClean hUpdate hPoll hSuccess hAt hPhase
  exact ⟨e,he,hLane,hOrd,hId ▸ hObserved⟩

/-- The joint generation acquires the publication of each of its 128 softmax lanes. -/
theorem jointPollObservesLane {cta index phase : Nat} (stage : Fin 2) {g : Nat}
    (hOwner : g/l.block = cta) (hWarp : warpIndex l g < 8) (hStage : warpIndex l g/4 = stage.val)
    {poll : Record Ref} (hPoll : (X.objects (probabilityObject l cta stage 0))[index]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (probabilityObject l cta stage 0)) index = some phase) :
    ∃ credit, ProbabilityCredit l X credit cta stage 0 ∧ credit.1 = g ∧
      probabilityOrdinal l X cta stage 0 credit = phase ∧
      MbarObserved X (.thread credit) poll.id :=
  jointPollObservesProducer hp hX hGuard stage hOwner (.inl ⟨hWarp,hStage⟩) hPoll hSuccess hPhase

/-- Every completed joint generation contains a softmax credit observed by its poll.
The correction lanes alone cannot fill the 256-credit object. -/
theorem jointPollObservesSoftmax {cta index phase : Nat} (stage : Fin 2) {poll : Record Ref}
    (hPoll : (X.objects (probabilityObject l cta stage 0))[index]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (probabilityObject l cta stage 0)) index = some phase) :
    ∃ credit, ProbabilityCredit l X credit cta stage 0 ∧ warpIndex l credit.1 < 8 ∧
      probabilityOrdinal l X cta stage 0 credit = phase ∧
      MbarObserved X (.thread credit) poll.id := by
  let g := cta*l.block + 128*stage.val
  have hOwner : g/l.block = cta := by
    have hs := stage.isLt
    unfold g
    rw [hp.block]
    omega
  have hWarp : warpIndex l g = 4*stage.val := by
    have hs := stage.isLt
    unfold warpIndex g
    rw [hp.block]
    omega
  have hw : warpIndex l g < 8 := by have hs := stage.isLt; omega
  have hStage : warpIndex l g/4 = stage.val := by omega
  obtain ⟨credit,hCredit,hLane,hOrdinal,hObs⟩ :=
    jointPollObservesLane hp hX hGuard stage hOwner hw hStage hPoll hSuccess hPhase
  exact ⟨credit,hCredit,hLane.symm ▸ hw,hOrdinal,hObs⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
