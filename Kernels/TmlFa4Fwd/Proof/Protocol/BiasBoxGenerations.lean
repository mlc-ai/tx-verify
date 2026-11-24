-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasNotificationFaults
public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasCredits
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Order.DependencyWitness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem completedBiasBeforeState {cta i phase : Nat} (stage : Fin 2) {r : Record Ref}
    {s : State} (hr : (X.objects (biasReadyObject l cta stage))[i]? = some r)
    (hs : stateBefore (X.objects (biasReadyObject l cta stage)) i = some s)
    (hPhase : phase < s.phase) :
    ∃ stop ≤ i,
      (pairTxPhaseRecords (X.objects (biasReadyObject l cta stage)) stop phase
        (.completeTx 16384)).card = 2 := by
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hInit : PairTmaRing.InitFirst X loc 1 := by
    have hMem := List.mem_of_getElem? hr
    fin_cases stage
    · exact (activeObjectHistory hp hX (30 : Fin 34) hMem).1
    · exact (activeObjectHistory hp hX (31 : Fin 34) hMem).1
  have hShape (r : Record Ref) (hr : r ∈ log) : PairTxAction r := by
    cases biasReadyRecord hp hX stage hr with
    | init ha => exact .init ha
    | poll ha => exact .poll ha
    | expect _ _ _ ha => exact .expect ha
    | notify _ _ _ _ _ _ ha => exact .notify ha
  obtain ⟨stop, hStop, _, hTwo, _⟩ := completedPairTxCountsBeforeState hChecked hNo hShape
    (fun _ _ hs => PairTmaRing.expected_of_init hX hInit hNo hs)
    (List.getElem?_eq_some_iff.mp hr).1.le hs hPhase
  exact ⟨stop, hStop, hTwo⟩

private theorem biasCompleteOrigin {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : (X.objects (biasReadyObject l cta stage))[i]? = some r)
    (ha : r.action = .completeTx 16384) :
    ∃ e half spec, r.id = .async e (.notify .load) ∧
      e.1 / l.block = cta ∧ BiasSubbox p l X e stage half spec := by
  cases biasReadyRecord hp hX stage (List.mem_of_getElem? hr) with
  | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
  | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
  | expect _ _ _ h => rw [h] at ha; cases ha
  | notify e half spec hid hOwner hBox _ => exact ⟨e, half, spec, hid, hOwner, hBox⟩

private theorem biasCompletedHalf {cta stop phase : Nat} (stage half : Fin 2)
    (hCount : (pairTxPhaseRecords (X.objects (biasReadyObject l cta stage)) stop phase
      (.completeTx 16384)).card = 2)
    (hOrdinal : ∀ {i : Nat} {r : Record Ref} {e : EvId} {half : Fin 2} {spec : TensorCopy.Spec},
      (X.objects (biasReadyObject l cta stage))[i]? = some r →
      r.id = .async e (.notify .load) → e.1 / l.block = cta →
      BiasSubbox p l X e stage half spec → r.action = .completeTx 16384 →
      phaseAt (X.objects (biasReadyObject l cta stage)) i = some phase →
      biasTensorOrdinal l X stage half e = phase) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ i r e spec, i < stop ∧ log[i]? = some r ∧ r.id = .async e (.notify .load) ∧
      e.1 / l.block = cta ∧ BiasSubbox p l X e stage half spec ∧
      biasTensorOrdinal l X stage half e = phase ∧ phaseAt log i = some phase ∧
      r.fault = none ∧ r.action = .completeTx 16384 := by
  let log := X.objects (biasReadyObject l cta stage)
  have hChecked := X.objects_checked hX (biasReadyObject l cta stage)
  obtain ⟨u, v, huv, hMembers⟩ := Finset.card_eq_two.mp hCount
  have origin {k : Nat} (hk : k ∈ pairTxPhaseRecords log stop phase (.completeTx 16384)) :
      ∃ r e half spec, k < stop ∧ log[k]? = some r ∧ r.id = .async e (.notify .load) ∧
        e.1 / l.block = cta ∧ BiasSubbox p l X e stage half spec ∧
        biasTensorOrdinal l X stage half e = phase ∧ phaseAt log k = some phase ∧
        r.fault = none ∧ r.action = .completeTx 16384 := by
    obtain ⟨hk, hP, r, hr, hClean, hAct⟩ := memPairTxPhaseRecords.mp hk
    obtain ⟨e, half, spec, hId, hOwner, hBox⟩ := biasCompleteOrigin hp hX stage hr hAct
    exact ⟨r, e, half, spec, hk, hr, hId, hOwner, hBox, hOrdinal hr hId hOwner hBox hAct hP,
      hP, hClean, hAct⟩
  have hU : u ∈ pairTxPhaseRecords log stop phase (.completeTx 16384) :=
    hMembers ▸ Finset.mem_insert_self _ _
  have hV : v ∈ pairTxPhaseRecords log stop phase (.completeTx 16384) :=
    hMembers ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨rA, a, ha, specA, hu, hGetA, hIdA, hCtaA, hBoxA, hOrdA, hPA, hCleanA, hActA⟩ := origin hU
  obtain ⟨rB, b, hb, specB, hv, hGetB, hIdB, hCtaB, hBoxB, hOrdB, hPB, hCleanB, hActB⟩ := origin hV
  have hHalves : ha ≠ hb := by
    intro hh
    subst hb
    have hab := biasTensorOrdinalInjective hp hX hBoxA hBoxB
      (hCtaA.trans hCtaB.symm) (hOrdA.trans hOrdB.symm)
    subst b
    exact huv (ObjectInit.checked_record_index_eq hChecked hGetA hGetB (hIdA.trans hIdB.symm))
  have hMatch : ha = half ∨ hb = half := by
    fin_cases ha <;> fin_cases hb <;> fin_cases half <;>
      first | exact (hHalves rfl).elim | decide
  rcases hMatch with rfl | rfl
  · exact ⟨u, rA, a, specA, hu, hGetA, hIdA, hCtaA, hBoxA, hOrdA, hPA, hCleanA, hActA⟩
  · exact ⟨v, rB, b, specB, hv, hGetB, hIdB, hCtaB, hBoxB, hOrdB, hPB, hCleanB, hActB⟩

/-- Each real Bias completion is recorded in the exact generation of its half's source issue. -/
theorem biasNotificationPhaseExact {cta phase i : Nat} (stage : Fin 2) {r : Record Ref} {e : EvId}
    {half : Fin 2} {spec : TensorCopy.Spec}
    (hr : (X.objects (biasReadyObject l cta stage))[i]? = some r)
    (hId : r.id = .async e (.notify .load)) (hOwner : e.1 / l.block = cta)
    (hBox : BiasSubbox p l X e stage half spec) (ha : r.action = .completeTx 16384)
    (hPhase : phaseAt (X.objects (biasReadyObject l cta stage)) i = some phase) :
    biasTensorOrdinal l X stage half e = phase := by
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  induction phase using Nat.strong_induction_on generalizing i r e half spec with
  | h phase ih =>
    cases hs : stateBefore log i with
    | none => simp [phaseAt, log, loc, hs] at hPhase
    | some s =>
      have hS : s.phase = phase := by
        change (stateBefore log i).map State.phase = some phase at hPhase
        simpa only [hs, Option.map_some, Option.some.injEq] using hPhase
      have hLe := biasNotificationPhaseLower hp hX stage hr hId hOwner hBox ha hs
      by_contra hNe
      let ordinal := biasTensorOrdinal l X stage half e
      have hPrior : ordinal < s.phase := by omega
      obtain ⟨stop, hStop, hTwo⟩ := completedBiasBeforeState hp hX stage hr hs hPrior
      obtain ⟨k, r', a, spec', hk, hr', hid', hOwner', hBox', hOrd', _, _, _⟩ :=
        biasCompletedHalf hp hX stage half hTwo
          (fun hGet hId hOwner hBox hAct hP => ih ordinal (by omega) hGet hId hOwner hBox hAct hP)
      have hSame := biasTensorOrdinalInjective hp hX hBox' hBox (hOwner'.trans hOwner.symm) hOrd'
      subst a
      have hIndices := ObjectInit.checked_record_index_eq hChecked hr' hr (hid'.trans hId.symm)
      omega


/-- A successful Bias acquire sees the actual copy of each half in the observed generation,
with the source issue's per-half ordinal equal to that generation. -/
theorem biasReadyObservedHalfOwner {cta j phase : Nat} (stage half : Fin 2) {poll : Record Ref}
    (hj : (X.objects (biasReadyObject l cta stage))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasReadyObject l cta stage)) j = some phase) :
    ∃ e spec, e.1 / l.block = cta ∧ BiasSubbox p l X e stage half spec ∧
      biasTensorOrdinal l X stage half e = phase ∧
      MbarObserved X (.async e (.notify .load)) poll.id := by
  let loc := biasReadyObject l cta stage
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨stop, _, _, hCount, _⟩ := biasReadyObservedCredits hp hX stage hj hSuccess hPhase
  obtain ⟨k, r, e, spec, _, hr, hid, hOwner, hb, hOrdinal, hP, hClean, hAct⟩ :=
    biasCompletedHalf hp hX stage half hCount (biasNotificationPhaseExact hp hX stage)
  have hObs := hX.observed_of_phase hNo hr hClean (hAct.symm ▸ trivial) hj hSuccess hP hPhase
  rw [hid] at hObs
  exact ⟨e, spec, hOwner, hb, hOrdinal, hObs⟩

/-- Every successful Bias acquire obtains both halves of its exact ready generation. -/
theorem biasReadyObservedHalf {cta j phase : Nat} (stage half : Fin 2) {poll : Record Ref}
    (hj : (X.objects (biasReadyObject l cta stage))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasReadyObject l cta stage)) j = some phase) :
    ∃ e spec, BiasSubbox p l X e stage half spec ∧
      biasTensorOrdinal l X stage half e = phase ∧
      MbarObserved X (.async e (.notify .load)) poll.id := by
  obtain ⟨e, spec, _, hBox, hOrd, hObs⟩ := biasReadyObservedHalfOwner hp hX stage half hj
    hSuccess hPhase
  exact ⟨e, spec, hBox, hOrd, hObs⟩

/-- A real reused half, even before its notification exists, observes the immediately
previous Bias-empty generation before issuing. -/
theorem biasTensorReuseGuardExact {g j : Nat} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X (g,j) stage half spec)
    (hReused : 0 < biasTensorOrdinal l X stage half (g,j)) :
    let ordinal := biasTensorOrdinal l X stage half (g,j)
    let log := X.objects (biasEmptyObject l (g / l.block) stage)
    ∃ (k i : Nat) (r : Record Ref), log[i]? = some r ∧ r.id = .thread (g,k) ∧
      r.reply.waited = some true ∧ Resumes kernel X (g,k) (g,j) ∧
      observedAt log i = some (ordinal - 1) := by
  let ordinal := biasTensorOrdinal l X stage half (g,j)
  let loc := biasReadyObject l (g / l.block) stage
  let readyLog := X.objects loc
  obtain ⟨k, i, phase, poll, hPoll, hPollId, hReply, hResume, hObs, hLower⟩ :=
    biasTensorGuardObserved hp hX hIssue hReused
  change ordinal ≤ phase + 1 at hLower
  have hExact : phase = ordinal - 1 := by
    by_contra hNe
    have hOld : ordinal ≤ phase := by omega
    obtain ⟨release, hReturn, hRetOrdinal, hWaits⟩ :=
      biasEmptyObservedReturn hp hX stage hPoll hReply hObs
    obtain ⟨sensor, atReady, seenPhase, ready, hReady, hReadyId, hSeen, hReadyObs, hGe, hRelease⟩ :=
      Thread.Softmax.biasReadyObservedOfReturn hp hX stage hReturn
    have hChecked := X.objects_checked hX loc
    obtain ⟨st, hState, hFound⟩ := hChecked.observed_phase hReady hSeen hReadyObs
    change biasArrivalOrdinal X (biasEmptyObject l (g / l.block) stage) release ≤
      seenPhase at hGe
    have hOlder : ordinal < st.phase := by omega
    obtain ⟨stop, hStop, hTwo⟩ := completedBiasBeforeState hp hX stage hReady hState hOlder
    obtain ⟨q, r, e, box, hq, hr, hId, hOwner, hBox, hOrdinal, _, _, _⟩ :=
      biasCompletedHalf hp hX stage half hTwo (biasNotificationPhaseExact hp hX stage)
    have hSelf : e = (g,j) :=
      biasTensorOrdinalInjective hp hX hBox hIssue hOwner hOrdinal
    subst e
    have hPresent := object_record_present hX.tma (List.mem_of_getElem? hr)
    rw [hId] at hPresent
    rw [hPollId] at hWaits
    have hPath := (Relation.TransGen.single (DepStep.of_resumes l hRelease)).tail
      (DepStep.of_witness l (Witness.of_mbarObserved hWaits))
    have hChain := (hPath.tail (DepStep.of_resumes l hResume)).trans
      (biasNotificationAfterIssue hX hIssue hPresent)
    rw [← hReadyId, ← hId] at hChain
    have hNot := MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hChain
    exact hNot ⟨q, atReady, r, ready, hr, rfl, hReady, rfl, hq.trans_le hStop⟩
  exact ⟨k, i, poll, hPoll, hPollId, hReply, hResume, hExact ▸ hObs⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
