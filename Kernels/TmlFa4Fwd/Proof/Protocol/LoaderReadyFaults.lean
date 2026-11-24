-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy
import Lemmas.Protocol.GatedFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing
open Thread.Loader (publicationProducer publicationUniqueAtSlot producer readyObject)
open Thread.Mma.Observation (emptyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem readyGuardingPoll (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner k : Nat} {slot : Fin 3} {r : Record Ref} {issue : EvId}
    (hr : (X.objects (readyObject l owner slot))[k]? = some r) (hId : r.id = .async issue .arriveOn)
    (hPub : X.AsyncArrive issue (readyObject l owner slot) true)
    (hDone : X.async.arrived issue = true) (hPositive : 0 < generation l X issue slot) :
    ∃ j poll st, j < k ∧ (X.objects (readyObject l owner slot))[j]? = some poll ∧
      poll.reply.waited = some true ∧ stateBefore (X.objects (readyObject l owner slot)) j =
        some st ∧ generation l X issue slot = st.phase := by
  let n := generation l X issue slot - 1
  have hGen : generation l X issue slot = n + 1 := by dsimp [n]; omega
  obtain ⟨guard, g, pos, release, hOrdinal, hObserved⟩ :=
    actualReleaseForNextPublicationExact hp hX hPub hGen
  have hReady := release.matched.ready
  rw [release.matchedSlot] at hReady
  obtain ⟨completion⟩ := actualCompletedForIssuer hp hX release.issue hReady
  unfold Thread.Mma.EmptyReleaseAt.ordinal at hOrdinal
  rw [release.matchedSlot] at hOrdinal
  rw [hOrdinal] at completion
  have hCta : owner / l.block = g / l.block := by
    rw [publicationCta hp hX hPub, ← guard.issuer, release.issuerCta hp hX]
  have hObject : readyObject l g slot = readyObject l owner slot :=
    congrArg (fun cta => Prologue.initObject l cta (Loader.readySlot slot)) hCta.symm
  have hPoll := completion.record
  have hSeen := completion.observed
  rw [hObject] at hPoll hSeen
  obtain ⟨st, hState, hPhase⟩ := (X.objects_checked hX _).observed_phase
    hPoll completion.success hSeen
  have hWitness : EmptyReuseWitness X (.async (g, release.index) (.tcNotify release.rank)) issue :=
    ⟨guard.acquire, guard.copy, release.notification ▸ hObserved, guard.guarded, guard.tracked⟩
  have hPath := hWitness.afterIssuerReady hX release.issue release.matched release.matched.ready
    (Nat.le_refl _) hDone
  have hBefore : completion.position < k := by
    rcases Nat.lt_trichotomy completion.position k with hLt | hEq | hGt
    · exact hLt
    · rw [hEq, hr] at hPoll
      have hRecord := Option.some.inj hPoll
      have hIdent := (congrArg Record.id hRecord).symm.trans hId
      rw [completion.id] at hIdent
      cases hIdent
    · exact (Round.Slot.not_before_of_reach hX hPath
        ⟨k, completion.position, r, completion.poll, hr, hId, hPoll, completion.id, hGt⟩).elim
  exact ⟨completion.position, completion.poll, st, hBefore, hPoll, completion.success,
    hState, hGen.trans hPhase.symm⟩

/-- Every KV-ready record is clean, and every actual publication arrives in its own generation.
The gate also covers a publication whose record is a candidate fault in the raw history. -/
theorem readyHistoryClean (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (owner : Nat) (slot : Fin 3) {r : Record Ref} (hr : r ∈ X.objects (readyObject l owner slot)) :
    r.fault = none ∧ ∀ k issue,
      (X.objects (readyObject l owner slot))[k]? = some r →
      r.action = .arrive 1 0 → r.id = .async issue .arriveOn →
      phaseAt (X.objects (readyObject l owner slot)) k = some (generation l X issue slot) := by
  classical
  let loc := readyObject l owner slot
  let log := X.objects loc
  have hObj := Loader.actualReadyHistoryObject hp hX (cta := owner/l.block) slot hr
  let lanes := (Finset.univ : Finset (Fin 64)).image (producer l (owner/l.block))
  let label (ref : Ref) := (ref.issuer.1, generation l X ref.issuer slot)
  have hInj : Function.Injective (producer l (owner/l.block)) := by
    intro a b h
    apply Fin.ext
    unfold producer Loader.readyProducer at h
    omega
  have hCard : lanes.card = 64 := by
    rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin]
  have hNoIncr (r : Record Ref) (hr : r ∈ log) : r.action ≠ .increment := by
    intro h
    cases hObj.source r hr with
    | init ha | poll ha | arriveOn _ _ _ ha => rw [h] at ha; cases ha
  have hNoComplete (r : Record Ref) (hr : r ∈ log) (n : Nat) :
      r.action ≠ .completeTx n := by
    intro h
    cases hObj.source r hr with
    | init ha | poll ha | arriveOn _ _ _ ha => rw [h] at ha; cases ha
  have hChecked := X.objects_checked hX loc
  have hGated := hChecked.gated_arrive hObj.noInval lanes label
    (fun i st hLen hState => ⟨hCard.symm ▸
      PairTmaRing.expected_of_init hX hObj.init hObj.noInval hState,
      tx_zero_of hX hObj.noInval (fun r hr c tx ha => by
        cases hObj.source r hr with
        | init ha' | poll ha' => rw [ha] at ha'; cases ha'
        | arriveOn _ _ _ ha' => rw [ha] at ha'; exact (Action.arrive.inj ha').2)
        hNoComplete hLen hState⟩)
    (fun k r c tx hk ha => by
      obtain ⟨_, st, hs, _⟩ := PairTmaRing.state_of_init hX hObj.init hObj.noInval hk
        (by intro n; rw [ha]; simp)
      exact ⟨st, hs⟩)
    (fun k r c tx hk ha => by
      obtain ⟨rfl, rfl, issue, hId, hPub, _⟩ := hObj.arrive_source hk ha
      obtain ⟨lane, hLane⟩ := publicationProducer hp hX hPub
      refine ⟨rfl, rfl, ?_⟩
      rw [hId]
      change issue.1 ∈ lanes
      rw [hLane]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ lane))
    (fun k k' r r' c tx c' tx' hk hk' ha ha' hLabel => by
      obtain ⟨_, _, issue, hId, hPub, _⟩ := hObj.arrive_source hk ha
      obtain ⟨_, _, other, hOtherId, hOther, _⟩ := hObj.arrive_source hk' ha'
      rw [hId, hOtherId] at hLabel
      change (issue.1, generation l X issue slot) =
        (other.1, generation l X other slot) at hLabel
      have hThread := congrArg Prod.fst hLabel
      have hUse : generation l X issue slot = generation l X other slot :=
        congrArg Prod.snd hLabel
      have hEq := publicationUniqueAtSlot hp hX hPub hOther hThread hUse
      apply ObjectInit.checked_record_index_eq hChecked hk hk'
      rw [hId, hOtherId, hEq])
    (fun k r c tx hk ha hPositive => by
      obtain ⟨_, _, issue, hId, hPub, hDone⟩ := hObj.arrive_source hk ha
      rw [hId] at hPositive ⊢
      obtain ⟨j, poll, st, hBefore, hPoll, hSuccess, hState, hPhase⟩ :=
        readyGuardingPoll hp hX hk hId hPub hDone hPositive
      exact ⟨j, poll, st, hBefore, hPoll, hSuccess, hState, hPhase.le⟩)
    (incrementsBefore_length_of log hNoIncr)
  refine ⟨?_, fun k issue hk ha hid => ?_⟩
  · cases hObj.source r hr with
    | init ha => exact PairTmaRing.init_clean hObj.init hr ha
    | poll ha => exact PairTmaRing.poll_clean hX hObj.init hObj.noInval r hr ⟨_, _, ha⟩
    | arriveOn _ _ _ ha =>
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      exact (hGated k r 1 0 hk ha).1
  · simpa only [label, hid, Ref.issuer] using (hGated k r 1 0 hk ha).2

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
