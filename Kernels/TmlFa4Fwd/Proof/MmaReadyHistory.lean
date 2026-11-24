-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyOrdinals
public import Kernels.TmlFa4Fwd.Proof.MbarSafety
public import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.MbarUnitTx
import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Proof PTX.MBarrier PTX.MbarRing PTX.AsyncCopy Prologue

noncomputable section

private theorem actualNoInvalidation {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (loc : Loc) : NoInval (X.objects loc) := by
  intro r hr hInval
  cases record_source hX.tma.2.2.1 hr <;> rename_i ha
  all_goals try (rw [ha] at hInval; cases hInval; done)
  rename_i _ hGet
  exact noMbarInval hX ⟨_, hGet⟩

/-- Once its operand has a published initializer, even a failed actual poll has a clean record. -/
theorem actualPollRecordClean {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait : EvId} {pc parity : Nat} {loc : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get wait = some ⟨pc, .wait loc parity ok acq scope⟩) :
    ∃ (j : Nat) (poll : Record Ref), (X.objects loc)[j]? = some poll ∧
      poll.id = .thread wait ∧ poll.action = .pollParity parity ok ∧
      poll.fault = none ∧ poll.reply.waited = some ok := by
  have hAction : objectAction X X.async loc (.thread wait) = some (.pollParity parity ok) := by
    simp [objectAction, he]
  obtain ⟨poll, hm, hId⟩ := (hX.tma.2.2.1 loc).2.2 _ _ hAction
  have hAct := ((hX.tma.2.2.1 loc).2.1 poll hm).1
  rw [hId, hAction] at hAct
  have ha := (Option.some.inj hAct).symm
  obtain ⟨site, rfl⟩ := actualWaitInitObject hp hX he
  have hInit := (activeObjectHistory hp hX site hm).1
  have hClean := PairTmaRing.poll_clean hX hInit (actualNoInvalidation hX _) poll hm
    ⟨parity, ok, ha⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have hWaited : poll.reply.waited = some ok := by
    cases ok
    · obtain ⟨_, s, hState, _⟩ := PairTmaRing.state_of_init hX hInit
        (actualNoInvalidation hX _) hj (by intro n; rw [ha]; simp)
      have hRecord := (X.objects_checked hX _).at hj
      rw [hState] at hRecord
      unfold RecordOk at hRecord
      rw [ha] at hRecord
      simp [perform, pure, Except.pure] at hRecord
      rw [hRecord.1]
    · exact (hX.object_thread_waited_iff hm hId hClean).mpr (by simp [he, sourceWaitSuccess])
  exact ⟨j, poll, hj, hId, ha, hClean, hWaited⟩

namespace Loader

/-- A ready acquire observes its lane-local generation if the actual parity trace alternates
and later producer uses are causally gated. Those are the two remaining trace obligations. -/
theorem readyGenerationOfLaneReuse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g index pc parity : Nat} (stage : Fin 3)
    (he : X.get (g, index) = some ⟨pc,
      .wait (initObject l cta (readySlot stage)) parity true true .cta⟩)
    (hAlternating : let loc := initObject l cta (readySlot stage)
      ∀ j pc q acq scope, X.get (g, j) = some ⟨pc, .wait loc q true acq scope⟩ →
        q % 2 = Flow.okPolls loc ((X.tr g).take j) % 2)
    (hReuse : let loc := initObject l cta (readySlot stage)
      ∀ issue, X.AsyncArrive issue loc true → X.async.arrived issue = true →
        Flow.okPolls loc ((X.tr g).take index) < readyOrdinal X loc issue →
        Relation.TransGen (DepStep l kernel X) (.thread (g, index), true)
          (.async issue .arriveOn, false)) :
    let loc := initObject l cta (readySlot stage)
    ∃ (j : Nat) (poll : Record Ref), (X.objects loc)[j]? = some poll ∧
      poll.id = .thread (g, index) ∧ poll.reply.waited = some true ∧
      observedAt (X.objects loc) j = some (Flow.okPolls loc ((X.tr g).take index)) := by
  dsimp only
  let loc := initObject l cta (readySlot stage)
  obtain ⟨hObj, j, poll, hj, hId, hSuccess⟩ := actualReadyAcquireRecord hp hX stage he
  have hClean := PairTmaRing.poll_clean hX hObj.init hObj.noInval
  have hCount := Poll.count_before hX hj hId hClean
  have hAlt := Poll.alternates hX (m := loc) (g := g) (δ := 0) hClean
    (by simpa using hAlternating)
  have hSelected : objectThreadSelected g poll.id = true :=
    objectThreadSelected_iff.mpr ⟨index, hId⟩
  have hPhase := readyPhaseOfCausalReuse hp hX stage (objectThreadSelected g)
    hObj hj hId hSuccess hSelected hAlt (fun issue hi hDone hUse =>
      hReuse issue hi hDone (by rw [← hCount]; exact hUse))
  exact ⟨j, poll, hj, hId, hSuccess, hPhase.trans (congrArg some hCount)⟩

end Loader
end
end PTX.Kernels.TmlFa4Fwd
