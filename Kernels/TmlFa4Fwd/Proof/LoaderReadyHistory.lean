-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderObservedPhase
public import Kernels.TmlFa4Fwd.Proof.MbarRecordOwner
public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Lemmas.Protocol.PairTmaRing.ItemFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.MBarrier PTX.MbarRing PTX.AsyncCopy

noncomputable section

/-- An active ready history has the initialized count and only no-increment updates
when the other instruction families' targets exclude its location. -/
theorem readyHistoryObject {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 3) {r : Record Ref}
    (hMem : r ∈ X.objects (Prologue.initObject l cta (readySlot stage)))
    (hArrive : ∀ i tx count release scope,
      ¬ X.Arrive i (Prologue.initObject l cta (readySlot stage)) tx count release scope)
    (hTensor : ∀ i addr spec, X.TensorIssue i addr spec →
      spec.mbar ≠ Prologue.initObject l cta (readySlot stage))
    (hCommit : ∀ i spec rank, X.Commit i spec →
      TcCommit.target spec rank ≠ some (Prologue.initObject l cta (readySlot stage))) :
    let loc := Prologue.initObject l cta (readySlot stage)
    NoIncObject X loc 64 := by
  dsimp only
  let loc := Prologue.initObject l cta (readySlot stage)
  have hCount : (Prologue.initSite (readySlot stage)).count = 64 := by
    fin_cases stage <;> rfl
  have hInit : PairTmaRing.InitFirst X loc 64 := by
    rw [← hCount]
    exact (activeObjectHistory hp hX (readySlot stage) hMem).1
  exact NoIncObject.of_issues hX hInit
    (fun _ => noMbarInval hX) hArrive (fun _ => noIncrementingCopyArrival hX) hTensor
    (fun _ _ hCopy => by rw [(actualCopyShape hX hCopy).completion]; simp)
    hCommit (fun _ _ _ _ hClc => (noClcIssue hX hClc).elim)

/-- Recover the successful history record and initialized no-increment object from the actual
acquire. The three target exclusions concern instruction types with a separate mbarrier operand. -/
theorem readyAcquireRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta pc parity : Nat} (stage : Fin 3) {wait : EvId}
    (hWait : X.get wait = some ⟨pc,
      .wait (Prologue.initObject l cta (readySlot stage)) parity true true .cta⟩)
    (hArrive : ∀ i tx count release scope,
      ¬ X.Arrive i (Prologue.initObject l cta (readySlot stage)) tx count release scope)
    (hTensor : ∀ i addr spec, X.TensorIssue i addr spec →
      spec.mbar ≠ Prologue.initObject l cta (readySlot stage))
    (hCommit : ∀ i spec rank, X.Commit i spec →
      TcCommit.target spec rank ≠ some (Prologue.initObject l cta (readySlot stage))) :
    let loc := Prologue.initObject l cta (readySlot stage)
    NoIncObject X loc 64 ∧ ∃ (j : Nat) (poll : Record Ref),
      (X.objects loc)[j]? = some poll ∧
      poll.id = .thread wait ∧ poll.reply.waited = some true := by
  dsimp only
  let loc := Prologue.initObject l cta (readySlot stage)
  have hAction : objectAction X X.async loc (.thread wait) = some (.pollParity parity true) := by
    change objectAction X X.async (Prologue.initObject l cta (readySlot stage)) (.thread wait) = _
    simp [objectAction, hWait]
  obtain ⟨poll, hMem, hId⟩ := (hX.tma.2.2.1 loc).2.2 _ _ hAction
  have hAct := ((hX.tma.2.2.1 loc).2.1 poll hMem).1
  rw [hId, hAction] at hAct
  have hObject := readyHistoryObject hp hX stage hMem hArrive hTensor hCommit
  have hInit := hObject.init
  have hClean := PairTmaRing.poll_clean hX hInit hObject.noInval poll hMem
    ⟨parity, true, (Option.some.inj hAct).symm⟩
  have hSuccess := (hX.object_thread_waited_iff hMem hId hClean).mpr
    (by simp [hWait, sourceWaitSuccess, loc])
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hMem
  exact ⟨hObject, j, poll, hj, hId, hSuccess⟩

/-- A selected consumer's acquire observes the generation indexed by its prior successful
acquires when producer run-ahead is bounded by the available arrival units. -/
theorem readyAcquireExactPhase {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc} (hObject : NoIncObject X loc 64)
    (selected : Ref → Bool)
    (hAlternates : SelectedAlternates selected (X.objects loc) 0)
    {j : Nat} {poll : Record Ref} (hRecord : (X.objects loc)[j]? = some poll)
    (hSelected : selected poll.id = true) (hSuccess : poll.reply.waited = some true)
    (hUnits : unitsBefore (X.objects loc) j <
      64 * (selectedBefore selected (X.objects loc) j + 2)) :
    observedAt (X.objects loc) j = some (selectedBefore selected (X.objects loc) j) := by
  have hChecked := X.objects_checked hX loc
  obtain ⟨state, hBefore, hPhase⟩ := hChecked.selected_poll_phase_of_units hObject.noInval
    selected (by decide) hAlternates hRecord hSelected hSuccess (fun st hs => by
      rw [PairTmaRing.expected_of_init hX hObject.init hObject.noInval hs]
      simpa using hUnits)
  obtain ⟨st, _, hs, _, _, hComplete⟩ := hChecked.okPoll hRecord hSuccess
  rw [hBefore] at hs
  obtain rfl := Option.some.inj hs
  have hPos : 0 < state.phase := by omega
  have hGeneration : state.phase - 1 = selectedBefore selected (X.objects loc) j := by omega
  simp [observedAt, hRecord, hComplete, hPos, hGeneration]

end
end PTX.Kernels.TmlFa4Fwd.Loader
