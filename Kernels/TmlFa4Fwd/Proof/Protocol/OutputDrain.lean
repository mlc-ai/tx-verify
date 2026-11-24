-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Drain
public import Kernels.TmlFa4Fwd.Proof.TerminalSite
public import Lemmas.Flow.BulkCount
public import Lemmas.Kernel.ExitChain
public import Kernels.TmlFa4Fwd.Proof.Thread.TensorForms
public import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Lemmas.Step.BulkWaitReady
public import Lemmas.Step.StoreDoneInOrder
public import Lemmas.Kernel.SharedLifetime
public import Lemmas.TensorStore.SourceBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX
open PTX.EventFrame PTX.Flow PTX.Proof in

/-- If the issuing CTA has exited, an actual output issue is covered by a later read wait
that the issuing lane passed on its way to exit. -/
theorem drainWaitBeforeExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {addr : Nat}
    {spec : TensorStore.Spec} (hIssue : X.TensorStoreIssue i addr spec)
    (hx : CtaExited l X (i.1 / l.block)) :
    ∃ waiter finish, BulkWaitsFor X .read i waiter ∧ Returned X waiter ∧
      Resumes kernel X waiter finish ∧ OwnerExit l X (i.1 / l.block) finish := by
  obtain ⟨g, k⟩ := i
  obtain ⟨site, he⟩ := hIssue
  have hk := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1
  have hg : g < l.threads := by
    by_contra h
    rw [hX.outside g (by omega)] at hk
    simp at hk
  obtain ⟨finishPc, hl⟩ := hx g hg rfl
  let finish := (X.tr g).length - 1
  have hFinish : X.get (g, finish) = some ⟨finishPc, .exit⟩ := by
    simpa only [List.getLast?_eq_getElem?, Execution.get, finish] using hl
  obtain rfl := actualExitPc hX hFinish
  obtain ⟨c, w, hKC, hCW, hReturned, hC, hW⟩ := Proof2.Epilogue.commit_wait hp hX he hl
  have hCount : commits ((X.tr g).take k) < commits ((X.tr g).take w) := by
    have monotone (a b : Nat) (hle : a ≤ b) :
        commits ((X.tr g).take a) ≤ commits ((X.tr g).take b) := by
      exact (List.take_sublist_take_left hle).countP_le
    have hBefore := monotone k c hKC.le
    have hAfter := monotone (c + 1) w (by omega)
    have hCommit : commits ((X.tr g).take (c + 1)) = commits ((X.tr g).take c) + 1 := by
      rw [List.take_add_one, show (X.tr g)[c]? = _ from hC]
      simp [commits, List.countP_append, isCommit]
    omega
  have hWait : BulkWaitsFor X .read (g, k) (g, w) :=
    ⟨2984, 0, hW, observes_of_commits he (hKC.trans hCW) (by simpa using hCount)⟩
  have hAfter : w < finish := by dsimp [finish]; omega
  refine ⟨(g, w), (g, finish), hWait, ?_, ?_, hg, rfl, 9205, hFinish⟩
  · simpa only [Returned, hW, Kind.resume] using hReturned
  · exact Resumes.of_blocking hW (b := false) rfl
      ⟨rfl, hAfter, show finish < (X.tr g).length by dsimp [finish]; omega⟩


/-- An actual output store finishes reading its shared source before its issuing CTA exits.
The exit follows a returned bulk-group wait that observes the store's read completion. -/
theorem storeReadsFinished {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {addr : Nat}
    {spec : TensorStore.Spec} (hIssue : X.TensorStoreIssue i addr spec)
    (hx : CtaExited l X (i.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async i .readsDone) (i.1 / l.block) := by
  obtain ⟨waiter, finish, hWait, hReturned, hResumes, hExit⟩ :=
    drainWaitBeforeExit hp hX hIssue hx
  obtain ⟨site, he⟩ := hIssue
  have hStage : AsyncCopy.Part.readsDone ∈ GroupWaitStages X i (.bulk .read) := by
    simp [GroupWaitStages, he]
  have hNeed := Step.BulkWait.stage_need (L := l) hWait hStage
  obtain ⟨present, hPresent, rfl⟩ := hX.dependency.ready waiter hReturned _ hNeed
  exact SharedFinished.of_observer_exit hPresent
    (Step.BulkWait.witness_of_waitsFor hWait hStage hPresent) hResumes hExit

/-- Any performed source byte of an output store is finished before the issuing CTA exits. -/
theorem storeReadFinished {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {addr x y k : Nat}
    {spec : TensorStore.Spec} (hIssue : X.TensorStoreIssue i addr spec)
    (hRead : X.AsyncPresent i (.read (.store x y k))) (hx : CtaExited l X (i.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async i (.read (.store x y k)))
      (i.1 / l.block) := by
  have h := storeReadsFinished hp hX hIssue hx
  exact SharedFinished.of_stage (j := i) (q := .readsDone) hRead
    (.inr ⟨rfl, rfl, rfl, hRead, h.1⟩) h

variable {l : Launch} {m : Mem0} {X : Execution} (hMax : Maximal l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {spec : TensorStore.Spec} (hIssue : X.TensorStoreIssue i addr spec)
include hMax hIssue

/-- A maximal output store with visible input bytes cannot still be pending. -/
theorem storeFullyDoneOfVisibleSources (hSource : Step.StoreDone.VisibleReadSources l X i spec)
    (hGuarded : SyncGuarded l kernel X) : X.AsyncPresent i .fullDone := by
  by_contra hPending
  have hForm := Thread.actualTensorStoreForm hMax.1 hIssue
  obtain ⟨Y, hY, hExtends, hGrows⟩ :=
    Step.StoreDone.pending_issue_visible_inOrder Assumptions.wfStep hMax.1
      ⟨addr, hIssue⟩ hForm.1 hPending hSource hGuarded hForm.2.2
  exact (Nat.not_lt_of_ge (hMax.2 Y hY hExtends)) hGrows

/-- A maximal output store can use its staging protocol's ordered source for each
backed slot, including a slot whose earlier writes were ordered through an MMA commit. -/
theorem storeFullyDoneOfOrderedSources
    (hSources : ∀ slot dest, TensorStore.destination spec slot = some dest →
      ∃ writer access bytes value,
        SourceOrdered l X (storeSlotReadRef i slot) (spec.sharedLoc slot) writer access bytes ∧
          wbyte access bytes (spec.sharedLoc slot) = some value) (hGuarded : SyncGuarded l kernel X)
    : X.AsyncPresent i .fullDone := by
  by_contra pending
  have form := Thread.actualTensorStoreForm hMax.1 hIssue
  let sources (Y : Execution) (s : TensorStore.Spec) : Prop :=
    SyncGuarded l kernel Y ∧ s.reduce = none ∧
      ∀ slot dest, TensorStore.destination s slot = some dest →
        ∃ writer access bytes value,
          SourceOrdered l Y (storeSlotReadRef i slot) (s.sharedLoc slot) writer access bytes ∧
            wbyte access bytes (s.sharedLoc slot) = some value
  have initSources {Y : Execution} (empty : Y.tensorStores i = none)
      (h : sources Y spec) : sources (Y.initStoreObservation i spec) spec := by
    obtain ⟨guarded, plain, allSlots⟩ := h
    refine ⟨⟨guarded.spin, guarded.noMemSync, guarded.noFault⟩, plain, fun slot dest backed => ?_⟩
    obtain ⟨writer, access, bytes, value, ⟨written, cover, visible, order⟩, contents⟩ :=
      allSlots slot dest backed
    refine ⟨writer, access, bytes, value, ⟨(storeInit_writes empty _ _ _).mpr written, cover,
      (storeInit_byteCausality empty _ _ _).mpr visible, ?_⟩, contents⟩
    intro other footprint data writes covers
    exact (order other footprint data ((storeInit_writes empty _ _ _).mp writes) covers).imp
      id (fun h => h.imp (storeInit_byteCausality empty _ _ _).mpr
        (storeInit_byteCausality empty _ _ _).mpr)
  obtain ⟨Y, hY, hExtends, grows⟩ :=
    Step.StoreDone.pending_issue_of_inOrder sources initSources
      (fun {Y o} hY ho notDone ⟨guarded, plain, allSlots⟩ => by
        refine Step.StoreDone.pending_observation_of_read_progress_inOrder Assumptions.wfStep
          hY ho notDone ?_ (fun _ h => by rw [plain] at h; cases h)
        intro slot dest backed missing
        obtain ⟨writer, access, bytes, value, ⟨written, cover, _, order⟩, contents⟩ :=
          allSlots slot dest backed
        refine Step.StoreDone.read_of_latest_writer_counted_inOrder Assumptions.wfStep
          hY ho backed missing written cover contents ?_
        intro other footprint data writes covers visible after
        have acyclic := ByteCausality.acyclic hY.effectValidity hY.object
          (DepStepAcyclic.of_dependency hY.dependency) guarded hY.guardOk (o.spec.sharedLoc slot)
        rcases order other footprint data writes covers with rfl | earlier | later
        · exact acyclic _ (.single after)
        · exact acyclic _ ((Relation.TransGen.single after).tail earlier)
        · exact acyclic _ ((Relation.TransGen.single visible).tail later))
      Assumptions.wfStep hMax.1 ⟨addr, hIssue⟩ form.1 pending ⟨hGuarded, form.2.2, hSources⟩
  exact (Nat.not_lt_of_ge (hMax.2 Y hY hExtends)) grows

/-- At an exited CTA, a maximal execution has completed the output store's global writes.
The returned read wait already supplies every source byte needed for counted progress. -/
theorem storeFullyDoneAtExit {p : Params} (hp : Pre p l m) (hx : CtaExited l X (i.1 / l.block)) :
    X.AsyncPresent i .fullDone := by
  have hFinished := storeReadsFinished hp hMax.1 hIssue hx
  obtain ⟨o, ho, hReads⟩ := hFinished.1
  cases hFull : o.effects.fullDone with
  | true => exact ⟨o, ho, hFull⟩
  | false =>
    obtain ⟨⟨address, hActual⟩, _, hCopy⟩ := hMax.1.store i o ho
    have hReduce := (Thread.actualTensorStoreForm hMax.1 hActual).2.2
    obtain ⟨Y, hY, hExtends, hGrows⟩ :=
      Step.StoreDone.pending_observation_of_read_progress_inOrder Assumptions.wfStep
        hMax.1 ho hFull
        (fun slot loc hDst hMissing => by
          obtain ⟨byte, hByte⟩ := hCopy.readsComplete hReads slot loc hDst
          rw [hByte] at hMissing
          cases hMissing)
        (fun red hRed => by rw [hReduce] at hRed; cases hRed)
    exact ((Nat.not_lt_of_ge (hMax.2 Y hY hExtends)) hGrows).elim

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
