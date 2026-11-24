-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyReadyExtent
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorContinue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- The selected request's extent of acquired cache packets before an output commit. -/
structure SelectedCacheExtent (l : Launch) (p : Params) (X : Execution) (final : EvId) where
  batch : Nat
  batch_lt : batch < p.batch
  cta_lower : tilePrefix p batch * p.heads ≤ final.1 / l.block
  cta_upper : final.1 / l.block < tilePrefix p (batch + 1) * p.heads
  acquires : ∀ use < 2 * trips p batch (assignedCoordinates p batch (final.1 / l.block)).1,
    ∃ wait, TraceBefore X (final.1, wait) final ∧
      ReadyPoll l X final.1 wait (readyStage use) (readyWord use) true .cta ∧
      (atPrefix l X final.1 wait).kvAcquires (readyStage use) = use / 3

/-- An observed scheduler checkpoint with a suffix reaching the terminal
commit supplies every acquisition of the selected request. -/
noncomputable def SelectedCacheExtent.ofSelectedPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {final : EvId} {spec : TcCommit.Spec}
    (hFinal : SecondOutputCommit X final spec)
    {pos batch : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ final.1 / l.block)
    (hHi : final.1 / l.block < tilePrefix p (batch + 1) * p.heads)
    {s : TState} {ending : Option TState} (hs : At s 2109
      [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * ((assignedCoordinates p batch (final.1 / l.block)).1 + 1))),
        (2535, b32 l.sharedBase)])
    (hRun : Run kernel Assumptions.all l final.1 s ((X.tr final.1).drop pos) ending)
    (hReaches : ending = none ∨ pos ≤ final.2) : SelectedCacheExtent l p X final :=
  ⟨batch, hb, hLo, hHi, fun _ hUse =>
    selectedReadyOccurrenceBeforeSecondOutputCommitInPrefix hp hX hFrame hFinal
      hb (assignedCoordinates_valid hp hLo hHi).1 hs hRun hReaches hUse⟩

private theorem recurringVectorLower {e : Event} (h : Loader.recurringVectorEvent e) :
    909 ≤ e.pc := by
  obtain ⟨site, pair, upper, _, rfl⟩ := h
  change 909 ≤ Loader.packetPlanePc (Loader.recurringPacketSite site) pair upper
  fin_cases site <;> fin_cases pair <;> cases upper <;> decide

private theorem primingKeyUpper (pair : Fin 16) (upper : Bool) :
    Loader.kCopyPc pair + (if upper then 1 else 0) < 909 := by
  fin_cases pair <;> cases upper <;> decide

private theorem primingValueUpper (pair : Fin 16) (upper : Bool) :
    Loader.vCopyPc pair + (if upper then 1 else 0) < 909 := by
  fin_cases pair <;> cases upper <;> decide

private theorem recurringVectorUseBound {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {copy : EvId} {e : Event} (he : X.get copy = some e)
    (hVector : Loader.recurringVectorEvent e) {spec : AsyncCopy.Spec}
    (hKind : e.kind = .copy spec) :
    ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ copy.1 / l.block ∧
      copy.1 / l.block < tilePrefix p (batch + 1) * p.heads ∧
      Loader.recurringUseBefore X copy <
        2 * trips p batch (assignedCoordinates p batch (copy.1 / l.block)).1 := by
  have hCopy : X.Copy copy spec := ⟨e.pc, by cases e; cases hKind; exact he⟩
  have hLower := recurringVectorLower hVector
  have hKey : ∀ pair upper, ¬ Loader.PrimingKeyVector X copy pair upper spec := by
    intro pair upper hKey
    have hEvent := Option.some.inj (he.symm.trans hKey)
    rw [hEvent] at hLower
    exact (Nat.not_lt_of_le hLower) (primingKeyUpper pair upper)
  have hValue : ∀ pair upper, ¬ Loader.PrimingValueVector X copy pair upper spec := by
    intro pair upper hValue
    have hEvent := Option.some.inj (he.symm.trans hValue)
    rw [hEvent] at hLower
    exact (Nat.not_lt_of_le hLower) (primingValueUpper pair upper)
  exact Loader.recurringCopyUseBound hp hX hFrame hCopy hKey hValue

/-- An observed recurring cache vector belongs to a CTA with an assigned tile. -/
theorem recurringVectorHasWork {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {copy : EvId} {e : Event} (he : X.get copy = some e)
    (hVector : Loader.recurringVectorEvent e) {spec : AsyncCopy.Spec}
    (hKind : e.kind = .copy spec) :
    copy.1 / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨batch,hb,_,hUpper,_⟩ := recurringVectorUseBound hp hX hFrame he hVector hKind
  exact hUpper.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))

/-- An actual recurring copy in the selected request has its exact successful ready
observation before the given final commit in the consistent prefix. -/
theorem SelectedCacheExtent.readyForRecurringCopy {l : Launch} {p : Params} {m : Mem0}
    {X : Execution} {final : EvId} (extent : SelectedCacheExtent l p X final)
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {output : TcCommit.Spec} (hFinal : SecondOutputCommit X final output)
    {copy : EvId} {e : Event} (he : X.get copy = some e) (hVector : Loader.recurringVectorEvent e)
    {spec : AsyncCopy.Spec} (hKind : e.kind = .copy spec)
    (hCta : copy.1 / l.block = final.1 / l.block) :
    let use := Loader.recurringUseBefore X copy
    ∃ wait, ReadyPoll l X final.1 wait (readyStage use) (readyWord use) true .cta ∧
      readyCount X final.1 wait = use ∧ TraceBefore X (final.1,wait) final := by
  obtain ⟨batch,hBatch,hLo,hHi,hUse⟩ := recurringVectorUseBound hp hX hFrame he hVector hKind
  rw [hCta] at hLo hHi hUse
  have hActive := extent.cta_upper.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt extent.batch_lt)))
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hActive
  have hBatch' : batch = extent.batch := (hUnique batch ⟨hBatch,hLo,hHi⟩).trans
    (hUnique extent.batch ⟨extent.batch_lt,extent.cta_lower,extent.cta_upper⟩).symm
  rw [hBatch'] at hUse
  obtain ⟨wait,hBefore,hReady,hPhase⟩ := extent.acquires _ hUse
  have hw := hFinal.issuerWarp hp hX
  have hThread := event_thread_lt hX hFinal.decoded
  have hCount := readyUsesAtPrefix hp hX hThread hw wait
  have hOccurrence := hReady.exactOccurrence hp hX hw
  change _ = _ ∧ _ = _ ∧ _ = _ at hOccurrence
  rw [← hCount] at hOccurrence
  have hMod := hOccurrence.1
  change (Loader.recurringUseBefore X copy) % 3 = readyCount X final.1 wait % 3 at hMod
  have hDiv := hOccurrence.2.1
  change _ = readyCount X final.1 wait / 3 at hDiv
  rw [hPhase] at hDiv
  exact ⟨wait,hReady,by omega,hBefore⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
