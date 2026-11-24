-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetimeUses
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSpins
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceExitTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemAsyncRelease

public section

/-! # Observed asynchronous stages finish before CTA exit -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime

open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A returned canonical poll of an exited lane enables its own final instruction. -/
theorem exit_after_poll (hX : Consistent L kernel Assumptions.all mem0 X)
    {w : EvId} {m : Loc} {tag parity : Nat} {acq : Bool} {scope : MbarScope}
    (hw : X.get w = some ⟨tag, .wait m parity true acq scope⟩)
    (hx : CtaExited L X (ctaOf L w.1)) : ∃ finish, OwnerExit L X (ctaOf L w.1) finish ∧
      Relation.TransGen (DepStep L kernel X) (.thread w, true) (.thread finish, false) := by
  obtain ⟨finish, he, htrace⟩ := exit_after hX hw (by simp) hx
  obtain ⟨_, hspin⟩ := RingSpins.successful_poll hX hw
  exact ⟨finish, he, .single (DepStep.of_resumes L
    (Resumes.of_spin hw hspin htrace.1 htrace.2.1 htrace.2.2))⟩

/-- A performed record's completion precedes an owner exit in the lifetime order of a barrier. -/
@[expose] def RecordExitOrder (L : Launch) (X : Execution) (ref : Ref) (cta : Nat) : Prop :=
  X.RefPresent ref ∧ ∃ finish m, OwnerExit L X cta finish ∧
    Relation.TransGen (LifetimeStep L kernel Assumptions.all X (.mbar m))
      (ref, true) (.thread finish, false)

/-- The barrier-specific order establishes the shared lifetime check. -/
theorem RecordExitOrder.finished {ref : Ref} {cta : Nat}
    (h : RecordExitOrder L X ref cta) : SharedFinished L kernel Assumptions.all X ref cta := by
  obtain ⟨hp, finish, m, hExit, hPath⟩ := h
  exact SharedFinished.of_completedBefore hp hExit (.inl (.inr ⟨.mbar m, trivial, hPath⟩))

/-- An observed record that precedes a successful poll finishes before the polling lane exits. -/
theorem record_exit_order (hX : Consistent L kernel Assumptions.all mem0 X)
    {ref : Ref} {w : EvId} {m : Loc} {acq : Bool} {scope : MbarScope}
    (hp : X.RefPresent ref) (hw : WaitObserves X ref w m acq scope)
    (hx : CtaExited L X (ctaOf L w.1)) :
    RecordExitOrder L X ref (ctaOf L w.1) := by
  obtain ⟨tag, parity, he⟩ := hw.1
  obtain ⟨finish, hExit, hPath⟩ := exit_after_poll hX he hx
  obtain ⟨i, j, ri, rj, _, hi, hid, _, hj, hjd, _, _, hij, _, _, _⟩ := hw.2
  exact ⟨hp, finish, m, hExit,
    .head (.inr (.inl ⟨rfl, rfl, i, j, ri, rj, hi, hid, hj, hjd, hij⟩))
      (Relation.TransGen.mono (fun _ _ => Or.inl) _ _ hPath)⟩

/-- An observed record whose waiter exits satisfies the shared lifetime check. -/
theorem record_finished (hX : Consistent L kernel Assumptions.all mem0 X)
    {ref : Ref} {w : EvId} {m : Loc} {acq : Bool} {scope : MbarScope}
    (hp : X.RefPresent ref) (hw : WaitObserves X ref w m acq scope)
    (hx : CtaExited L X (ctaOf L w.1)) :
    SharedFinished L kernel Assumptions.all X ref (ctaOf L w.1) :=
  (record_exit_order hX hp hw hx).finished

/-- The actual phase observation orders a tensor-load notification before the waiter exits. -/
theorem load_notify_finished (hX : Consistent L kernel Assumptions.all mem0 X)
    {i w : EvId} {acq : Bool} {scope : MbarScope}
    (hObs : AsyncObserved X i (.notify .load) w acq scope)
    (hx : CtaExited L X (ctaOf L w.1)) :
    SharedFinished L kernel Assumptions.all X (.async i (.notify .load)) (ctaOf L w.1) := by
  obtain ⟨o, _, ho, _, hNote, hw⟩ := hObs.tensor
  exact record_finished hX ⟨o, ho, hNote⟩ hw hx

private theorem mma_observed_finished (hX : Consistent L kernel Assumptions.all mem0 X)
    {i w : EvId} {acq : Bool} {scope : MbarScope}
    (hObs : AsyncObserved X i .mmaDone w acq scope)
    (hx : CtaExited L X (ctaOf L w.1)) :
    SharedFinished L kernel Assumptions.all X (.async i .mmaDone) (ctaOf L w.1) := by
  obtain ⟨_, _, _, _, _, _, _, _, hw⟩ := hObs.mma
  obtain ⟨tag, parity, he⟩ := hw.1
  obtain ⟨finish, hExit, hPath⟩ := exit_after_poll hX he hx
  obtain ⟨hp, hb⟩ := CompletedBefore.of_observesMma (A := Assumptions.all)
    hX.tcCommit hObs hPath
  exact SharedFinished.of_completedBefore hp hExit hb

/-- The lane at the head of an exited CTA has an actual deallocation in its trace. -/
theorem dealloc_of_cta_exited (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {c : Nat} (hc : c < L.grid) (hx : CtaExited L X c) :
    ∃ owner j tag, ctaOf L owner = c ∧
      X.get (owner, j) = some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩ := by
  let owner := c * L.block
  have hOwner : owner < L.threads := by
    change c * L.block < L.grid * L.block
    exact Nat.mul_lt_mul_of_pos_right hc (by rw [hpre.block]; decide)
  have hCta : ctaOf L owner = c := by
    simp [owner, ctaOf, hpre.block]
  have hWarp : warpOf L owner = 0 := by
    simp [warpOf, tidOf_eq hpre, owner, hpre.block]
  obtain ⟨tag, hLast⟩ := hx owner hOwner hCta
  rw [List.getLast?_eq_getElem?] at hLast
  have hExit : X.get (owner, (X.tr owner).length - 1) = some ⟨tag, .exit⟩ := hLast
  obtain ⟨j, _, t, hDealloc⟩ := ResourceEvents.dealloc_before_exit hpre hX
    (hs owner hOwner).machine ht hWarp hExit rfl
  exact ⟨owner, j, t, hCta, hDealloc⟩

/-- Every query copy, QK or PV issue completes before the CTA exit that follows deallocation. -/
theorem mma_finished (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    MmaFinished L X := by
  rintro ⟨g, i⟩ hi hx
  obtain ⟨e, hGet⟩ : ∃ e, X.get (g, i) = some e := by
    rcases hi with ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
    all_goals exact ⟨_, h⟩
  have hc : ctaOf L g < L.grid := NamedBar.cta_lt (Frame.lt_of_get hX hGet)
  obtain ⟨owner, j, _, hCta, hDealloc⟩ := dealloc_of_cta_exited hpre hX hs ht hc hx
  obtain ⟨w, _, sc, hObs, _⟩ := tc_async_observed_before_dealloc hpre hX hs ht hi hCta.symm hDealloc
  change SharedFinished L kernel Assumptions.all X (.async (g, i) .mmaDone) (ctaOf L g)
  rw [← hCta]
  exact mma_observed_finished hX hObs (hCta ▸ hx)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime
