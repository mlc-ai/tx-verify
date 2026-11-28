-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Exit
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll
import Lemmas.Kernel.SharedLifetime
public import Lemmas.Kernel.SharedEnabled
import Lemmas.Async.AsyncOrigins

@[expose] public section

/-! # An observed update finishes before its observer exits

A successful poll `w` that observes the update `x` of an object (`WaitObserves`) is a canonical
spin: it resumes the lane's exit, so `x`'s completion is before that exit in the lifetime order of
the object (the object's order from `x` to `w`, then the dependency edge). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.AsyncCopy

variable {L : Launch} {m : Mem0} {X : Execution}

/-- **A returned poll of an exited lane enables the lane's exit.** -/
theorem exit_after_poll (hX : Consistent L kernel Assumptions.all m X) {w : EvId} {mb : Loc}
    {tag parity : Nat} {acq : Bool} {scope : MbarScope}
    (hw : X.get w = some ⟨tag, .wait mb parity true acq scope⟩)
    (hx : CtaExited L X (w.1 / L.block)) : ∃ finish, OwnerExit L X (w.1 / L.block) finish ∧
      Relation.TransGen (DepStep L kernel X) (.thread w, true) (.thread finish, false) := by
  obtain ⟨finish, he, htrace⟩ := exit_after hX hw (by simp) hx
  obtain ⟨_, hspin⟩ := poll_canonical hX hw
  exact ⟨finish, he, .single (DepStep.of_resumes L
    (Resumes.of_spin hw hspin htrace.1 htrace.2.1 htrace.2.2))⟩

/-- **An update a poll observes is enabled before an exit of the polling lane's CTA**: the
object's order from the update to the poll, then the dependency edge. -/
theorem observed_enabled (hX : Consistent L kernel Assumptions.all m X) {ref} {w : EvId}
    {mb : Loc} {acq : Bool} {scope : MbarScope} (hw : WaitObserves X ref w mb acq scope)
    (hx : CtaExited L X (w.1 / L.block)) :
    SharedEnabled L kernel Assumptions.all X (w.1 / L.block) ref := by
  obtain ⟨⟨tag, parity, he⟩, i, j, ri, rj, _, hi, hid, _, hj, hjd, _, _, hij, _, _, _⟩ := hw
  have hp := object_record_present hX.tma (List.mem_of_getElem? hi)
  rw [hid] at hp
  obtain ⟨finish, hExit, hPath⟩ := exit_after_poll hX he hx
  exact ⟨hp, finish, hExit, .inl ⟨.mbar mb, trivial,
    .head (.inr (.inl ⟨rfl, rfl, i, j, ri, rj, hi, hid, hj, hjd, hij⟩))
      (Relation.TransGen.mono (fun _ _ => Or.inl) _ _ hPath)⟩⟩

/-- **An update a poll observes finishes before the polling lane's exit.** -/
theorem observed_finished (hX : Consistent L kernel Assumptions.all m X) {ref} {w : EvId}
    {mb : Loc} {acq : Bool} {scope : MbarScope} (hw : WaitObserves X ref w mb acq scope)
    (hx : CtaExited L X (w.1 / L.block)) :
    SharedFinished L kernel Assumptions.all X ref (w.1 / L.block) :=
  (observed_enabled hX hw hx).finished

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
