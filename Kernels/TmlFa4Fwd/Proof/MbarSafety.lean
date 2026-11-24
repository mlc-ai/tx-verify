-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Lemmas.Protocol.PairTmaRing.ItemFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX Prologue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Every issued mbarrier operand has a published initializer in the actual execution. -/
theorem noMbarUninit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    ¬ MbarUninit l X :=
  noUninitializedMbarOfAddresses hp hX (actualMbarAddresses hp hX)

private theorem recordNamesOperand {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc} {r : MBarrier.Record AsyncCopy.Ref}
    (hr : r ∈ X.objects loc) : X.UsesMbar r.id.issuer loc := by
  cases AsyncCopy.record_source hX.tma.2.2.1 hr with
  | init hi he _ => rw [hi]; exact Execution.UsesMbar.of_init ⟨_, he⟩
  | inval hi he _ => rw [hi]; exact Execution.UsesMbar.of_inval ⟨_, he⟩
  | arrive hi he _ => rw [hi]; exact .inl ⟨_, _, _, _, _, he⟩
  | wait hi he _ => rw [hi]; exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, he⟩))))
  | increment hi he _ => rw [hi]; exact .inr (.inr (.inl ⟨_, _, he⟩))
  | tensor hi he hLoc _ =>
    rw [hi, ← hLoc]
    exact Execution.UsesMbar.of_tensor ⟨_, he⟩
  | arriveOn hi he hLoc _ _ =>
    rw [hi, ← hLoc]
    exact .inr (.inr (.inl ⟨_, _, he⟩))
  | bulk hi he hComp _ _ => rw [hi]; exact .inr (.inl ⟨_, ⟨_, he⟩, hComp⟩)
  | commit hi he hTarget _ => rw [hi]; exact .inr (.inr (.inr (.inl ⟨_, _, ⟨_, he⟩, hTarget⟩)))
  | clc hi he hLoc hCta _ =>
    rw [hi, hLoc]
    exact Execution.UsesMbar.of_clc ⟨_, he⟩ hCta

/-- Every performed object operation is within the lifetime published by the initial warp. -/
theorem actualObjectPublished (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {loc : Loc} {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ X.objects loc) :
    ObjectPublished l X loc r := by
  obtain ⟨site, rfl⟩ := actualMbarAddresses hp hX _ _ (recordNamesOperand hX hr)
  exact (activeObjectHistory hp hX site hr).2 r hr

/-- Each history of an actual object starts with its decoded initializer. -/
theorem actualObjectInitialized (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {loc : Loc} {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ X.objects loc) :
    ∃ count, PairTmaRing.InitFirst X loc count := by
  obtain ⟨site, hLoc⟩ := actualMbarAddresses hp hX _ _ (recordNamesOperand hX hr)
  rw [hLoc] at hr ⊢
  exact ⟨_, (activeObjectHistory hp hX site hr).1⟩

/-- Actual initializers and parity polls are fault free, regardless of the update history. -/
theorem actualInitOrPollClean (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {loc : Loc} {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ X.objects loc)
    (hAction : (∃ count, r.action = .init count) ∨ ∃ parity ok, r.action = .pollParity parity ok)
    : r.fault = none := by
  obtain ⟨_, hInit⟩ := actualObjectInitialized hp hX hr
  rcases hAction with ⟨_, h⟩ | h
  · exact PairTmaRing.init_clean hInit hr h
  · exact PairTmaRing.poll_clean hX hInit
      (AsyncCopy.objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc) r hr h

end
end PTX.Kernels.TmlFa4Fwd
