-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TensorShared
public import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
public import Lemmas.Protocol.Region

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX

/-- Neither a Q or Bias shared destination nor an O shared source touches a barrier's storage. -/
theorem tensorSharedFootprintsOutsideMbar {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue user : EvId} {x y k : Nat} {a : Acc} {loc object : Loc}
    (hUse : X.UsesMbar user object)
    (hTensor : X.AsyncFootprint issue (.write (.load x y k)) a ∨
      X.AsyncFootprint issue (.read (.store x y k)) a)
    (hCover : a.Covers loc) : ¬ Acc.Covers {loc := object, size := 8} loc := by
  have hBase : l.sharedBase + 3072 ≤ a.loc.addr := by
    rcases hTensor with ⟨load, address, hi, hl, _⟩ | ⟨store, address, hi, hl, _⟩
    · obtain ⟨slot, _, hAt⟩ := Option.map_eq_some_iff.mp hl
      obtain ⟨offset, hLo, _, hLoc⟩ := actualTensorInputSharedRange hp hX hi slot
      rw [← hAt, hLoc]
      exact Nat.add_le_add_left hLo _
    · obtain ⟨slot, _, hAt⟩ := Option.map_eq_some_iff.mp hl
      obtain ⟨offset, hLo, _, hLoc⟩ := actualTensorOutputSharedRange hp hX hi slot
      rw [← hAt, hLoc]
      exact Nat.add_le_add_left hLo _
  have hObject := actualMbarAddressBound hp hX hUse
  intro hOverlap
  have hLo := hCover.2.2.1
  have hHi : loc.addr < object.addr + 8 := hOverlap.2.2.2
  omega

/-- The shared destinations of all ordinary copies are outside the barrier
storage, including when the producing group is still open. -/
theorem ordinaryCopyDestinationsOutsideMbar {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue user : EvId} {spec : AsyncCopy.Spec} {loc object : Loc}
    (hUse : X.UsesMbar user object) (hCopy : X.Copy issue spec)
    (hCover : spec.dst.Covers loc) : ¬ Acc.Covers {loc := object, size := 8} loc := by
  obtain ⟨_, slot, pair, upper, hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
  let address := kvCopyAddress l.sharedBase slot (issue.1 % l.block) pair upper
  have hRing : l.sharedBase + 68608 ≤ address := by
    have := (kvCopyAddress_range hp.shared.1 (lane := issue.1 % l.block) (upper := upper)
      slot.isLt pair.isLt (show 0 < 16 by decide)).1
    simpa only [address, Nat.add_zero] using this
  rw [hDst] at hCover
  have hLower := hCover.2.2.1
  change address ≤ loc.addr at hLower
  have hBarrier := actualMbarAddressBound hp hX hUse
  intro hOverlap
  have hUpper := hOverlap.2.2.2
  change loc.addr < object.addr + 8 at hUpper
  omega

/-- Write intents, including copies that are still pending, avoid all barrier storage. -/
theorem writeIntentOutsideMbar {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : AsyncCopy.Ref} {user : EvId} {a : Acc} {loc object : Loc}
    (hUse : X.UsesMbar user object) (hWrite : X.Intent issue a true)
    (hCover : a.Covers loc) : ¬ Acc.Covers {loc := object, size := 8} loc := by
  intro hOverlap
  obtain ⟨_, hObj⟩ := actualMbarAddresses hp hX user object hUse
  have hShared : a.loc.space = .shared :=
    hCover.1.symm.trans (hOverlap.1.trans (congrArg Loc.space hObj))
  cases issue with
  | thread i =>
    rcases hWrite with ⟨_, _, hNot⟩ | ⟨_, hw, _⟩ | ⟨_, _, hr⟩
    · cases hNot
    · exact Thread.ordinarySharedWriteOutsideMbar hp hX hw hCover hUse hOverlap
    · exact noActualRmw hX hr
  | async i part =>
    obtain ⟨hMode, hFoot⟩ := hWrite
    cases part <;> simp only [AsyncCopy.Part.writes, Bool.true_eq_false] at hMode <;>
      try (exact False.elim hFoot)
    case writeStore x y k =>
      obtain ⟨_, _, _, hLoc, _⟩ := hFoot
      rw [Execution.store_writeLoc_global hLoc] at hShared
      cases hShared
    case writeLoad x y k =>
      exact tensorSharedFootprintsOutsideMbar hp hX hUse (.inl hFoot) hCover hOverlap
    case writeCta c =>
      obtain ⟨_, _, hi, _, _⟩ := hFoot
      exact noClcIssue hX hi
    case writeCopy =>
      obtain ⟨s, hi, _, rfl⟩ := hFoot
      exact ordinaryCopyDestinationsOutsideMbar hp hX hUse hi hCover hOverlap
    case writeElem j =>
      obtain ⟨s, hi, hElem⟩ := hFoot
      simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, (actualCopyShape hX hi).whole]
        at hElem

end PTX.Kernels.TmlFa4Fwd.Safety
