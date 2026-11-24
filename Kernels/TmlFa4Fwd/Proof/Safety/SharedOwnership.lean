-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.StageOwnership
public import Kernels.TmlFa4Fwd.Proof.Safety.TensorShared
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocal
public import Kernels.TmlFa4Fwd.Proof.Thread.TensorForms
public import Lemmas.Protocol.RegionOrder
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX

private theorem noTcCopy : kernel.NoTcCp = true := by decide +kernel

/-- Every shared footprint of an asynchronous stage stays in its issuer's CTA. -/
theorem asyncFootprintOwnsShared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {part : AsyncCopy.Part} {a : Acc}
    (hFoot : X.AsyncFootprint i part a) (hSpace : a.loc.space = .shared) :
    a.loc.cta = i.1 / l.block := by
  cases part <;> try (exact False.elim hFoot)
  case mmaRead isB index =>
    rcases hFoot.2 with ⟨_, s, _, _, hi, hByte⟩ | ⟨cp, _, _, hi, _⟩
    · obtain ⟨hLow, hHigh⟩ := mmaOperandOwners hp hX hi
      exact (TcMma.OperandSpec.byteLoc_cta hByte).elim (·.trans hLow) (·.trans hHigh)
    · exact (noCp_of_consistent noTcCopy hX i cp hi).elim
  case readCopy =>
    rcases hFoot with ⟨s, hi, rfl⟩ | hPrefetch
    · rw [(actualCopyShape hX hi).srcGlobal] at hSpace
      cases hSpace
    · exact (Thread.noBulkPrefetch hX hPrefetch).elim
  case readStore x y k =>
    obtain ⟨s, _, hi, hl, _⟩ := hFoot
    obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp hl
    obtain ⟨_, _, _, hAt⟩ := actualTensorOutputSharedRange hp hX hi slot
    exact congrArg Loc.cta (hLoc.symm.trans hAt)
  case readLoad x y k =>
    obtain ⟨_, _, _, hl, _⟩ := hFoot
    rw [Execution.tensor_readLoc_global hl] at hSpace
    cases hSpace
  case readPrefetch x y k =>
    obtain ⟨_, _, _, hl, _⟩ := hFoot
    rw [TensorTransfer.sourceLoc_global hl] at hSpace
    cases hSpace
  case writeCopy =>
    obtain ⟨s, hi, _, rfl⟩ := hFoot
    exact (actualCopyFrame hX hi).2
  case writeElem index =>
    obtain ⟨s, hi, hAt⟩ := hFoot
    simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, (actualCopyShape hX hi).whole] at hAt
  case writeStore x y k =>
    obtain ⟨_, _, _, hl, _⟩ := hFoot
    rw [Execution.store_writeLoc_global hl] at hSpace
    cases hSpace
  case writeLoad x y k =>
    obtain ⟨s, _, hi, hl, _⟩ := hFoot
    obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp hl
    obtain ⟨_, _, _, hAt⟩ := actualTensorInputSharedRange hp hX hi slot
    exact congrArg Loc.cta (hLoc.symm.trans hAt)
  case writeCta owner =>
    obtain ⟨_, _, hi, _, _⟩ := hFoot
    exact (noClcIssue hX hi).elim
  case oldElem index =>
    obtain ⟨s, _, hi, hw, _⟩ := hFoot
    rw [(actualCopyShape hX hi).whole] at hw
    cases hw
  case oldStore x y k =>
    obtain ⟨_, _, _, _, hl, _⟩ := hFoot
    rw [Execution.store_writeLoc_global hl] at hSpace
    cases hSpace

/-- Every shared-memory user is in the owner CTA, including stages that have yet to run. -/
theorem sharedUseOwnsShared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {ref : AsyncCopy.Ref} {owner : Nat} (hUse : SharedUse l X ref owner) :
    owner = ref.issuer.1 / l.block := by
  rcases hUse with ⟨_, ⟨a, w, hIntent, hSpace, hOwner⟩ | ⟨addr, act, hAction⟩⟩ |
    ⟨i, s, rfl, hi, hGroup⟩ | ⟨i, _, s, _, _, _, rfl, hi, _, hOwner⟩ |
    ⟨i, _, s, rfl, hi, hOwner⟩ | ⟨i, part, rfl, hStage, hStageUse⟩
  · rw [← hOwner]
    cases ref with
    | thread i =>
      rcases hIntent with ⟨_, hRead, _⟩ | ⟨_, hWrite, _⟩ | ⟨_, _, hRmw⟩
      · exact Thread.Loader.sharedReadOwned hX hRead hSpace
      · exact sharedWriteOwned hX hWrite hSpace
      · exact (noActualRmw hX hRmw).elim
    | async i part => exact asyncFootprintOwnsShared hp hX hIntent.2 hSpace
  · obtain ⟨r, hr, rfl⟩ := (hX.tma.2.2.1 ⟨.shared, owner, addr⟩).2.2 ref act hAction
    exact mbarRecordOwner hp hX hr
  · exact sameClusterOwner hp hGroup.1
  · exact hOwner.symm.trans (sameClusterOwner hp (actualTensorRoute hX hi).2.2.2.1)
  · obtain ⟨_, _, stage, box, hBase⟩ := OutputWarp.storeBox hp hX hi
    rw [hBase] at hOwner
    exact hOwner.symm
  · exact finalStageOwnsShared hp hX hStage hStageUse

end PTX.Kernels.TmlFa4Fwd.Safety
