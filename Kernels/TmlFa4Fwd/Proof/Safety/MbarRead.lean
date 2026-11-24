-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TensorMbar
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedByteRange
import Kernels.TmlFa4Fwd.Proof.Thread.TensorForms

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety

open PTX

/-- Actual ordinary and asynchronous reads have no byte in a barrier object. -/
theorem mbarReadDisjoint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : AsyncCopy.Ref} {user : EvId} {a : Acc} {loc object : Loc}
    (hUse : X.UsesMbar user object) (hRead : X.Intent issue a false)
    (hCover : a.Covers loc) (hOverlap : Acc.Covers {loc := object, size := 8} loc) :
    False := by
  obtain ⟨_, hObj⟩ := actualMbarAddresses hp hX user object hUse
  have hLocShared : loc.space = .shared := hOverlap.1.trans (congrArg Loc.space hObj)
  have hShared : a.loc.space = .shared := hCover.1.symm.trans hLocShared
  have outside (hLo : l.sharedBase + 352 ≤ a.loc.addr) : False := by
    have hBegin := hCover.2.2.1
    have hEnd : loc.addr < object.addr + 8 := hOverlap.2.2.2
    have hBarrier := actualMbarAddressBound hp hX hUse
    omega
  cases issue with
  | thread i =>
    rcases hRead with ⟨bytes, hBytes, _⟩ | ⟨_, _, hBad⟩ | ⟨_, _, hRmw⟩
    · rcases Thread.sharedReadObservation hX hBytes hShared with
        hAlloc | ⟨repeated, vector, hBias⟩ | ⟨stage, kind, hStats⟩
      · obtain ⟨g, j⟩ := i
        have hExact : a = {loc := Mma.allocationSlot l g, size := 4} :=
          Mma.allocationReadFootprint hp hX hAlloc
        exact (Thread.allocationSlotOutsideMbar hp hX (hCover := hExact ▸ hCover) hUse
          hOverlap).elim
      · have hLo := (Thread.Scores.biasVectorReadLower hp hX hBias).1
        exact outside (by omega)
      · have hLo := (Thread.Correction.statisticsReadLower hp hX hStats).1
        exact outside (by omega)
    · cases hBad
    · exact (noActualRmw hX hRmw).elim
  | async i part =>
    obtain ⟨hMode, hFoot⟩ := hRead
    cases part <;> simp only [AsyncCopy.Part.writes, Bool.false_eq_true] at hMode <;>
      try (exact False.elim hFoot)
    case mmaRead isB index =>
      have hLower := (Thread.mmaSharedByteRange hp hX hFoot.2).lower
      exact outside (by omega)
    case readStore x y k =>
      exact (tensorSharedFootprintsOutsideMbar hp hX hUse (.inr hFoot) hCover hOverlap).elim
    case readLoad x y k =>
      obtain ⟨_, _, _, hLoc, _⟩ := hFoot
      rw [Execution.tensor_readLoc_global hLoc] at hShared
      cases hShared
    case readPrefetch x y k =>
      obtain ⟨_, _, _, hLoc, _⟩ := hFoot
      rw [TensorTransfer.sourceLoc_global hLoc] at hShared
      cases hShared
    case readCopy =>
      rcases hFoot with ⟨spec, hCopy, rfl⟩ | hPrefetch
      · rw [(actualCopyShape hX hCopy).srcGlobal] at hShared
        cases hShared
      · exact (Thread.noBulkPrefetch hX hPrefetch).elim
    case oldStore x y k =>
      obtain ⟨_, _, _, _, hLoc, _⟩ := hFoot
      rw [Execution.store_writeLoc_global hLoc] at hShared
      cases hShared
    case oldElem j =>
      obtain ⟨spec, _, hCopy, hReduce, _⟩ := hFoot
      rw [(actualCopyShape hX hCopy).whole] at hReduce
      cases hReduce

end PTX.Kernels.TmlFa4Fwd.Safety
