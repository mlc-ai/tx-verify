-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaStartup
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsStoreGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX Prologue

/-- Ordinary shared writes above the scratch words are actual correction staging writes. -/
theorem ordinarySharedWriteBelowOrStaging {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {loc : Loc} {data : List Byte} (hWrite : X.Writes i a data)
    (hCover : a.Covers loc) (hShared : loc.space = .shared) :
    loc.addr < l.sharedBase + 3072 ∨ Correction.StagingWrite X (.thread i) a data := by
  rcases sharedWriteSite hX hWrite (hCover.1.symm.trans hShared) with
    hAlloc | ⟨site, hStats⟩ | ⟨stage, box, chunk, hStage⟩
  · exact .inl (allocatorWriteBelowScratchLimit hp hX hAlloc hCover)
  · left
    obtain ⟨warp, _, hFoot⟩ := Scores.statisticsStoreFootprint hp hX site hStats
    have hend := hCover.2.2.2
    rw [hFoot] at hend
    change loc.addr <
      l.sharedBase + 4 * (32 * warp.val + laneOf l i.1) +
        (Softmax.statsStore site).offset + 4 at hend
    have hw := warp.isLt
    have hl : laneOf l i.1 < 32 := Nat.mod_lt _ (by decide)
    have hOff := (by decide : ∀ j : Fin 4, (Softmax.statsStore j).offset ≤ 1392) site
    omega
  · exact .inr (Correction.StagingWrite.of_event stage box chunk hStage)

/-- Every actual shared store byte is in the allocated instance of the shared layout. -/
theorem ordinarySharedWriteBounds {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {loc : Loc} {data : List Byte} (hWrite : X.Writes i a data)
    (hCover : a.Covers loc) (hShared : loc.space = .shared) :
    l.sharedBase ≤ loc.addr ∧ loc.addr < l.sharedBase + 232448 := by
  have hSpace := hCover.1.symm.trans hShared
  obtain ⟨_, _, hLo, hHi⟩ := hCover
  rcases sharedWriteSite hX hWrite hSpace with
    hAlloc | ⟨site, hStats⟩ | ⟨stage, box, chunk, hStage⟩
  · rw [(allocatorStoreOrigin hp hX hAlloc).1] at hLo hHi
    change l.sharedBase + 312 ≤ loc.addr at hLo
    change loc.addr < l.sharedBase + 312 + 4 at hHi
    omega
  · obtain ⟨warp, _, hFoot⟩ := Scores.statisticsStoreFootprint hp hX site hStats
    rw [hFoot] at hLo hHi
    change l.sharedBase + 4 * (32 * warp.val + laneOf l i.1) +
      (Softmax.statsStore site).offset ≤ loc.addr at hLo
    change loc.addr < l.sharedBase + 4 * (32 * warp.val + laneOf l i.1) +
      (Softmax.statsStore site).offset + 4 at hHi
    have hw := warp.isLt
    have hl : laneOf l i.1 < 32 := Nat.mod_lt _ (by decide)
    have hOff := (by decide : ∀ j : Fin 4, (Softmax.statsStore j).offset ≤ 1392) site
    omega
  · obtain ⟨element, hFoot⟩ := Correction.stagingWriteElement hp hX stage box chunk hStage
    rw [hFoot] at hLo hHi
    have hx : 4 * chunk.val + element.val < 32 := by
      have hChunk := chunk.isLt
      have hElement := element.isLt
      omega
    have hRow : TmlFa4Fwd.Correction.rowOf l i.1 < 128 := Nat.mod_lt _ (by decide)
    have hXor : (4 * chunk.val + element.val) / 4 ^^^
        (TmlFa4Fwd.Correction.rowOf l i.1) % 8 < 2 ^ 3 :=
      Nat.xor_lt_two_pow (by omega) (by omega)
    have hs := stage.isLt
    have hb := box.isLt
    simp only [TmlFa4Fwd.Correction.outputElementAccess,
      TmlFa4Fwd.Correction.outputChunkLoc, Epilogue.sharedSlot, Loc.at] at hLo hHi
    omega

/-- The four-byte allocation result slot is disjoint from every barrier object. -/
theorem allocationSlotOutsideMbar {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {user : EvId} {loc object : Loc} (hUse : X.UsesMbar user object)
    (hCover : Acc.Covers {loc := Mma.allocationSlot l g, size := 4} loc) :
    ¬ Acc.Covers {loc := object, size := 8} loc := by
  intro hOverlap
  obtain ⟨init, hObject⟩ := actualMbarAddresses hp hX user object hUse
  have hAddr := congrArg Loc.addr hObject
  change object.addr = l.sharedBase + (initSite init).baseOffset +
    (initSite init).displacement at hAddr
  have hApart : ∀ j : Fin 34, (initSite j).baseOffset + (initSite j).displacement + 8 ≤ 312 ∨
      316 ≤ (initSite j).baseOffset + (initSite j).displacement := by decide
  have hLo : l.sharedBase + 312 ≤ loc.addr := hCover.2.2.1
  have hEnd : loc.addr < l.sharedBase + 312 + 4 := hCover.2.2.2
  have hOther : object.addr ≤ loc.addr := hOverlap.2.2.1
  have hHi : loc.addr < object.addr + 8 := hOverlap.2.2.2
  rcases hApart init with h | h <;> omega

/-- An ordinary shared write uses the allocator result slot, statistics, or output data.
None of those bytes belong to a published barrier's storage. -/
theorem ordinarySharedWriteOutsideMbar {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i user : EvId} {a : Acc} {loc object : Loc} {data : List Byte}
    (hWrite : X.Writes i a data) (hCover : a.Covers loc) (hUse : X.UsesMbar user object) :
    ¬ Acc.Covers {loc := object, size := 8} loc := by
  intro hOverlap
  obtain ⟨_, hObject⟩ := actualMbarAddresses hp hX user object hUse
  have hSpace : loc.space = .shared := hOverlap.1.trans (congrArg Loc.space hObject)
  have hUpper := actualMbarAddressBound hp hX hUse
  have hLow := hCover.2.2.1
  have hHi : loc.addr < object.addr + 8 := hOverlap.2.2.2
  rcases sharedWriteSite hX hWrite (hCover.1.symm.trans hSpace) with
    hAlloc | ⟨site, hStats⟩ | ⟨stage, box, chunk, hStage⟩
  · exact allocationSlotOutsideMbar hp hX hUse
      (by simpa only [(allocatorStoreOrigin hp hX hAlloc).1] using hCover) hOverlap
  · obtain ⟨warp, _, hFoot⟩ := Scores.statisticsStoreFootprint hp hX site hStats
    rw [hFoot] at hLow
    change l.sharedBase + 4 * (32 * warp.val + laneOf l i.1) +
      (Softmax.statsStore site).offset ≤ loc.addr at hLow
    have hMin := (by decide : ∀ j : Fin 4, 368 ≤ (Softmax.statsStore j).offset) site
    omega
  · obtain ⟨element, hFoot⟩ := Correction.stagingWriteElement hp hX stage box chunk hStage
    rw [hFoot] at hLow
    simp only [TmlFa4Fwd.Correction.outputElementAccess,
      TmlFa4Fwd.Correction.outputChunkLoc, Epilogue.sharedSlot, Loc.at] at hLow
    change _ ≤ loc.addr at hLow
    omega

end PTX.Kernels.TmlFa4Fwd.Thread
