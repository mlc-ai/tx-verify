-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
public import Kernels.TmlFa4Fwd.Proof.Thread.SharedReadSites
public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.AllocationPublication
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup
import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlotGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsStoreGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX Prologue

private inductive WriteCoordinates (l : Launch) (g : Nat) (a : Acc) : Prop
  | allocation (hThread : g % l.block = 384)
      (hAcc : a = {loc := Mma.allocationSlot l g, size := 4})
  | statistics (site : Fin 4) (hThread : g % l.block < 256)
      (hAcc : a = {loc := ⟨.shared, g / l.block,
        l.sharedBase + 4 * (g % l.block) + (Softmax.statsStore site).offset⟩, size := 4})
  | staging (stage : Fin 2) (box : Fin 4) (x : Nat) (hx : x < 32)
      (hThread : 256 ≤ g % l.block ∧ g % l.block < 384)
      (hAcc : a = TmlFa4Fwd.Correction.outputElementAccess l g stage box x
        (TmlFa4Fwd.Correction.rowOf l g))

private theorem writeCoordinates {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {data : List Byte} (hw : X.Writes i a data)
    (hShared : a.loc.space = .shared) : WriteCoordinates l i.1 a := by
  obtain ⟨g,j⟩ := i
  change WriteCoordinates l g a
  rcases sharedWriteSite hX hw hShared with he | ⟨site,he⟩ | ⟨stage,box,chunk,he⟩
  · obtain ⟨hFoot, hLane, _, _⟩ := allocatorStoreOrigin hp hX he
    have hWarp := allocatorStoreWarp hp hX he
    unfold warpIndex at hWarp
    unfold laneOf at hLane
    exact .allocation (by omega) hFoot
  · obtain ⟨warp,hWarp,hAcc⟩ := Scores.statisticsStoreFootprint hp hX site he
    have hLimit := warp.isLt
    change warp.val = g % l.block / 32 at hWarp
    have hLane : 32 * warp.val + laneOf l g = g % l.block := by unfold laneOf; omega
    exact .statistics site (by omega) (by
      rw [hAcc]
      simp only [Softmax.statsAcc, Softmax.statsBase, hLane])
  · obtain ⟨elem,hAcc⟩ := Correction.stagingWriteElement hp hX stage box chunk he
    obtain ⟨hLo,hHi,_,_⟩ := Correction.stagingWriteWarp hp hX stage box chunk he
    change 8 ≤ g % l.block / 32 at hLo
    change g % l.block / 32 < 12 at hHi
    exact .staging stage box (4 * chunk.val + elem.val)
      (by have := chunk.isLt; have := elem.isLt; omega) ⟨by omega, by omega⟩ hAcc

private theorem rangeAllocation {l : Launch} {g : Nat} {loc : Loc}
    (h : ({loc := Mma.allocationSlot l g, size := 4} : Acc).Covers loc) :
    loc.cta = g / l.block ∧ l.sharedBase + 312 ≤ loc.addr ∧ loc.addr < l.sharedBase + 316 := by
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

private def statsByteAccess (l : Launch) (g : Nat) (site : Fin 4) : Acc :=
  {loc := ⟨.shared, g / l.block,
    l.sharedBase + 4 * (g % l.block) + (Softmax.statsStore site).offset⟩, size := 4}

private theorem rangeStatistics {l : Launch} {g : Nat} {site : Fin 4} {loc : Loc}
    (hThread : g % l.block < 256) (h : (statsByteAccess l g site).Covers loc) :
    loc.cta = g / l.block ∧ l.sharedBase + 368 ≤ loc.addr ∧ loc.addr < l.sharedBase + 3072 := by
  have hLo : l.sharedBase + 4 * (g % l.block) + (Softmax.statsStore site).offset ≤ loc.addr :=
    h.2.2.1
  have hHi : loc.addr < l.sharedBase + 4 * (g % l.block) + (Softmax.statsStore site).offset + 4 :=
    h.2.2.2
  have hOff := (show ∀ site : Fin 4,
    368 ≤ (Softmax.statsStore site).offset ∧ (Softmax.statsStore site).offset ≤ 1392 by decide) site
  exact ⟨h.2.1, by omega, by omega⟩

private theorem rangeStaging {l : Launch} {g x : Nat} {stage : Fin 2} {box : Fin 4}
    (hx : x < 32) {loc : Loc} (h : (TmlFa4Fwd.Correction.outputElementAccess l g stage box x
      (TmlFa4Fwd.Correction.rowOf l g)).Covers loc) :
    l.sharedBase + 3072 ≤ loc.addr ∧ loc.addr < l.sharedBase + 134144 := by
  have hRow : TmlFa4Fwd.Correction.rowOf l g < 128 := Nat.mod_lt _ (by decide)
  obtain ⟨hLo,hHi⟩ := Output.elementStageRange hx hRow h
  have hStage := stage.isLt
  omega

private theorem statsSameLane {l : Launch} {g h : Nat} {loc : Loc} {s t : Fin 4}
    (hg : g % l.block < 256) (hh : h % l.block < 256)
    (ha : (statsByteAccess l g s).Covers loc) (hb : (statsByteAccess l h t).Covers loc) :
    g = h := by
  have gLo := ha.2.2.1
  have gHi := ha.2.2.2
  have hLo := hb.2.2.1
  have hHi := hb.2.2.2
  simp only [statsByteAccess] at gLo gHi hLo hHi
  have offsets := (show ∀ site : Fin 4, (Softmax.statsStore site).offset = 368 ∨
    (Softmax.statsStore site).offset = 1392 by decide)
  have hLane : g % l.block = h % l.block := by
    rcases offsets s with hs | hs <;> rcases offsets t with ht | ht <;>
      simp only [hs, ht] at gLo gHi hLo hHi <;> omega
  have hCta : g / l.block = h / l.block := ha.2.1.symm.trans hb.2.1
  exact (Nat.mod_add_div g l.block).symm.trans (by rw [hLane,hCta,Nat.mod_add_div])

private theorem sameStagingLane {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g h x y : Nat} {s t : Fin 2} {box box' : Fin 4} {loc : Loc}
    (hx : x < 32) (hy : y < 32) (hg : 256 ≤ g % l.block ∧ g % l.block < 384)
    (hh : 256 ≤ h % l.block ∧ h % l.block < 384)
    (ha : (TmlFa4Fwd.Correction.outputElementAccess l g s box x
      (TmlFa4Fwd.Correction.rowOf l g)).Covers loc)
    (hb : (TmlFa4Fwd.Correction.outputElementAccess l h t box' y
      (TmlFa4Fwd.Correction.rowOf l h)).Covers loc) : g = h := by
  obtain ⟨hCta, _, _, hRow, _⟩ := Output.sameNormalizedElementOfCover hx hy
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ha hb
  change g % l.block % 128 = h % l.block % 128 at hRow
  rw [hp.block] at hRow hCta hg hh
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- An ordinary writer covering a correction statistics word is the corresponding softmax
lane's store from the same statistics buffer. -/
theorem ordinaryStatisticsWriter {i j : EvId} {a b : Acc} {data : List Byte}
    {bytes : List (Option Byte)} {stage : Fin 2} {kind : TmlFa4Fwd.Correction.StatsKind} {loc : Loc}
    (hw : X.Writes i a data) (hr : Correction.StatisticsRead X j stage kind b bytes)
    (ha : a.Covers loc) (hb : b.Covers loc) :
    i.1 = TmlFa4Fwd.Correction.terminalStatsProducer l j.1 stage ∧
      ∃ site : Fin 4, Scores.StatisticsStore X i site a data ∧
        (Softmax.statsStore site).offset + 512 * stage.val =
          TmlFa4Fwd.Correction.statsOff stage kind := by
  have hShared : a.loc.space = .shared :=
    ha.1.symm.trans (hb.1.trans (by rw [hr.footprint hp hX]; rfl))
  obtain ⟨hReadLo, hReadSize, hReadHi⟩ := Correction.statisticsReadRange hp hX hr
  have hLo := hb.2.2.1
  have hHi := hb.2.2.2
  rcases sharedWriteSite hX hw hShared with hAlloc | ⟨site, hStats⟩ | ⟨s, box, chunk, hStore⟩
  · rw [(allocatorStoreOrigin hp hX hAlloc).1] at ha
    have hEnd := (rangeAllocation ha).2.2
    omega
  · obtain ⟨warp, hWarp, hAcc⟩ := Scores.statisticsStoreFootprint hp hX site hStats
    have hLane : 32 * warp.val + laneOf l i.1 = i.1 % l.block := by
      rw [hWarp]
      unfold warpIndex laneOf
      omega
    have hProducer : i.1 % l.block < 256 := by
      have hWarp := warp.isLt
      have hL : laneOf l i.1 < 32 := Nat.mod_lt _ (by decide)
      omega
    rw [hAcc, Softmax.statsAcc, Softmax.statsBase, hLane] at ha
    rw [hr.footprint hp hX] at hb
    have hCta : i.1 / l.block = j.1 / l.block := ha.2.1.symm.trans hb.2.1
    have hStoreLo : l.sharedBase + 4 * (i.1 % l.block) +
        (Softmax.statsStore site).offset ≤ loc.addr := ha.2.2.1
    have hStoreHi : loc.addr < l.sharedBase + 4 * (i.1 % l.block) +
        (Softmax.statsStore site).offset + 4 := ha.2.2.2
    have hStatsLo : l.sharedBase + 4 * TmlFa4Fwd.Correction.rowOf l j.1 +
        TmlFa4Fwd.Correction.statsOff stage kind ≤ loc.addr := hb.2.2.1
    have hStatsHi : loc.addr < l.sharedBase + 4 * TmlFa4Fwd.Correction.rowOf l j.1 +
        TmlFa4Fwd.Correction.statsOff stage kind + 4 := hb.2.2.2
    have hRow : TmlFa4Fwd.Correction.rowOf l j.1 < 128 := Nat.mod_lt _ (by decide)
    have hStage := stage.isLt
    have hOff := (show ∀ site : Fin 4,
      (Softmax.statsStore site).offset = 368 ∨ (Softmax.statsStore site).offset = 1392
      by decide) site
    have ⟨hRowEq, hOffEq⟩ :
        i.1 % l.block = TmlFa4Fwd.Correction.rowOf l j.1 + 128 * stage.val ∧
          (Softmax.statsStore site).offset + 512 * stage.val =
            TmlFa4Fwd.Correction.statsOff stage kind := by
      cases kind <;> rcases hOff with h | h <;>
        simp [h, TmlFa4Fwd.Correction.statsOff] at hStoreLo hStoreHi hStatsLo hStatsHi ⊢ <;>
        omega
    refine ⟨?_, site, hStats, hOffEq⟩
    unfold TmlFa4Fwd.Correction.terminalStatsProducer
    rw [hp.block] at hCta hRowEq ⊢
    omega
  · obtain ⟨elem, hFoot⟩ := Correction.stagingWriteElement hp hX s box chunk hStore
    have hx : 4 * chunk.val + elem.val < 32 := by
      have := chunk.isLt
      have := elem.isLt
      omega
    rw [hFoot] at ha
    have hBegin := (rangeStaging hx ha).1
    omega

/-- Ordinary stores that overlap in shared memory always belong to one physical lane. -/
theorem ordinarySharedWritersSameLane {i j : EvId} {a b : Acc} {data bytes : List Byte} {loc : Loc}
    (hs : loc.space = .shared) (hi : X.Writes i a data) (hj : X.Writes j b bytes)
    (ha : a.Covers loc) (hb : b.Covers loc) :
    i.1 = j.1 := by
  cases writeCoordinates hp hX hi (ha.1.symm.trans hs) with
  | allocation hLane hFoot =>
    rw [hFoot] at ha
    obtain ⟨hCtaA,hLow,hHigh⟩ := rangeAllocation ha
    cases writeCoordinates hp hX hj (hb.1.symm.trans hs) with
    | allocation hLane' hFoot' =>
      rw [hFoot'] at hb
      have hCta : i.1 / l.block = j.1 / l.block := hCtaA.symm.trans (rangeAllocation hb).1
      exact (Nat.mod_add_div i.1 l.block).symm.trans (by
        rw [hCta,hLane,← hLane',Nat.mod_add_div])
    | statistics site hLane' hFoot' =>
      rw [hFoot'] at hb
      have hLo := (rangeStatistics (site := site) hLane' hb).2.1
      omega
    | staging stage box x hx hLane' hFoot' =>
      rw [hFoot'] at hb
      have hLo := (rangeStaging hx hb).1
      omega
  | statistics site hLane hFoot =>
    rw [hFoot] at ha
    obtain ⟨_,hLow,hHigh⟩ := rangeStatistics (site := site) hLane ha
    cases writeCoordinates hp hX hj (hb.1.symm.trans hs) with
    | allocation hLane' hFoot' =>
      rw [hFoot'] at hb
      have hHi := (rangeAllocation hb).2.2
      omega
    | statistics site' hLane' hFoot' =>
      rw [hFoot'] at hb
      exact statsSameLane (s := site) (t := site') hLane hLane' ha hb
    | staging stage box x hx hLane' hFoot' =>
      rw [hFoot'] at hb
      have hLo := (rangeStaging hx hb).1
      omega
  | staging stage box x hx hLane hFoot =>
    rw [hFoot] at ha
    have hLow := (rangeStaging hx ha).1
    cases writeCoordinates hp hX hj (hb.1.symm.trans hs) with
    | allocation hLane' hFoot' =>
      rw [hFoot'] at hb
      have hHi := (rangeAllocation hb).2.2
      omega
    | statistics site hLane' hFoot' =>
      rw [hFoot'] at hb
      have hHi := (rangeStatistics (site := site) hLane' hb).2.2
      omega
    | staging stage' box' x' hx' hLane' hFoot' =>
      rw [hFoot'] at hb
      exact sameStagingLane hp hx hx' hLane hLane' ha hb

private theorem coveringAllocationWriter {i : EvId} {a : Acc} {data : List Byte} {loc : Loc}
    {g : Nat} (hShared : loc.space = .shared) (hw : X.Writes i a data) (ha : a.Covers loc)
    (hSlot : Acc.Covers {loc := Mma.allocationSlot l g, size := 4} loc) :
    ∃ pos, X.get i = some ⟨1909, .wr a data⟩ ∧ i.2 = pos ∧ pos = 7 := by
  obtain ⟨_,hSlotLo,hSlotHi⟩ := rangeAllocation hSlot
  rcases sharedWriteSite hX hw (ha.1.symm.trans hShared) with he | ⟨site,he⟩ | ⟨stage,box,chunk,he⟩
  · obtain ⟨g',j⟩ := i
    exact ⟨j, he, rfl, (allocatorStoreOrigin hp hX he).2.2.1⟩
  · obtain ⟨warp,hWarp,hAcc⟩ := Scores.statisticsStoreFootprint hp hX site he
    have hLower := ha.2.2.1
    rw [hAcc] at hLower
    change l.sharedBase + 4 * (32 * warp.val + laneOf l i.1) +
      (Softmax.statsStore site).offset ≤ loc.addr at hLower
    have hOff := (show ∀ site : Fin 4, 368 ≤ (Softmax.statsStore site).offset by decide) site
    omega
  · obtain ⟨elem,hAcc⟩ := Correction.stagingWriteElement hp hX stage box chunk he
    rw [hAcc] at ha
    have hX : 4 * chunk.val + elem.val < 32 := by
      have := elem.isLt
      have := chunk.isLt
      omega
    have hLo := (rangeStaging hX ha).1
    omega

/-- A shared ordinary read and covering write either meet at the allocator publication
or at a correction statistics word. -/
theorem ordinarySharedReadOrderOrStatistics {i j : EvId} {a b : Acc} {data : List Byte}
    {read : List (Option Byte)} {loc : Loc} (hs : loc.space = .shared) (hw : X.Writes i a data)
    (hr : X.Reads j b read) (ha : a.Covers loc) (hb : b.Covers loc) :
    ByteCausality l X loc (.thread i) (.thread j) ∨
      ∃ stage kind, Correction.StatisticsRead X j stage kind b read := by
  rcases sharedReadObservation hX hr (hb.1.symm.trans hs) with
    hAlloc | ⟨repeated,vector,hBias⟩ | ⟨stage,kind,hStats⟩
  · left
    obtain ⟨g,index⟩ := j
    have hFoot : b = {loc := Mma.allocationSlot l g, size := 4} :=
      Mma.allocationReadFootprint hp hX hAlloc
    rw [hFoot] at hb
    obtain ⟨owner,pos,_,_,_,_,hStore,hOrder⟩ := Mma.allocationStorePublished hp hX hAlloc
    have hWrite : X.Writes (owner,pos) {loc := Mma.allocationSlot l g, size := 4} _ := ⟨_,hStore⟩
    have hLane := ordinarySharedWritersSameLane hp hX hs hw hWrite ha hb
    have hOther : pos = 7 := (allocatorStoreOrigin hp hX hStore).2.2.1
    obtain ⟨_,_,hIndex,hEq⟩ := coveringAllocationWriter hp hX hs hw ha hb
    have hSame : i = (owner,pos) := Prod.ext hLane (hIndex.trans (hEq.trans hOther.symm))
    exact hSame.symm ▸ ByteCausality.direct (.inl (.single (.inr (.inl hOrder))))
  · obtain ⟨hBiasLo,_⟩ := Scores.biasVectorReadLower hp hX hBias
    have hByteLo := hb.2.2.1
    cases writeCoordinates hp hX hw (ha.1.symm.trans hs) with
    | allocation _ hFoot =>
      rw [hFoot] at ha
      have hHi := (rangeAllocation ha).2.2
      omega
    | statistics site hLane hFoot =>
      rw [hFoot] at ha
      have hHi := (rangeStatistics (site := site) hLane ha).2.2
      omega
    | staging _ _ _ hx _ hFoot =>
      rw [hFoot] at ha
      have hHi := (rangeStaging hx ha).2
      omega
  · exact .inr ⟨stage,kind,hStats⟩

end PTX.Kernels.TmlFa4Fwd.Thread
