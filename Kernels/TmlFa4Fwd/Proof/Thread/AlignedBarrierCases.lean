-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationRendezvousOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBarrierOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
import Kernels.TmlFa4Fwd.Proof.AllocationBarrierControl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX Prologue

/-- The two aligned CTA barrier observations disagree at the same work ordinal in a warp
that performs softmax or correction. -/
@[no_expose] def AlignedWorkBarrierMismatch (l : Launch) (X : Execution)
    (limit : Nat := 12) : Prop :=
  ∃ (i j : EvId) (site site' id id' : Nat) (count count' : Option Nat) (mode mode' : BarMode),
    SameWarp l i.1 j.1 ∧ warpIndex l i.1 < limit ∧
    X.get i = some ⟨site, .bar id count mode⟩ ∧ X.get j = some ⟨site', .bar id' count' mode'⟩ ∧
    1 < barrierOrdinal X i ∧ barrierOrdinal X i = barrierOrdinal X j ∧
    (kernel.alignedAt site || kernel.alignedAt site') = true ∧ site ≠ site'

theorem AlignedWorkBarrierMismatch.ofObservations {l : Launch} {X : Execution}
    {i j : EvId} {site site' id id' : Nat} {count count' : Option Nat} {mode mode' : BarMode}
    {limit : Nat} (hw : SameWarp l i.1 j.1) (hRole : warpIndex l i.1 < limit)
    (hi : X.get i = some ⟨site, .bar id count mode⟩)
    (hj : X.get j = some ⟨site', .bar id' count' mode'⟩)
    (hPast : 1 < barrierOrdinal X i) (hOrd : barrierOrdinal X i = barrierOrdinal X j)
    (hAligned : (kernel.alignedAt site || kernel.alignedAt site') = true) (hNe : site ≠ site') :
    AlignedWorkBarrierMismatch l X limit :=
  ⟨i, j, site, site', id, id', count, count', mode, mode', hw, hRole, hi, hj,
    hPast, hOrd, hAligned, hNe⟩

/-- A correction work barrier waits for one statistics round or returns the allocation. -/
private inductive CorrectionWorkRendezvous (X : Execution) (i : EvId) : Prop where
  | statistics (round : CorrectionRound) (stage : Fin 2) (h : CorrectionWaits X i round stage)
  | finalAllocation (h : FinalAllocationArrival X i .arrive)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem correctionWorkRendezvous {i : EvId} {site id : Nat} {count : Option Nat}
    {mode : BarMode} (hi : X.get i = some ⟨site, .bar id count mode⟩)
    (hRole : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12) (hPast : 1 < barrierOrdinal X i)
    : CorrectionWorkRendezvous X i := by
  obtain ⟨g, k⟩ := i
  let hArr : BarrierArrival X (g,k) id count mode := ⟨_, hi, rfl⟩
  have hNamed : id ≠ 0 := by
    intro hId
    have hZero := (hArr.ordinalZeroIff hp hX).mpr hId
    omega
  by_cases hId : id = 2
  · subst id
    rcases hArr.correctionAllocation hp hX hRole with ⟨_, hOrd⟩ | ⟨_, hFinal, _⟩
    · exact (Nat.ne_of_gt hPast hOrd).elim
    · exact .finalAllocation hFinal
  · obtain ⟨stage, round, hWait, _, _⟩ := hArr.correctionStatistics hp hX hRole hNamed hId
    exact .statistics round stage hWait

/-- Once correction agrees on the abstract rendezvous at each work ordinal,
an aligned work mismatch is confined to the softmax warps. -/
theorem AlignedWorkBarrierMismatch.softmaxOfCorrectionAgreement
    (hAcross : ∀ {i j round stage}, SameWarp l i.1 j.1 →
      CorrectionWaits X i round stage → FinalAllocationArrival X j .arrive →
      barrierOrdinal X i < barrierOrdinal X j)
    (hRounds : ∀ {i j round round' stage stage'}, SameWarp l i.1 j.1 →
      barrierOrdinal X i = barrierOrdinal X j →
      CorrectionWaits X i round stage → CorrectionWaits X j round' stage' →
      round = round' ∧ stage = stage') (hBad : AlignedWorkBarrierMismatch l X)
    : AlignedWorkBarrierMismatch l X 8 := by
  obtain ⟨i, j, site, site', _, _, _, _, _, _, hw, hRole, hi, hj, hPast, hOrd, hAligned, hNe⟩ :=
    hBad
  by_cases hSoft : warpIndex l i.1 < 8
  · exact .ofObservations hw hSoft hi hj hPast hOrd hAligned hNe
  have hCorrection : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := ⟨by omega,hRole⟩
  have hSame : warpIndex l i.1 = warpIndex l j.1 := hw.2
  have hCorrection' : 8 ≤ warpIndex l j.1 ∧ warpIndex l j.1 < 12 := hSame ▸ hCorrection
  have ri := correctionWorkRendezvous hp hX hi hCorrection hPast
  have rj := correctionWorkRendezvous hp hX hj hCorrection' (hOrd ▸ hPast)
  exfalso
  cases ri with
  | statistics round stage hWait =>
    cases rj with
    | statistics round' stage' hWait' =>
      obtain ⟨rfl,rfl⟩ := hRounds hw hOrd hWait hWait'
      exact hNe (hWait.sameStation hi hj hWait')
    | finalAllocation hFinal => exact Nat.ne_of_lt (hAcross hw hWait hFinal) hOrd
  | finalAllocation hFinal =>
    cases rj with
    | statistics _ _ hWait =>
      have hw' : SameWarp l j.1 i.1 :=
        ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩
      exact Nat.ne_of_lt (hAcross hw' hWait hFinal) hOrd.symm
    | finalAllocation hFinal' =>
      obtain ⟨g,k⟩ := i
      obtain ⟨h,z⟩ := j
      have hi' := hFinal.correctionDecoded hp hX hCorrection.1 hCorrection.2
      have hj' := hFinal'.correctionDecoded hp hX hCorrection'.1 hCorrection'.2
      exact hNe ((congrArg Event.pc (Option.some.inj (hi.symm.trans hi'))).trans
        (congrArg Event.pc (Option.some.inj (hj.symm.trans hj'))).symm)

private theorem allocationEntryOfSite {i : EvId} {site id : Nat} {count : Option Nat}
    {mode : BarMode} (h : X.get i = some ⟨site, .bar id count mode⟩)
    (hs : site ∈ Mma.allocationEntrySites) :
    X.IsBarrier i 2 (some 416) site := by
  obtain ⟨_, hCount, _, _, _, _, hAlloc⟩ := actualNamedBarrier hp hX h
  have hSize := (by decide : ∀ k ∈ Mma.allocationEntrySites, namedBarrierCount k = some 416)
    site hs
  exact Mma.actualAllocationEntry hp hX hs (hAlloc (hCount.trans hSize) ▸ h)

private theorem ordinalOfEarlyBarrier {g i site id : Nat} {count : Option Nat} {mode : BarMode}
    (h : X.get (g, i) = some ⟨site, .bar id count mode⟩) :
    (barrierOrdinal X (g, i) = 0 ↔ site = 173) ∧
      (barrierOrdinal X (g, i) = 1 ↔ site ∈ Mma.allocationEntrySites) := by
  have hArr : BarrierArrival X (g, i) id count mode := ⟨_, h, rfl⟩
  obtain ⟨_, _, _, _, hCommon, hZero, _⟩ := actualNamedBarrier hp hX h
  have hStartup : barrierOrdinal X (g, i) = 0 ↔ site = 173 := by
    rw [hArr.ordinalZeroIff hp hX]
    refine ⟨?_, hZero⟩
    intro hId
    have hCount := actualNamedBarrierCountById hp hX h
    rw [hId] at hCount
    exact hCommon.mp hCount
  refine ⟨hStartup, ?_, fun hs =>
    initialAllocationOrdinal hp hX (allocationEntryOfSite hp hX h hs) hs⟩
  intro hOrd
  by_contra hSite
  have hNoncommon : site ≠ 173 := by
    intro h
    have h0 := hStartup.mpr h
    omega
  have hPast := afterInitialAllocationOrdinal hp hX h hNoncommon hSite
  omega

private theorem barrierSiteOfMmaOrDrain {i : EvId} {site id : Nat} {count : Option Nat}
    {mode : BarMode} (h : X.get i = some ⟨site, .bar id count mode⟩) (hAfter : 173 < site)
    (hw : 12 ≤ warpIndex l i.1) : site = 1910 ∨ site = 2764 := by
  have hSites := (actualNamedBarrier hp hX h).1
  have hAudit : namedBarrierSites.all (fun s => !(registerHintSites.contains s)) = true := by
    decide +kernel
  have hNotHint : site ∉ registerHintSites := by
    simpa using List.all_eq_true.mp hAudit site hSites
  have hRole := roleBodyPcOfEvent hp hX h hAfter hNotHint
  change roleBodyPc (warpIndex l i.1) site at hRole
  unfold roleBodyPc at hRole
  simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSites
  rcases hRole with hExit | hRole
  · omega
  · split_ifs at hRole <;> omega

/-- Startup and allocation entry cannot disagree at their ordinals. In the MMA, loader,
and drain warps, there is at most one later CTA barrier instruction. -/
theorem alignedBarrierDivergenceIsWork (hBad : AlignedClass.bar.Divergent l kernel X)
    : AlignedWorkBarrierMismatch l X := by
  obtain ⟨g, h, i, j, id, id', count, count', mode, mode', site, site',
    hw, he, hf, hOrd, hA, hNe⟩ :=
    (AlignedClass.divergent_bar_iff l).mp hBad
  change barrierOrdinal X (g, i) = barrierOrdinal X (h, j) at hOrd
  obtain ⟨h0, h1⟩ := ordinalOfEarlyBarrier hp hX he
  obtain ⟨h0', h1'⟩ := ordinalOfEarlyBarrier hp hX hf
  have hPast : 1 < barrierOrdinal X (g, i) := by
    by_contra! hEarly
    rcases (show barrierOrdinal X (g, i) = 0 ∨ barrierOrdinal X (g, i) = 1 by omega)
      with hZero | hOne
    · exact hNe ((h0.mp hZero).trans (h0'.mp (hOrd.symm.trans hZero)).symm)
    · have hs := h1.mp hOne
      have hs' := h1'.mp (hOrd.symm.trans hOne)
      have hRole := Mma.allocationEntryRole hp hX hs (allocationEntryOfSite hp hX he hs)
      have hRole' := Mma.allocationEntryRole hp hX hs' (allocationEntryOfSite hp hX hf hs')
      have hWarp : warpIndex l g = warpIndex l h := hw.2
      omega
  have hWarp : warpIndex l g < 12 := by
    by_contra! hTooHigh
    have hSame : warpIndex l g = warpIndex l h := hw.2
    have hOther : 12 ≤ warpIndex l h := hSame ▸ hTooHigh
    have hAfter {k index s cid : Nat} {cnt : Option Nat} {md : BarMode}
        (hGet : X.get (k, index) = some ⟨s, .bar cid cnt md⟩) (hNot : s ≠ 173) : 173 < s := by
      have hs := (actualNamedBarrier hp hX hGet).1
      simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hs
      omega
    have hs := barrierSiteOfMmaOrDrain hp hX he (hAfter he (fun hz => by have := h0.mpr hz; omega))
      hTooHigh
    have hLate' := hAfter hf (fun hz => by have := h0'.mpr hz; omega)
    have hs' := barrierSiteOfMmaOrDrain hp hX hf hLate' hOther
    have hNotEntry : site ≠ 1910 := fun h => by
      have := h1.mpr (h.symm ▸ (by decide : 1910 ∈ Mma.allocationEntrySites))
      omega
    have hNotEntry' : site' ≠ 1910 := fun h => by
      have := h1'.mpr (h.symm ▸ (by decide : 1910 ∈ Mma.allocationEntrySites))
      omega
    omega
  exact .ofObservations hw hWarp he hf hPast hOrd hA hNe

end PTX.Kernels.TmlFa4Fwd.Thread
