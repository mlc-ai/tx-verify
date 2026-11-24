-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.AllocationBarrierGeneration

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue

/-- An observed allocation rendezvous identifies its lane's generation-zero arrival. -/
theorem firstObservedAllocationEntry {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hex : ∃ j pc, pc ∈ allocationEntrySites ∧ X.IsBarrier (g,j) 2 (some 416) pc) :
    ∃ j pc, pc ∈ allocationEntrySites ∧ X.IsBarrier (g,j) 2 (some 416) pc ∧
      ((X.tr g).take j).countP (Execution.isBarId 2) = 0 := by
  classical
  let j := Nat.find hex
  obtain ⟨pc, hPc, hBar⟩ := Nat.find_spec hex
  refine ⟨j, pc, hPc, hBar, List.countP_eq_zero.mpr ?_⟩
  intro e hMem hId
  obtain ⟨idx, hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hLt := (List.getElem?_eq_some_iff.mp hGet).1
  simp only [List.length_take] at hLt
  have hIdx : idx < j := by omega
  rw [List.getElem?_take_of_lt hIdx] at hGet
  obtain ⟨site, kind⟩ := e
  cases kind <;> simp [Execution.isBarId] at hId
  case bar id count mode =>
    subst id
    change X.get (g,idx) = some ⟨site, .bar 2 count mode⟩ at hGet
    by_cases hSite : site ∈ allocationEntrySites
    · exact Nat.find_min hex hIdx ⟨site, hSite, actualAllocationEntry hp hX hSite hGet⟩
    · obtain ⟨i, hi, source, hm, he⟩ := allocationEntryBeforeBarrier hp hX hGet hSite
      exact Nat.find_min hex (show i < j by omega) ⟨source, hm, he⟩

private theorem allocationUnreleasedProtocol {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {c : Nat} (hc : c < l.grid) {s : CtaBarrier.State}
    (hs : CtaBarrier.run l.block {} (X.barriers c) = .ok s) (hZero : (s.slots 2).generation = 0) :
    NamedBar.Protocol (some 416) (Finset.range 13) 2 (X.barriers c) := by
  have hAt : CtaBarrier.At l.block (X.barriers c) (X.barriers c).length s := by
    simpa [CtaBarrier.At] using hs
  have h := allocationProtocolPrefix hp hX hc hAt hZero
  rwa [List.take_of_length_le (by omega)] at h

/-- When the thirteen participating warps have issued their initial allocation arrival,
a maximal extension with the same thread traces releases the initial resource-2 wait.
The concrete first-generation protocol suffices for all recorded appends. -/
theorem allocationBarrierCanRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pc : Nat} (hg : g < l.threads)
    (hPc : pc ∈ allocationEntrySites)
    (hLast : X.IsBarrier (g,(X.tr g).length-1) 2 (some 416) pc)
    (hOrd : ((X.tr g).take ((X.tr g).length-1)).countP (Execution.isBarId 2) = 0)
    (hArrived : ∀ h, h < l.threads → h/l.block = g/l.block → warpIndex l h < 13 →
      ∃ j pc, pc ∈ allocationEntrySites ∧ X.IsBarrier (h,j) 2 (some 416) pc) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
  let c := g/l.block
  have hc := NamedBar.cta_lt hg
  have hb := NamedBar.block_pos_of_thread_lt hg
  have hShape := allocationBarrierShape hp
  have hLanes (y : Nat) (hy : y < l.block) (hWarp : y/32 ∈ Finset.range 13) :=
    firstObservedAllocationEntry hp hMax.1
      (hArrived _ (NamedBar.cta_thread_lt hc hy) (NamedBar.lane_cta hb hy).1 (by
        unfold warpIndex
        rw [(NamedBar.lane_cta (c := c) hb hy).2]
        exact Finset.mem_range.mp hWarp))
  obtain ⟨Y, hY, hTr, _, hRecords⟩ := NamedBar.warps_record_of_noLocalFault
    Assumptions.wfStep.ctaHistory hShape hc (G := 0)
    (fun Z hz w hw hord => CtaBarrier.first_generation_no_append_fault hz hc hShape hw hord
      (fun s hs he => allocationUnreleasedProtocol hp hz hc hs he) (fun h hT hC hW hDone => by
        obtain ⟨i, _, _, _, hKey⟩ := allocationGenerationZeroMember hp hz hT
          (Finset.mem_range.mp hW) (by simpa only [CtaBarDone, hC] using hDone)
        exact ⟨i, by simpa only [hC] using hKey.2.2⟩))
    (fun y hy hw => by
      obtain ⟨j, pc', _, he, hZero⟩ := hLanes y hy hw
      exact ⟨j, pc', .sync, he, hZero⟩)
    (Finset.range 13).toList (fun w hw => Finset.mem_toList.mp hw) hMax rfl
  have hGet (e : EvId) : Y.get e = X.get e := by simp only [Execution.get, hTr]
  have hDone : CtaBarDone l Y c 2 :=
    CtaBarrier.first_generation_released_of_recorded hY.1.ctaBar hc hShape
      (fun _ hs hh => allocationUnreleasedProtocol hp hY.1 hc hs hh) (fun w hw => by
        have hLane : w*32 < l.block := by have := hShape.bound w hw; omega
        have hWarp : w*32/32 = w := Nat.mul_div_cancel _ (by decide)
        obtain ⟨j, pc', _, he, hZero⟩ :=
          hLanes (w*32) hLane (by rw [hWarp]; exact hw)
        exact ⟨j, pc', .sync, by rwa [hGet],
          hRecords w (Finset.mem_toList.mpr hw) (w*32) hLane hWarp j pc' .sync
            (some 416) he hZero⟩)
  have hRole := allocationEntryRole hp hMax.1 hPc hLast
  obtain ⟨i, source, _, hEntry, hi⟩ :=
    allocationGenerationZeroMember hp hY.1 hg (by omega) hDone
  have hLastY : Y.IsBarrier (g,(X.tr g).length-1) 2 (some 416) pc := by
    change Y.get (g,(X.tr g).length-1) = _
    rwa [hGet]
  have hAt : i = (X.tr g).length-1 := by
    have hBound : (X.tr g).length-1 < (Y.tr g).length :=
      (List.getElem?_eq_some_iff.mp hLastY).1
    have hLen : i < (Y.tr g).length := (List.getElem?_eq_some_iff.mp hEntry).1
    have hi' : i ≤ (X.tr g).length-1 := by rw [hTr] at hLen; omega
    rcases Nat.eq_or_lt_of_le hi' with h | h
    · exact h
    · change Y.get (g,i) = some ⟨source, .bar 2 (some 416) .sync⟩ at hEntry
      rw [hGet] at hEntry
      have hEvent : ((X.tr g).take ((X.tr g).length-1))[i]? =
          some ⟨source, .bar 2 (some 416) .sync⟩ := by
        rwa [List.getElem?_take_of_lt h]
      exact (List.countP_eq_zero.mp hOrd _ (List.mem_of_getElem? hEvent)
        (by simp [Execution.isBarId])).elim
  exact ⟨Y, hY, hTr, NamedBar.released_of_key hY.1.ctaBar hTr hLast (hAt ▸ hi) hDone⟩

end PTX.Kernels.TmlFa4Fwd.Mma
