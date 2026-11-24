-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierExit
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccessEntry
import Kernels.TmlFa4Fwd.Proof.AllocationBarrierControl
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.NotTcMma

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue

private def allocationSites : List Nat := [1910, 3103, 7747, 2764, 7741, 9204]

private theorem allocationSiteOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {site : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get i = some ⟨site, .bar 2 count mode⟩) : site ∈ allocationSites := by
  obtain ⟨hs, hCount, _, _, _, _, _⟩ := actualNamedBarrier hp hX he
  have hc : count = some 416 := by
    simpa [countOfBarrierId] using actualNamedBarrierCountById hp hX he
  have audit : namedBarrierSites.all (fun s =>
      !decide (namedBarrierCount s = some 416) || allocationSites.contains s) = true := by decide
  have h := List.all_eq_true.mp audit _ hs
  simpa [← hCount, hc] using h

set_option maxRecDepth 100000 in
private theorem allocationBranchFloors : allocationSites.all (fun site =>
    (kernel.code.drop (site + 1)).all (fun i => staysPastEvent (site + 1) i.op)) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
private theorem allocationSegmentFloors : allocationSites.all (fun barrier =>
    Assumptions.swExp2Sites.all (fun site =>
      if barrier + 1 ≤ site then
        match cuteExp2.matchAt kernel site with
        | some seg => decide (barrier + 1 ≤ seg.stop)
        | none => false
      else true)) = true := by decide +kernel

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- After either allocation arrival returns, the issuing lane stays beyond that arrival. -/
theorem afterAllocationArrival {g i j site : Nat} {count : Option Nat} {mode : BarMode} {e : Event}
    (hi : X.get (g,i) = some ⟨site, .bar 2 count mode⟩) (hBefore : i < j)
    (hj : X.get (g,j) = some e) : site < e.pc := by
  have hLen : j < (X.tr g).length := PTX.len_of_get hj
  have hPast : i + 1 < (X.tr g).length := by omega
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX hj)
  obtain ⟨t, u, hStep, hTail⟩ := hr.after_event hi hPast
  obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source hStep
  have hPc : t.pc = site := (estep_source_pc hStep).symm
  have hOp := fires_bar_op hFire rfl
  have hAdvance := followsMarkedBarrier rfl hCode hOp hStep
  have hSite := allocationSiteOfEvent hp hX hi
  have hBranches := List.all_eq_true.mp allocationBranchFloors _ hSite
  have hSegments := List.all_eq_true.mp allocationSegmentFloors _ hSite
  obtain ⟨_, hw⟩ := TmlFa4Fwd.Mma.walkFromRun hTail
  have hMember : e ∈ (X.tr g).drop (i+1) := by
    apply List.mem_of_getElem? (i := j - (i+1))
    rwa [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
  apply eventTailEventsOfSegmentFloor hBranches _ hw (by omega) _ hMember
  intro source hFloor hMem seg hMatch
  have h := List.all_eq_true.mp hSegments _ hMem
  rw [ite_eq_left hFloor, hMatch] at h
  exact of_decide_eq_true h

omit hp hX in
private def sitesOfWarp (warp : Nat) : Nat × Nat :=
  if warp < 8 then (3103, 7741) else if warp < 12 then (7747, 9204) else (1910, 2764)

private theorem allocationSiteOfWarp {g i site : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g,i) = some ⟨site, .bar 2 count mode⟩) :
    site = (sitesOfWarp (warpIndex l g)).1 ∨ site = (sitesOfWarp (warpIndex l g)).2 := by
  have hSite := allocationSiteOfEvent hp hX he
  have hLate : 173 < site ∧ site ∉ registerHintSites :=
    (by decide : ∀ k ∈ allocationSites, 173 < k ∧ k ∉ registerHintSites) site hSite
  have hRole := roleBodyPcOfEvent hp hX he hLate.1 hLate.2
  change roleBodyPc (warpIndex l g) site at hRole
  simp only [allocationSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
  unfold roleBodyPc at hRole
  unfold sitesOfWarp
  rcases hRole with h | h
  · omega
  · split_ifs at h ⊢ <;> omega

/-- The correction role's final arrival is the arrival following output finalization. -/
theorem FinalAllocationArrival.correctionDecoded {g j : Nat} {mode : BarMode}
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hArrival : FinalAllocationArrival X (g,j) mode) :
    X.get (g,j) = some ⟨9204,.bar 2 (some 416) mode⟩ := by
  obtain ⟨site, hSite, he⟩ := hArrival.decoded
  have hClass := allocationSiteOfWarp hp hX he
  have hWarp : ¬warpIndex l g < 8 := by omega
  simp only [sitesOfWarp, hWarp, hHi, ↓reduceIte] at hClass
  rcases hClass with rfl | rfl
  · exact (by decide : 7747 ∉ [2764, 7741, 9204]) hSite |>.elim
  · exact he

omit hp hX in
private theorem countP_eq_one_at {α : Type} (p : α → Bool) {xs : List α} {k : Nat} {x : α}
    (hGet : xs[k]? = some x) (hMark : p x = true)
    (hOnly : ∀ j y, xs[j]? = some y → p y = true → j = k) : xs.countP p = 1 := by
  induction xs generalizing k with
  | nil => simp at hGet
  | cons a xs ih =>
    cases k with
    | zero =>
      obtain rfl : a = x := Option.some.inj hGet
      have hNone : xs.countP p = 0 := by
        apply List.countP_eq_zero.mpr
        intro y hm hy
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
        have := hOnly (j+1) y hj hy
        omega
      simp [hMark, hNone]
    | succ j =>
      have hNo : p a = false := Bool.eq_false_iff.mpr (fun h => by
        have := hOnly 0 a rfl h
        omega)
      have hLess : xs.countP p = 1 := ih hGet (fun k y hy hp => by
        have := hOnly (k+1) y hy hp
        omega)
      simp [hNo, hLess]

/-- The final allocation arrival is the second arrival of barrier 2 in its lane. -/
theorem finalAllocationArrivalOrdinal {g j : Nat} {mode : BarMode}
    (hFinal : FinalAllocationArrival X (g,j) mode) :
    observedBarrierOrdinal X (g,j) 2 = 1 := by
  obtain ⟨site, hSite, hBar⟩ := hFinal.decoded
  have hNotEntry := (by decide : ∀ k ∈ [2764, 7741, 9204],
    k ∉ TmlFa4Fwd.Mma.allocationEntrySites) site hSite
  obtain ⟨i, hBefore, source, hSource, hInit⟩ :=
    TmlFa4Fwd.Mma.allocationEntryBeforeBarrier hp hX hBar hNotEntry
  let warp := warpIndex l g
  have hInitSite : source = (sitesOfWarp warp).1 := by
    have hClass := allocationSiteOfWarp hp hX hInit
    rcases hClass with h | h
    · exact h
    · rw [h] at hSource
      unfold sitesOfWarp at hSource
      split_ifs at hSource <;> simp [TmlFa4Fwd.Mma.allocationEntrySites] at hSource
  have hFinalSite : site = (sitesOfWarp warp).2 := by
    have hClass := allocationSiteOfWarp hp hX hBar
    rcases hClass with h | h
    · rw [h] at hNotEntry
      unfold sitesOfWarp at hNotEntry
      split_ifs at hNotEntry <;> exact (hNotEntry (by decide)).elim
    · exact h
  let records := (X.tr g).take j
  have hAt : records[i]? = some ⟨source, .bar 2 (some 416) .sync⟩ := by
    rwa [List.getElem?_take_of_lt hBefore]
  change records.countP (Execution.isBarId 2) = 1
  apply countP_eq_one_at _ hAt rfl
  rintro k ⟨addr, kind⟩ hGet hMark
  have hLt : k < j := by
    have hK := (List.getElem?_eq_some_iff.mp hGet).1
    simp only [records, List.length_take, Nat.lt_min] at hK
    omega
  have hReal : X.get (g,k) = some ⟨addr, kind⟩ := by
    rwa [List.getElem?_take_of_lt hLt] at hGet
  cases kind <;> simp [Execution.isBarId] at hMark
  case bar id count mode =>
    obtain rfl := hMark
    rcases allocationSiteOfWarp hp hX hReal with h | h
    · have hEq : addr = source := h.trans hInitSite.symm
      by_contra! hNe
      rcases Nat.lt_or_gt_of_ne hNe with hl | hl
      · have hPast := afterAllocationArrival hp hX hReal hl hInit
        change addr < source at hPast
        omega
      · have hPast := afterAllocationArrival hp hX hInit hl hReal
        change source < addr at hPast
        omega
    · have hPast := afterAllocationArrival hp hX hReal hLt hBar
      change addr < site at hPast
      change addr = (sitesOfWarp warp).2 at h
      omega

/-- Any second arrival of barrier 2 is a lane's final allocation arrival. -/
theorem finalAllocationArrivalOfOrdinal {g j : Nat} {mode : BarMode}
    (hArrive : BarrierArrival X (g,j) 2 (some 416) mode)
    (hOrdinal : observedBarrierOrdinal X (g,j) 2 = 1) : FinalAllocationArrival X (g,j) mode := by
  obtain ⟨⟨site, kind⟩, hGet, rfl⟩ := hArrive
  have hSites : (sitesOfWarp (warpIndex l g)).1 < (sitesOfWarp (warpIndex l g)).2 ∧
      (sitesOfWarp (warpIndex l g)).2 ∈ [2764, 7741, 9204] := by
    unfold sitesOfWarp
    split_ifs <;> decide
  rcases allocationSiteOfWarp hp hX hGet with hStart | hEnd
  · have hSome : 0 < ((X.tr g).take j).countP (Execution.isBarId 2) := by
      change 0 < observedBarrierOrdinal X (g,j) 2
      omega
    obtain ⟨⟨pc, kind⟩, hMem, hMark⟩ := List.countP_pos_iff.mp hSome
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hMem
    have hLt : i < j := by
      have hLen := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_take, Nat.lt_min] at hLen
      omega
    rw [List.getElem?_take_of_lt hLt] at hi
    cases kind <;> simp [Execution.isBarId] at hMark
    case bar id count earlierMode =>
      obtain rfl := hMark
      have hPast := afterAllocationArrival hp hX hi hLt hGet
      change pc < site at hPast
      rcases allocationSiteOfWarp hp hX hi with h | h <;> omega
  · exact FinalAllocationArrival.of_decoded (hEnd.symm ▸ hSites.2) hGet

/-- No Tensor Memory data access in the lane follows its final allocation arrival. -/
theorem FinalAllocationArrival.afterTensorData {g i j : Nat} {mode : BarMode}
    (hFinal : FinalAllocationArrival X (g,j) mode) (hData : TensorDataEvent X (g,i)) : i < j := by
  cases mode
  case arrive => exact tensorDataBeforeTerminalArrival hp hX hData hFinal.arrival
  case sync =>
    obtain ⟨site, hs, hGet⟩ := hFinal.decoded
    have hMode := (actualNamedBarrier hp hX hGet).2.2.1
    have hSite : site = 2764 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl <;> first | rfl | cases hMode
    subst site
    have hWarp : warpIndex l g = 12 := by
      have hRole := roleBodyPcOfEvent hp hX hGet (by decide) (by decide)
      change roleBodyPc (warpIndex l g) 2764 at hRole
      unfold roleBodyPc at hRole
      rcases hRole with h | h
      · omega
      · split_ifs at h <;> omega
    obtain ⟨e, he, hShape⟩ := hData
    by_contra! hEarlier
    rcases hEarlier.eq_or_lt with rfl | hEarlier
    · obtain rfl := Option.some.inj (he.symm.trans hGet)
      rcases hShape with h | ⟨_, _, _, _, h⟩ <;> cases h
    have hLater := afterAllocationArrival hp hX hGet hEarlier he
    rcases get_source hX he with ⟨_, hFault⟩ | ⟨_, ins, _, _, hc, hf⟩
    · rcases hShape with h | ⟨_, _, _, _, h⟩
      · simp [isTcData, hFault] at h
      · rw [hFault] at h
        cases h
    have hOp : (tcDataOp ins.op || tcMmaOp ins.op) = true := by
      rcases hShape with h | ⟨_, _, _, _, h⟩
      · simp only [fires_tcData_op hf h, Bool.true_or]
      · simp only [fires_tcMma_op hf h, Bool.or_true]
    have hRole := roleBodyPcOfEvent hp hX he (by omega) (by
      have hNoHint : (registerHintSites.all (fun site =>
          (kernel.code[site]?.map fun ins => !(tcDataOp ins.op || tcMmaOp ins.op)) = some true)) =
            true := by decide +kernel
      intro hHint
      have h := List.all_eq_true.mp hNoHint _ hHint
      simp [hc] at h
      simp [h.1, h.2] at hOp)
    change roleBodyPc (warpIndex l g) e.pc at hRole
    rw [hWarp] at hRole
    have hTail : e.pc ∈ [2765, 2766, 2767, 9205] := by
      unfold roleBodyPc at hRole
      simp at hRole ⊢
      omega
    have hAudit : ∀ pc ∈ [2765, 2766, 2767, 9205],
        (kernel.code[pc]?.map fun ins => !(tcDataOp ins.op || tcMmaOp ins.op)) = some true :=
      by decide +kernel
    have h := hAudit _ hTail
    simp [hc] at h
    simp [h.1, h.2] at hOp

end PTX.Kernels.TmlFa4Fwd.Thread
