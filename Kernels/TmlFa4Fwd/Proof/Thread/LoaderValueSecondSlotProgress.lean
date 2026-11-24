-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVSecondSlot
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Epilogue

set_option maxRecDepth 15000 in
private theorem afterSecondReloadCode :
    (kernel.code.drop 855).all (fun i => Thread.staysPastEvent 855 i.op) = true := by kernel_rfl

private theorem afterSecondReloadSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (855 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

/-- The last second-pointer store remains current just before its actual reload,
even if the reload is still pending. -/
theorem primingVSecondSlotLatestAtCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first second : Nat} (hWarp : 14 ≤ warpIndex l g)
    {e : Event} (hFirst : X.get (g,first) = some e) (hFirstPc : e.pc = 804)
    {before state : TState}
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take second) (some before))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before state)
    (hPC : state.pc = 854) (hOrder : first ≤ second)
    {data : List Byte} (hSaved : PrimingCellValue X g first 799 (sourceScratchAccess l g 1) data) :
    PrimingCellValue X g second 799 (sourceScratchAccess l g 1) data := by
  obtain ⟨w,hw,hs,hLast⟩ := hSaved
  refine ⟨w,by omega,hs,?_⟩
  intro byte hb j hj dst hWrite hCover
  by_cases hOld : j < first
  · exact hLast byte hb j hOld dst hWrite hCover
  obtain ⟨write,hEvent,hPc⟩ := vSecondStackWindow hX hWrite hCover.1.symm
  rcases hPc with ⟨hStart,hEarly⟩ | hLate
  · have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 804) (by decide)
      (vSecondCuts (by decide)) hFirst hEvent (by omega) hStart hEarly
    omega
  · have hReach := hPrefix.returning_reach.append (TraceReach.of_local hLocal)
    simp only [List.append_nil] at hReach
    have hRecorded : ((X.tr g).take second)[j]? = some write := by
      rwa [List.getElem?_take_of_lt hj]
    exact (Nat.not_lt_of_ge hLate) (Thread.Loader.noEventAboveFinalFloor
      afterSecondReloadCode afterSecondReloadSegments hReach (by rw [hPC]; decide)
      (List.mem_of_getElem? hRecorded)) |>.elim

end PTX.Kernels.TmlFa4Fwd.Loader
