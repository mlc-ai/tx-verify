-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Kernel.ReadValue
public import Lemmas.Flow.WarpScan
public import Lemmas.Flow.TauFrame
public import Lemmas.Step.Released
public import Lemmas.Step.ProtectedReadProgress
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Lemmas.Flow.Local
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Step.WarpShfl
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
public import Kernels.TmlFa4Fwd.Proof.SchedulerDrainWords
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanGuard
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads
public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

noncomputable section

/-- The cumulative query array is immutable throughout the accepted execution. -/
def DrainCuQProtected (p : Params) (X : Execution) : Prop :=
  ∀ idx ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
    ¬ a.Covers ((globalLoc (p.cuQBase + 4 * idx)).at k)

/-- A slice containing as many shuffles as events consists of shuffles. -/
theorem getIsShuffleBetween {X : Execution} {g start stop j : Nat} {e : Event}
    (hLen : stop ≤ (X.tr g).length) (hStart : start ≤ j) (hStop : j < stop)
    (hCount : ((X.tr g).take stop).countP Execution.isShfl =
      ((X.tr g).take start).countP Execution.isShfl + (stop - start))
    (he : X.get (g, j) = some e) : Execution.isShfl e = true := by
  let middle := ((X.tr g).drop start).take (stop - start)
  have hLength : middle.length = stop - start := by
    simp only [middle, List.length_take, List.length_drop]
    omega
  have hTrace : (X.tr g).take stop = (X.tr g).take start ++ middle := by
    rw [← Nat.add_sub_of_le (show start ≤ stop by omega)]
    exact List.take_add ..
  have hMiddle : middle.countP Execution.isShfl = middle.length := by
    rw [hTrace, List.countP_append] at hCount
    omega
  apply List.countP_eq_length.mp hMiddle e
  apply List.mem_of_getElem? (i := j - start)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hStart]
  exact he

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
