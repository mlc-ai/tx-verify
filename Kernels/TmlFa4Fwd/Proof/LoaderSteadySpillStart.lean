-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyRoundPageWords
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchSave

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- The two pointer-spill sites of the steady packet pair. -/
def steadySpillSite (value : Bool) : Fin 4 := if value then 3 else 2

def steadySpillFirst (value : Bool) : Nat :=
  (recurringScratchWord (steadySpillSite value) false).pc - 2

def steadySpillPred (value : Bool) : Nat := if value then 13 else 12

def steadySpillFacts (value : Bool) (slot : Fin 2) (more : Bool) : List (Nat × Value) :=
  [((recurringSaveInputs (steadySpillSite value)).slot, b64 slot.val),
    (steadySpillPred value, .pred more)]

set_option maxRecDepth 100000 in
/-- The live steady lane crosses its K or V wait and enters the first actual pointer spill. -/
theorem steadySpillStartFromPages {p : Params} {l : Launch} {X : Execution}
    {thread next j batch head trips warp tid tile : Nat} (value : Bool)
    {s : TState} {ending : Option TState}
    (hs : At s 1424 (steadySlotFrame p l batch head trips warp tid tile 1 false))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop next) ending)
    {e : Event} (he : X.get (thread, j) = some e) (hOrder : next ≤ j)
    (hLate : pointerSavePc (steadySpillSite value) < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ start, At start 1427 (steadyCacheFrame p l batch head trips warp tid) ∧
      Run kernel Assumptions.all l thread start ((X.tr thread).drop next) ending ∧
      ∃ pos, next ≤ pos ∧ pos ≤ j ∧ ∃ u stop,
        At u (steadySpillFirst value) (steadySpillFacts value 0 true ++
          steadyCacheFrame p l batch head trips warp tid) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop pos) stop ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          ((X.tr thread).take next).countP Execution.isShfl + if value then 32 else 0 := by
  let F := steadyCacheFrame p l batch head trips warp tid
  let cut := steadySpillFirst value - 3
  obtain ⟨start, hLocal, hStart⟩ := steadyPageLoopExit (g := thread) hs
  have hStartRun := hr.after_local_nonempty (run_rtg hLocal) (traceAfterObservedEvent he hOrder)
  have hScope : 174 ≤ 1427 ∧ 1427 ≤ cut ∧ cut ≤ 1901 := by cases value <;> decide
  have hAudit (n : Nat) : ((kernel.code.drop 1427).take (cut - 1427)).all
      (fun ins => loaderPipelineCutOp 1427 cut n (F.map Prod.fst) ins.op) = true := by
    cases value <;> kernel_rfl
  have hRanked : (((kernel.code.drop 1427).take (cut - 1427)).zipIdx 1427).all
      (fun (ins, pc) => LoaderRankedInstr cut pc ins) = true := by cases value <;> kernel_rfl
  have hCut : cut ≤ pointerSavePc (steadySpillSite value) := by cases value <;> decide
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut hScope hAudit hRanked hStart hStartRun he hOrder
      (.inl (hCut.trans hLate.le)) hSafe
  have hSeed : Seg kernel [] l thread 3 cut [] (steadySpillFirst value)
      (steadySpillFacts value 0 true) := by
    cases value <;> intro v hv <;> seg_fp hv using rfl
  obtain ⟨u, hu, hU⟩ := hSeed t (ht.mono (G := []) trivial)
  obtain ⟨huA, huF⟩ := loaderLinear (regs := F.map Prod.fst)
    (show 174 ≤ cut by omega) (by cases value <;> decide) ht.1
    (by cases value <;> kernel_rfl) (by cases value <;> kernel_rfl) hu
  have huAt := hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,
    holdsSchedulerFrame ht.2.2.2.2 huF (fun _ hm => List.mem_map_of_mem hm)⟩)
  have huRun := htRun.after_local_nonempty (run_rtg huA) (traceAfterObservedEvent he htBefore)
  have hCount : loaderShuffleTail cut 1427 = (if value then 32 else 0) := by
    cases value <;> kernel_rfl
  exact ⟨start, hStart, hStartRun, next + front.length, Nat.le_add_right _ _, htBefore,
    u, stop, huAt, huRun, by simpa only [hCount] using htRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
