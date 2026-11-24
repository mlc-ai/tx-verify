-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

private theorem warmValueSaveSeed {l : Launch} {g : Nat} :
    Seg kernel [] l g 3 1209 [] 1212 [(9538, b64 0), (10, .pred true)] := by
  intro s hs
  seg_fp hs using rfl

set_option maxRecDepth 100000 in
/-- Cross the actual K packet and V empty-acquire window after a page refresh. -/
theorem warmValueSaveStartFromPages {p : Params} {l : Launch} {X : Execution}
    {thread index j batch head trips warp tid tile : Nat} {s : TState} {ending : Option TState}
    (hs : At s 954 (warmSlotFrame p l batch head trips warp tid tile 1 false))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop index) ending)
    {e : Event} (he : X.get (thread, j) = some e) (hOrder : index ≤ j)
    (hPc : 1212 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    let F := warmCacheFrame p l batch head trips warp tid
    ∃ seed, At seed 957 F ∧ Run kernel Assumptions.all l thread seed
      ((X.tr thread).drop index) ending ∧
      ∃ pos, index ≤ pos ∧ pos ≤ j ∧ ∃ u stop,
        At u 1212 ([(9538, b64 0), (10, .pred true)] ++ F) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop pos) stop ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          ((X.tr thread).take index).countP Execution.isShfl + 32 := by
  let F := warmCacheFrame p l batch head trips warp tid
  obtain ⟨seed, hSeed, hAtSeed⟩ := warmPageLoopExit (g := thread) hs
  have hrSeed := hr.after_local_nonempty (run_rtg hSeed) (traceAfterObservedEvent he hOrder)
  have hAudit (n : Nat) : ((kernel.code.drop 957).take (1209 - 957)).all
      (fun ins => loaderPipelineCutOp 957 1209 n (F.map Prod.fst) ins.op) = true := by
    kernel_rfl
  have hRanked : (((kernel.code.drop 957).take (1209 - 957)).zipIdx 957).all
      (fun (ins, pc) => LoaderRankedInstr 1209 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1209 957 = 32 := by kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut (by decide) hAudit hRanked hAtSeed hrSeed he hOrder
      (.inl (by omega)) hSafe
  obtain ⟨u, hu, hU⟩ := warmValueSaveSeed (g := thread) t (ht.mono trivial)
  obtain ⟨hRun, hKeep⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) ht.1
    (by kernel_rfl) (by kernel_rfl) hu
  have hF := holdsSchedulerFrame ht.2.2.2.2 hKeep (fun _ hm => List.mem_map_of_mem hm)
  have hrU := htRun.after_local_nonempty (run_rtg hRun) (traceAfterObservedEvent he htBefore)
  refine ⟨seed, hAtSeed, hrSeed, index + front.length, Nat.le_add_right _ _, htBefore,
    u, stop, ?_, hrU, ?_⟩
  · exact hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, hF⟩
  · rw [htRank, hCount]

end
end PTX.Kernels.TmlFa4Fwd.Loader
