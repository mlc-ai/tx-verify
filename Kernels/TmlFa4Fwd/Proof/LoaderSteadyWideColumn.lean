-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Flow.Code.Part025

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem steadyWideColumnCore {l : Launch} {g tid : Nat} :
    Seg kernel [] l g 1 1636 [(1147, b32 (8 * (tid % 8)))] 1637
      [(7825, b64 (16 * (tid % 8)))] := by
  have hFit : 8 * (tid % 8) < 2 ^ 32 := by omega
  intro s hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hFit, show 8 * (tid % 8) * 2 = 16 * (tid % 8) by omega]

set_option maxRecDepth 100000 in
/-- The first V address calculation leaves the lane's wide column live for all later pairs. -/
theorem steadyValueWideColumnOfEvent {l : Launch} {X : Execution} {g index j start tid : Nat}
    {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hRange : 174 ≤ start ∧ start ≤ 1636)
    (hAudit : ∀ branch, ((kernel.code.drop start).take (1636 - start)).all
      (fun ins => loaderPipelineCutOp start 1636 branch (F.map Prod.fst) ins.op) = true)
    (hRanked : (((kernel.code.drop start).take (1636 - start)).zipIdx start).all
      (fun (i, pc) => LoaderRankedInstr 1636 pc i) = true)
    (hKeep : ((kernel.code.drop 1636).take 1).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true)
    (hColumn : (1147, b32 (8 * (tid % 8))) ∈ F)
    (hs : At s start F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {e : Event} (he : X.get (g, j) = some e) (hBefore : index ≤ j)
    (hDemand : 1636 ≤ e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail 1636 start ≤
        ((X.tr g).take j).countP Execution.isShfl))
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ pos, index ≤ pos ∧ pos ≤ j ∧ ∃ u stop,
      At u 1637 ((7825, b64 (16 * (tid % 8))) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail 1636 start := by
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut ⟨hRange.1, hRange.2, by decide⟩
      hAudit hRanked hs hr he hBefore hDemand hSafe
  obtain ⟨u, hu, huAt⟩ := steadyWideColumnCore (g := g) (tid := tid) t
    (ht.mono ⟨holds_mem ht.2.2.2.2 hColumn, trivial⟩)
  obtain ⟨huA, huF⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) ht.1 hKeep rfl hu
  have huRun := htRun.after_local_nonempty (run_rtg huA) (traceAfterObservedEvent he htBefore)
  exact ⟨index + front.length, Nat.le_add_right _ _, htBefore, u, stop,
    huAt.mono ⟨huAt.2.2.2.2.1,
      holdsSchedulerFrame ht.2.2.2.2 huF (fun _ hm => List.mem_map_of_mem hm)⟩, huRun, htRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
