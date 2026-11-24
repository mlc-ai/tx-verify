-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmStartInPrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmFirstRow
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Flow.Code.Part014

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
include hp hX hg hw hl writes hCTA

set_option maxRecDepth 10000 in
/-- The actual warm entry initializes the loop counter and preserves the launch frame. -/
theorem warmFirstIterationOfEventRanked {e : Event} (he : X.get (warpLane l g src, j) = some e)
    (hLate : 917 ≤ e.pc) (hWarm : e.pc < 1353 ∨ HasWarmTile p l g) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      let trips := Mma.trips p batch co.1
      2 ≤ trips ∧ ∃ pos ≤ j, ∃ s ending,
        At s 917 ([(7174, b32 0), (1116, b32 (trips - 2))] ++
          warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block)) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch, hb, hLo, hHi, hTwo, pos, hBefore, s, ending, hs, hr, hRank⟩ :=
    loaderWarmArmOfEventRanked hp hX hg hw hl writes hCTA he (by omega) hWarm hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g src
  let trips := Mma.trips p batch co.1
  let tid := thread % l.block
  let F := warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
  let G := (1116, b32 (trips - 2)) :: F
  have hAudit₁ : ∀ branch, ((kernel.code.drop 912).take 1).all
      (fun ins => loaderPipelineCutOp 912 913 branch (G.map Prod.fst) ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨a, front, _, _, ha, haRun, haRank, haBefore⟩ :=
    prefixQuietCut (stop := 913) (by decide) hAudit₁
      (by set_option maxRecDepth 100000 in kernel_rfl) ⟨_, Flow.code_913, rfl⟩
      hs hr he hBefore (by omega) hSafe
  obtain ⟨b, hbStep, hbAt⟩ :=
    warmCounterSeedCore (l := l) (g := thread) a (ha.mono (G := []) trivial)
  obtain ⟨hbA, hbFrame⟩ := loaderLinear (regs := G.map Prod.fst)
    (by decide) (by decide) ha.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hbStep
  have hbG : At b 914 ((7174, b32 0) :: G) :=
    hbAt.mono ⟨hbAt.2.2.2.2.1, holdsSchedulerFrame ha.2.2.2.2 hbFrame
      (fun _ hm => List.mem_map_of_mem hm)⟩
  have hbRun := haRun.after_local_nonempty (run_rtg hbA) (traceAfterObservedEvent he haBefore)
  have hAudit₂ : ∀ branch, ((kernel.code.drop 914).take 3).all
      (fun ins => loaderPipelineCutOp 914 917 branch
        (((7174, b32 0) :: G).map Prod.fst) ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨c, passed, stop, _, hc, hcRun, hcRank, hcBefore⟩ :=
    prefixQuietCut (stop := 917) (by decide) hAudit₂
      (by set_option maxRecDepth 100000 in kernel_rfl) ⟨_, Flow.code_917, rfl⟩
      hbG hbRun he haBefore (by omega) hSafe
  exact ⟨batch, hb, hLo, hHi, hTwo, pos + front.length + passed.length, hcBefore, c, stop,
    hc, hcRun, hcRank.trans (haRank.trans hRank)⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Loader
