-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEntry
public import Kernels.TmlFa4Fwd.Flow.Code.Part029
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem loaderSchedulerExit (l : Launch) (g : Nat) (warp : Fin 2) :
    Seg kernel Assumptions.all l g 5 3099 [(1062, b32 (14 + warp.val))] 9205 [] := by
  fin_cases warp <;> intro t ht <;> seg_fp ht using seg_close

/-- After draining the loader-specific rings, either loader warp follows the common
role split and returns through the decoded exit. -/
theorem loaderRoleExit {l : Launch} {g : Nat} {t : TState} (warp : Fin 2)
    (ht : At t 1901 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]) :
    ∃ u, u.pc = 9205 ∧ Next kernel Assumptions.all l g t u .exit := by
  obtain ⟨u, hu, hU⟩ : ∃ u, run kernel [] l g 2 t = some u ∧
      At u 1903 [(263, .pred false), (1062, b32 (14 + warp.val))] := by
    fin_cases warp <;> seg_fp ht using rfl
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1903 false hU hU.2.2.2.2.1 (by simp)
  obtain ⟨hvA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hU.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  obtain ⟨w, hw, hW⟩ : ∃ w, run kernel [] l g 1 v = some w ∧
      At w 1905 [(264, .pred true), (1062, b32 (14 + warp.val))] := by
    fin_cases warp <;> seg_fp hV using rfl
  obtain ⟨hwA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  obtain ⟨z, hz, hZ⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1905 true hW hW.2.2.2.2.1 (by simp)
  obtain ⟨hzA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hW.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hz
  obtain ⟨u', hu', hU'⟩ := (loaderSchedulerExit l g warp).rtg
    (hZ.mono hZ.2.2.2.2.2)
  have he : out kernel Assumptions.all l g u' = .ev .exit := by
    rw [out_event hU'.2.2.2.1 (by rw [hU'.1]; exact Flow.code_9205) rfl rfl]
    rfl
  exact ⟨u', hU'.1, (run_rtg (run_comp (run_comp huA hvA) (run_comp hwA hzA))).trans hu', he⟩

/-- Only the common exit can follow the loader's drained continuation. -/
theorem loaderRoleExitSuffix {l : Launch} {g : Nat} {t : TState} {events : List Event}
    (warp : Fin 2)
    (ht : At t 1901 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hr : Run kernel Assumptions.all l g t events none) :
    events = [⟨9205, .exit⟩] := by
  obtain ⟨u, hp, hn⟩ := loaderRoleExit warp ht
  have hs : Stops kernel Assumptions.all l g u := ⟨_, hn.stop⟩
  cases hr with
  | step hlocal he _ =>
    have hEq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst u
    obtain ⟨a, ha, hFire⟩ := he
    rw [hn.stop] at ha
    obtain rfl := Out.ev.inj ha
    cases hFire.2
  | last hlocal he =>
    have hEq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst u
    obtain ⟨a, ha, hFire⟩ := he
    rw [hn.stop] at ha
    obtain rfl := Out.ev.inj ha
    rw [hFire.1, hp]

end
end PTX.Kernels.TmlFa4Fwd.Loader
