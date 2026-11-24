-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderFallback
public import Kernels.TmlFa4Fwd.Flow.Code.Part005
public import Kernels.TmlFa4Fwd.Flow.Code.Part029
public import Lemmas.Flow.LoadShared

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The exhausted path skips all copy issues and initializes the released-stage cursor. -/
private theorem loaderIdleLocal (l : Launch) (g : Nat) (stride tid : Nat) :
    Seg kernel [] l g 20 355
      [(1663, b32 stride), (1061, b32 tid), (2535, b32 l.sharedBase), (771, .pred false)] 375
      [(102, .pred true), (7179, b32 0), (7180, b32 1), (7192, b32 1)] := by
  intro t ht
  seg_fp ht using rfl

/-- From the masked work state, execute the decoded local prelude and skip straight to the
three-stage release drain, preserving the warp number and launch shared base. -/
theorem loaderIdleDrainEntry {l : Launch} {g warp stride tid : Nat} {t : TState}
    (ht : At t 355 [(1663, b32 stride), (1061, b32 tid), (2535, b32 l.sharedBase),
      (771, .pred false), (1062, b32 warp)]) :
    ∃ u, run kernel Assumptions.all l g 21 t = some u ∧ At u 1862
      [(7179, b32 0), (7180, b32 1), (7192, b32 1),
        (2535, b32 l.sharedBase), (1062, b32 warp)] := by
  obtain ⟨v, hv, hV⟩ := loaderIdleLocal l g stride tid t
    (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨hvA, hFrame⟩ := loaderLinear (regs := [2535, 1062]) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  let carry := [(7179, b32 0), (7180, b32 1), (7192, b32 1),
    (2535, b32 l.sharedBase), (1062, b32 warp)]
  have hAt : At v 375 ((102, .pred true) :: carry) := by
    exact hV.mono ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.1,
      (hFrame 2535 (by simp)).trans ht.2.2.2.2.2.2.1,
      (hFrame 1062 (by simp)).trans ht.2.2.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_375 true hAt hAt.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  exact ⟨u, run_comp hvA huA, hU.mono hU.2.2.2.2.2⟩

def loaderIdleDrainFacts (l : Launch) (warp : Nat) : List (Nat × Value) :=
  [(7179, b32 0), (7180, b32 1), (7192, b32 1), (2535, b32 l.sharedBase), (1062, b32 warp)]

/-- Lanes following the exhausted scheduler retain the prologue's decoded thread index
through the idle branch, then enter the release drain with the same cursor. -/
theorem loaderIdleWarpAtPreserving {p : Params} {l : Launch} {X : Execution}
    {g warp shuffles votes : Nat}
    {ends : Nat → Option TState} (cur : SchedulerWarpAt l X g 355 (fun lane =>
      [(771, .pred false), (7168, b32 0), (7169, b32 0), (7165, b32 p.batch)] ++
        loaderCuQFacts p l (warpLane l g lane) warp) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 1862 (fun _ => loaderIdleDrainFacts l warp)
      shuffles votes ends, next.pos = cur.pos ∧ next.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  have ht := cur.checkpoint lane hl
  have hAbi : Holds (cur.state lane).regs (loaderCuQFacts p l thread warp) :=
    ht.2.2.2.2.2.2.2.2
  have hStride : (cur.state lane).regs 1663 = some (b32 16) := holds_lookup hAbi rfl
  have hTid : (cur.state lane).regs 1061 = some (b32 (thread % l.block)) :=
    holds_lookup hAbi rfl
  have hBase : (cur.state lane).regs 2535 = some (b32 l.sharedBase) := holds_lookup hAbi rfl
  have hWarp : (cur.state lane).regs 1062 = some (b32 warp) := holds_lookup hAbi rfl
  obtain ⟨u, hu, hU⟩ := loaderIdleDrainEntry
    (ht.mono ⟨hStride, hTid, hBase, ht.2.2.2.2.1, hWarp, trivial⟩)
  exact ⟨u, run_rtg hu, hU⟩

/-- The local transition keeps every trace index. -/
theorem loaderIdleWarpAt {p : Params} {l : Launch} {X : Execution} {g warp shuffles votes : Nat}
    {ends : Nat → Option TState} (cur : SchedulerWarpAt l X g 355 (fun lane =>
      [(771, .pred false), (7168, b32 0), (7169, b32 0), (7165, b32 p.batch)] ++
        loaderCuQFacts p l (warpLane l g lane) warp) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 1862 (fun _ => loaderIdleDrainFacts l warp)
      shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := loaderIdleWarpAtPreserving cur
  exact ⟨next,hPos⟩

theorem loaderIdleWarp {p : Params} {l : Launch} {X : Execution} {g warp shuffles votes : Nat}
    (cur : SchedulerWarpAt l X g 355 (fun lane =>
      [(771, .pred false), (7168, b32 0), (7169, b32 0), (7165, b32 p.batch)] ++
        loaderCuQFacts p l (warpLane l g lane) warp) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 1862 (fun _ => loaderIdleDrainFacts l warp)
      shuffles votes) := by
  obtain ⟨next, _⟩ := loaderIdleWarpAt cur
  exact ⟨next⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
