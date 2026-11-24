-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLaterSelectionProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderIdle

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
noncomputable section

private theorem idleDrainFromFinalGroup {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first shuffles : Nat} (hg : g < l.threads)
    (hFirst : first < p.batch) (hClip : p.batch ≤ first + 31) {ends : Nat → Option TState}
    (head : SchedulerWarpReached l X g 234 (loaderFallbackFacts p l g (warpIndex l g) first)
      shuffles 0 ends) :
    Nonempty (SchedulerWarpReached l X g 1862
      (fun _ => loaderIdleDrainFacts l (warpIndex l g)) shuffles 0 ends) := by
  have hAdvance := loaderFallbackAdvanceAtPreserving hp hFirst head.toSchedulerWarpAt
  rw [ite_eq_left hClip] at hAdvance
  obtain ⟨ready,hPos',hBefore'⟩ := hAdvance
  let group := head.reframe ready hPos' hBefore'
  obtain ⟨finish,hPos'',hBefore''⟩ :=
    loaderFallbackExhaustedAtPreserving hp hg hClip group.toSchedulerWarpAt
  let exhausted := group.reframe finish hPos'' hBefore''
  obtain ⟨drain,hPos,hBefore⟩ := loaderIdleWarpAtPreserving exhausted.toSchedulerWarpAt
  exact ⟨exhausted.reframe drain hPos hBefore⟩

/-- With no tile in a short batch, a maximal loader warp reaches the idle release drain. -/
theorem idleDrainOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X)
    (hBatch : p.batch ≤ 31) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 1862
      (fun _ => loaderIdleDrainFacts l (warpIndex l g)) 10 0 ends) := by
  have hRoute := firstRouteOfMaximal hp hMax hg hw hCuQ
  rw [ite_eq_right (by rw [Nat.min_eq_left hBatch]; exact Nat.not_lt_of_ge hIdle)] at hRoute
  obtain ⟨ends,⟨cur⟩⟩ := hRoute
  obtain ⟨start,hPos,hBefore⟩ := loaderFallbackStartAtPreserving hp hg cur.toSchedulerWarpAt
  let head := cur.reframe start hPos hBefore
  exact ⟨ends,idleDrainFromFinalGroup hp hg hp.shape.1 hBatch head⟩

/-- An idle loader of any batch size reaches the release drain after its final request group. -/
theorem idleDrainForBatchesOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ shuffles ends, Nonempty (SchedulerWarpReached l X g 1862
      (fun _ => loaderIdleDrainFacts l (warpIndex l g)) shuffles 0 ends) := by
  let n := (p.batch - 1) / 31
  have hSplit := Nat.div_add_mod (p.batch - 1) 31
  have hRem := Nat.mod_lt (p.batch - 1) (show 0 < 31 by decide)
  have hPos := hp.shape.1
  cases hn : n with
  | zero =>
    have hBatch : p.batch ≤ 31 := by dsimp [n] at hn; omega
    obtain ⟨ends,cur⟩ := idleDrainOfMaximal hp hMax hg hw hCuQ hBatch hIdle
    exact ⟨10,ends,cur⟩
  | succ group =>
    have hFirst : 31 * (group + 1) < p.batch := by dsimp [n] at hn; omega
    have hLast : p.batch ≤ 31 * (group + 2) := by dsimp [n] at hn; omega
    obtain ⟨ends,⟨cur⟩⟩ :=
      laterIdleLoaderGroupOfMaximal hp hMax hg hw hCuQ group hFirst hLast hIdle
    exact ⟨_,ends,idleDrainFromFinalGroup hp hg hFirst (by omega) cur⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
