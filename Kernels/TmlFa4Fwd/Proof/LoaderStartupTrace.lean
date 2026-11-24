-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCuQ
public import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- A completed loader lane issues its register hint after the three broadcasts and
the common CTA fence and barrier. Its next actual trace position is six. -/
theorem loaderStartupLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g : Nat} (hg : g < l.threads) (hWarp : 14 ≤ warpIndex l g) :
    ∃ u, At u 180 (loaderEntryFacts p l g (warpIndex l g)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop 6) none ∧
      ((X.tr g).take 6).countP Execution.isShfl = 3 ∧
      ((X.tr g).take 6).countP isFullWarpVote = 0 := by
  obtain ⟨t, ht, hTid, hFence, hBar, hr⟩ :=
    nonzeroAfterCommonBarrierWithTid hp hX hComplete hg (by omega)
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have hAt : At t 174 (loaderBarrierFacts p l g warp.val) := by
    have h := ht.2.2.2.2
    have hAbi : Holds t.regs (abiFacts p l) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    apply ht.mono
    rw [loaderBarrierFacts, holds_append]
    exact ⟨⟨h.1, h.2.1, hAbi⟩, hTid, trivial⟩
  obtain ⟨inst, u, he, hu, hTail⟩ := loaderHintObserved hp hg warp hWarp hAt hr
  have hLen : 5 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  let e0 := (X.tr g)[0]'(by omega)
  let e1 := (X.tr g)[1]'(by omega)
  let e2 := (X.tr g)[2]'(by omega)
  have hGet0 : X.get (g, 0) = some e0 := by
    change (X.tr g)[0]? = some e0
    exact List.getElem?_eq_getElem (by omega)
  have hGet1 : X.get (g, 1) = some e1 := by
    change (X.tr g)[1]? = some e1
    exact List.getElem?_eq_getElem (by omega)
  have hGet2 : X.get (g, 2) = some e2 := by
    change (X.tr g)[2]? = some e2
    exact List.getElem?_eq_getElem (by omega)
  have hGets (j : Nat) (hj : j < (X.tr g).length) (e : Event)
      (he' : X.get (g, j) = some e) :
      (X.tr g).drop j = e :: (X.tr g).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj]
    exact congrArg (fun x => x :: (X.tr g).drop (j + 1))
      (Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans he'))
  have hPrefix : X.tr g =
      [e0, e1, e2, ⟨172, .fenceMbarInit⟩, ⟨173, .bar 0 none .sync⟩,
        ⟨179, .setMaxReg false 80 inst⟩] ++ (X.tr g).drop 6 := by
    have h0 := hGets 0 (by omega) e0 hGet0
    rw [hGets (0 + 1) (by omega) e1 hGet1,
      hGets (0 + 1 + 1) (by omega) e2 hGet2,
      hGets (0 + 1 + 1 + 1) (by omega) _ hFence,
      hGets (0 + 1 + 1 + 1 + 1) (by omega) _ hBar,
      hGets (0 + 1 + 1 + 1 + 1 + 1) hLen _ he] at h0
    exact h0
  refine ⟨u, hu, hTail, ?_⟩
  -- Compute the counts on the six known events, rather than on the rest of the execution.
  have hTake : (X.tr g).take 6 =
      [e0, e1, e2, ⟨172, .fenceMbarInit⟩, ⟨173, .bar 0 none .sync⟩,
        ⟨179, .setMaxReg false 80 inst⟩] := by
    rw [hPrefix]
    rfl
  rw [hTake, firstSharedValue hp hX g hg hGet0, secondWarpValue hp hX g hg hGet1,
    thirdWarpValue hp hX g hg hGet2]
  exact ⟨rfl, rfl⟩

/-- A completed execution supplies a synchronized loader scheduler checkpoint for each warp
14 and 15. The checkpoint starts from observed events of the actual execution. -/
theorem loaderStartupWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g : Nat} (hg : g < l.threads) (hWarp : 14 ≤ warpIndex l g) :
    Nonempty (SchedulerWarpAt l X g 180 (fun lane =>
      loaderEntryFacts p l (warpLane l g lane) (warpIndex l g)) 3 0) := by
  let _ : Nonempty TState := ⟨{}⟩
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) :
      ∃ u, At u 180 (loaderEntryFacts p l (warpLane l g lane) (warpIndex l g)) ∧
        Run kernel Assumptions.all l (warpLane l g lane) u
          ((X.tr (warpLane l g lane)).drop 6) none ∧
        ((X.tr (warpLane l g lane)).take 6).countP Execution.isShfl = 3 ∧
        ((X.tr (warpLane l g lane)).take 6).countP isFullWarpVote = 0 := by
    have hw := (Step.sameWarp_lane hBlock hg hl).1
    have hw' : warpIndex l (warpLane l g lane) = warpIndex l g := hw.2.symm
    obtain ⟨u, hu, hRun, hCount⟩ := loaderStartupLane hp hX hComplete hw.1.2.1 (hw' ▸ hWarp)
    change At u 180 (loaderEntryFacts p l (warpLane l g lane)
      (warpIndex l (warpLane l g lane))) at hu
    rw [hw'] at hu
    exact ⟨u, hu, hRun, hCount⟩
  choose! state ht hRun hS hV using hLane
  exact ⟨⟨fun _ => 6, state, state, ⟨hS, hV⟩, hRun, fun _ _ => .refl, ht⟩⟩

/-- From a completed trace of warp 14 or 15, reach the first scheduler scan with the
actual down-shuffle result and all ABI registers. -/
theorem loaderStartupCuQ {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g : Nat} (hg : g < l.threads) (hWarp : 14 ≤ warpIndex l g)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) :
    Nonempty (SchedulerWarpAt l X g 188 (fun lane =>
      (1707, b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
        loaderCuQFacts p l (warpLane l g lane) (warpIndex l g)) 4 0) := by
  obtain ⟨cur⟩ := loaderStartupWarp hp hX hComplete hg hWarp
  exact loaderFirstWarpCuQ hp hX hg cur hProtected

end
end PTX.Kernels.TmlFa4Fwd.Loader
