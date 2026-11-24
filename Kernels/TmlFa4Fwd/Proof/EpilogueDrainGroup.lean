-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainRounds
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainFirstRoute
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainLaterRead

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

noncomputable section

/-- The exact cursor of each lane at a common scheduler checkpoint. -/
structure DrainWarpPoint (l : Launch) (X : Execution) (g pc : Nat)
    (facts : Nat → List (Nat × Value)) (shuffles votes : Nat) where
  pos : Nat → Nat
  state : Nat → TState
  ordinals : WarpOrdinals l X g pos shuffles votes
  atState : ∀ lane < 32, At (state lane) pc (facts lane)
  suffix : ∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) (state lane)
    ((X.tr (warpLane l g lane)).drop (pos lane)) none

/-- Assemble the same trace checkpoint across all live lanes. -/
theorem DrainWarpPoint.ofLanes {l : Launch} {X : Execution} {g pc : Nat}
    {facts : Nat → List (Nat × Value)} {pos : Nat → Nat} {shuffles votes : Nat}
    (hOrd : WarpOrdinals l X g pos shuffles votes) (fallback : TState)
    (hAt : ∀ lane < 32, ∃ s, At s pc (facts lane) ∧
      Run kernel Assumptions.all l (warpLane l g lane) s
        ((X.tr (warpLane l g lane)).drop (pos lane)) none) :
    ∃ point : DrainWarpPoint l X g pc facts shuffles votes, point.pos = pos := by
  have make (lane : Nat) : ∃ s, lane < 32 → At s pc (facts lane) ∧
      Run kernel Assumptions.all l (warpLane l g lane) s
        ((X.tr (warpLane l g lane)).drop (pos lane)) none := by
    by_cases hl : lane < 32
    · obtain ⟨s, hs⟩ := hAt lane hl
      exact ⟨s, fun _ => hs⟩
    · exact ⟨fallback, fun h => (hl h).elim⟩
  choose state hState using make
  exact ⟨⟨pos, state, hOrd, fun lane hl => (hState lane hl).1,
    fun lane hl => (hState lane hl).2⟩, rfl⟩

/-- The inclusive lane prefix used by the drain group selection. -/
def drainPrefix (p : Params) (first lane : Nat) : Nat :=
  ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i

/-- Each lane at the end of the first or a subsequent group's sweep. -/
def drainFinishFacts (p : Params) (first cta lane : Nat) : List (Nat × Value) :=
  [(7235, b32 first), (7147, b32 p.batch), (7234, b32 (drainPrefix p first 31)),
   (7138, b32 p.heads), (7236, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
   (7233, b32 (drainPrefix p first lane)), (1072, b32 cta),
   (7232, b32 (groupLaneTiles p first lane)), (1062, b32 13)]

/-- A new group starts from the previous group's exhausted work boundary. -/
def drainNextFacts (p : Params) (l : Launch) (g first cta lane : Nat) : List (Nat × Value) :=
  drainLaterEntry p l (warpLane l g lane) first
    (tilePrefix p (min p.batch (first + 31)) * p.heads) (cta + 1) cta

/-- The first scan and broadcast either finish the search or start the next group at PC 3032. -/
theorem drainFirstGroup {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta : Nat} (hg : g < l.threads) (hc : cta < l.grid)
    {pos : Nat → Nat} {state : Nat → TState} {shuffles votes : Nat}
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hScan : DrainRound p l X g 0 false 0 pos state)
    (hGuards : ∀ lane < 32, ∀ stage : Fin 5, (state lane).regs (drainScanGuardReg false stage) =
      some (.pred (drainScanGuard stage lane)))
    (hFrame : ∀ lane < 32, Holds (state lane).regs
      [(7138, b32 p.heads), (1072, b32 cta), (1062, b32 13), (1201, b32 lane),
       (7147, b32 p.batch), (7506, b64 p.cuQBase)]) :
    let limit := tilePrefix p (min p.batch 31) * p.heads
    if cta < limit then
      ∃ next : DrainWarpPoint l X g 3086 (drainFinishFacts p 0 cta) (shuffles + 6) votes,
        next.pos = (fun lane => pos lane + 6)
    else
      ∃ next : DrainWarpPoint l X g 3032 (drainNextFacts p l g 0 cta) (shuffles + 6) votes,
        next.pos = (fun lane => pos lane + 6) := by
  let count := drainPrefix p 0 31
  let limit := tilePrefix p (min p.batch 31) * p.heads
  have hSum := groupTiles_eq p (Nat.zero_le p.batch) (show 32 ≤ 32 by decide)
  have hZero : tilePrefix p 0 = 0 := by simp only [tilePrefix, Finset.range_zero, Finset.sum_empty]
  have hCount : count = tilePrefix p (min p.batch 31) := by
    change tilePrefix p 0 + count = tilePrefix p (min p.batch 31) at hSum
    simpa only [hZero, Nat.zero_add] using hSum
  have hLimit : count * p.heads = limit := by rw [hCount]
  have hEnd := hp.prefixWork_signed (Nat.min_le_left p.batch 31)
  have hFit := hp.groupWindow_signed (Nat.zero_le p.batch) (show 31 < 32 by decide) 32
  rw [prefixWindow_warp _ (show 31 < 32 by decide)] at hFit
  have hCTA : cta < 2 ^ 31 := hc.trans hp.grid.2.2
  obtain ⟨_, hO5, hS⟩ := hScan.scan hp hX hg (Nat.zero_le p.batch) hOrd hGuards
  obtain ⟨v, hO6, hV⟩ := drainTotalObserved hp hX hg false hO5
    (fun lane hl => (hS lane hl).1) (fun lane hl => (hS lane hl).2.1)
  let cursor := fun lane => pos lane + 6
  have hRoute (lane : Nat) (hl : lane < 32) :
      (cta < limit ∧ ∃ u, At u 3086 (drainFinishFacts p 0 cta lane) ∧
        Run kernel Assumptions.all l (warpLane l g lane) u
          ((X.tr (warpLane l g lane)).drop (cursor lane)) none) ∨
      (limit ≤ cta ∧ ∃ u, At u 3032 (drainNextFacts p l g 0 cta lane) ∧
        Run kernel Assumptions.all l (warpLane l g lane) u
          ((X.tr (warpLane l g lane)).drop (cursor lane)) none) := by
    have hlane : laneOf l (warpLane l g lane) = lane :=
      (Step.sameWarp_lane (by rw [hp.block]) hg hl).2
    have saved (r : Nat) (hr : r ∈ drainRoundPersistent) (hNe : r ≠ 7234) :
        (v lane).regs r = (state lane).regs r :=
      ((hV lane hl).2.2 r hNe).trans ((hS lane hl).2.2 r hr)
    have hd := (hV lane hl).1
    have hStarts := hScan.atWord lane hl
    have hTiles : (state lane).regs 7232 = some (b32 (groupLaneTiles p 0 lane)) := by
      have h := hStarts.2.2.2.2.2.1
      change (state lane).regs 7232 = some (b32 (prefixWindow (groupLaneTiles p 0) 1 lane)) at h
      simpa only [prefixWindow_one] using h
    have ht : At (v lane) 3025 (drainFirstRouteInputs p l (warpLane l g lane)
        count (drainPrefix p 0 lane) (groupLaneTiles p 0 lane) cta) := by
      rw [drainFirstRouteInputs, hlane]
      have hs := hFrame lane hl
      exact hd.mono ⟨hd.2.2.2.2.1, (saved 7138 (by decide) (by decide)).trans hs.1,
        (saved 1072 (by decide) (by decide)).trans hs.2.1, hd.2.2.2.2.2.1,
        (saved 7232 (by decide) (by decide)).trans hTiles,
        (saved 1062 (by decide) (by decide)).trans hs.2.2.1,
        (saved 1201 (by decide) (by decide)).trans hs.2.2.2.1,
        (saved 7147 (by decide) (by decide)).trans hs.2.2.2.2.1,
        (saved 7506 (by decide) (by decide)).trans hs.2.2.2.2.2.1, trivial⟩
    have hEnd' : count * p.heads < 2 ^ 31 := hLimit.symm ▸ hEnd
    rcases drainFirstRoute hp (show count < 2 ^ 31 from hFit) hCTA hEnd'
      ht (hV lane hl).2.1 with ⟨hLt, u, hu, hr, _⟩ | ⟨hLe, u, hu, hr, _⟩
    · rw [hLimit] at hLt hu
      exact .inl ⟨hLt, u, hu, hr⟩
    · rw [hLimit] at hLe hu
      exact .inr ⟨hLe, u, hu, hr⟩
  change if cta < limit then _ else _
  by_cases hHit : cta < limit
  · rw [ite_eq_left hHit]
    refine DrainWarpPoint.ofLanes hO6 (v 0) (fun lane hl => ?_)
    rcases hRoute lane hl with ⟨_, u, hu, hr⟩ | ⟨hn, _, _, _⟩
    · exact ⟨u, hu, hr⟩
    · omega
  · rw [ite_eq_right hHit]
    refine DrainWarpPoint.ofLanes hO6 (v 0) (fun lane hl => ?_)
    rcases hRoute lane hl with ⟨hn, _, _, _⟩ | ⟨_, u, hu, hr⟩
    · omega
    · exact ⟨u, hu, hr⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
