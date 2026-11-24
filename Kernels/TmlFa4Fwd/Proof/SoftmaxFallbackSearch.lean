-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

def NoExhaustedRoute (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (warp : Fin 8) (src index : Nat) (target : Event) : Prop :=
  ∀ first shuffles ends (_hLast : p.batch ≤ first+31),
    tilePrefix p p.batch * p.heads ≤ g/l.block →
    ∀ stop : SchedulerWarpAt l X g 3209 (fun lane => fallbackAdvanceFacts p l
      (warpLane l g lane) warp first (tilePrefix p (min p.batch (first+31))*p.heads))
      shuffles 0 ends, WarpFollowsEvent l X g stop.pos src index target → False

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem warpFallbackSearch (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {warp : Fin 8} (hg : g < l.threads) (hCuQ : CuQReadsFromLaunch p X)
    {ends : Nat → Option TState} {src index : Nat} {target : Event} (hTarget : 3207 < target.pc)
    (hExhausted : NoExhaustedRoute p l X g warp src index target) (fuel : Nat)
    (first shuffles : Nat) (hFuel : p.batch - first ≤ fuel) (hFirst : first < p.batch)
    (hPast : tilePrefix p (min p.batch (first + 31)) * p.heads ≤ g / l.block)
    (cur : SchedulerWarpAt l X g 3158 (fun lane => fallbackScanFacts p l
      (warpLane l g lane) warp first (tilePrefix p (min p.batch (first + 31)) * p.heads))
      shuffles 0 ends) (hFollow : WarpFollowsEvent l X g cur.pos src index target) :
    ∃ start ord, tilePrefix p start * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (min p.batch (start + 31)) * p.heads ∧
      ∃ result : SchedulerWarpAt l X g 3212
        (fun lane => groupRouteFacts p l (warpLane l g lane) warp start) ord 0 ends,
      WarpFollowsEvent l X g result.pos src index target := by
  have hGroup : first + 31 < p.batch := by
    by_contra! h
    have hStop := warpFallbackAdvancePreserving hp hFirst cur
    have hFlag : (if p.batch ≤ first+31 then 3209 else 3163) = 3209 := ite_eq_left h
    generalize (if p.batch ≤ first+31 then 3209 else 3163) = frontier at hStop hFlag
    subst frontier
    obtain ⟨stop,hPos,_⟩ := hStop
    rw [Nat.min_eq_left h] at hPast
    exact hExhausted first shuffles ends h hPast stop (hPos.symm ▸ hFollow)
  cases fuel with
  | zero => omega
  | succ fuel =>
    let start := first + 31
    let bound := tilePrefix p (min p.batch (start + 31)) * p.heads
    have hClip : ¬ p.batch ≤ first + 31 := Nat.not_le.mpr hGroup
    have hCapped : min p.batch (first + 31) = start := Nat.min_eq_right hGroup.le
    obtain ⟨reframed, hFrame⟩ := cur.advanceLocalAt (pc' := 3158)
      (G := fun lane => fallbackScanFacts p l (warpLane l g lane) warp first
        (tilePrefix p start * p.heads)) (by
          intro lane hl
          exact ⟨cur.state lane, .refl, by simpa only [hCapped] using cur.checkpoint lane hl⟩)
    obtain ⟨advance, hAdvance⟩ :=
      warpFallbackAdvance hp (by omega : first < p.batch) reframed
    obtain ⟨openGroup, hOpen⟩ := advance.advanceLocalAt (pc' := 3163)
      (G := fun lane => fallbackAdvanceFacts p l (warpLane l g lane) warp first
        (tilePrefix p start * p.heads)) (by
          intro lane hl
          refine ⟨advance.state lane, .refl, ?_⟩
          simpa only [hClip, ↓reduceIte] using advance.checkpoint lane hl)
    have hA : WarpFollowsEvent l X g openGroup.pos src index target :=
      hOpen.symm ▸ hAdvance.symm ▸ hFrame.symm ▸ hFollow
    obtain ⟨down, hDown⟩ := warpFallbackDown hp hX hg hGroup hCuQ openGroup (.inr hA) (by omega)
    obtain ⟨tiles, hTiles⟩ := warpFallbackTiles hp hg hGroup down
    obtain ⟨entry, hEntry⟩ := warpFallbackFoldStart tiles
    have hE := hEntry.symm ▸ hTiles.symm ▸ hDown hA
    obtain ⟨folded, hFolded⟩ := warpFallbackFold hp hX hg hGroup.le entry (.inr hE) (by omega)
    have hF := hFolded hE
    obtain ⟨route, hRoute⟩ := warpFallbackRouteTo hp hX hg hGroup folded (.inr hF) hTarget
    by_cases hBound : bound ≤ g / l.block
    · obtain ⟨loop, hLoop⟩ := route.advanceLocalAt (pc' := 3158)
        (G := fun lane => fallbackScanFacts p l (warpLane l g lane) warp start bound) (by
          intro lane hl
          have h := route.checkpoint lane hl
          simp only [show tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤
            g / l.block from hBound, ↓reduceIte] at h
          exact ⟨route.state lane, .refl, h⟩)
      exact warpFallbackSearch hp hX hg hCuQ hTarget hExhausted fuel start _ (by omega) hGroup
        hBound loop (hLoop.symm ▸ hRoute hF)
    · obtain ⟨selected, hSelected⟩ := route.advanceLocalAt (pc' := 3212)
        (G := fun lane => groupRouteFacts p l (warpLane l g lane) warp start) (by
          intro lane hl
          have h := route.checkpoint lane hl
          simp only [show ¬ tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤
            g / l.block from hBound, ↓reduceIte] at h
          exact ⟨route.state lane, .refl, h⟩)
      exact ⟨start, _, hCapped ▸ hPast, Nat.lt_of_not_ge hBound, selected,
        hSelected.symm ▸ hRoute hF⟩

/-- Every observed active route comes from its containing group when exhaustion is excluded.
-/
theorem activeGroupOfEventUnlessExhausted (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src index : Nat} {target : Event}
    (hg : g < l.threads) (hWarp : warpIndex l g < 8) (hSrc : src < 32)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hEvent : X.get (warpLane l g src,index) = some target) (hPc : 3207 < target.pc)
    (hExhausted : NoExhaustedRoute p l X g ⟨warpIndex l g,hWarp⟩ src index target) :
    let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
    ∃ start ord, tilePrefix p start * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (min p.batch (start + 31)) * p.heads ∧
      ∃ (ends : Nat → Option TState) (result : SchedulerWarpAt l X g 3212
        (fun lane => groupRouteFacts p l (warpLane l g lane) warp start) ord 0 ends),
      WarpFollowsEvent l X g result.pos src index target := by
  dsimp only
  let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
  let limit := tilePrefix p (min p.batch 31) * p.heads
  have hCuQ : CuQReadsFromLaunch p X := fun i hi =>
    cuQWordReadsFromLaunchOfProtected hp hX hi (hProtected i hi)
  obtain ⟨ends, route, hRoute⟩ := firstSchedulerRouteOfEvent hp hX hg hWarp hSrc
    hProtected hEvent (by omega)
  by_cases hFirst : g / l.block < limit
  · have hBlock : l.block % 32 = 0 := by rw [hp.block]
    obtain ⟨result, hPos⟩ := route.advanceLocalAt (pc' := 3212)
      (G := fun lane => groupRouteFacts p l (warpLane l g lane) warp 0) (by
        intro lane hl
        have hAt : At (route.state lane) 3212 (firstRouteFacts p l g warp lane) := by
          simpa only [show g / l.block < tilePrefix p (min p.batch 31) * p.heads from hFirst,
            ↓reduceIte] using route.checkpoint lane hl
        have hs := hAt.2.2.2.2
        have hHeads := hs.2.2.2.2.2.1
        have hLane := hs.2.2.2.2.2.2.2.1
        have hEntry := hs.2.2.2.2.2.2.2.2.2
        have hTotal : (∑ i ∈ Finset.range 32, groupLaneTiles p 0 i) =
            tilePrefix p (min p.batch 31) := by
          simpa [tilePrefix] using groupTiles_eq p (Nat.zero_le _) (by decide : 32 ≤ 32)
        have hPrefix := hs.2.2.2.1
        change (route.state lane).regs 7241 =
          some (b32 (prefixWindow (groupLaneTiles p 0) 32 lane)) at hPrefix
        rw [prefixWindow_warp _ hl] at hPrefix
        have hSame : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
        refine ⟨route.state lane, .refl, hAt.mono ?_⟩
        unfold groupRouteFacts fallbackBaseFrame
        rw [hSame]
        have hOwn := hs.2.2.2.2.1
        change (route.state lane).regs 7240 =
          some (b32 (groupLaneTiles p 0 (laneOf l (warpLane l g lane)))) at hOwn
        rw [hSame] at hLane hOwn
        exact ⟨hs.1, hs.2.1, hTotal.symm ▸ hs.2.2.1, hPrefix, hOwn, hHeads, hLane, hEntry⟩)
    exact ⟨0, 10, by simp [tilePrefix], hFirst, ends, result, hPos.symm ▸ hRoute⟩
  · obtain ⟨miss, hMiss⟩ := route.advanceLocalAt (pc' := 3155) (G := firstRouteFacts p l g warp)
      (by
        intro lane hl
        refine ⟨route.state lane, .refl, ?_⟩
        simpa only [show ¬ g / l.block < tilePrefix p (min p.batch 31) * p.heads from hFirst,
          ↓reduceIte] using route.checkpoint lane hl)
    obtain ⟨start, hStart⟩ := warpFallbackStart hp (warp := warp) hg miss
    have hPast : limit ≤ g / l.block := Nat.le_of_not_gt hFirst
    obtain ⟨first, ord, hLo, hHi, result, hResult⟩ :=
      warpFallbackSearch hp hX hg hCuQ hPc hExhausted p.batch 0 10 (by simp) hp.shape.1
        hPast start (hStart.symm ▸ hMiss.symm ▸ hRoute)
    exact ⟨first, ord, hLo, hHi, ends, result, hResult⟩

/-- Every active CTA reaches its containing 31-request group through the observed softmax warp.
The earlier groups' totals are obtained from the actual protected reads and shuffle instances. -/
theorem activeGroupOfEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index : Nat} {target : Event} (hg : g < l.threads) (hWarp : warpIndex l g < 8)
    (hSrc : src < 32) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hEvent : X.get (warpLane l g src,index) = some target) (hPc : 3207 < target.pc) :
    let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
    ∃ start ord, tilePrefix p start * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (min p.batch (start + 31)) * p.heads ∧
      ∃ (ends : Nat → Option TState) (result : SchedulerWarpAt l X g 3212
        (fun lane => groupRouteFacts p l (warpLane l g lane) warp start) ord 0 ends),
      WarpFollowsEvent l X g result.pos src index target :=
  activeGroupOfEventUnlessExhausted hp hX hg hWarp hSrc hProtected hEvent hPc
    (fun _ _ _ _ hIdle _ _ => (Nat.not_le_of_gt hWork) hIdle)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
