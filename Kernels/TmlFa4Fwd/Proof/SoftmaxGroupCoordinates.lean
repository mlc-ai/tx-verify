-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxGroupChoice
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTileCoordinates

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

private def withinGroupTiles (p : Params) (first batch : Nat) : Nat :=
  ∑ i ∈ Finset.range (batch - first), groupLaneTiles p first i

private theorem tilePrefix_group_add (p : Params) {first batch : Nat} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hb : batch < p.batch) :
    tilePrefix p first + withinGroupTiles p first batch = tilePrefix p batch := by
  have hj : batch - first ≤ 31 := by omega
  have h := groupTiles_eq p (hFirst.trans hb.le) (show batch - first ≤ 32 by omega)
  simpa [withinGroupTiles, Nat.min_eq_right hj, Nat.add_sub_of_le hFirst,
    Nat.min_eq_right hb.le] using h

private theorem withinGroupWork {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {first batch : Nat} (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hb : batch < p.batch) :
    Seg kernel [] l g 1 3228
      [(2729, b32 (withinGroupTiles p first batch)), (7140, b32 p.heads)] 3229
      [(7245, b32 (withinGroupTiles p first batch * p.heads))] := by
  let count := withinGroupTiles p first batch
  let work := count * p.heads
  have hFit := hp.prefixWork_signed hb.le
  have hSum := congrArg (· * p.heads) (tilePrefix_group_add p hFirst hGroup hb)
  rw [Nat.add_mul] at hSum
  change tilePrefix p first * p.heads + work = _ at hSum
  have hHeadsPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hCountLe : count ≤ work := Nat.le_mul_of_pos_right count hHeadsPos
  have hHeadsFit := hp.heads_signed
  have hCountMod : count % 4294967296 = count := Nat.mod_eq_of_lt (by omega)
  have hHeadsMod : p.heads % 4294967296 = p.heads := Nat.mod_eq_of_lt (by omega)
  have hWorkMod : work % 4294967296 = work := Nat.mod_eq_of_lt (by omega)
  have hWork64 : work % 18446744073709551616 = work := Nat.mod_eq_of_lt (by omega)
  intro t ht
  change At t 3228 [(2729, b32 count), (7140, b32 p.heads)] at ht
  change ∃ u, run kernel [] l g 1 t = some u ∧ At u 3229 [(7245, b32 work)]
  seg_fp ht using norm_bits [hCountMod,hHeadsMod,hWorkMod,hWork64,work]

private def groupExclusiveFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (first batch : Nat) :=
  (7245, b32 (withinGroupTiles p first batch * p.heads)) ::
    selectedGroupFacts p l g warp first batch

private theorem warpGroupExclusive {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hb : batch < p.batch)
    {ends : Nat → Option TState} {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 3223 (fun lane =>
      selectedGroupFacts p l (warpLane l g lane) warp first batch) shuffles votes ends)
    (hf : WarpFollowsEvent l X g cur.pos src index target) (htarget : 3227 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 3229 (fun lane =>
      groupExclusiveFacts p l (warpLane l g lane) warp first batch)
      (shuffles + if batch = first then 0 else 1) votes ends,
      WarpFollowsEvent l X g next.pos src index target := by
  let t := warpLane l g
  let F := fun lane => selectedGroupFacts p l (t lane) warp first batch
  let G := fun lane => groupExclusiveFacts p l (t lane) warp first batch
  let digit := batch - first
  let idx := digit - 1
  let part := fun lane => ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
  have hDigit : digit < 31 := by omega
  have hIdx : idx < 32 := by omega
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨gate, hGate⟩ : ∃ gate : SchedulerWarpAt l X g 3225
      (fun lane => [(467, .pred (decide (digit = 0))), (7245, b32 0)] ++ F lane)
      shuffles votes ends, gate.pos = cur.pos := by
    apply cur.advanceLocalAt
    intro lane hl
    have ht := cur.checkpoint lane hl
    obtain ⟨u, hu, hU⟩ := (prefixGate l (t lane) hDigit).apply
      (ht.mono ⟨ht.2.2.2.2.2.2.1, trivial⟩)
    obtain ⟨huA, huFrame⟩ := selectionLocal (regs := (F lane).map Prod.fst)
      (by decide) (by decide) ht.1
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hu
    have hSave := holdsSchedulerFrame ht.2.2.2.2 huFrame (fun _ h => List.mem_map_of_mem h)
    exact ⟨u, run_rtg huA, hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, hSave⟩⟩
  have hFollow : WarpFollowsEvent l X g gate.pos src index target := hGate.symm ▸ hf
  by_cases hz : batch = first
  · rw [ite_eq_left hz, Nat.add_zero]
    obtain ⟨u, hu⟩ := gate.advanceLocalAt (G := G) (pc' := 3229) (by
      intro lane hl
      have ht := gate.checkpoint lane hl
      have hHit : (gate.state lane).regs 467 = some (.pred true) := by
        simpa only [digit, hz, Nat.sub_self, decide_true] using ht.2.2.2.2.1
      obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t lane)
        Flow.code_3225 true ht hHit (by simp)
      obtain ⟨hvA, _⟩ := selectionLocal (regs := []) (by decide) (by decide) ht.1
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
      have hZero : withinGroupTiles p first batch * p.heads = 0 := by
        simp [withinGroupTiles, hz]
      exact ⟨v, run_rtg hvA, hV.mono ⟨hZero.symm ▸ hV.2.2.2.2.2.1, hV.2.2.2.2.2.2⟩⟩)
    exact ⟨u, hu.symm ▸ hFollow⟩
  · rw [ite_eq_right hz]
    have hDigitPos : digit ≠ 0 := by dsimp only [digit]; omega
    obtain ⟨ready, hReady⟩ : ∃ u : SchedulerWarpAt l X g 3227
        (fun lane => (2728, b32 idx) :: F lane) shuffles votes ends,
        u.pos = gate.pos := by
      apply gate.advanceLocalAt
      intro lane hl
      have ht := gate.checkpoint lane hl
      have hHit : (gate.state lane).regs 467 = some (.pred false) := by
        simpa only [decide_eq_false hDigitPos] using ht.2.2.2.2.1
      obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t lane)
        Flow.code_3225 false ht hHit (by simp)
      obtain ⟨hvA, _⟩ := selectionLocal (regs := []) (by decide) (by decide) ht.1
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
      have hStep : Seg kernel [] l (t lane) 1 3226 [(1222, b32 digit)] 3227 [(2728, b32 idx)] := by
        intro s hs
        seg_fp hs using norm_bits [idx]
      obtain ⟨w, hw, hW⟩ := hStep.apply (hV.mono ⟨hV.2.2.2.2.2.2.1, trivial⟩)
      obtain ⟨hwA, hwFrame⟩ := selectionLocal (regs := (F lane).map Prod.fst)
        (by decide) (by decide) hV.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
      have hSave := holdsSchedulerFrame hV.2.2.2.2.2.2 hwFrame
        (fun _ h => List.mem_map_of_mem h)
      exact ⟨w, run_rtg (run_comp hvA hwA), hW.mono ⟨hW.2.2.2.2.1, hSave⟩⟩
    have hR : WarpFollowsEvent l X g ready.pos src index target := hReady.symm ▸ hFollow
    obtain ⟨read, hRead⟩ := ready.consumeShuffleTo hp hX hg (dst := 2729) .idx
      (fun lane => b32 (part lane)) (fun _ => idx) (fun _ => 31)
      (fun lane _ => of_decide_eq_true rfl)
      (fun lane hl => by
        have ht := ready.checkpoint lane hl
        have hPart := holds_lookup ht.2.2.2.2 (show ((2728, b32 idx) :: F lane).lookup 7241 =
          some (b32 (part (laneOf l (t lane)))) from rfl)
        have hLane : laneOf l (t lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
        rw [hLane] at hPart
        exact prefixIndexOut hp hIdx (ht.mono ⟨ht.2.2.2.2.1, hPart, trivial⟩))
      (.inr hR) htarget
    obtain ⟨u, hu⟩ := read.advanceLocalAt (G := G) (pc' := 3229) (by
      intro lane hl
      have ht := read.checkpoint lane hl
      have hCount := ht.2.2.2.2.1
      have hWithin : part idx = withinGroupTiles p first batch := by
        unfold part withinGroupTiles
        rw [show idx + 1 = batch - first by dsimp only [idx, digit] at *; omega]
      rw [shflSource_idx lane hIdx, hWithin] at hCount
      have hF : Holds (read.state lane).regs (F lane) := ht.2.2.2.2.2.2
      have hArgs : At (read.state lane) 3228
          [(2729, b32 (withinGroupTiles p first batch)), (7140, b32 p.heads)] :=
        ht.mono ⟨hCount, holds_lookup hF (show (F lane).lookup 7140 = _ from rfl), trivial⟩
      obtain ⟨v, hv, hV⟩ := (withinGroupWork hp (t lane) hFirst hGroup hb).apply hArgs
      obtain ⟨hvA, hvFrame⟩ := selectionLocal (regs := (F lane).map Prod.fst)
        (by decide) (by decide) hArgs.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
      have hSave := holdsSchedulerFrame hF hvFrame (fun _ h => List.mem_map_of_mem h)
      exact ⟨v, run_rtg hvA, hV.mono ⟨hV.2.2.2.2.1, hSave⟩⟩)
    exact ⟨u, hu.symm ▸ hRead hR⟩

private theorem warpGroupCoordinates {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {ends : Nat → Option TState} {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 3229 (fun lane =>
      groupExclusiveFacts p l (warpLane l g lane) warp first batch) shuffles votes ends)
    (hFollow : WarpFollowsEvent l X g cur.pos src index target) (hTarget : 3231 < target.pc) :
    ∃ u : SchedulerWarpAt l X g 3274 (fun _ => firstActiveTileFacts p l g warp batch)
      (shuffles + 1) votes ends, WarpFollowsEvent l X g u.pos src index target := by
  let t := warpLane l g
  let beforeGroup := tilePrefix p first * p.heads
  let within := withinGroupTiles p first batch * p.heads
  let work := tilePrefix p batch * p.heads
  let ref := batch - first
  let localTiles := groupLaneTiles p first
  let F := fun lane => groupExclusiveFacts p l (t lane) warp first batch
  let G := fun lane => (7150, b32 p.batch) :: (7157, b32 800) :: F lane
  have hTotal : beforeGroup + within = work := by
    have h := congrArg (· * p.heads) (tilePrefix_group_add p hFirst hGroup hb)
    rwa [Nat.add_mul] at h
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hRef : ref < 32 := by omega
  have hCta : g / l.block < 2 ^ 31 := by
    have hGrid : g / l.block < l.grid :=
      (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    exact hGrid.trans hp.grid.2.2
  obtain ⟨ready, hReady⟩ := cur.advanceLocalAt (G := G) (pc' := 3231) (by
    intro lane hl
    have ht := cur.checkpoint lane hl
    obtain ⟨u, hu, hU⟩ := coordinateParams hp (g := t lane) ht (of_decide_eq_true rfl)
    exact ⟨u, run_rtg hu, hU⟩)
  have hR : WarpFollowsEvent l X g ready.pos src index target := hReady.symm ▸ hFollow
  obtain ⟨read, hRead⟩ := ready.consumeShuffleTo hp hX hg (dst := 2730) .idx
    (fun lane => b32 (localTiles lane)) (fun _ => ref) (fun _ => 31)
    (fun lane _ => of_decide_eq_true rfl)
    (fun lane hl => by
      have ht := ready.checkpoint lane hl
      have hValue := holds_lookup ht.2.2.2.2 (show (G lane).lookup 7240 =
        some (b32 (localTiles (laneOf l (t lane)))) from rfl)
      have hLane : laneOf l (t lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      rw [hLane] at hValue
      exact tileCountOut hp hRef (ht.mono ⟨holds_lookup ht.2.2.2.2
        (show (G lane).lookup 1222 = some (b32 ref) from rfl), hValue, trivial⟩))
    (.inr hR) hTarget
  obtain ⟨active, hActive⟩ := read.advanceLocalAt (pc' := 3274)
    (G := fun _ => firstActiveTileFacts p l g warp batch) (by
      intro lane hl
      let th := t lane
      have hSame : th / l.block = g / l.block := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
      have ht := read.checkpoint lane hl
      have hF : Holds (read.state lane).regs (G lane) := ht.2.2.2.2.2
      have hCtaWord : (read.state lane).regs 1072 = some (b32 (g / l.block)) := by
        rw [← hSame]
        exact holds_lookup hF rfl
      have hArgs : At (read.state lane) 3232
          [(1221, b32 beforeGroup), (7245, b32 within), (1072, b32 (g / l.block))] :=
        ht.mono ⟨holds_lookup hF (show (G lane).lookup 1221 = _ from rfl),
          holds_lookup hF (show (G lane).lookup 7245 = _ from rfl), hCtaWord, trivial⟩
      obtain ⟨u, hu, hU⟩ := (relativeGroupItem th l (hTotal.symm ▸ hLo) hCta).apply hArgs
      have hTiles : (read.state lane).regs 2730 = some (b32 (requestTiles p batch)) := by
        have h := ht.2.2.2.2.1
        change (read.state lane).regs 2730 =
          some (b32 (localTiles (shflSource .idx lane ref 31).1)) at h
        have hVal : localTiles ref = requestTiles p batch := by
          have hLt : ref < 31 := by omega
          simp [localTiles, groupLaneTiles, hLt, Nat.add_sub_of_le hFirst, ref, hb]
        rwa [shflSource_idx lane hRef, hVal] at h
      let keep := (2730, b32 (requestTiles p batch)) :: G lane
      have hKeep : Holds (read.state lane).regs keep := ⟨hTiles, hF⟩
      obtain ⟨huA, huFrame⟩ := selectionLocal (regs := keep.map Prod.fst) (by decide)
        (by decide) hArgs.1 (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hu
      have hs := holdsSchedulerFrame hKeep huFrame (fun _ hm => List.mem_map_of_mem hm)
      have hItem := hU.2.2.2.2.1
      change u.regs 2732 = some (b32 (g / l.block - (beforeGroup + within))) at hItem
      rw [hTotal] at hItem
      have hInput : At u 3234
          [(2730, b32 (requestTiles p batch)), (7140, b32 p.heads),
           (2732, b32 (g / l.block - work)), (7157, b32 800),
           (7150, b32 p.batch), (7247, b32 batch)] :=
        hU.mono ⟨hs.1, holds_lookup hs (show keep.lookup 7140 = _ from rfl), hItem,
          holds_lookup hs (show keep.lookup 7157 = _ from rfl),
          holds_lookup hs (show keep.lookup 7150 = _ from rfl),
          holds_lookup hs (show keep.lookup 7247 = _ from rfl), trivial⟩
      have hDispatch : Holds u.regs (dispatchInput p l warp) :=
        ⟨holds_lookup hs (show keep.lookup 1062 = _ from rfl),
          holds_lookup hs (show keep.lookup 2535 = _ from rfl),
          holds_lookup hs (show keep.lookup 7502 = _ from rfl),
          holds_lookup hs (show keep.lookup 7503 = _ from rfl),
          holds_lookup hs (show keep.lookup 7506 = _ from rfl), trivial⟩
      obtain ⟨v, hv, hV⟩ := selectedTileWithDispatch hp (thread := th) hb hLo hHi hInput hDispatch
      exact ⟨v, run_rtg (run_comp huA hv), hV⟩)
  exact ⟨active, hActive.symm ▸ hRead hR⟩

/-- The complete active scheduler picks the actual batch and query tile for every CTA. -/
theorem activeTileOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index : Nat} {target : Event} (hg : g < l.threads) (hWarp : warpIndex l g < 8)
    (hSrc : src < 32) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hEvent : X.get (warpLane l g src,index) = some target) (hTarget : 3231 < target.pc) :
    let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
    ∃ batch ord, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      ∃ (ends : Nat → Option TState) (u : SchedulerWarpAt l X g 3274
        (fun _ => firstActiveTileFacts p l g warp batch) ord 1 ends),
      WarpFollowsEvent l X g u.pos src index target := by
  obtain ⟨first, batch, ord, hFirst, hGroup, hb, hLo, hHi, ends, chosen, hChosen⟩ :=
    activeBatchOfEvent hp hX hg hWarp hSrc hWork hCuQ hEvent (by omega)
  obtain ⟨exclusive, hPrefix⟩ :=
    warpGroupExclusive hp hX hg hFirst hGroup hb chosen hChosen (by omega)
  obtain ⟨u, hu⟩ := warpGroupCoordinates hp hX hg hFirst hGroup hb hLo hHi exclusive hPrefix hTarget
  exact ⟨batch, _, hb, hLo, hHi, ends, u, hu⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g first batch shuffles votes : Nat}
    {warp : Fin 8} (hg : g < l.threads)
include hp hMax hg

private theorem warpGroupExclusiveOfMaximal (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hb : batch < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3223 (fun lane =>
      selectedGroupFacts p l (warpLane l g lane) warp first batch) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 3229 (fun lane =>
      groupExclusiveFacts p l (warpLane l g lane) warp first batch)
      (shuffles + if batch = first then 0 else 1) votes ends) := by
  let t := warpLane l g
  let F := fun lane => selectedGroupFacts p l (t lane) warp first batch
  let G := fun lane => groupExclusiveFacts p l (t lane) warp first batch
  let digit := batch - first
  let idx := digit - 1
  let part := fun lane => ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
  have hDigit : digit < 31 := by omega
  have hIdx : idx < 32 := by omega
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨gate⟩ : Nonempty (SchedulerWarpReached l X g 3225
      (fun lane => [(467, .pred (decide (digit = 0))), (7245, b32 0)] ++ F lane)
      shuffles votes ends) := by
    apply cur.advanceLocal
    intro lane hl
    have ht := cur.checkpoint lane hl
    obtain ⟨u, hu, hU⟩ := (prefixGate l (t lane) hDigit).apply
      (ht.mono ⟨ht.2.2.2.2.2.2.1, trivial⟩)
    obtain ⟨huA, huFrame⟩ := selectionLocal (regs := (F lane).map Prod.fst)
      (by decide) (by decide) ht.1
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hu
    have hSave := holdsSchedulerFrame ht.2.2.2.2 huFrame (fun _ h => List.mem_map_of_mem h)
    exact ⟨u, run_rtg huA, hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, hSave⟩⟩
  by_cases hz : batch = first
  · rw [ite_eq_left hz, Nat.add_zero]
    exact gate.advanceLocal (G := G) (pc' := 3229) (by
      intro lane hl
      have ht := gate.checkpoint lane hl
      have hHit : (gate.state lane).regs 467 = some (.pred true) := by
        simpa only [digit, hz, Nat.sub_self, decide_true] using ht.2.2.2.2.1
      obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t lane)
        Flow.code_3225 true ht hHit (by simp)
      obtain ⟨hvA, _⟩ := selectionLocal (regs := []) (by decide) (by decide) ht.1
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
      have hZero : withinGroupTiles p first batch * p.heads = 0 := by
        simp [withinGroupTiles, hz]
      exact ⟨v, run_rtg hvA, hV.mono ⟨hZero.symm ▸ hV.2.2.2.2.2.1, hV.2.2.2.2.2.2⟩⟩)
  · rw [ite_eq_right hz]
    have hDigitPos : digit ≠ 0 := by dsimp only [digit]; omega
    obtain ⟨ready⟩ : Nonempty (SchedulerWarpReached l X g 3227
        (fun lane => (2728, b32 idx) :: F lane) shuffles votes ends) := by
      apply gate.advanceLocal
      intro lane hl
      have ht := gate.checkpoint lane hl
      have hHit : (gate.state lane).regs 467 = some (.pred false) := by
        simpa only [decide_eq_false hDigitPos] using ht.2.2.2.2.1
      obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t lane)
        Flow.code_3225 false ht hHit (by simp)
      obtain ⟨hvA, _⟩ := selectionLocal (regs := []) (by decide) (by decide) ht.1
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
      have hStep : Seg kernel [] l (t lane) 1 3226 [(1222, b32 digit)] 3227 [(2728, b32 idx)] := by
        intro s hs
        seg_fp hs using norm_bits [idx]
      obtain ⟨w, hw, hW⟩ := hStep.apply (hV.mono ⟨hV.2.2.2.2.2.2.1, trivial⟩)
      obtain ⟨hwA, hwFrame⟩ := selectionLocal (regs := (F lane).map Prod.fst)
        (by decide) (by decide) hV.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
      have hSave := holdsSchedulerFrame hV.2.2.2.2.2.2 hwFrame
        (fun _ h => List.mem_map_of_mem h)
      exact ⟨w, run_rtg (run_comp hvA hwA), hW.mono ⟨hW.2.2.2.2.1, hSave⟩⟩
    obtain ⟨read⟩ := ready.consumeShuffle hp hMax hg (dst := 2729) .idx
      (fun lane => b32 (part lane)) (fun _ => idx) (fun _ => 31)
      (fun lane _ => of_decide_eq_true rfl)
      (fun lane hl => by
        have ht := ready.checkpoint lane hl
        have hPart := holds_lookup ht.2.2.2.2 (show ((2728, b32 idx) :: F lane).lookup 7241 =
          some (b32 (part (laneOf l (t lane)))) from rfl)
        have hLane : laneOf l (t lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
        rw [hLane] at hPart
        exact prefixIndexOut hp hIdx (ht.mono ⟨ht.2.2.2.2.1, hPart, trivial⟩))
    exact read.advanceLocal (G := G) (pc' := 3229) (by
      intro lane hl
      have ht := read.checkpoint lane hl
      have hCount := ht.2.2.2.2.1
      have hWithin : part idx = withinGroupTiles p first batch := by
        unfold part withinGroupTiles
        rw [show idx + 1 = batch - first by dsimp only [idx, digit] at *; omega]
      rw [shflSource_idx lane hIdx, hWithin] at hCount
      have hF : Holds (read.state lane).regs (F lane) := ht.2.2.2.2.2.2
      have hArgs : At (read.state lane) 3228
          [(2729, b32 (withinGroupTiles p first batch)), (7140, b32 p.heads)] :=
        ht.mono ⟨hCount, holds_lookup hF (show (F lane).lookup 7140 = _ from rfl), trivial⟩
      obtain ⟨v, hv, hV⟩ := (withinGroupWork hp (t lane) hFirst hGroup hb).apply hArgs
      obtain ⟨hvA, hvFrame⟩ := selectionLocal (regs := (F lane).map Prod.fst)
        (by decide) (by decide) hArgs.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
      have hSave := holdsSchedulerFrame hF hvFrame (fun _ h => List.mem_map_of_mem h)
      exact ⟨v, run_rtg hvA, hV.mono ⟨hV.2.2.2.2.1, hSave⟩⟩)

private theorem warpGroupCoordinatesOfMaximal (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3229 (fun lane =>
      groupExclusiveFacts p l (warpLane l g lane) warp first batch) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 3274 (fun _ => firstActiveTileFacts p l g warp batch)
      (shuffles + 1) votes ends) := by
  let t := warpLane l g
  let beforeGroup := tilePrefix p first * p.heads
  let within := withinGroupTiles p first batch * p.heads
  let work := tilePrefix p batch * p.heads
  let ref := batch - first
  let localTiles := groupLaneTiles p first
  let F := fun lane => groupExclusiveFacts p l (t lane) warp first batch
  let G := fun lane => (7150, b32 p.batch) :: (7157, b32 800) :: F lane
  have hTotal : beforeGroup + within = work := by
    have h := congrArg (· * p.heads) (tilePrefix_group_add p hFirst hGroup hb)
    rwa [Nat.add_mul] at h
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hRef : ref < 32 := by omega
  have hCta : g / l.block < 2 ^ 31 := by
    have hGrid : g / l.block < l.grid :=
      (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    exact hGrid.trans hp.grid.2.2
  obtain ⟨ready⟩ := cur.advanceLocal (G := G) (pc' := 3231) (by
    intro lane hl
    have ht := cur.checkpoint lane hl
    obtain ⟨u, hu, hU⟩ := coordinateParams hp (g := t lane) ht (of_decide_eq_true rfl)
    exact ⟨u, run_rtg hu, hU⟩)
  obtain ⟨read⟩ := ready.consumeShuffle hp hMax hg (dst := 2730) .idx
    (fun lane => b32 (localTiles lane)) (fun _ => ref) (fun _ => 31)
    (fun lane _ => of_decide_eq_true rfl)
    (fun lane hl => by
      have ht := ready.checkpoint lane hl
      have hValue := holds_lookup ht.2.2.2.2 (show (G lane).lookup 7240 =
        some (b32 (localTiles (laneOf l (t lane)))) from rfl)
      have hLane : laneOf l (t lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      rw [hLane] at hValue
      exact tileCountOut hp hRef (ht.mono ⟨holds_lookup ht.2.2.2.2
        (show (G lane).lookup 1222 = some (b32 ref) from rfl), hValue, trivial⟩))
  exact read.advanceLocal (pc' := 3274)
    (G := fun _ => firstActiveTileFacts p l g warp batch) (by
      intro lane hl
      let th := t lane
      have hSame : th / l.block = g / l.block := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
      have ht := read.checkpoint lane hl
      have hF : Holds (read.state lane).regs (G lane) := ht.2.2.2.2.2
      have hCtaWord : (read.state lane).regs 1072 = some (b32 (g / l.block)) := by
        rw [← hSame]
        exact holds_lookup hF rfl
      have hArgs : At (read.state lane) 3232
          [(1221, b32 beforeGroup), (7245, b32 within), (1072, b32 (g / l.block))] :=
        ht.mono ⟨holds_lookup hF (show (G lane).lookup 1221 = _ from rfl),
          holds_lookup hF (show (G lane).lookup 7245 = _ from rfl), hCtaWord, trivial⟩
      obtain ⟨u, hu, hU⟩ := (relativeGroupItem th l (hTotal.symm ▸ hLo) hCta).apply hArgs
      have hTiles : (read.state lane).regs 2730 = some (b32 (requestTiles p batch)) := by
        have h := ht.2.2.2.2.1
        change (read.state lane).regs 2730 =
          some (b32 (localTiles (shflSource .idx lane ref 31).1)) at h
        have hVal : localTiles ref = requestTiles p batch := by
          have hLt : ref < 31 := by omega
          simp [localTiles, groupLaneTiles, hLt, Nat.add_sub_of_le hFirst, ref, hb]
        rwa [shflSource_idx lane hRef, hVal] at h
      let keep := (2730, b32 (requestTiles p batch)) :: G lane
      have hKeep : Holds (read.state lane).regs keep := ⟨hTiles, hF⟩
      obtain ⟨huA, huFrame⟩ := selectionLocal (regs := keep.map Prod.fst) (by decide)
        (by decide) hArgs.1 (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hu
      have hs := holdsSchedulerFrame hKeep huFrame (fun _ hm => List.mem_map_of_mem hm)
      have hItem := hU.2.2.2.2.1
      change u.regs 2732 = some (b32 (g / l.block - (beforeGroup + within))) at hItem
      rw [hTotal] at hItem
      have hInput : At u 3234
          [(2730, b32 (requestTiles p batch)), (7140, b32 p.heads),
           (2732, b32 (g / l.block - work)), (7157, b32 800),
           (7150, b32 p.batch), (7247, b32 batch)] :=
        hU.mono ⟨hs.1, holds_lookup hs (show keep.lookup 7140 = _ from rfl), hItem,
          holds_lookup hs (show keep.lookup 7157 = _ from rfl),
          holds_lookup hs (show keep.lookup 7150 = _ from rfl),
          holds_lookup hs (show keep.lookup 7247 = _ from rfl), trivial⟩
      have hDispatch : Holds u.regs (dispatchInput p l warp) :=
        ⟨holds_lookup hs (show keep.lookup 1062 = _ from rfl),
          holds_lookup hs (show keep.lookup 2535 = _ from rfl),
          holds_lookup hs (show keep.lookup 7502 = _ from rfl),
          holds_lookup hs (show keep.lookup 7503 = _ from rfl),
          holds_lookup hs (show keep.lookup 7506 = _ from rfl), trivial⟩
      obtain ⟨v, hv, hV⟩ := selectedTileWithDispatch hp (thread := th) hb hLo hHi hInput hDispatch
      exact ⟨v, run_rtg (run_comp huA hv), hV⟩)

/-- A reached selection from any request group supplies the softmax tile coordinates. -/
theorem groupActiveTileOfChosen (hFirst : first ≤ batch) (hGroup : batch < first+31)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3223 (fun lane =>
      selectedGroupFacts p l (warpLane l g lane) warp first batch) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 3274 (fun _ => firstActiveTileFacts p l g warp batch)
      (shuffles + (if batch = first then 0 else 1) + 1) votes ends) := by
  obtain ⟨pref⟩ := warpGroupExclusiveOfMaximal hp hMax hg hFirst hGroup hb cur
  exact warpGroupCoordinatesOfMaximal hp hMax hg hFirst hGroup hb hLo hHi pref


end
end PTX.Kernels.TmlFa4Fwd.Softmax
