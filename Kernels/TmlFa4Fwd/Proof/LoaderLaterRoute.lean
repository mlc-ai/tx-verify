-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderLaterScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

variable {p : Params} {l : Launch} {m : Mem0}

theorem laterTotalTemplate (hp : Pre p l m) (g : Nat) (t : TState) (sum : Nat) (hpc : t.pc = 283)
    (hf : t.fault = none) (hv : t.regs 7163 = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7164 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_283) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7164 none (.reg 7163) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hBlock, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

/-- Use lane 31's total for the current group and either move to the next group or select work
within this one. The cutoff remains a signed scheduler word by the launch precondition. -/
theorem laterGroupLimit (hp : Pre p l m) (g : Nat) {first cta : Nat} (hf : first ≤ p.batch)
    (hCta : cta < 2 ^ 31) :
    let count := ∑ lane ∈ Finset.range 32, groupLaneTiles p first lane
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    Seg kernel [] l g 4 284
      [(7164, b32 count), (7136, b32 p.heads),
       (7160, b32 (tilePrefix p first * p.heads)), (1072, b32 cta)]
      (if limit ≤ cta then 234 else 288) [(7160, b32 limit), (7166, b32 limit)] := by
  dsimp only
  let count := ∑ lane ∈ Finset.range 32, groupLaneTiles p first lane
  let start := tilePrefix p first * p.heads
  let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
  have hFormula : count * p.heads + start = limit := by
    have hi := groupTiles_eq p hf (by decide : 32 ≤ 32)
    change tilePrefix p first + count = tilePrefix p (min p.batch (first + 31)) at hi
    simpa only [Nat.add_mul, Nat.add_comm, start, limit] using
      congrArg (fun n => n * p.heads) hi
  have hh := hp.heads_signed
  have hLimit : limit < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hStart : start < 2 ^ 31 := hp.prefixWork_signed hf
  have hHeads : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hCount : count < 2 ^ 32 := by
    have := Nat.le_mul_of_pos_right count hHeads
    omega
  have hh32 : p.heads < 2 ^ 32 := by omega
  have hStart32 : start < 2 ^ 32 := by omega
  have hLimit32 : limit < 2 ^ 32 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  intro t ht
  change At t 284 [(7164, b32 count), (7136, b32 p.heads), (7160, b32 start), (1072, b32 cta)]
    at ht
  obtain ⟨u, hRun, hu⟩ : ∃ u, run kernel [] l g 3 t = some u ∧
      At u 287 [(87, .pred (decide (limit ≤ cta))), (7160, b32 limit), (7166, b32 limit)] := by
    seg_fp ht using
      simp only [b32, truncBits_ofNat hCount (by decide), truncBits_ofNat hh32 (by decide),
        truncBits_ofNat hStart32 (by decide), truncBits_ofNat hCta32 (by decide),
        ← BitVec.ofNat_add, ← BitVec.ofNat_mul, hFormula, truncBits_ofNat hLimit32 (by decide),
        compare, Option.getD_some, signedWord hLimit, signedWord hCta, Int.ofNat_le]
  have hReg : u.regs 87 = some (.pred (decide (limit ≤ cta))) :=
    holds_mem hu.2.2.2.2 (by simp)
  obtain ⟨v, hBra, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_287 _ hu hReg (by simp)
  refine ⟨v, run_comp hRun hBra, ?_⟩
  change At v (if limit ≤ cta then 234 else 288) [(7160, b32 limit), (7166, b32 limit)]
  simpa only [decide_eq_true_eq] using hv.mono hv.2.2.2.2.2


/-- The chosen later group carries the total and each lane's contributions into selection. -/
def loaderLaterChoiceFacts (p : Params) (l : Launch) (g warp first lane : Nat) :
    List (Nat × Value) :=
  [(7166, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)), (7165, b32 first),
    (7164, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
    (7163, b32 (prefixWindow (groupLaneTiles p first) 32 lane)),
    (7162, b32 (groupLaneTiles p first lane)), (7136, b32 p.heads)] ++
  loaderCuQFacts p l (warpLane l g lane) warp

private def laterLimit (p : Params) (first : Nat) : Nat :=
  tilePrefix p (min p.batch (first + 31)) * p.heads

private def laterPart (p : Params) (first : Nat) : Nat → Nat :=
  prefixWindow (groupLaneTiles p first) 32

private theorem laterTotalFresh {p : Params} {l : Launch} {g warp first lane : Nat}
    {pair : Nat × Value} (hm : pair ∈ laterScanFacts p l g warp first 5 lane) : pair.1 ≠ 7164 := by
  have hMem := List.mem_map_of_mem (f := Prod.fst) hm
  intro he
  rw [he] at hMem
  exact (of_decide_eq_true rfl : 7164 ∉ (laterScanFacts p l g warp first 5 lane).map Prod.fst)
    hMem

private theorem laterTotalOut (hp : Pre p l m) {g warp first lane : Nat} {t : TState}
    (ht : At t 283 (laterScanFacts p l g warp first 5 lane)) :
    out kernel Assumptions.all l (warpLane l g lane) t =
      .ev (.shfl .idx (b32 (laterPart p first lane)) 31 31
        (fun v _ => next (setReg t 7164 v))) := by
  refine (loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans ?_
  exact laterTotalTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1

private def laterRouteFrame (p : Params) (l : Launch) (g warp first lane : Nat) :
    List (Nat × Value) :=
  let limit := laterLimit p first
  let count := ∑ i ∈ Finset.range 32, groupLaneTiles p first i
  [(7166, b32 limit), (7160, b32 limit), (7165, b32 first), (1075, b32 (g / l.block + 1)),
    (7164, b32 count), (7163, b32 (laterPart p first lane)),
    (7162, b32 (groupLaneTiles p first lane)),
    (7136, b32 p.heads)] ++ loaderCuQFacts p l (warpLane l g lane) warp

private theorem laterRouteLocal (hp : Pre p l m) {g warp first lane : Nat} (hg : g < l.threads)
    (hf : first < p.batch) (hl : lane < 32) {t : TState}
    (ht : At t 284 ((7164, b32 (laterPart p first (shflSource .idx lane 31 31).1)) ::
      laterScanFacts p l g warp first 5 lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u (if laterLimit p first ≤ g / l.block then 234 else 288)
        (laterRouteFrame p l g warp first lane) := by
  let part := laterPart p first
  let count := ∑ i ∈ Finset.range 32, groupLaneTiles p first i
  let cta := g / l.block
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCta : cta < 2 ^ 31 :=
    ((Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg).trans hp.grid.2.2
  have hTotal : part 31 = count := prefixWindow_warp _ (by decide)
  let fixed := [(7165, b32 first), (1075, b32 (cta + 1)),
    (7164, b32 count), (7163, b32 (part lane)), (7162, b32 (groupLaneTiles p first lane)),
    (7136, b32 p.heads)] ++ loaderCuQFacts p l (warpLane l g lane) warp
  let thread := warpLane l g lane
  let keep := fixed.map Prod.fst
  have hSame : thread / l.block = cta := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  have hLane : laneOf l thread = lane := (Step.sameWarp_lane hBlock hg hl).2
  have h := ht.2.2.2.2
  have hScan : Holds (t).regs (laterScanCarry p l g warp first lane) :=
    h.2.2
  have hTileFacts : Holds (t).regs (laterTilesFacts p l thread warp first) :=
    hScan.2.2.2.2.2
  have hReadFacts : Holds (t).regs (laterReadFacts p l thread warp first) :=
    hTileFacts.2
  have hCarry : Holds (t).regs (laterCarry p l thread warp first) :=
    hReadFacts.2.2.2
  have hFrame : Holds (t).regs (loaderCuQFacts p l thread warp) :=
    hCarry.2.2.2.2.2
  have hCount : (t).regs 7164 = some (b32 count) := by
    have hv := h.1
    rw [shflSource_idx lane (show (31 : Nat) < 32 by decide)] at hv
    change t.regs 7164 = some (b32 (part 31)) at hv
    rw [hTotal] at hv
    exact hv
  have hCtaWord := hFrame.2.2.2.1
  rw [hSame] at hCtaWord
  have hStop := hCarry.2.2.1
  rw [hSame] at hStop
  have hTile := hTileFacts.1
  rw [hLane] at hTile
  have hAt : At (t) 284
      [(7164, b32 count), (7136, b32 p.heads), (7160, b32 (tilePrefix p first * p.heads)),
        (1072, b32 cta)] :=
    ht.mono ⟨hCount, hCarry.2.2.2.2.1, hCarry.2.2.2.1, hCtaWord, trivial⟩
  obtain ⟨u, hu, hU⟩ := laterGroupLimit hp thread (Nat.le_of_lt hf) hCta _ hAt
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := keep) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hFixed : Holds (t).regs fixed :=
    ⟨hCarry.2.1, hStop, hCount, h.2.1, hTile, hCarry.2.2.2.2.1, hFrame⟩
  have hSave := holdsSchedulerFrame hFixed huFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, run_rtg huA, hU.mono ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hSave⟩⟩

private theorem laterRouteContinue (hp : Pre p l m) {g warp first lane : Nat} (hg : g < l.threads)
    (hf : first < p.batch) (hl : lane < 32) (hPast : laterLimit p first ≤ g / l.block) {t : TState}
    (ht : At t 284 ((7164, b32 (laterPart p first (shflSource .idx lane 31 31).1)) ::
      laterScanFacts p l g warp first 5 lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 234 (loaderFallbackFacts p l g warp first lane) := by
  obtain ⟨u, hu, hU⟩ := laterRouteLocal hp hg hf hl ht
  have h := hU.2.2.2.2
  have hAt : At u (if laterLimit p first ≤ g / l.block then 234 else 288)
      (loaderFallbackFacts p l g warp first lane) :=
    hU.mono ⟨h.2.2.2.1, h.2.2.1, h.2.1, h.2.2.2.2.2.2.2⟩
  exact ⟨u, hu, by simpa only [ite_eq_left hPast] using hAt⟩

private theorem laterRouteChoose (hp : Pre p l m) {g warp first lane : Nat} (hg : g < l.threads)
    (hf : first < p.batch) (hl : lane < 32) (hPast : ¬laterLimit p first ≤ g / l.block) {t : TState}
    (ht : At t 284 ((7164, b32 (laterPart p first (shflSource .idx lane 31 31).1)) ::
      laterScanFacts p l g warp first 5 lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 288 (loaderLaterChoiceFacts p l g warp first lane) := by
  obtain ⟨u, hu, hU⟩ := laterRouteLocal hp hg hf hl ht
  have h := hU.2.2.2.2
  have hAt : At u (if laterLimit p first ≤ g / l.block then 234 else 288)
      (loaderLaterChoiceFacts p l g warp first lane) := hU.mono
    ⟨h.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  exact ⟨u, hu, by simpa only [ite_eq_right hPast] using hAt⟩

/-- The last lane broadcasts the group total. The decoded branch uses the resulting work
limit to choose this group or continue the fallback loop. -/
theorem loaderLaterRouteWithLength {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 283 (laterScanFacts p l g warp first 5) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 283 < target.pc) :
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    let cta := g / l.block
    (limit ≤ cta ∧ ∃ next : SchedulerWarpAt l X g 234
      (loaderFallbackFacts p l g warp first) (shuffles + 1) votes ends,
      next.pos = (fun lane => cur.pos lane + 1) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target)) ∨
    (cta < limit ∧ ∃ next : SchedulerWarpAt l X g 288
      (loaderLaterChoiceFacts p l g warp first) (shuffles + 1) votes ends,
      next.pos = (fun lane => cur.pos lane + 1) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target)) := by
  dsimp only
  obtain ⟨read, hRead, _, hAdvance⟩ := cur.consumeShuffleToRecorded hp hX hg .idx
    (fun lane => b32 (laterPart p first lane)) (fun _ => 31) (fun _ => 31)
    (fun _ _ _ => laterTotalFresh) (fun lane hl => laterTotalOut hp (cur.checkpoint lane hl))
    hProgress hPc
  by_cases hPast : laterLimit p first ≤ g / l.block
  · obtain ⟨next, hPos⟩ := read.advanceLocalAt
      (fun lane hl => laterRouteContinue hp hg hf hl hPast (read.checkpoint lane hl))
    exact .inl ⟨hPast, next, hPos.trans hRead, fun h => hPos.symm ▸ hAdvance h⟩
  · obtain ⟨next, hPos⟩ := read.advanceLocalAt
      (fun lane hl => laterRouteChoose hp hg hf hl hPast (read.checkpoint lane hl))
    exact .inr ⟨Nat.lt_of_not_ge hPast, next, hPos.trans hRead, fun h => hPos.symm ▸ hAdvance h⟩

theorem loaderLaterRouteTo {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 283 (laterScanFacts p l g warp first 5) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 283 < target.pc) :
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    let cta := g / l.block
    (limit ≤ cta ∧ ∃ next : SchedulerWarpAt l X g 234
      (loaderFallbackFacts p l g warp first) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target) ∨
    (cta < limit ∧ ∃ next : SchedulerWarpAt l X g 288
      (loaderLaterChoiceFacts p l g warp first) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target) := by
  rcases loaderLaterRouteWithLength hp hX hg hf cur hProgress hPc with
    ⟨hPast,next,_,hAdvance⟩ | ⟨hFound,next,_,hAdvance⟩
  · exact .inl ⟨hPast,next,hAdvance⟩
  · exact .inr ⟨hFound,next,hAdvance⟩

/-- A maximal fallback scan takes its actual cutoff branch after broadcasting the full total. -/
theorem loaderLaterRouteOfMaximal {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 283 (laterScanFacts p l g warp first 5) shuffles votes ends) :
    if tilePrefix p (min p.batch (first + 31)) * p.heads ≤ g / l.block then
      Nonempty (SchedulerWarpReached l X g 234
        (loaderFallbackFacts p l g warp first) (shuffles + 1) votes ends)
    else
      Nonempty (SchedulerWarpReached l X g 288
        (loaderLaterChoiceFacts p l g warp first) (shuffles + 1) votes ends) := by
  change if laterLimit p first ≤ g / l.block then _ else _
  obtain ⟨read⟩ := cur.consumeShuffle hp hMax hg .idx
    (fun lane => b32 (laterPart p first lane)) (fun _ => 31) (fun _ => 31)
    (fun _ _ _ => laterTotalFresh) (fun lane hl => laterTotalOut hp (cur.checkpoint lane hl))
  split_ifs with hPast
  · exact read.advanceLocal
      (fun lane hl => laterRouteContinue hp hg hf hl hPast (read.checkpoint lane hl))
  · exact read.advanceLocal
      (fun lane hl => laterRouteChoose hp hg hf hl hPast (read.checkpoint lane hl))

/-- The old terminated fallback route. -/
theorem loaderLaterRoute {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first < p.batch)
    (cur : SchedulerWarpAt l X g 283 (laterScanFacts p l g warp first 5) shuffles votes) :
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    let cta := g / l.block
    (limit ≤ cta ∧ Nonempty (SchedulerWarpAt l X g 234
      (loaderFallbackFacts p l g warp first) (shuffles + 1) votes)) ∨
    (cta < limit ∧ Nonempty (SchedulerWarpAt l X g 288
      (loaderLaterChoiceFacts p l g warp first) (shuffles + 1) votes)) := by
  rcases loaderLaterRouteTo hp hX hg hf cur (src := 0) (index := 0) (target := ⟨284, .exit⟩)
    (.inl (fun _ _ => rfl)) (by decide) with ⟨hPast, next, _⟩ | ⟨hFound, next, _⟩
  · exact .inl ⟨hPast, ⟨next⟩⟩
  · exact .inr ⟨hFound, ⟨next⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
