-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleScan
import Kernels.TmlFa4Fwd.Flow.Code.Part049
import Kernels.TmlFa4Fwd.Flow.Code.Part050
import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionObservations

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Lemmas.Step.WarpVoteProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem firstTotalTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (sum : Nat)
    (hpc : t.pc = 3150) (hf : t.fault = none) (hv : t.regs 7241 = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7242 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_3150) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7242 none (.reg 7241) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

private theorem scanSignedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem firstLimit (l : Launch) (g : Nat) {count heads cta : Nat}
    (hc : count < 2 ^ 31) (hh : heads < 2 ^ 31)
    (hCta : cta < 2 ^ 31) (hTotal : count * heads < 2 ^ 31) :
    Seg kernel [] l g 3 3151 [(7242, b32 count), (7140, b32 heads), (1072, b32 cta)] 3154
      [(7244, b32 (count * heads)), (450, .pred (decide (cta < count * heads))),
        (7243, b32 0)] := by
  intro t ht
  have hCount32 : count < 2 ^ 32 := by omega
  have hHeads32 : heads < 2 ^ 32 := by omega
  have hTotal32 : count * heads < 2 ^ 32 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_mul, truncBits_ofNat hCount32 (by decide),
        truncBits_ofNat hHeads32 (by decide), truncBits_ofNat hCta32 (by decide),
        truncBits_ofNat hTotal32 (by decide), compare, Option.getD_some, scanSignedWord hCta,
        scanSignedWord hTotal, Int.ofNat_lt]

/-- The first group's total and lane prefix are preserved across its scheduler branch. -/
def firstRouteFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) (lane : Nat) :
    List (Nat × Value) :=
  [(7244, b32 (tilePrefix p (min p.batch 31) * p.heads)), (7243, b32 0),
    (7242, b32 (tilePrefix p (min p.batch 31))),
    (7241, b32 (prefixWindow (groupLaneTiles p 0) 32 lane))] ++
  firstScanFacts p l (warpLane l g lane) warp

private theorem firstTotalFresh {p : Params} {l : Launch} {g : Nat} {warp : Fin 8}
    (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
    (hm : pair ∈ firstUpScanFacts p l g warp 5 lane) : pair.1 ≠ 7242 := by
  have hMem := List.mem_map_of_mem (f := Prod.fst) hm
  intro he
  rw [he] at hMem
  exact (of_decide_eq_true rfl : 7242 ∉ (firstUpScanFacts p l g warp 5 lane).map Prod.fst) hMem

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem firstTotalOut (hp : Pre p l m) {g shuffles votes : Nat} {warp : Fin 8}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3150 (firstUpScanFacts p l g warp 5) shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.shfl .idx (b32 (prefixWindow (groupLaneTiles p 0) 32 lane)) 31 31
        (fun v _ => next (setReg (cur.state lane) 7242 v))) := by
  have ht := cur.checkpoint lane hl
  refine (firstScanOut (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans ?_
  exact firstTotalTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1

private theorem firstRouteLocal (hp : Pre p l m) {g shuffles votes : Nat} {warp : Fin 8}
    (hg : g < l.threads) {ends : Nat → Option TState}
    (read : SchedulerWarpAt l X g 3151
      (fun lane => (7242, b32 (prefixWindow (groupLaneTiles p 0) 32
        (shflSource .idx lane 31 31).1)) :: firstUpScanFacts p l g warp 5 lane)
      shuffles votes ends) :
    ∀ lane < 32, ∃ u, Relation.ReflTransGen
      (Tau kernel Assumptions.all l (warpLane l g lane)) (read.state lane) u ∧
      At u (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 3212 else 3155)
        (firstRouteFacts p l g warp lane) := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  let count := tilePrefix p (min p.batch 31)
  let cta := g / l.block
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLimit : count * p.heads < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hCount : count < 2 ^ 31 := by
    have hPos : 0 < p.heads := by
      have h := hp.shape.2.2.1
      simp [Params.heads]
      omega
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_right count hPos) hLimit
  have hCta : cta < 2 ^ 31 := by
    have hGrid : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    exact hGrid.trans hp.grid.2.2
  have hCountPart : part 31 = count := by
    change prefixWindow (groupLaneTiles p 0) 32 31 = _
    rw [prefixWindow_warp _ (show (31 : Nat) < 32 by decide)]
    have h := groupTiles_eq p (Nat.zero_le p.batch) (show (32 : Nat) ≤ 32 by decide)
    simpa [count, tilePrefix] using h
  intro lane hl
  let thread := warpLane l g lane
  let carry := (7242, b32 count) :: firstUpScanFacts p l g warp 5 lane
  let regs := carry.map Prod.fst
  have ht := read.checkpoint lane hl
  have hCountWord := ht.2.2.2.2.1
  rw [shflSource_idx lane (show (31 : Nat) < 32 by decide)] at hCountWord
  change (read.state lane).regs 7242 = some (b32 (part 31)) at hCountWord
  rw [hCountPart] at hCountWord
  have hCarry : Holds (read.state lane).regs carry := ⟨hCountWord, ht.2.2.2.2.2⟩
  have hWarp := (Step.sameWarp_lane hBlock hg hl).1
  have hSame : thread / l.block = cta := hWarp.1.2.2.symm
  have hFrame : Holds (read.state lane).regs (firstScanFacts p l thread warp) := hCarry.2.2
  have hHeads := hFrame.2.1
  have hCtaWord : (read.state lane).regs 1072 = some (b32 cta) := by
    have h := holds_mem hFrame (by
      simp [firstScanFacts, schedulerLane, schedulerEntry, dispatchOutput] :
      (1072, b32 (thread / l.block)) ∈ firstScanFacts p l thread warp)
    rwa [hSame] at h
  have hAt : At (read.state lane) 3151
      [(7242, b32 count), (7140, b32 p.heads), (1072, b32 cta)] :=
    ht.mono ⟨hCountWord, hHeads, hCtaWord, trivial⟩
  obtain ⟨u, hu, hU⟩ := firstLimit l thread hCount hp.heads_signed hCta hLimit _ hAt
  obtain ⟨huA, huFrame⟩ := firstScanLocal (regs := regs) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hPreserved := holdsSchedulerFrame hCarry huFrame (fun _ h => List.mem_map_of_mem h)
  let guard := decide (cta < count * p.heads)
  have hBranch : At u 3154
      ((450, .pred guard) :: (7244, b32 (count * p.heads)) :: (7243, b32 0) ::
        carry) :=
    hU.mono ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.2.1, hPreserved⟩
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_3154 guard hBranch hBranch.2.2.2.2.1 (by simp)
  have hEq : tauStep kernel Assumptions.all l thread u = tauStep kernel [] l thread u :=
    Assumptions.tauStep_all_eq_nil (by rw [hBranch.1]; decide)
      (hBranch.1.symm ▸ Flow.code_3154) rfl
  have hvA : run kernel Assumptions.all l thread 1 u = some v := by
    simpa only [run, hEq] using hv
  refine ⟨v, run_rtg (run_comp huA hvA), ?_⟩
  have hLast : Holds v.regs (firstRouteFacts p l g warp lane) := by
    unfold firstRouteFacts
    have h := hV.2.2.2.2.2
    change Holds v.regs
      ((7244, b32 (count * p.heads)) :: (7243, b32 0) ::
        (7242, b32 count) :: firstUpScanFacts p l g warp 5 lane) at h
    exact h
  simpa only [guard, cta, count, decide_eq_true_eq, Nat.reduceAdd] using hV.mono hLast

/-- Broadcast the computed total from lane 31, then take the actual first-group branch.
Every lane selects the same path because the total and CTA index are common. -/
theorem warpFirstRouteTo (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads) {ends : Nat → Option TState}
    {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 3150 (firstUpScanFacts p l g warp 5) shuffles votes ends)
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hTarget : 3150 < target.pc) :
    ∃ next : SchedulerWarpAt l X g
        (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 3212 else 3155)
        (firstRouteFacts p l g warp) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  obtain ⟨read, hRead⟩ := cur.consumeShuffleTo hp hX hg .idx (fun lane => b32 (part lane))
    (fun _ => 31) (fun _ => 31) firstTotalFresh (firstTotalOut hp cur) hProgress hTarget
  obtain ⟨next, hNextPos⟩ := read.advanceLocalAt (firstRouteLocal hp hg read)
  exact ⟨next, fun h => hNextPos.symm ▸ hRead h⟩

/-- The first scheduler branch of a maximal softmax warp uses the actual collective's
total from lane 31. -/
theorem warpFirstRouteOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3150 (firstUpScanFacts p l g warp 5) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 3212 else 3155)
      (firstRouteFacts p l g warp) (shuffles + 1) votes ends) := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  obtain ⟨read⟩ := cur.consumeShuffle hp hMax hg .idx (fun lane => b32 (part lane))
    (fun _ => 31) (fun _ => 31) firstTotalFresh (firstTotalOut hp cur.toSchedulerWarpAt)
  exact read.advanceLocal (firstRouteLocal hp hg read.toSchedulerWarpAt)

/-- The observed warp takes its first route exactly when the CTA falls before the
protected first-group tile cutoff. -/
theorem firstSchedulerRouteOfEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index : Nat} {target : Event} (hg : g < l.threads) (hWarp : warpIndex l g < 8)
    (hSrc : src < 32)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hEvent : X.get (warpLane l g src,index) = some target) (hPc : 3150 < target.pc) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    ∃ (ends : Nat → Option TState)
      (cur : SchedulerWarpAt l X g
        (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 3212 else 3155)
        (firstRouteFacts p l g warp) 10 0 ends),
      WarpFollowsEvent l X g cur.pos src index target := by
  obtain ⟨ends, down, hDown⟩ :=
    firstSchedulerWarpOfEvent hp hX hg hWarp hSrc hProtected hEvent (by omega)
  obtain ⟨tiles, hTiles⟩ := warpFirstLaneTiles hp hg down
  have hTileFollow : WarpFollowsEvent l X g tiles.pos src index target := hTiles.symm ▸ hDown
  obtain ⟨scan, hScan⟩ := warpFirstScanTo hp hX hg tiles (.inr hTileFollow) (by omega)
  obtain ⟨route, hRoute⟩ := warpFirstRouteTo hp hX hg scan (.inr (hScan hTileFollow)) hPc
  exact ⟨ends, route, hRoute (hScan hTileFollow)⟩
/-- A nonexhausted softmax group sets the default coordinates and falls through to the ballot. -/
theorem firstGroupAvailable (l : Launch) (g : Nat) {first batch : Nat}
    (hGroup : first < batch) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 4 3212 [(7243, b32 first), (7247, b32 batch)] 3216
      [(783, .pred false), (7246, b32 0)] := by
  intro t ht
  have hf : first < 2 ^ 31 := by omega
  obtain ⟨u, hu, hU⟩ : ∃ u, run kernel [] l g 3 t = some u ∧
      At u 3215 [(465, .pred false), (783, .pred false), (7246, b32 0)] := by
    seg_fp ht using
      first
      | rfl
      | simp only [compare, Option.getD_some, truncBits_ofNat (show first < 2 ^ 32 by omega)
          (by decide), truncBits_ofNat (show batch < 2 ^ 32 by omega) (by decide),
          scanSignedWord hf, scanSignedWord hBatch, ge_iff_le, Int.ofNat_le,
          decide_eq_false (Nat.not_le_of_lt hGroup)]
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_3215 false hU hU.2.2.2.2.1 (by simp)
  exact ⟨v, run_comp hu hv, hV.mono hV.2.2.2.2.2⟩

/-- The decoded ballot comparison marks precisely the lanes preceding the selected batch. -/
theorem groupBallotSegment {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {first batch lane cta : Nat} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch) (hLane : lane < 32)
    (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel [] l g 4 3216
      [(7242, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
       (7241, b32 (∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i)),
       (7244, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
       (7140, b32 p.heads), (1072, b32 cta)] 3220
      [(1221, b32 (tilePrefix p first * p.heads)),
       (466, .pred (decide (first + lane < batch)))] := by
  let start := tilePrefix p first * p.heads
  let tail := tilePrefix p (min p.batch (first + 31)) * p.heads
  let total := ∑ i ∈ Finset.range 32, groupLaneTiles p first i
  let part := ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
  have hStart : start < 2 ^ 31 := hp.prefixWork_signed (by omega)
  have hTail : tail < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hPart : part * p.heads + start < 2 ^ 31 := by
    have h := congrArg (fun n => n * p.heads) (groupTiles_eq p (by omega : first ≤ p.batch)
      (by omega : lane + 1 ≤ 32))
    change (tilePrefix p first + part) * p.heads = _ at h
    rw [Nat.add_mul, Nat.add_comm] at h
    exact h ▸ hp.prefixWork_signed (Nat.min_le_left _ _)
  have hTotal : total * p.heads + start = tail := by
    have h := congrArg (fun n => n * p.heads) (groupTiles_eq p (by omega : first ≤ p.batch)
      (by decide : 32 ≤ 32))
    change (tilePrefix p first + total) * p.heads = tail at h
    rw [Nat.add_mul, Nat.add_comm] at h
    exact h
  have hBallot : part * p.heads + start ≤ cta ↔ first + lane < batch := by
    simpa only [Nat.add_mul, Nat.add_comm, start] using
      groupBallot_iff p hFirst hGroup hBatch hLane hLo hHi
  have hHeads := hp.heads_signed
  have hCta : cta < 2 ^ 31 := lt_trans hHi (hp.prefixWork_signed (by omega))
  have hPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hTotal32 : total < 2 ^ 32 := by have := Nat.le_mul_of_pos_right total hPos; omega
  have hPart32 : part < 2 ^ 32 := by have := Nat.le_mul_of_pos_right part hPos; omega
  have hTail32 : tail < 2 ^ 32 := by omega
  have hHeads32 : p.heads < 2 ^ 32 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  have hTotalWork32 : total * p.heads < 2 ^ 32 := by omega
  have hStart32 : start < 2 ^ 32 := by omega
  have hPartWork32 : part * p.heads + start < 2 ^ 32 := by omega
  have hSub : tail - total * p.heads = start := by omega
  intro t ht
  change At t 3216
    [(7242, b32 total), (7241, b32 part), (7244, b32 tail), (7140, b32 p.heads), (1072, b32 cta)]
    at ht
  change ∃ u, run kernel [] l g 4 t = some u ∧
    At u 3220 [(1221, b32 start), (466, .pred (decide (first + lane < batch)))]
  seg_fp ht using
    simp only [b32, truncBits_ofNat hTotal32 (by decide), truncBits_ofNat hPart32 (by decide),
      truncBits_ofNat hTail32 (by decide), truncBits_ofNat hHeads32 (by decide),
      truncBits_ofNat hCta32 (by decide), truncBits_ofNat hStart32 (by decide),
      ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
      truncBits_ofNat hTotalWork32 (by decide), truncBits_ofNat hPartWork32 (by decide),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show total * p.heads < 2 ^ 64 by omega)
        (show total * p.heads ≤ tail by omega),
      hSub, compare, Option.getD_some, scanSignedWord hPart, scanSignedWord hCta,
      Int.ofNat_le, hBallot]

theorem groupVoteOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hit : Bool)
    (hpc : t.pc = 3220) (hf : t.fault = none) (hv : t.regs 466 = some (.pred hit)) :
    out kernel [] l g t = .ev (.vote (2 ^ 32 - 1) hit
      (fun mask => next (setReg t 2727 (b32 mask.toNat)))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_3220) rfl rfl]
  change Out.ev (voteTmpl l g t 2727 466 false (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [voteTmpl, readPred, readReg, hv, hBlock, bind, Except.bind, pure, Except.pure, b32]
  rfl

/-- The ballot popcount gives the selected request relative to the group's first request. -/
theorem selectedBatchWord (l : Launch) (g : Nat) {first n : Nat} (hn : n < 32)
    (hBatch : first + n < 2 ^ 32) :
    Seg kernel [] l g 2 3221 [(2727, b32 (2 ^ n - 1)), (7243, b32 first)]
      3223 [(1222, b32 n), (7247, b32 (first + n))] := by
  intro t ht
  have hp : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
  have hMask : 2 ^ n - 1 < 2 ^ 32 := by omega
  have hMask64 : 2 ^ n - 1 < 2 ^ 64 := by omega
  have hN : n < 2 ^ 32 := by omega
  have hFirst : first < 2 ^ 32 := by omega
  have hc := ballotPrefixPopcount (Nat.le_of_lt hn)
  seg_fp ht using
    simp only [b32, truncBits_ofNat hMask (by decide), toNat_ofNat_lt hMask64, hc,
      truncBits_ofNat hN (by decide), truncBits_ofNat hFirst (by decide),
      truncBits_ofNat hBatch (by decide), ← BitVec.ofNat_add, Nat.add_comm]

private theorem selectionCoreSlice :
    ((kernel.code.drop 3212).take 22).all (fun i => Assumptions.coreOp i.op) = true := by
  set_option maxRecDepth 10000 in kernel_rfl

/-- The checked scheduler selection instructions use the Core transition rules. -/
theorem selectionOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 3212 ≤ t.pc) (hHi : t.pc < 3234) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 3212).take 22 := by
      apply List.mem_of_getElem? (i := t.pc - 3212)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp selectionCoreSlice _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

/-- Transport a checked selection segment and its register frame to the actual hooks. -/
theorem selectionLocal {l : Launch} {g pc n : Nat} {t u : TState} {regs : List Nat}
    (hLo : 3212 ≤ pc) (hHi : pc + n ≤ 3234) (ht : t.pc = pc)
    (hWrites : ((kernel.code.drop pc).take n).all
      (fun i => regs.all (fun r => !(writesRegs i.op).contains r)) = true)
    (hFallthrough : ((kernel.code.drop pc).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧
      ∀ r ∈ regs, u.regs r = t.regs r := by
  have hlo : pc ≤ t.pc := ht.ge
  have hhi : t.pc + n ≤ pc + n := by rw [ht]
  exact ⟨schedulerLocalTransport hFallthrough
    (fun ha hb => selectionOut (by omega) (by omega)) hr hlo hhi,
    fun _ h => schedulerLocalFrame hWrites hFallthrough hr hlo hhi h⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
