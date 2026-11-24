-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFirstScan
import Kernels.TmlFa4Fwd.Flow.Code.Part121

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

variable {p : Params}

theorem correctionFirstTotalTemplate {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) (t : TState)
    (sum : Nat) (hpc : t.pc = 7801) (hf : t.fault = none) (hv : t.regs 7271 = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7272 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_7801) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7272 none (.reg 7271) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

private theorem scanSignedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

/-- The CTA reads its own index and compares it with the first group's total work. -/
theorem correctionFirstLimit {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) {count heads : Nat}
    (hc : count < 2 ^ 31) (hh : heads < 2 ^ 31) (hg : g / l.block < 2 ^ 31)
    (htotal : count * heads < 2 ^ 31) :
    Seg kernel [] l g 4 7802 [(7272, b32 count), (7142, b32 heads)] 7806
      [(7274, b32 (count * heads)), (694, .pred (decide (g / l.block < count * heads))),
        (7273, b32 0), (1618, b32 (g / l.block))] := by
  intro t ht
  have hCount : count < 2 ^ 32 := by omega
  have hHeads : heads < 2 ^ 32 := by omega
  have hCta : g / l.block < 2 ^ 32 := by omega
  have hTotal : count * heads < 2 ^ 32 := by omega
  have hCtaX : (l.ctaidOf (g / l.block)).get .x = g / l.block :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_mul, hCtaX, truncBits_ofNat hCount (by decide),
        truncBits_ofNat hHeads (by decide), truncBits_ofNat hCta (by decide),
        truncBits_ofNat hTotal (by decide), compare, Option.getD_some, scanSignedWord hg,
        scanSignedWord htotal, Int.ofNat_lt]

/-- The first group's total and lane prefix are preserved across its scheduler branch. -/
def correctionFirstRouteFacts (p : Params) (l : Launch) (g lane : Nat) :
    List (Nat × Value) :=
  [(7274, b32 (tilePrefix p (min p.batch 31) * p.heads)), (7273, b32 0),
    (1618, b32 (g / l.block)), (7272, b32 (tilePrefix p (min p.batch 31))),
    (7271, b32 (prefixWindow (groupLaneTiles p 0) 32 lane))] ++
  firstCorrectionScanFacts p l (warpLane l g lane)

private theorem correctionFirstTotalFresh {l : Launch} {g : Nat} (lane : Nat) (_ : lane < 32)
    (pair : Nat × Value) (hm : pair ∈ correctionScanFacts p l g 5 lane) : pair.1 ≠ 7272 := by
  have hMem := List.mem_map_of_mem (f := Prod.fst) hm
  intro he
  rw [he] at hMem
  exact (of_decide_eq_true rfl : 7272 ∉ (correctionScanFacts p l g 5 lane).map Prod.fst) hMem

private theorem correctionFirstTotalOut {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g shuffles votes : Nat} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7801 (correctionScanFacts p l g 5) shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    let part := prefixWindow (groupLaneTiles p 0) 32
    out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.shfl .idx (b32 (part lane)) 31 31
        (fun v _ => next (setReg (cur.state lane) 7272 v))) := by
  dsimp only
  let part := prefixWindow (groupLaneTiles p 0) 32
  have ht := cur.checkpoint lane hl
  refine (correctionSchedulerOut (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans ?_
  exact correctionFirstTotalTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1

private theorem correctionFirstRouteLocal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (read : SchedulerWarpAt l X g 7802
      (fun lane => (7272, b32 (prefixWindow (groupLaneTiles p 0) 32
        (shflSource .idx lane 31 31).1)) :: correctionScanFacts p l g 5 lane)
      shuffles votes ends) :
    ∀ lane < 32, ∃ u, Relation.ReflTransGen
      (Tau kernel Assumptions.all l (warpLane l g lane)) (read.state lane) u ∧
      At u (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 7864 else 7807)
        (correctionFirstRouteFacts p l g lane) := by
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
  let carry := (7272, b32 count) :: correctionScanFacts p l g 5 lane
  let regs := carry.map Prod.fst
  have ht := read.checkpoint lane hl
  have hCountWord := ht.2.2.2.2.1
  rw [shflSource_idx lane (show (31 : Nat) < 32 by decide)] at hCountWord
  change (read.state lane).regs 7272 = some (b32 (part 31)) at hCountWord
  rw [hCountPart] at hCountWord
  have hCarry : Holds (read.state lane).regs carry := ⟨hCountWord, ht.2.2.2.2.2⟩
  have hWarp := (Step.sameWarp_lane hBlock hg hl).1
  have hSame : thread / l.block = cta := hWarp.1.2.2.symm
  have hFrame : Holds (read.state lane).regs (firstCorrectionScanFacts p l thread) := hCarry.2.2
  have hHeads := hFrame.2.1
  have hAt : At (read.state lane) 7802 [(7272, b32 count), (7142, b32 p.heads)] :=
    ht.mono ⟨hCountWord, hHeads, trivial⟩
  obtain ⟨u, hu, hU⟩ := correctionFirstLimit hp thread hCount hp.heads_signed
    (by rw [hSame]; exact hCta) hLimit _ hAt
  rw [hSame] at hU
  obtain ⟨huA, huFrame⟩ := correctionLinear (regs := regs) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hPreserved := holdsSchedulerFrame hCarry huFrame (fun _ h => List.mem_map_of_mem h)
  let guard := decide (cta < count * p.heads)
  have hBranch : At u 7806
      ((694, .pred guard) :: (7274, b32 (count * p.heads)) :: (7273, b32 0) ::
        (1618, b32 cta) :: carry) :=
    hU.mono ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.2.1,
      hU.2.2.2.2.2.2.2.1, hPreserved⟩
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_7806 guard hBranch hBranch.2.2.2.2.1 (by simp)
  obtain ⟨hvA, _⟩ := correctionLinear (regs := []) (by decide) (by decide) hBranch.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  refine ⟨v, run_rtg (run_comp huA hvA), ?_⟩
  have hLast : Holds v.regs (correctionFirstRouteFacts p l g lane) := by
    unfold correctionFirstRouteFacts
    have h := hV.2.2.2.2.2
    change Holds v.regs
      ((7274, b32 (count * p.heads)) :: (7273, b32 0) :: (1618, b32 cta) ::
        (7272, b32 count) :: correctionScanFacts p l g 5 lane) at h
    exact h
  simpa only [guard, cta, count, decide_eq_true_eq, Nat.reduceAdd] using hV.mono hLast

/-- Broadcast the computed total from lane 31, then take the actual first-group branch.
Every lane selects the same path because the total and CTA index are common. -/
theorem correctionFirstRouteTo {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState} {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 7801 (correctionScanFacts p l g 5) shuffles votes ends)
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hTarget : 7801 < target.pc) :
    ∃ next : SchedulerWarpAt l X g
        (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 7864 else 7807)
        (correctionFirstRouteFacts p l g) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  obtain ⟨read, hRead⟩ := cur.consumeShuffleTo hp hX hg .idx (fun lane => b32 (part lane))
    (fun _ => 31) (fun _ => 31) (correctionFirstTotalFresh)
    (correctionFirstTotalOut hp cur) hProgress hTarget
  obtain ⟨next, hNextPos⟩ := read.advanceLocalAt (correctionFirstRouteLocal hp hg read)
  exact ⟨next, fun h => hNextPos.symm ▸ hRead h⟩

/-- Every reached correction warp observes the first group's actual total and takes its branch. -/
theorem correctionFirstRouteOfMaximal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7801 (correctionScanFacts p l g 5) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 7864 else 7807)
      (correctionFirstRouteFacts p l g) (shuffles + 1) votes ends) := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  obtain ⟨read⟩ := cur.consumeShuffle hp hMax hg .idx (fun lane => b32 (part lane))
    (fun _ => 31) (fun _ => 31) correctionFirstTotalFresh
    (correctionFirstTotalOut hp cur.toSchedulerWarpAt)
  exact read.advanceLocal (correctionFirstRouteLocal hp hg read.toSchedulerWarpAt)

end
end PTX.Kernels.TmlFa4Fwd.Correction
