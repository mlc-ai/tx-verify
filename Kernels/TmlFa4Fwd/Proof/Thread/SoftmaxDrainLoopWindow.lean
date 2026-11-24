-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainLoopRead
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainUpScan
import Kernels.TmlFa4Fwd.Flow.Code.Part119
import Kernels.TmlFa4Fwd.Flow.Code.Part120

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

private theorem laterDownShuffle {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7679
      (fun lane => terminalLaterDownFrame p l (warpLane l g lane) first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7680
      (fun lane =>
        (5836,b32 (terminalLaterWord p l (warpLane l g (shflSource .down lane 1 31).1) first)) ::
          terminalLaterDownFrame p l (warpLane l g lane) first) (shuffles+1) votes ends) := by
  apply cur.consumeShuffle hp hMax hg .down
    (fun lane => b32 (terminalLaterWord p l (warpLane l g lane) first)) (fun _ => 1) (fun _ => 31)
  · intro lane _ item hm
    simp [terminalLaterDownFrame,terminalSearchGroup,terminalSearchCommon,RowDrainRole.roots,
      RowDrainRole.batchReg,RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp
  · intro lane hl
    let t := cur.state lane
    let thread := warpLane l g lane
    let word := terminalLaterWord p l thread first
    have ht := cur.checkpoint lane hl
    have hCore := RowDrainRole.softmax.drainCore (l := l) (g := thread) (s := t)
      (by rw [ht.1]; decide) (by rw [ht.1]; decide)
    rw [hCore,out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_7679) rfl rfl]
    change Out.ev (shflTmpl l thread t .down 5836 none (.reg 7261)
      (.imm 1) (.imm 31) (.imm (-1))) = _
    have hb : l.block%32 = 0 := by rw [hp.block]
    have hReg : t.regs 7261 = some (.bits 32 (BitVec.ofNat 64 word)) := ht.2.2.2.2.1
    simp [shflTmpl,readValue,readReg,hReg,hb,Value.bytes,readBits,pure,Except.pure]
    rfl

private theorem laterDrainLane {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first : Nat} (hFirst : first ≤ p.batch) {t : TState}
    (ht : At t 7680
      ((5836,b32 (drainCuQ p (first+(shflSource .down (laneOf l g) 1 31).1)))::
        terminalLaterDownFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 7695 ((7262,b32 (groupLaneTiles p first (laneOf l g)))::
        terminalSearchGroup p l g first) := by
  let lane := laneOf l g
  let left := drainCuQ p (first+lane)
  let right := drainCuQ p (first+(shflSource .down lane 1 31).1)
  let active := decide (first+lane < p.batch ∧ lane < 31)
  let diff := truncBits 32 (BitVec.ofNat 64 right-BitVec.ofNat 64 left)
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hBatch := hp.shape.2.2
  have hIndex : first+lane < 2^31 := by omega
  obtain ⟨hLeft,hRight,hMono,hLength,hTile⟩ := drainWordTiles hp first lane
  change left < 2^32 at hLeft
  change right < 2^32 at hRight
  have hGuard : (decide (lane = 31) || decide (p.batch ≤ first+lane)) = !active := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,decide_eq_true_eq,active]
    have hNeg : (!decide (first+lane < p.batch ∧ lane < 31)) = true ↔
        ¬(first+lane < p.batch ∧ lane < 31) := by
      by_cases h : first+lane < p.batch ∧ lane < 31 <;> simp [h]
    rw [hNeg]
    omega
  have hSet : Seg kernel [] l g 4 7680
      [(5836,b32 right),(7261,b32 left),(1609,b32 (first+lane)),(7151,b32 p.batch),
        (665,.pred (decide (lane = 31)))] 7684
      [(667,.pred (!active)),(1610,.bits 32 diff),(7262,b32 0)] := by
    intro s hs
    seg_fp hs using
      first
      | rfl
      | simp only [truncBits_ofNat hLeft (by decide),truncBits_ofNat hRight (by decide),diff]
      | simpa only [compare,Option.getD_some,
          truncBits_ofNat (show first+lane < 2^32 by omega) (by decide),
          truncBits_ofNat (show p.batch < 2^32 by omega) (by decide),
          RowDrainRole.signedWord hIndex,
          RowDrainRole.signedWord (show p.batch < 2^31 by omega),ge_iff_le,Int.ofNat_le]
          using congrArg Value.pred hGuard
  have hStable : At t 7680 (terminalSearchGroup p l g first) :=
    ht.mono ht.2.2.2.2.2.2.2.2
  have ht' : At t 7680
      [(5836,b32 right),(7261,b32 left),(1609,b32 (first+lane)),(7151,b32 p.batch),
        (665,.pred (decide (lane = 31)))] :=
    ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,
      hStable.2.2.2.2.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨s,hs,hsAt⟩ := hSet.apply ht'
  obtain ⟨v,hv,hvAt⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7684 (!active) hsAt hsAt.2.2.2.2.1 (by simp)
  obtain ⟨hPath,hStableV⟩ := drainLocalKeep hStable (by decide) (by decide)
    (by
      dsimp only [terminalSearchGroup,terminalSearchCommon,RowDrainRole.roots,RowDrainRole.frame,
        RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,List.cons_append,
        List.nil_append,List.map]
      decide +kernel) (by decide +kernel) (run_comp hs hv)
  by_cases ha : active = true
  · have hPc : v.pc = 7685 := by simpa [ha] using hvAt.1
    have hDiff : diff = BitVec.ofNat 64 (right-left) := by
      dsimp only [diff]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show left < 2^64 by omega) (hMono ha),
        truncBits_ofNat (show right-left < 2^32 by omega) (by decide)]
    have hLen : At v 7685 [(1610,b32 (right-left))] := by
      refine ⟨hPc,hvAt.2.1,hvAt.2.2.1,hvAt.2.2.2.1,?_,trivial⟩
      simpa only [b32, hDiff] using hvAt.2.2.2.2.2.1
    obtain ⟨u,hu,hAt⟩ := (drainRoundUpTiles true l g hLength).apply hLen
    have hCount : (right-left+255)/256 = groupLaneTiles p first lane := by
      change (if active then (right-left+255)/256 else 0) = _ at hTile
      rwa [ite_eq_left ha] at hTile
    obtain ⟨hTail,hKeep⟩ := drainLocalKeep (hLen.mono hStableV) (by decide) (by decide)
      (by
        dsimp only [terminalSearchGroup,terminalSearchCommon,RowDrainRole.roots,RowDrainRole.frame,
          RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,List.cons_append,
          List.nil_append,List.map]
        decide +kernel) (by decide +kernel) hu
    exact ⟨u,hPath.trans hTail,hAt.mono ⟨hCount ▸ hAt.2.2.2.2.1,hKeep⟩⟩
  · have hNo : active = false := Bool.eq_false_of_not_eq_true ha
    have hPc : v.pc = 7695 := by simpa [hNo] using hvAt.1
    have hCount : 0 = groupLaneTiles p first lane := by
      change (if active then (right-left+255)/256 else 0) = _ at hTile
      simpa only [hNo,Bool.false_eq_true,ite_false] using hTile
    exact ⟨v,hPath,⟨hPc,hvAt.2.1,hvAt.2.2.1,hvAt.2.2.2.1,
      hCount ▸ hvAt.2.2.2.2.2.2.1,hStableV⟩⟩

/-- Carry the requested count and input frame across a later group's scan. -/
def laterDrainScanCarry (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  (7262,b32 (groupLaneTiles p first (laneOf l g)))::terminalSearchGroup p l g first

private theorem laterScanPrepared {p : Params} {l : Launch} {g first : Nat} {t : TState}
    (ht : At t 7695 (laterDrainScanCarry p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 7700 (terminalScanFrame p l g first true 0 (laterDrainScanCarry p l g first)) := by
  let lane := laneOf l g
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have h32 : lane < 2^32 := by omega
  have h64 : lane < 2^64 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have h1 : (↑(truncBits 32 (BitVec.ofInt 64 1)).toNat : Int) = 1 := rfl
  have h3 : (↑(truncBits 32 (BitVec.ofInt 64 3)).toNat : Int) = 3 := rfl
  have h7 : (↑(truncBits 32 (BitVec.ofInt 64 7)).toNat : Int) = 7 := rfl
  have h15 : (↑(truncBits 32 (BitVec.ofInt 64 15)).toNat : Int) = 15 := rfl
  let guards := (scanKeep true lane [])
  have hSet : Seg kernel [] l g 5 7695 [(1215,b32 lane)] 7700 guards := by
    have hG0 : drainScanGuard 0 lane = decide (lane = 0) := rfl
    have hG1 : drainScanGuard 1 lane = decide (2 ≤ lane) := rfl
    have hG2 : drainScanGuard 2 lane = decide (4 ≤ lane) := rfl
    have hG3 : drainScanGuard 3 lane = decide (8 ≤ lane) := rfl
    have hG4 : drainScanGuard 4 lane = decide (16 ≤ lane) := rfl
    change Seg kernel [] l g 5 7695 [(1215,b32 lane)] 7700
      [(671,.pred (drainScanGuard 4 lane)),(672,.pred (drainScanGuard 3 lane)),
       (673,.pred (drainScanGuard 2 lane)),(674,.pred (drainScanGuard 1 lane)),
       (675,.pred (drainScanGuard 0 lane))]
    intro t ht
    seg_fp ht using
      (simp only [hG0,hG1,hG2,hG3,hG4,compare,Option.getD_some,
         truncBits_ofNat h32 (by decide),toNat_ofNat_lt h64,
         Value.pred.injEq,decide_eq_decide,hz,h1,h3,h7,h15]
       all_goals omega)
  have hRoot : Holds t.regs (RowDrainRole.softmax.roots p l g) :=
    ht.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨u,hu,hU⟩ := hSet.apply (ht.mono ⟨hRoot.2.1,trivial⟩)
  obtain ⟨hPath,hKeep⟩ := drainLocalKeep ht (by decide) (by decide)
    (by
      dsimp only [laterDrainScanCarry,terminalSearchGroup,terminalSearchCommon,
        RowDrainRole.roots,RowDrainRole.frame,RowDrainRole.batchReg,RowDrainRole.laneReg,
        RowDrainRole.ctaReg,List.cons_append,List.nil_append,List.map]
      decide +kernel) (by decide +kernel) hu
  refine ⟨u,hPath,hU.mono ?_⟩
  simpa only [terminalScanFrame,scanKeep,guards,scanSrc,Fin.val_zero,ite_true,List.append_nil,
    pow_zero,prefixWindow_one] using
    (show Holds u.regs ((7262,b32 (groupLaneTiles p first lane))::
      (guards ++ laterDrainScanCarry p l g first)) from
      ⟨hKeep.1,(holds_append ..).mpr ⟨hU.2.2.2.2,hKeep⟩⟩)

/-- Advance a later group's actual down shuffle through its five up-shuffles. -/
theorem terminalDrainLaterWindowOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7679
      (fun lane => terminalLaterDownFrame p l (warpLane l g lane) first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7715
      (fun lane => let t := warpLane l g lane
        (7263,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::
          laterDrainScanCarry p l t first) (shuffles+6) votes ends) := by
  obtain ⟨mid⟩ := laterDownShuffle hp hMax hg cur
  have hStart : Nonempty (SchedulerWarpReached l X g 7700
      (fun lane => let t := warpLane l g lane
        terminalScanFrame p l t first true 0 (laterDrainScanCarry p l t first))
      (shuffles+1) votes ends) := by
    apply mid.advanceLocal
    intro lane hl
    let t := warpLane l g lane
    have hb : l.block%32 = 0 := by rw [hp.block]
    have hLane : laneOf l t = lane := (Step.sameWarp_lane hb hg hl).2
    have hPeer : laneOf l (warpLane l g (shflSource .down lane 1 31).1) =
        (shflSource .down lane 1 31).1 :=
      (Step.sameWarp_lane hb hg (Step.shflSource_lt .down hl 1 31)).2
    have hAt := mid.checkpoint lane hl
    have hAt' : At (mid.state lane) 7680
        ((5836,b32 (drainCuQ p (first+(shflSource .down (laneOf l t) 1 31).1)))::
          terminalLaterDownFrame p l t first) := by
      simpa only [terminalLaterWord,hLane,hPeer] using hAt
    obtain ⟨u,hu,hU⟩ := laterDrainLane hp hFirst hAt'
    obtain ⟨v,hv,hV⟩ := laterScanPrepared hU
    exact ⟨v,hu.trans hv,hV⟩
  obtain ⟨start⟩ := hStart
  apply warpTerminalUpScanOfMaximal hp hMax hg hFirst true _ start
  intro lane _ x hx stage
  simp only [laterDrainScanCarry,terminalSearchGroup,terminalSearchCommon,RowDrainRole.roots,
    RowDrainRole.frame,RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only <;> fin_cases stage <;> decide

end PTX.Kernels.TmlFa4Fwd.Softmax
