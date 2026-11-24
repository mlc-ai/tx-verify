-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainLaterRead
import Kernels.TmlFa4Fwd.Flow.Code.Part042

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread.Allocation (drainRoots signedWord)

private theorem laterDownShuffle {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2709
      (fun i => activeDrainDownFrame p l (warpLane l g i) first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2710 (fun i =>
      (2654,b32 (drainCuQ p (first+laneOf l (warpLane l g (shflSource .down i 1 31).1))))::
        activeDrainDownFrame p l (warpLane l g i) first) (shuffles+1) votes ends) := by
  let word i := b32 (drainCuQ p (first+laneOf l (warpLane l g i)))
  have hb : l.block % 32 = 0 := by rw [hp.block]
  apply cur.consumeShuffle (dst := 2654) hp hMax hg .down word (fun _ => 1) (fun _ => 31)
  · intro i _ x hx
    simp only [activeDrainDownFrame,activeDrainGroupFrame,activeDrainCommon,drainRoots,
      List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i hi
    have ht := cur.checkpoint i hi
    rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
      out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_2709) rfl rfl]
    change Out.ev (shflTmpl l (warpLane l g i) (cur.state i) .down 2654 none
      (.reg 7211) (.imm 1) (.imm 31) (.imm (-1))) = _
    have hReg : (cur.state i).regs 7211 = some (word i) := ht.2.2.2.2.1
    simp [shflTmpl,readValue,readReg,hReg,hb,b32,Value.bytes,readBits,pure,Except.pure,word]
    rfl

private theorem laterLaneTiles {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first : Nat} (hf : first ≤ p.batch) {t : TState}
    (ht : At t 2710
      ((2654,b32 (drainCuQ p (first+(shflSource .down (laneOf l g) 1 31).1)))::
        activeDrainDownFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2725 ((7212,b32 (groupLaneTiles p first (laneOf l g)))::
        activeDrainGroupFrame p l g first) := by
  let lane := laneOf l g
  let left := drainCuQ p (first+lane)
  let right := drainCuQ p (first+(shflSource .down lane 1 31).1)
  let active := decide (first+lane < p.batch ∧ lane < 31)
  let diff := truncBits 32 (BitVec.ofNat 64 right-BitVec.ofNat 64 left)
  let F := activeDrainGroupFrame p l g first
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hb := hp.shape.2.1
  have hMargin := hp.shape.2.2.2.2.2
  have hIndex : first+lane < 2^31 := by omega
  obtain ⟨hLeft,hRight,hMono,hLength,hTile⟩ := drainWordTiles hp first lane
  change left < 2^32 at hLeft
  change right < 2^32 at hRight
  have hPred : (decide (lane = 31) || decide (p.batch ≤ first+lane)) = !active := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,decide_eq_true_eq,active]
    have hNeg : (!decide (first+lane < p.batch ∧ lane < 31)) = true ↔
        ¬(first+lane < p.batch ∧ lane < 31) := by
      by_cases h : first+lane < p.batch ∧ lane < 31 <;> simp [h]
    rw [hNeg]
    omega
  have hSet : Seg kernel [] l g 4 2710
      [(2654,b32 right),(7211,b32 left),(1198,b32 (first+lane)),(7149,b32 p.batch),
        (422,.pred (decide (lane=31)))] 2714
      [(424,.pred (!active)),(1199,.bits 32 diff),(7212,b32 0)] := by
    intro s hs
    seg_fp hs using
      first
      | rfl
      | simp only [truncBits_ofNat hLeft (by decide),truncBits_ofNat hRight (by decide),diff]
      | simpa only [compare,Option.getD_some,
          truncBits_ofNat (show first+lane < 2^32 by omega) (by decide),
          truncBits_ofNat (show p.batch < 2^32 by omega) (by decide),
          signedWord hIndex,signedWord hb,ge_iff_le,Int.ofNat_le] using congrArg Value.pred hPred
  let source := (2654,b32 right)::activeDrainDownFrame p l g first
  have H : Holds t.regs source := ht.2.2.2.2
  obtain ⟨v,hv,hV⟩ := hSet.apply (ht.mono ⟨H.1,H.2.1,H.2.2.1,holds_lookup H rfl,
    H.2.2.2.1,trivial⟩)
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2714 (!active) hV hV.2.2.2.2.1 (by simp)
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep (ht.mono (show Holds t.regs F from H.2.2.2.2))
    (by decide) (by decide) (by
      change ((kernel.code.drop 2710).take 5).all
        (fun i => [7215,1196,7210,7149,7139,1180,7506,1072].all
          (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel) (by decide +kernel) (run_comp hv hw)
  by_cases ha : active = true
  · have hPc : w.pc = 2715 := by simpa [ha] using hW.1
    have hDiff : diff = BitVec.ofNat 64 (right-left) := by
      dsimp only [diff]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show left < 2^64 by omega) (hMono ha),
        truncBits_ofNat (show right-left < 2^32 by omega) (by decide)]
    have hLen : At w 2715 [(1199,b32 (right-left))] :=
      ⟨hPc,hW.2.1,hW.2.2.1,hW.2.2.2.1,by
        simpa only [b32,hDiff] using hW.2.2.2.2.2.1,trivial⟩
    obtain ⟨u,hu,hU⟩ := (activeDrainRoundUpTiles true l g hLength).apply hLen
    obtain ⟨hMore,hF⟩ := activeDrainLocalKeep (hLen.mono hKeep) (by decide) (by decide) (by
      change ((kernel.code.drop 2715).take 10).all
        (fun i => [7215,1196,7210,7149,7139,1180,7506,1072].all
          (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel) (by decide +kernel) hu
    have hCount : (right-left+255)/256 = groupLaneTiles p first lane := by
      change (if active then (right-left+255)/256 else 0) = _ at hTile
      rwa [ite_eq_left ha] at hTile
    exact ⟨u,hPath.trans hMore,hU.mono ⟨by rw [← hCount]; exact hU.2.2.2.2.1,hF⟩⟩
  · have ha' : active = false := Bool.eq_false_of_not_eq_true ha
    have hPc : w.pc = 2725 := by simpa [ha'] using hW.1
    have hCount : 0 = groupLaneTiles p first lane := by
      change (if active then (right-left+255)/256 else 0) = _ at hTile
      rwa [ite_eq_right ha] at hTile
    exact ⟨w,hPath,⟨hPc,hW.2.1,hW.2.2.1,hW.2.2.2.1,
      by rw [← hCount]; exact hW.2.2.2.2.2.2.1,hKeep⟩⟩

/-- The recurring MMA drain group uses the same five-round warp prefix fold as the initial one. -/
theorem activeDrainLaterScanOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hf : first ≤ p.batch)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2709
      (fun i => activeDrainDownFrame p l (warpLane l g i) first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2746 (fun i => let th := warpLane l g i
      [(7214,b32 (prefixWindow (groupLaneTiles p first) 32 31)),
       (7213,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l th))),
       (7212,b32 (groupLaneTiles p first (laneOf l th)))] ++ activeDrainGroupFrame p l th first)
      (shuffles+7) votes ends) := by
  obtain ⟨word⟩ := laterDownShuffle hp hMax hg cur
  let F i := let th := warpLane l g i
    (7212,b32 (groupLaneTiles p first (laneOf l th)))::activeDrainGroupFrame p l th first
  have hPrepare : Nonempty (SchedulerWarpReached l X g (drainScanPc true 0)
      (fun i => activeDrainScanFrame p l (warpLane l g i) first true 0 (F i))
      (shuffles+1) votes ends) := by
    apply word.advanceLocal
    intro i hi
    have hb : l.block%32 = 0 := by rw [hp.block]
    let th := warpLane l g i
    have hLane : laneOf l th = i := (Step.sameWarp_lane hb hg hi).2
    have hPeer : laneOf l (warpLane l g (shflSource .down i 1 31).1) =
        (shflSource .down i 1 31).1 :=
      (Step.sameWarp_lane hb hg (Step.shflSource_lt .down hi 1 31)).2
    have hAt := word.checkpoint i hi
    have hAt' : At (word.state i) 2710
        ((2654,b32 (drainCuQ p (first+(shflSource .down (laneOf l th) 1 31).1)))::
          activeDrainDownFrame p l th first) :=
      hAt.mono ⟨by simpa only [hLane,hPeer] using hAt.2.2.2.2.1,hAt.2.2.2.2.2⟩
    obtain ⟨v,hv,hV⟩ := laterLaneTiles hp hf hAt'
    obtain ⟨u,hu,hU⟩ := activeDrainPrepareScan (g := th) (F := F i) true
      (hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2⟩)
      (by simp [F,th,activeDrainGroupFrame,activeDrainCommon,drainRoots]) (by
        change ((kernel.code.drop 2725).take 5).all
          (fun ins => [7212,7212,7215,1196,7210,7149,7139,1180,7506,1072].all
            fun r => !(writesRegs ins.op).contains r) = true
        decide +kernel)
    exact ⟨u,hv.trans hu,hU⟩
  obtain ⟨ready⟩ := hPrepare
  obtain ⟨scan⟩ := activeDrainUpScanOfMaximal hp hMax hg hf true (F := F) (by
    intro i _ x h stage
    simp only [F,activeDrainGroupFrame,activeDrainCommon,drainRoots,List.mem_cons,
      List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp only <;> fin_cases stage <;> decide) ready
  apply activeDrainBroadcast hp hMax hg (by decide) (by decide) Flow.code_2745 (F := F) _ scan
  intro i _ x h
  simp only [F,activeDrainGroupFrame,activeDrainCommon,drainRoots,List.mem_cons,
    List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PTX.Kernels.TmlFa4Fwd.Mma
