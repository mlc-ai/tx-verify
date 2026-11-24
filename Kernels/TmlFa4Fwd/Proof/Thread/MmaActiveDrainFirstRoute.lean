-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainScan
import Kernels.TmlFa4Fwd.Proof.MmaScanCounter
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Kernels.TmlFa4Fwd.Flow.Code.Part042

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread.Allocation (drainRoots signedWord)

/-- The loop carries the prefix work of the batches before the next group. -/
def activeDrainLoopFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  (7215,b32 first)::(1196,b32 (g/l.block+1))::
    (7210,b32 (tilePrefix p (min p.batch (first+31))*p.heads))::activeDrainCommon p l g

/-- The terminal branch retains both per-lane inputs to the final selected-index shuffles. -/
def activeDrainSelectedFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(7212,b32 (groupLaneTiles p first (laneOf l g))),
    (7213,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g))),
    (7214,b32 (prefixWindow (groupLaneTiles p first) 32 31)),
    (7216,b32 (tilePrefix p (min p.batch (first+31))*p.heads)),(7215,b32 first)] ++
    activeDrainCommon p l g

/-- The exhausted branch needs only the launch batch word and its equal final group word. -/
def activeDrainExhaustedFrame (p : Params) : List (Nat × Value) :=
  [(7215,b32 p.batch),(7149,b32 p.batch)]

theorem activeDrainPrepareScan {p : Params} {l : Launch} {g first : Nat}
    {t : TState} {F : List (Nat × Value)} (later : Bool)
    (ht : At t (if later then 2725 else 2668)
      ((7212,b32 (groupLaneTiles p first (laneOf l g)))::F))
    (hLaneReg : (1180,b32 (laneOf l g)) ∈ F)
    (hKeep : ((kernel.code.drop (if later then 2725 else 2668)).take 5).all
      (fun i => ((7212::F.map Prod.fst)).all fun r => !(writesRegs i.op).contains r) = true) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (drainScanPc later 0) (activeDrainScanFrame p l g first later 0 F) := by
  let lane := laneOf l g
  let start := if later then 2725 else 2668
  let stop := drainScanPc later 0
  let guards := drainScanKeep later lane []
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hh : At t start [(1180,b32 lane)] :=
    ht.mono ⟨holds_mem ht.2.2.2.2 (.tail _ hLaneReg),trivial⟩
  have hSeg : Seg kernel [] l g 5 start [(1180,b32 lane)] stop guards := by
    let packed : Nat → List (Nat × Value) := fun base =>
      [(base-4,.pred (decide (15 < lane))),(base-3,.pred (decide (7 < lane))),
       (base-2,.pred (decide (3 < lane))),(base-1,.pred (decide (1 < lane))),
       (base,.pred (decide (lane=0)))]
    have hPacked : guards = packed (if later then 432 else 418) := by
      cases later <;> rfl
    rw [hPacked]
    cases later <;> intro s hs <;> dsimp only [start,stop,drainScanPc,packed] <;>
      seg_fp hs using
        simp [compare,truncBits_ofNat (show lane < 2^32 by omega) (by decide),
          toNat_ofNat_lt (show lane < 2^64 by omega),
          show (truncBits 32 15#64).toNat = 15 by decide,
          show (truncBits 32 7#64).toNat = 7 by decide,
          show (truncBits 32 3#64).toNat = 3 by decide,
          show (truncBits 32 1#64).toNat = 1 by decide,
          show (truncBits 32 0#64).toNat = 0 by decide]
  obtain ⟨u,hr,hu⟩ := hSeg.apply hh
  obtain ⟨hPath,hF⟩ := activeDrainLocalKeep ht
    (by cases later <;> decide) (by cases later <;> decide) hKeep
    (by cases later <;> decide +kernel) hr
  have hGuard : Holds u.regs (drainScanKeep later lane F) := by
    change Holds u.regs (((List.finRange 5).reverse.map fun i =>
      (drainGuardReg later i,.pred (drainScanGuard i lane))) ++ F)
    exact (holds_append _ _ _).mpr ⟨by simpa only [guards,drainScanKeep,List.append_nil]
      using hu.2.2.2.2,hF.2⟩
  exact ⟨u,hPath,hu.mono ⟨by simpa only [drainScanSrc,Fin.val_zero,↓reduceIte,pow_zero,
    prefixWindow_one] using hF.1,hGuard⟩⟩

def drainBroadcastInstr : Instr := ⟨none,.warp
  {kind := .shfl .idx,ty := some (.int .b 32),dsts := [some 7214],
    srcs := [.reg 7213,.imm 31,.imm 31],mask := some (.imm (-1))}⟩

private theorem drainBroadcastOut {l : Launch} {g pc : Nat} {t : TState} {word : Nat}
    (hLo : 1904 ≤ pc) (hHi : pc < 2768) (hCode : kernel.code[pc]? = some drainBroadcastInstr)
    (hpc : t.pc = pc) (hf : t.fault = none) (hBlock : l.block%32 = 0)
    (hr : t.regs 7213 = some (b32 word)) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 word) 31 31
      (fun v _ => next (setReg t 7214 v))) := by
  rw [out_eq_core (hpc.symm ▸ hLo) (hpc.symm ▸ hHi),
    out_event hf (hpc.symm ▸ hCode) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7214 none (.reg 7213) (.imm 31) (.imm 31) (.imm (-1))) = _
  simp [shflTmpl,readValue,readReg,hr,hBlock,b32,Value.bytes,readBits,pure,Except.pure]
  rfl

theorem activeDrainBroadcast {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first pc shuffles votes : Nat} (hg : g < l.threads)
    (hLo : 1904 ≤ pc) (hHi : pc < 2768) (hCode : kernel.code[pc]? = some drainBroadcastInstr)
    {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ 7214)
    (cur : SchedulerWarpReached l X g pc
      (fun lane => let th := warpLane l g lane
        (7213,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l th)))::F lane)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (pc+1)
      (fun lane => let th := warpLane l g lane
        (7214,b32 (prefixWindow (groupLaneTiles p first) 32 31))::
          (7213,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l th)))::F lane)
      (shuffles+1) votes ends) := by
  let word := fun lane => b32
    (prefixWindow (groupLaneTiles p first) 32 (laneOf l (warpLane l g lane)))
  have hb : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨mid⟩ := cur.consumeShuffle (dst := 7214) hp hMax hg .idx word
    (fun _ => 31) (fun _ => 31) (by
      intro lane hl pair hm
      rcases List.mem_cons.mp hm with rfl | h
      · exact (by decide : 7213 ≠ 7214)
      · exact hFresh lane hl pair h) (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      exact drainBroadcastOut hLo hHi hCode ht.1 ht.2.2.2.1 hb ht.2.2.2.2.1)
  apply mid.advanceLocal
  intro lane hl
  have h31 : laneOf l (warpLane l g 31) = 31 :=
    (Step.sameWarp_lane hb hg (show 31 < 32 by decide)).2
  have hFrom := congrArg Prod.fst (shflSource_idx lane (by decide : (31 : Nat) < 32))
  have ht := mid.checkpoint lane hl
  exact ⟨_,.refl,ht.mono ⟨by simpa only [word,hFrom,h31] using ht.2.2.2.2.1,ht.2.2.2.2.2⟩⟩

private theorem firstRouteLocal {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) {t : TState}
    (ht : At t 2689
      ([(7214,b32 (prefixWindow (groupLaneTiles p 0) 32 31)),
        (7213,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l g))),
        (7212,b32 (groupLaneTiles p 0 (laneOf l g)))] ++ activeDrainCommon p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      if g/l.block < tilePrefix p (min p.batch 31)*p.heads then
        At u 2750 (activeDrainSelectedFrame p l g 0)
      else At u 2696 (activeDrainLoopFrame p l g 0) := by
  let cutoff := tilePrefix p (min p.batch 31)*p.heads
  let total := prefixWindow (groupLaneTiles p 0) 32 31
  let cta := g/l.block
  let F := [(7214,b32 total),(7213,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l g))),
    (7212,b32 (groupLaneTiles p 0 (laneOf l g)))] ++ activeDrainCommon p l g
  have ht : At t 2689 F := ht
  have hTotal : total = tilePrefix p (min p.batch 31) := by
    have h := groupTiles_eq p (Nat.zero_le p.batch) (by decide : 32 ≤ 32)
    simpa only [total,prefixWindow_warp _ (show 31 < 32 by decide),
      show tilePrefix p 0 = 0 by simp [tilePrefix],
      Nat.zero_add,show min 31 32 = 31 by decide] using h
  have hTotal31 := hp.groupWindow_signed (Nat.zero_le p.batch) (show 31 < 32 by decide) 32
  change total < 2^31 at hTotal31
  have hCut : cutoff < 2^31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hHeads := hp.heads_signed
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hNext : cta+1 < 2^31 := (Nat.succ_le_of_lt (NamedBar.cta_lt hg)).trans_lt hp.grid.2.2
  have hProd : total*p.heads = cutoff := by rw [hTotal]
  let takeGroup := decide (cta < cutoff)
  have hSeg : Seg kernel [] l g 3 2689
      [(7214,b32 total),(7139,b32 p.heads),(1072,b32 cta)] 2692
      [(419,.pred takeGroup),(7216,b32 cutoff),(7215,b32 0)] := by
    intro s hs
    seg_fp hs using
      first
      | rfl
      | simp only [b32,← BitVec.ofNat_mul,hProd,compare,Option.getD_some,
        truncBits_ofNat (show total < 2^32 by omega) (by decide),
        truncBits_ofNat (show p.heads < 2^32 by omega) (by decide),
        truncBits_ofNat (show cutoff < 2^32 by omega) (by decide),
        truncBits_ofNat (show cta < 2^32 by omega) (by decide),
        signedWord hCut,signedWord hCta,gt_iff_lt,Int.ofNat_lt,takeGroup]
  obtain ⟨s,hs,hS⟩ := hSeg.apply (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,
    holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2692 takeGroup hS hS.2.2.2.2.1 (by simp)
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep ht (by decide) (by decide)
    (by change ((kernel.code.drop 2689).take 4).all
          (fun ins => [7214,7213,7212,7149,7139,1180,7506,1072].all
            fun r => !(writesRegs ins.op).contains r) = true
        decide +kernel) (by decide +kernel) (run_comp hs hv)
  dsimp only [takeGroup] at hV
  change ∃ u, _ ∧ if cta < cutoff then _ else _
  by_cases hFound : cta < cutoff
  · simp only [ite_eq_left hFound]
    have hPc : v.pc = 2750 := by simpa [hFound] using hV.1
    exact ⟨v,hPath,⟨hPc,hV.2.1,hV.2.2.1,hV.2.2.2.1,
      hKeep.2.2.1,hKeep.2.1,hKeep.1,hV.2.2.2.2.2.1,hV.2.2.2.2.2.2.1,hKeep.2.2.2⟩⟩
  · simp only [ite_eq_right hFound]
    have hPc : v.pc = 2693 := by simpa [hFound] using hV.1
    have hSeg : Seg kernel [] l g 3 2693 [(1072,b32 cta),(7216,b32 cutoff)] 2696
        [(1196,b32 (cta+1)),(7210,b32 cutoff),(7215,b32 0)] := by
      intro w hw
      seg_fp hw using norm_bits
    have hIn : At v 2693 [(1072,b32 cta),(7216,b32 cutoff)] :=
      ⟨hPc,hV.2.1,hV.2.2.1,hV.2.2.2.1,holds_lookup hKeep rfl,hV.2.2.2.2.2.1,trivial⟩
    obtain ⟨w,hw,hW⟩ := hSeg.apply hIn
    have hReady := hIn.mono hKeep.2.2.2
    obtain ⟨hLocal,hTail⟩ := activeDrainLocalKeep hReady (by decide) (by decide)
      (by change ((kernel.code.drop 2693).take 3).all
            (fun ins => [7149,7139,1180,7506,1072].all
              fun r => !(writesRegs ins.op).contains r) = true
          decide +kernel)
      (by decide +kernel) hw
    exact ⟨w,hPath.trans hLocal,hW.mono ⟨hW.2.2.2.2.2.2.1,hW.2.2.2.2.1,hW.2.2.2.2.2.1,hTail⟩⟩

/-- The real first drain group scans all lanes before selecting the terminal
request interval or entering the recurring groups. -/
theorem ActiveDrainNeighbors.firstRoute {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (c : ActiveDrainNeighbors p l X g) :
    if g/l.block < tilePrefix p (min p.batch 31)*p.heads then
      Nonempty (SchedulerWarpReached l X g 2750
        (fun i => activeDrainSelectedFrame p l (warpLane l g i) 0) (c.shuffles+6) c.votes c.ends)
    else Nonempty (SchedulerWarpReached l X g 2696
        (fun i => activeDrainLoopFrame p l (warpLane l g i) 0) (c.shuffles+6) c.votes c.ends) := by
  let F i := let th := warpLane l g i
    (7212,b32 (groupLaneTiles p 0 (laneOf l th)))::activeDrainCommon p l th
  obtain ⟨tiles⟩ := c.tiles hp hg
  have hBegin : Nonempty (SchedulerWarpReached l X g (drainScanPc false 0)
      (fun i => activeDrainScanFrame p l (warpLane l g i) 0 false 0 (F i))
      c.shuffles c.votes c.ends) := by
    apply tiles.advanceLocal
    intro i hi
    let thread := warpLane l g i
    have h := tiles.checkpoint i hi
    apply activeDrainPrepareScan (g := thread) (F := F i) false
      (h.mono ⟨h.2.2.2.2.1,h.2.2.2.2⟩)
    · simp [F,thread,activeDrainCommon,drainRoots]
    · change ((kernel.code.drop 2668).take 5).all
          (fun ins => [7212,7212,7149,7139,1180,7506,1072].all
            fun r => !(writesRegs ins.op).contains r) = true
      decide +kernel
  obtain ⟨ready⟩ := hBegin
  obtain ⟨scan⟩ := activeDrainUpScanOfMaximal hp hMax hg (Nat.zero_le p.batch) false
    (F := F) (by
      intro lane _ item hm stage
      simp only [F,activeDrainCommon,drainRoots,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;> fin_cases stage <;> decide) ready
  -- The tile count lives in the first scan's operand register and is not overwritten.
  obtain ⟨after⟩ := activeDrainBroadcast hp hMax hg (by decide) (by decide) Flow.code_2688
    (F := F) (by
    intro i _ x hm
    simp only [F,activeDrainCommon,drainRoots,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)) scan
  have hLane (i : Nat) (hi : i < 32) :=
    (Step.sameWarp_lane (show l.block%32 = 0 by rw [hp.block]) hg hi).1
  by_cases hHit : g/l.block < tilePrefix p (min p.batch 31)*p.heads
  · rw [ite_eq_left hHit]
    apply after.advanceLocal
    intro i hi
    obtain ⟨u,hu,hAt⟩ := firstRouteLocal hp (hLane i hi).1.2.1 (after.checkpoint i hi)
    rw [← (hLane i hi).1.2.2,ite_eq_left hHit] at hAt
    exact ⟨u,hu,hAt⟩
  · rw [ite_eq_right hHit]
    apply after.advanceLocal
    intro i hi
    obtain ⟨u,hu,hAt⟩ := firstRouteLocal hp (hLane i hi).1.2.1 (after.checkpoint i hi)
    rw [← (hLane i hi).1.2.2,ite_eq_right hHit] at hAt
    exact ⟨u,hu,hAt⟩

end PTX.Kernels.TmlFa4Fwd.Mma
