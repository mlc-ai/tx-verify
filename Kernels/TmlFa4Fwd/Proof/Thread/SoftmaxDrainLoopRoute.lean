-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainLoopWindow
import Kernels.TmlFa4Fwd.Flow.Code.Part120

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

private def terminalGroupTotal (p : Params) (first : Nat) : Nat :=
  prefixWindow (groupLaneTiles p first) 32 31

private def laterTotalFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  (7264,b32 (terminalGroupTotal p first))::
    (7263,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g)))::
      laterDrainScanCarry p l g first

private theorem laterBroadcast {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7715
      (fun lane => let t := warpLane l g lane
        (7263,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::
          laterDrainScanCarry p l t first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7716
      (fun lane => laterTotalFrame p l (warpLane l g lane) first) (shuffles+1) votes ends) := by
  let word := fun lane => b32 (prefixWindow (groupLaneTiles p first) 32
    (laneOf l (warpLane l g lane)))
  have hb : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨after⟩ := cur.consumeShuffle (dst := 7264) hp hMax hg .idx word
    (fun _ => 31) (fun _ => 31) (by
      intro lane _ pair hm
      simp only [laterDrainScanCarry,terminalSearchGroup,terminalSearchCommon,
        List.cons_append,List.nil_append,RowDrainRole.roots,RowDrainRole.batchReg,
        RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg,
        List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;> decide)
    (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hCore := RowDrainRole.softmax.drainCore (l := l) (g := warpLane l g lane)
        (s := cur.state lane) (by rw [ht.1]; decide) (by rw [ht.1]; decide)
      rw [hCore,out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_7715) rfl rfl]
      change Out.ev (shflTmpl l (warpLane l g lane) (cur.state lane) .idx 7264 none
        (.reg 7263) (.imm 31) (.imm 31) (.imm (-1))) = _
      have hReg : (cur.state lane).regs 7263 = some (word lane) := ht.2.2.2.2.1
      simp [shflTmpl,readValue,readReg,hReg,hb,word,b32,Value.bytes,readBits,pure,Except.pure]
      rfl)
  apply after.advanceLocal
  intro lane hl
  have ht := after.checkpoint lane hl
  have h31 : laneOf l (warpLane l g 31) = 31 :=
    (Step.sameWarp_lane hb hg (by decide : 31 < 32)).2
  have hFrom : (shflSource .idx lane 31 31).1 = 31 :=
    congrArg Prod.fst (shflSource_idx lane (by decide : (31 : Nat) < 32))
  exact ⟨_,.refl,by simpa only [word,hFrom,h31,laterTotalFrame,terminalGroupTotal] using ht⟩

private theorem laterCutoff {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    {s : TState} (hs : At s 7716 (laterTotalFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      if tilePrefix p (min p.batch (first+31))*p.heads ≤ g/l.block then
        At u 7666 (terminalSearchLoop p l g first)
      else At u 7720 ((7262,b32 (groupLaneTiles p first (laneOf l g)))::
        terminalSelectedGroup p l g first) := by
  let cta := g/l.block
  let count := terminalGroupTotal p first
  let old := tilePrefix p first*p.heads
  let cutoff := tilePrefix p (min p.batch (first+31))*p.heads
  let part := prefixWindow (groupLaneTiles p first) 32 (laneOf l g)
  let own := groupLaneTiles p first (laneOf l g)
  let fixed := [(7265,b32 first),(7264,b32 count),(7263,b32 part),(7262,b32 own),
    (1607,b32 (cta+1))] ++ terminalSearchCommon p l g
  have hSum : count*p.heads+old = cutoff := by
    have h := congrArg (· * p.heads) (groupTiles_eq p hFirst (by decide : 32 ≤ 32))
    have hCount : count = ∑ i ∈ Finset.range 32, groupLaneTiles p first i :=
      prefixWindow_warp _ (by decide : 31 < 32)
    rw [hCount]
    simpa only [show min 31 32 = 31 by decide,Nat.add_mul,Nat.add_comm,cutoff,old] using h
  have hFit := hp.prefixWork_signed (Nat.min_le_left p.batch (first+31))
  change cutoff < 2^31 at hFit
  have hCount := hp.groupWindow_signed hFirst (show 31 < 32 by decide) 32
  change count < 2^31 at hCount
  have hOld : old < 2^31 := hp.prefixWork_signed hFirst
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  let more := decide (cutoff ≤ cta)
  have hSeg : Seg kernel [] l g 3 7716
      [(7264,b32 count),(7141,b32 p.heads),(7260,b32 old),(1606,b32 cta)] 7719
      [(676,.pred more),(7266,b32 cutoff),(7260,b32 cutoff)] := by
    intro t ht
    seg_fp ht using
      simp only [b32,← BitVec.ofNat_mul,← BitVec.ofNat_add,hSum,compare,Option.getD_some,
        truncBits_ofNat (show count < 2^32 by omega) (by decide),
        truncBits_ofNat (hp.heads_signed.trans (by decide : 2^31 < 2^32)) (by decide),
        truncBits_ofNat (show old < 2^32 by omega) (by decide),
        truncBits_ofNat (show cutoff < 2^32 by omega) (by decide),
        truncBits_ofNat (show cta < 2^32 by omega) (by decide),
        RowDrainRole.signedWord hFit,RowDrainRole.signedWord hCta,Int.ofNat_le,more]
  have hReg := hs.2.2.2.2
  obtain ⟨v,hRun,hv⟩ := hSeg.apply
    (hs.mono ⟨holds_lookup hReg rfl,holds_lookup hReg rfl,holds_lookup hReg rfl,
      holds_lookup hReg rfl,trivial⟩)
  have hFixed : At s 7716 fixed := by
    refine hs.mono ⟨holds_lookup hReg rfl,holds_lookup hReg rfl,holds_lookup hReg rfl,
      holds_lookup hReg rfl,holds_lookup hReg rfl,?_⟩
    exact hReg.2.2.2.2.2.2.2
  obtain ⟨hPath,hKeep⟩ := drainLocalKeep hFixed (by decide) (by decide)
    (by
      dsimp only [fixed,terminalSearchCommon,RowDrainRole.roots,RowDrainRole.frame,
        RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,List.cons_append,
        List.nil_append,List.map]
      decide +kernel) (by decide +kernel) hRun
  have hAt : At v 7719 ([(676,.pred more),(7266,b32 cutoff),(7260,b32 cutoff)] ++ fixed) :=
    hv.mono ⟨hv.2.2.2.2.1,hv.2.2.2.2.2.1,hv.2.2.2.2.2.2.1,hKeep⟩
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7719 more hAt hAt.2.2.2.2.1 (by simp)
  have hStep := RowDrainRole.softmax.drainLocals (n := 1) (by decide) (by decide)
    hAt.1 (by simp) hu
  have hRegs := hU.2.2.2.2
  have hRemain : Holds u.regs fixed := hRegs.2.2.2
  refine ⟨u,hPath.trans hStep,?_⟩
  change if cutoff ≤ cta then _ else _
  by_cases h : cutoff ≤ cta
  · rw [ite_eq_left h]
    refine ⟨by simpa [more,h] using hU.1,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩
    exact ⟨hRemain.1,hRegs.2.2.1,hRemain.2.2.2.2.1,hRemain.2.2.2.2.2⟩
  · rw [ite_eq_right h]
    refine ⟨by simpa [more,h] using hU.1,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩
    exact ⟨hRemain.2.2.2.1,hRemain.1,hRegs.2.1,hRemain.2.1,hRemain.2.2.1,
      hRemain.2.2.2.2.2⟩

/-- The later group's exact cumulative work reaches either the backedge or the ballot path. -/
theorem terminalDrainLaterRouteOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7715
      (fun lane => let t := warpLane l g lane
        (7263,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::
          laterDrainScanCarry p l t first) shuffles votes ends) :
    if tilePrefix p (min p.batch (first+31))*p.heads ≤ g/l.block then
      Nonempty (SchedulerWarpReached l X g 7666
        (fun lane => terminalSearchLoop p l (warpLane l g lane) first) (shuffles+1) votes ends)
    else Nonempty (SchedulerWarpReached l X g 7720
      (fun lane => let t := warpLane l g lane
        (7262,b32 (groupLaneTiles p first (laneOf l t)))::terminalSelectedGroup p l t first)
      (shuffles+1) votes ends) := by
  obtain ⟨after⟩ := laterBroadcast hp hMax hg cur
  have hb : l.block%32 = 0 := by rw [hp.block]
  have hCta lane (hl : lane < 32) : (warpLane l g lane)/l.block = g/l.block :=
    (Step.sameWarp_lane hb hg hl).1.1.2.2.symm
  by_cases h : tilePrefix p (min p.batch (first+31))*p.heads ≤ g/l.block
  · rw [ite_eq_left h]
    apply after.advanceLocal
    intro lane hl
    obtain ⟨u,hu,hU⟩ := laterCutoff (g := warpLane l g lane) hp
      (Step.sameWarp_lane hb hg hl).1.1.2.1 hFirst (after.checkpoint lane hl)
    rw [hCta lane hl,ite_eq_left h] at hU
    exact ⟨u,hu,hU⟩
  · rw [ite_eq_right h]
    apply after.advanceLocal
    intro lane hl
    obtain ⟨u,hu,hU⟩ := laterCutoff (g := warpLane l g lane) hp
      (Step.sameWarp_lane hb hg hl).1.1.2.1 hFirst (after.checkpoint lane hl)
    rw [hCta lane hl,ite_eq_right h] at hU
    exact ⟨u,hu,hU⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
