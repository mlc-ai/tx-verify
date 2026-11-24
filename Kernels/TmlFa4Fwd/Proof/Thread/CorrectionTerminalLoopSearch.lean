-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalLoopWindow
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

private def terminalLaterTotalFrame (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) :=
  (7284,b32 (terminalGroupTotal p first))::
    (7283,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g)))::
      laterDrainScanCarry p l g first

private theorem laterCutoff {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    {s : TState} (hs : At s 9183 (terminalLaterTotalFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      if terminalCutoff p first ≤ g/l.block then
        At u 9133 (terminalSearchFrame p l g first)
      else At u 9187 (terminalSelectedFrame p l g first) := by
  let cta := g/l.block
  let count := terminalGroupTotal p first
  let old := tilePrefix p first*p.heads
  let cutoff := terminalCutoff p first
  let part := prefixWindow (groupLaneTiles p first) 32 (laneOf l g)
  let own := groupLaneTiles p first (laneOf l g)
  let fixed := [(7285,b32 first),(7284,b32 count),(7283,b32 part),(7282,b32 own),
    (1658,b32 (cta+1)),(7143,b32 p.heads)] ++ RowDrainRole.correction.roots p l g
  have hSum : count*p.heads+old = cutoff := by
    have h := congrArg (· * p.heads) (groupTiles_eq p hFirst (by decide : 32 ≤ 32))
    have hCount : count = ∑ i ∈ Finset.range 32, groupLaneTiles p first i :=
      prefixWindow_warp _ (by decide : 31 < 32)
    rw [hCount]
    simpa only [show min 31 32 = 31 by decide,Nat.add_mul,Nat.add_comm,cutoff,
      terminalCutoff,old] using h
  have hFit : cutoff < 2^31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hCount : count < 2^31 := hp.groupWindow_signed hFirst (show 31 < 32 by decide) 32
  have hOld : old < 2^31 := hp.prefixWork_signed hFirst
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  let more := decide (cutoff ≤ cta)
  have hSeg : Seg kernel [] l g 3 9183
      [(7284,b32 count),(7143,b32 p.heads),(7280,b32 old),(1618,b32 cta)] 9186
      [(767,.pred more),(7286,b32 cutoff),(7280,b32 cutoff)] := by
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
  have hFixed : At s 9183 fixed := by
    exact hs.mono ⟨holds_lookup hReg rfl,holds_lookup hReg rfl,holds_lookup hReg rfl,
      holds_lookup hReg rfl,holds_lookup hReg rfl,holds_lookup hReg rfl,
      hReg.2.2.2.2.2.2.2⟩
  obtain ⟨hPath,hKeep⟩ := terminalLocalsKeep hFixed (by decide) (by decide) (by
      change ((kernel.code.drop 9183).take 3).all (fun i =>
        [7285,7284,7283,7282,1658,7143,7153,1616,7506,1618].all
          (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel) (by decide +kernel) hRun
  have hAt : At v 9186 ([(767,.pred more),(7286,b32 cutoff),(7280,b32 cutoff)] ++ fixed) :=
    hv.mono ⟨hv.2.2.2.2.1,hv.2.2.2.2.2.1,hv.2.2.2.2.2.2.1,hKeep⟩
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_9186 more hAt hAt.2.2.2.2.1 (by simp)
  have hStep := RowDrainRole.correction.drainLocals (n := 1) (by decide) (by decide)
    hAt.1 (by simp) hu
  have hRegs := hU.2.2.2.2
  have hRemain : Holds u.regs fixed := hRegs.2.2.2
  refine ⟨u,hPath.trans hStep,?_⟩
  change if cutoff ≤ cta then _ else _
  by_cases h : cutoff ≤ cta
  · rw [ite_eq_left h]
    refine ⟨by simpa [more,h] using hU.1,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩
    exact ⟨hRemain.2.2.2.2.1,hRemain.1,hRegs.2.2.1,hRemain.2.2.2.2.2⟩
  · rw [ite_eq_right h]
    refine ⟨by simpa [more,h] using hU.1,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩
    exact ⟨hRegs.2.1,hRemain.1,hRemain.2.1,hRemain.2.2.1,hRemain.2.2.2.1,
      hRemain.2.2.2.2.2⟩

private theorem chooseLaterGroup {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9182
      (fun lane => let t := warpLane l g lane
        (7283,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::
          laterDrainScanCarry p l t first) shuffles votes ends) :
    if terminalCutoff p first ≤ g/l.block then
      Nonempty (SchedulerWarpReached l X g 9133
        (fun lane => terminalSearchFrame p l (warpLane l g lane) first) (shuffles+1) votes ends)
    else Nonempty (SchedulerWarpReached l X g 9187
      (fun lane => terminalSelectedFrame p l (warpLane l g lane) first)
      (shuffles+1) votes ends) := by
  obtain ⟨after⟩ := terminalGroupTotalOfMaximal hp hMax hg true
    (by
      intro lane _ x hx
      simp only [laterDrainScanCarry,terminalLaterGroupFrame,RowDrainRole.roots,
        RowDrainRole.frame,RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
        List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
    cur
  have hb : l.block%32 = 0 := by rw [hp.block]
  have hCta lane (hl : lane < 32) : (warpLane l g lane)/l.block = g/l.block :=
    (Step.sameWarp_lane hb hg hl).1.1.2.2.symm
  by_cases h : terminalCutoff p first ≤ g/l.block
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

/-- A reached active correction warp searches all remaining request groups until the
actual group that owns its CTA is selected. -/
theorem terminalLaterSearchOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g first shuffles votes : Nat} (hg : g < l.threads)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads)
    (hMiss : terminalCutoff p first ≤ g/l.block) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9133
      (fun lane => terminalSearchFrame p l (warpLane l g lane) first) shuffles votes ends) :
    ∃ chosen steps, first < chosen ∧ chosen < p.batch ∧
      tilePrefix p chosen*p.heads ≤ g/l.block ∧ g/l.block < terminalCutoff p chosen ∧
      Nonempty (SchedulerWarpReached l X g 9187
        (fun lane => terminalSelectedFrame p l (warpLane l g lane) chosen)
        (shuffles+7*steps) votes ends) := by
  have hMore : first+31 < p.batch := by
    by_contra! h
    have hh : terminalCutoff p first = tilePrefix p p.batch*p.heads := by
      unfold terminalCutoff
      rw [Nat.min_eq_left h]
    rw [hh] at hMiss
    omega
  obtain ⟨reads⟩ := terminalLaterGroupEntry hp hMore cur
  obtain ⟨down⟩ := terminalDrainReadsNextGroup hp hMax hCuQ hg reads
  obtain ⟨next⟩ := terminalDrainLaterWindowOfMaximal hp hMax hg hMore.le down
  have hRoute := chooseLaterGroup hp hMax hg hMore.le next
  by_cases hNext : terminalCutoff p (first+31) ≤ g/l.block
  · rw [ite_eq_left hNext] at hRoute
    obtain ⟨edge⟩ := hRoute
    obtain ⟨chosen,steps,hChosen,hBatch,hLow,hHigh,hEnd⟩ :=
      terminalLaterSearchOfMaximal hp hMax hCuQ hg hWork hNext edge
    have hCount : (shuffles+6+1)+7*steps = shuffles+7*(steps+1) := by omega
    exact ⟨chosen,steps+1,by omega,hBatch,hLow,hHigh,by simpa only [hCount] using hEnd⟩
  · rw [ite_eq_right hNext] at hRoute
    have hLow : tilePrefix p (first+31)*p.heads ≤ g/l.block := by
      simpa only [terminalCutoff,Nat.min_eq_right hMore.le] using hMiss
    exact ⟨first+31,1,by omega,hMore,hLow,Nat.lt_of_not_ge hNext,by simpa using hRoute⟩
termination_by p.batch-first
decreasing_by omega

/-- After the first total, only the CTA's containing group is selected, including
tiles in any later group of the batch. -/
theorem terminalGroupSelectedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g shuffles votes : Nat} (hg : g < l.threads)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9126
      (fun lane => terminalFirstTotalFrame p l (warpLane l g lane)) shuffles votes ends) :
    ∃ chosen steps, chosen < p.batch ∧ tilePrefix p chosen*p.heads ≤ g/l.block ∧
      g/l.block < terminalCutoff p chosen ∧
      Nonempty (SchedulerWarpReached l X g 9187
        (fun lane => terminalSelectedFrame p l (warpLane l g lane) chosen)
        (shuffles+7*steps) votes ends) := by
  have hRoute := terminalFirstRouteOfMaximal hp hg cur
  by_cases hFirst : g/l.block < terminalCutoff p 0
  · rw [ite_eq_left hFirst] at hRoute
    exact ⟨0,0,hp.shape.1,by simp [tilePrefix],hFirst,by simpa using hRoute⟩
  · rw [ite_eq_right hFirst] at hRoute
    obtain ⟨edge⟩ := hRoute
    obtain ⟨chosen,steps,_,hBatch,hLow,hHigh,hEnd⟩ :=
      terminalLaterSearchOfMaximal hp hMax hCuQ hg hWork (Nat.le_of_not_gt hFirst) edge
    exact ⟨chosen,steps,hBatch,hLow,hHigh,hEnd⟩

end PTX.Kernels.TmlFa4Fwd.Correction
