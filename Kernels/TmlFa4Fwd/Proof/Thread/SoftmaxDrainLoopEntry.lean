-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainFirstTotal
import Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainLaterProgress
import all Kernels.TmlFa4Fwd.Proof.MmaScanCounter
import Kernels.TmlFa4Fwd.Flow.Code.Part119
import Kernels.TmlFa4Fwd.Flow.Code.Part120

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Mma

/-- The CTA and ABI state available to each group of the softmax terminal rescan. -/
def terminalSearchCommon (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1606,b32 (g/l.block)),(7141,b32 p.heads)] ++ RowDrainRole.softmax.roots p l g

/-- The old group start and the cumulative work through that group on a rescan backedge. -/
def terminalSearchLoop (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(7265,b32 first),(7260,b32 (tilePrefix p (min p.batch (first+31))*p.heads)),
    (1607,b32 (g/l.block+1))] ++ terminalSearchCommon p l g

/-- The new group's clipped start and CTA stop word. -/
def terminalSearchGroup (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(7265,b32 first),(7260,b32 (tilePrefix p first*p.heads)),
    (7266,b32 (g/l.block+1)),(1607,b32 (g/l.block+1))] ++ terminalSearchCommon p l g

/-- State at the first read guard of a subsequent group. -/
def terminalSearchRead (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(1609,b32 (first+laneOf l g)),(664,.pred (decide (p.batch < first+laneOf l g))),
    (7261,b32 0)] ++ terminalSearchGroup p l g first

/-- The selected group's cumulative count and warp prefixes at the terminal branch. -/
def terminalSelectedGroup (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(7265,b32 first),(7266,b32 (tilePrefix p (min p.batch (first+31))*p.heads)),
    (7264,b32 (prefixWindow (groupLaneTiles p first) 32 31)),
    (7263,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g)))] ++
    terminalSearchCommon p l g

theorem drainLocalKeep {l : Launch} {g start n : Nat} {s t : TState}
    {F : List (Nat × Value)} (hs : At s start F)
    (hLo : RowDrainRole.softmax.start ≤ start)
    (hHi : start+n ≤ RowDrainRole.softmax.exitFloor)
    (hWrites : ((kernel.code.drop start).take n).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
    (hStraight : ((kernel.code.drop start).take (n-1)).all
      (fun ins => schedulerFallsThrough ins.op) = true)
    (hRun : run kernel [] l g n s = some t) :
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧ Holds t.regs F := by
  refine ⟨RowDrainRole.softmax.drainLocals hLo hHi hs.1 hStraight hRun,?_⟩
  exact holdsSchedulerFrame hs.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hStraight hRun hs.1.ge (by rw [hs.1]) hr) (fun _ h =>
      List.mem_map_of_mem h)

private theorem firstGroupBranch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) {t : TState}
    (ht : At t 7658
      ([(7264,b32 (tilePrefix p (min p.batch 31))),
        (7263,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l g))),(7141,b32 p.heads)] ++
        RowDrainRole.softmax.roots p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      u.regs 7262 = t.regs 7262 ∧
      if g/l.block < tilePrefix p (min p.batch 31)*p.heads then
        At u 7720 (terminalSelectedGroup p l g 0)
      else At u 7666 (terminalSearchLoop p l g 0) := by
  let count := tilePrefix p (min p.batch 31)
  let cta := g/l.block
  let limit := count*p.heads
  let pick := decide (cta < limit)
  have hFit := hp.prefixWork_signed (Nat.min_le_left p.batch 31)
  change limit < 2^31 at hFit
  have hCount : count < 2^31 := by
    have h := hp.groupWindow_signed (Nat.zero_le p.batch) (show (31 : Nat) < 32 by decide) 32
    have hSum := groupTiles_eq p (Nat.zero_le p.batch) (show (32 : Nat) ≤ 32 by decide)
    have he : prefixWindow (groupLaneTiles p 0) 32 31 = count := by
      rw [prefixWindow_warp _ (by decide : (31 : Nat) < 32)]
      simpa [count,tilePrefix] using hSum
    rwa [he] at h
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hReg : (l.ctaidOf (g/l.block)).get .x = cta :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  have hGate : Seg kernel [] l g 4 7658 [(7264,b32 count),(7141,b32 p.heads)] 7662
      [(662,.pred pick),(7266,b32 limit),(1606,b32 cta),(7265,b32 0)] := by
    have hHead32 : p.heads < 2^32 := hp.heads_signed.trans (by decide)
    have hCount32 : count < 2^32 := hCount.trans (by decide)
    have hFit32 : count*p.heads < 2^32 := hFit.trans (by decide)
    have hCta32 : cta < 2^32 := hCta.trans (by decide)
    intro s hs
    seg_fp hs using
      first
      | rfl
      | simp only [b32,← BitVec.ofNat_mul,hReg,compare,Option.getD_some,
          truncBits_ofNat hHead32 (by decide),truncBits_ofNat hCount32 (by decide),
          truncBits_ofNat hFit32 (by decide),truncBits_ofNat hCta32 (by decide),
          RowDrainRole.signedWord (show count*p.heads < 2^31 from hFit),
          RowDrainRole.signedWord hCta,pick,limit,gt_iff_lt,Int.ofNat_lt]

  obtain ⟨s,hs,hsAt⟩ := hGate.apply (ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.2.1,trivial⟩)
  let old := ([(7264,b32 count),
      (7263,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l g))),(7141,b32 p.heads)] ++
        RowDrainRole.softmax.roots p l g)
  have hOld : At t 7658 old := ht
  obtain ⟨hLocal,hKeep⟩ := drainLocalKeep hOld (by decide) (by decide)
    (by dsimp only [old,RowDrainRole.roots,RowDrainRole.frame,RowDrainRole.batchReg,
          RowDrainRole.laneReg,RowDrainRole.ctaReg,List.cons_append,List.nil_append,List.map] ;
        decide +kernel)
    (by decide +kernel) hs
  let common := terminalSearchCommon p l g
  have hCommon : Holds s.regs common := ⟨hsAt.2.2.2.2.2.2.1,hKeep.2.2⟩
  have hSelected : Holds s.regs (terminalSelectedGroup p l g 0) := by
    refine ⟨hsAt.2.2.2.2.2.2.2.1,hsAt.2.2.2.2.2.1,?_,hKeep.2.1,hCommon⟩
    have he : prefixWindow (groupLaneTiles p 0) 32 31 = count := by
      rw [prefixWindow_warp _ (by decide : (31 : Nat) < 32)]
      simpa [count,tilePrefix] using
        groupTiles_eq p (Nat.zero_le p.batch) (show (32 : Nat) ≤ 32 by decide)
    rw [he]
    exact hKeep.1
  let carry := (7266,b32 limit)::(7265,b32 0)::common
  have hsAt' : At s 7662 ((terminalSelectedGroup p l g 0) ++ carry) :=
    hsAt.mono ((holds_append ..).mpr ⟨hSelected,hsAt.2.2.2.2.2.1,
      hsAt.2.2.2.2.2.2.2.1,hCommon⟩)
  obtain ⟨u,hu,huAt⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7662 pick hsAt' hsAt.2.2.2.2.1 (by simp)
  have hGo := hLocal.trans
    (RowDrainRole.softmax.drainLocals (by decide) (by decide) hsAt'.1 (by simp) hu)
  have hFirstCount : s.regs 7262 = t.regs 7262 := schedulerLocalFrame
    (lo := 7658) (len := 4) (regs := [7262]) (by decide +kernel) (by decide +kernel)
    hs ht.1.ge (by rw [ht.1]) (by simp)
  have hBranchCount : u.regs 7262 = s.regs 7262 := schedulerLocalFrame
    (lo := 7662) (len := 1) (regs := [7262]) (by decide +kernel) (by decide +kernel)
    hu hsAt'.1.ge (by rw [hsAt'.1]) (by simp)
  have hCountKeep := hBranchCount.trans hFirstCount
  by_cases h : cta < limit
  · refine ⟨u,hGo,hCountKeep,?_⟩
    change if cta < limit then _ else _
    rw [ite_eq_left h]
    have hAt := huAt.mono ((holds_append ..).mp huAt.2.2.2.2).1
    simpa only [pick,decide_eq_true h,ite_true] using hAt
  · have hu' : At u 7663 carry := by
      simpa only [pick,decide_eq_false h,Bool.false_eq_true,ite_false] using
        huAt.mono ((holds_append ..).mp huAt.2.2.2.2).2
    have hCtaAdd : cta+1 < 2^32 := by omega
    have hInit : Seg kernel [] l g 3 7663 carry 7666
        [(7265,b32 0),(7260,b32 limit),(1607,b32 (cta+1))] := by
      intro a ha
      have ht' : At a 7663 [(7266,b32 limit),(1606,b32 cta)] :=
        ha.mono ⟨ha.2.2.2.2.1,ha.2.2.2.2.2.2.1,trivial⟩
      seg_fp ht' using norm_bits [Nat.mod_eq_of_lt hCtaAdd]
    obtain ⟨v,hv,hvAt⟩ := hInit.apply hu'
    have hFixed : At u 7663 common := hu'.mono hu'.2.2.2.2.2.2
    obtain ⟨hLocal',hKeep'⟩ := drainLocalKeep hFixed (by decide) (by decide)
      (by dsimp only [common,terminalSearchCommon,RowDrainRole.roots,RowDrainRole.frame,
            RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
            List.cons_append,List.nil_append,List.map]
          decide +kernel)
      (by decide +kernel) hv
    have hLoop : At v 7666 (terminalSearchLoop p l g 0) :=
      hvAt.mono ⟨hvAt.2.2.2.2.1,hvAt.2.2.2.2.2.1,hvAt.2.2.2.2.2.2.1,hKeep'⟩
    have hSetupCount : v.regs 7262 = u.regs 7262 := schedulerLocalFrame
      (lo := 7663) (len := 3) (regs := [7262]) (by decide +kernel) (by decide +kernel)
      hv hu'.1.ge (by rw [hu'.1]) (by simp)
    refine ⟨v,hGo.trans hLocal',hSetupCount.trans hCountKeep,?_⟩
    change if cta < limit then _ else _
    rwa [ite_eq_right h]

/-- The actual first rescan group either selects the CTA or reaches the loop backedge. -/
theorem terminalDrainFirstRouteOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7658
      (fun lane => let t := warpLane l g lane
        [(7264,b32 (tilePrefix p (min p.batch 31))),
          (7263,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l t))),(7141,b32 p.heads)] ++
          RowDrainRole.softmax.roots p l t) shuffles votes ends) :
    if g/l.block < tilePrefix p (min p.batch 31)*p.heads then
      Nonempty (SchedulerWarpReached l X g 7720
        (fun lane => terminalSelectedGroup p l (warpLane l g lane) 0) shuffles votes ends)
    else Nonempty (SchedulerWarpReached l X g 7666
      (fun lane => terminalSearchLoop p l (warpLane l g lane) 0) shuffles votes ends) := by
  have hb : l.block%32 = 0 := by rw [hp.block]
  have hCta (lane : Nat) (hl : lane < 32) : warpLane l g lane/l.block = g/l.block :=
    (Step.sameWarp_lane hb hg hl).1.1.2.2.symm
  by_cases h : g/l.block < tilePrefix p (min p.batch 31)*p.heads
  · rw [ite_eq_left h]
    apply cur.advanceLocal
    intro lane hl
    obtain ⟨u,hLocal,_,hu⟩ := firstGroupBranch (g := warpLane l g lane) hp
      (Step.sameWarp_lane hb hg hl).1.1.2.1
      (cur.checkpoint lane hl)
    rw [hCta lane hl,ite_eq_left h] at hu
    exact ⟨u,hLocal,hu⟩
  · rw [ite_eq_right h]
    apply cur.advanceLocal
    intro lane hl
    obtain ⟨u,hLocal,_,hu⟩ := firstGroupBranch (g := warpLane l g lane) hp
      (Step.sameWarp_lane hb hg hl).1.1.2.1
      (cur.checkpoint lane hl)
    rw [hCta lane hl,ite_eq_right h] at hu
    exact ⟨u,hLocal,hu⟩

/-- The first selected group keeps the current lane's decoded tile count. -/
theorem terminalFirstSelectedWithTileCount {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g shuffles votes : Nat} (hg : g < l.threads)
    (hSelected : g/l.block < tilePrefix p (min p.batch 31)*p.heads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7658
      (fun lane => let t := warpLane l g lane
        [(7264,b32 (tilePrefix p (min p.batch 31))),
          (7263,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l t))),(7141,b32 p.heads)] ++
          RowDrainRole.softmax.roots p l t) shuffles votes ends)
    (hCount : ∀ lane < 32, (cur.state lane).regs 7262 =
      some (b32 (groupLaneTiles p 0 (laneOf l (warpLane l g lane))))) :
    Nonempty (SchedulerWarpReached l X g 7720
      (fun lane => let t := warpLane l g lane
        (7262,b32 (groupLaneTiles p 0 (laneOf l t)))::terminalSelectedGroup p l t 0)
      shuffles votes ends) := by
  have hb : l.block%32 = 0 := by rw [hp.block]
  apply cur.advanceLocal
  intro lane hl
  let thread := warpLane l g lane
  have hSame := (Step.sameWarp_lane hb hg hl).1
  have hCta : thread/l.block = g/l.block := hSame.1.2.2.symm
  obtain ⟨u,hu,hKept,hU⟩ := firstGroupBranch (g := thread) hp
    hSame.1.2.1 (cur.checkpoint lane hl)
  rw [hCta,ite_eq_left hSelected] at hU
  exact ⟨u,hu,hU.mono ⟨hKept.trans (hCount lane hl),hU.2.2.2.2⟩⟩

/-- Registers at the terminal comparison after the final group advance clips at the batch. -/
def terminalExhaustedSearch (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (7265,b32 p.batch)::terminalSearchCommon p l g

private theorem nextGroupBranch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch) {t : TState}
    (ht : At t 7666 (terminalSearchLoop p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      if p.batch ≤ first+31 then At u 7720 (terminalExhaustedSearch p l g)
      else At u 7674 (terminalSearchRead p l g (first+31)) := by
  let cta := g/l.block
  let base := tilePrefix p (min p.batch (first+31))*p.heads
  let saved := [(7260,b32 base),(7141,b32 p.heads)] ++ RowDrainRole.softmax.roots p l g
  have hBig := hp.shape.2.2
  have hBatch := hp.shape.2.1
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hNext : first+31 < 2^31 := by omega
  have hStop : cta+1 < 2^31 := (Nat.succ_le_of_lt (NamedBar.cta_lt hg)).trans_lt hp.grid.2.2
  have hInitial : At t 7666 (groupScanFacts .softmaxDrain first p.batch cta ++ saved) := by
    refine ht.mono ((holds_append ..).mpr ⟨?_,?_⟩)
    · exact ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.2.2.2.2.1,
        ht.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2.1,trivial⟩
    · exact ⟨ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.2.2⟩
  obtain ⟨u,hRun,hu⟩ := advanceGroupScanPreserving (l := l) (g := g) .softmaxDrain
    hNext hBatch (by
      dsimp only [scanSite,saved,RowDrainRole.roots,RowDrainRole.frame,RowDrainRole.batchReg,
        RowDrainRole.laneReg,RowDrainRole.ctaReg,List.cons_append,List.nil_append,List.map]
      decide +kernel) hInitial
  have hSaved := (holds_append ..).mp hu.2.2.2.2.2.2
  have hCommon : Holds u.regs (terminalSearchCommon p l g) :=
    ⟨hSaved.1.2.2.2.1,hSaved.2.2⟩
  have hPath := run_rtg hRun
  by_cases h : p.batch ≤ first+31
  · have hAt : At u 7717 [(7266,b32 (cta+1)),(1606,b32 cta)] := by
      have h' := hu.mono (G := [(7266,b32 (cta+1)),(1606,b32 cta)])
        ⟨hu.2.2.2.2.2.1,hCommon.1,trivial⟩
      simpa only [h,ite_true,scanSite] using h'
    have hStart : At u 7717 (terminalExhaustedSearch p l g) := by
      have hClip := hSaved.1.1
      change u.regs 7265 = some (b32 (min (first+31) p.batch)) at hClip
      rw [Nat.min_eq_right h] at hClip
      exact hAt.mono ⟨hClip,hCommon⟩
    obtain ⟨v,hCore,hv⟩ := (exhaustedSegment (l := l) (g := g) .softmaxDrain hStop).apply hAt
    obtain ⟨z,hBranch,hz⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
      Flow.code_7719 false hv hv.2.2.2.2.1 (by simp)
    have hCore' : run kernel [] l g 3 u = some z := run_comp hCore hBranch
    obtain ⟨hLocal,hKeep⟩ := drainLocalKeep hStart (by decide) (by decide)
      (by
        dsimp only [terminalExhaustedSearch, terminalSearchCommon, RowDrainRole.roots,
          RowDrainRole.frame,
          RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
          List.cons_append,List.nil_append,List.map]
        decide +kernel)
      (by decide +kernel) hCore'
    have hAtZ : At z 7720 (terminalExhaustedSearch p l g) :=
      hz.mono hKeep
    exact ⟨z,hPath.trans hLocal,by rwa [ite_eq_left h]⟩
  · have hClipped : min p.batch (first+31) = first+31 := Nat.min_eq_right (by omega)
    have hFrame : Holds u.regs (terminalSearchGroup p l g (first+31)) := by
      refine ⟨?_,?_,hu.2.2.2.2.2.1,hSaved.1.2.2.1,hCommon⟩
      · have hEq := hSaved.1.1
        change u.regs 7265 = some (b32 (min (first+31) p.batch)) at hEq
        simpa only [Nat.min_eq_left (by omega : first+31 ≤ p.batch)] using hEq
      · simpa only [base,hClipped] using hSaved.2.1
    let ix := first+31+laneOf l g
    have hIdx : ix < 2^31 := by dsimp [ix]; omega
    have hU : At u 7671 (terminalSearchGroup p l g (first+31)) := by
      simpa only [scanSite,h,ite_false] using hu.mono hFrame
    have hGate : Seg kernel [] l g 3 7671
        [(1608,b32 (first+31)),(1215,b32 (laneOf l g)),(7151,b32 p.batch)] 7674
        [(1609,b32 ix),(664,.pred (decide (p.batch < ix))),(7261,b32 0)] := by
      have hNext32 : first+31 < 2^32 := by omega
      have hLane32 : laneOf l g < 2^32 := by omega
      have hIdx32 : first+31+laneOf l g < 2^32 := by omega
      have hBatch32 : p.batch < 2^32 := by omega
      intro v hv
      seg_fp hv using
        first
        | rfl
        | simp only [b32,ix,← BitVec.ofNat_add,truncBits_ofNat hNext32 (by decide),
            truncBits_ofNat hLane32 (by decide),truncBits_ofNat hIdx32 (by decide),
            truncBits_ofNat hBatch32 (by decide),compare,Option.getD_some,
            RowDrainRole.signedWord (show first+31+laneOf l g < 2^31 from hIdx),
            RowDrainRole.signedWord hBatch,Int.ofNat_lt,gt_iff_lt]
    obtain ⟨v,hCode,hv⟩ := hGate.apply (hU.mono
      ⟨hu.2.2.2.2.1,hCommon.2.2.2.1,hCommon.2.2.1,trivial⟩)
    obtain ⟨hLocal,hKeep⟩ := drainLocalKeep hU (by decide) (by decide)
      (by
        dsimp only [terminalSearchGroup,terminalSearchCommon,RowDrainRole.roots,RowDrainRole.frame,
          RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
          List.cons_append,List.nil_append,List.map]
        decide +kernel)
      (by decide +kernel) hCode
    have hDone : At v 7674 (terminalSearchRead p l g (first+31)) :=
      hv.mono ⟨hv.2.2.2.2.1,hv.2.2.2.2.2.1,hv.2.2.2.2.2.2.1,hKeep⟩
    exact ⟨v,hPath.trans hLocal,by rwa [ite_eq_right h]⟩

/-- Every reached backedge clips at the batch or prepares the next group's protected reads. -/
theorem terminalDrainAdvanceGroup {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first ≤ p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7666
      (fun lane => terminalSearchLoop p l (warpLane l g lane) first) shuffles votes ends) :
    if p.batch ≤ first+31 then
      Nonempty (SchedulerWarpReached l X g 7720
        (fun lane => terminalExhaustedSearch p l (warpLane l g lane)) shuffles votes ends)
    else Nonempty (SchedulerWarpReached l X g 7674
      (fun lane => terminalSearchRead p l (warpLane l g lane) (first+31)) shuffles votes ends) := by
  have hb : l.block%32 = 0 := by rw [hp.block]
  by_cases h : p.batch ≤ first+31
  · rw [ite_eq_left h]
    apply cur.advanceLocal
    intro lane hl
    obtain ⟨u,hLocal,hu⟩ := nextGroupBranch hp (Step.sameWarp_lane hb hg hl).1.1.2.1
      hFirst (cur.checkpoint lane hl)
    rw [ite_eq_left h] at hu
    exact ⟨u,hLocal,hu⟩
  · rw [ite_eq_right h]
    apply cur.advanceLocal
    intro lane hl
    obtain ⟨u,hLocal,hu⟩ := nextGroupBranch hp (Step.sameWarp_lane hb hg hl).1.1.2.1
      hFirst (cur.checkpoint lane hl)
    rw [ite_eq_right h] at hu
    exact ⟨u,hLocal,hu⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
