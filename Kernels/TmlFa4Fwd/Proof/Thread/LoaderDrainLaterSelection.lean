-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainLaterGroup
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstDrainRetire
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainLaterGroup
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstDrainRetire
import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Flow.Code.Part028

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Loader (loaderLinear)

private theorem firstDrainGroupMissCore {l : Launch} {g count heads cta cutoff : Nat}
    (hCount : count < 2^31) (hHeads : heads < 2^31) (hCta : cta < 2^31)
    (hCutoff : cutoff < 2^31) (hProd : count*heads = cutoff) (hMiss : cutoff ≤ cta) :
    Seg kernel [] l g 3 1787 [(7189,b32 count),(7137,b32 heads),(1072,b32 cta)]
      1790 [(240,.pred false),(7191,b32 cutoff)] := by
  have hSize1 : count < 2^32 := hCount.trans (by decide)
  have hSize2 : cutoff < 2^32 := hCutoff.trans (by decide)
  have hSize3 : heads < 2^32 := hHeads.trans (by decide)
  have hSize4 : cta < 2^32 := hCta.trans (by decide)
  intro s hs
  seg_fp hs using
    simp only [b32,← BitVec.ofNat_mul,hProd,compare,Option.getD_some,
        truncBits_ofNat hSize1 (by decide),truncBits_ofNat hSize2 (by decide),
        truncBits_ofNat hSize3 (by decide),truncBits_ofNat hSize4 (by decide),
        RowDrainRole.signedWord hCta,RowDrainRole.signedWord hCutoff,gt_iff_lt,Int.ofNat_lt,
        decide_eq_false (Nat.not_lt_of_ge hMiss)]

private theorem afterFirstDrainGroupMiss {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g use shuffles votes : Nat} (hg : g < l.threads)
    (hMiss : drainGroupLimit p 0 ≤ g/l.block) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1787
      (fun lane => (7189,b32 (drainGroupCount p 0)) ::
        drainSelectionCarry p l (warpLane l g lane) 0 use) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1794
      (fun lane => laterDrainStart p l (warpLane l g lane) 0 use) shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  let t := warpLane l g lane
  let cta := t/l.block
  let cutoff := drainGroupLimit p 0
  let E := (7137,b32 p.heads)::firstGroupCarry p l t use
  have ht := cur.checkpoint lane hl
  have hOwner : cta = g/l.block := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.2.symm
  have hc : cta < l.grid := by rw [hOwner]; exact NamedBar.cta_lt hg
  have hc31 := hc.trans hp.grid.2.2
  have hBound := hp.prefixWork_signed (Nat.min_le_left p.batch (0+31))
  have hGroup := hp.groupWindow_signed (Nat.zero_le p.batch) (by decide : 31 < 32) 32
  have hProd : drainGroupCount p 0*p.heads = cutoff := by
    simpa [tilePrefix] using drainGroupCount_eq p (first := 0) (Nat.zero_le p.batch)
  have hMiss' : cutoff ≤ cta := by rw [hOwner]; exact hMiss
  have hSeg := firstDrainGroupMissCore (l := l) (g := t) hGroup hp.heads_signed hc31
    hBound hProd hMiss'
  have ht' : At (cur.state lane) 1787
      ([(7189,b32 (drainGroupCount p 0)),(7137,b32 p.heads),(1072,b32 cta)]++E) :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
      holds_lookup ht.2.2.2.2 rfl,ht.2.2.2.2.2.2.2⟩
  obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSeg ht'
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t)
    Flow.code_1790 false hU hU.2.2.2.2.1 (by simp)
  have hvAll := (loaderLinear (regs := []) (by decide) (by decide) hU.1
    (by simp) (by decide) hv).1
  have hIn : At v 1791 ([(1072,b32 cta),(7191,b32 cutoff)]++E) :=
    hV.mono ⟨holds_lookup hV.2.2.2.2 rfl,hV.2.2.2.2.2.1,hV.2.2.2.2.2.2⟩
  have hAfter : Seg kernel [] l t 3 1791 [(1072,b32 cta),(7191,b32 cutoff)] 1794
      [(7190,b32 0),(7185,b32 cutoff),(1173,b32 (cta+1))] := by
    have hCta32 : cta < 2^32 := hc31.trans (by decide)
    have hNext : cta+1 < 2^32 := by omega
    have hOne : truncBits 32 (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 := rfl
    intro s hs
    seg_fp hs using
      (simp only [b32,truncBits_ofNat hCta32 (by decide),
        hOne,← BitVec.ofNat_add,truncBits_ofNat hNext (by decide)]; try rfl)
  obtain ⟨w,hw,hW⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hAfter hIn
  exact ⟨w,(run_rtg hu).trans ((run_rtg hvAll).trans (run_rtg hw)), hW⟩

private theorem laterDrainGroupGateCore {l : Launch} {g count heads work cta cutoff : Nat}
    (hCount : count < 2^31) (hHeads : heads < 2^31) (hWork : work < 2^31)
    (hCta : cta < 2^31) (hCutoff : cutoff < 2^31) (hSum : count*heads+work = cutoff) :
    Seg kernel [] l g 3 1844 [(7189,b32 count),(7137,b32 heads),(7185,b32 work),(1072,b32 cta)]
      1847 [(254,.pred (decide (cutoff ≤ cta))),(7191,b32 cutoff),(7185,b32 cutoff)] := by
  have small {n : Nat} (h : n < 2^31) : n < 2^32 := h.trans (by decide)
  intro s hs
  seg_fp hs using
    simp only [b32,← BitVec.ofNat_mul,← BitVec.ofNat_add,hSum,compare,Option.getD_some,
        truncBits_ofNat (small hCount) (by decide),truncBits_ofNat (small hHeads) (by decide),
        truncBits_ofNat (small hWork) (by decide),truncBits_ofNat (small hCta) (by decide),
        truncBits_ofNat (small hCutoff) (by decide),RowDrainRole.signedWord hCta,
        RowDrainRole.signedWord hCutoff,Int.ofNat_le]

private theorem laterDrainGroupGate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use n : Nat} (hg : g < l.threads) (hn : n ≤ p.batch) {t : TState}
    (ht : At t 1844 (laterDrainTotalFrame p l g n use)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      if drainGroupLimit p n ≤ g/l.block then At u 1794 (laterDrainStart p l g n use)
      else At u 1848 (drainSelectedFrame p l g n use) := by
  let cta := g/l.block
  let count := drainGroupCount p n
  let work := tilePrefix p n*p.heads
  let cutoff := drainGroupLimit p n
  let keep := [(7189,b32 count),
    (7188,b32 (prefixWindow (groupLaneTiles p n) 32 (laneOf l g))),
    (7187,b32 (groupLaneTiles p n (laneOf l g))),(7190,b32 n),
    (1173,b32 (cta+1)),(7137,b32 p.heads)] ++ firstGroupCarry p l g use
  have hCount := hp.groupWindow_signed hn (by decide : 31 < 32) 32
  have hCta := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hSum : count*p.heads+work = cutoff := by simpa [Nat.add_comm] using drainGroupCount_eq p hn
  have hs := laterDrainGroupGateCore (l := l) (g := g) hCount hp.heads_signed
    (hp.prefixWork_signed hn) hCta (hp.prefixWork_signed (Nat.min_le_left ..)) hSum
  have hIn : At t 1844
      ([(7189,b32 count),(7137,b32 p.heads),(7185,b32 work),(1072,b32 cta)]++keep) := by
    apply ht.mono
    have h := ht.2.2.2.2
    simp only [laterDrainTotalFrame,laterScanCarry,laterDrainCarry,List.cons_append,List.nil_append]
      at h
    have hC := h.2.2.2.2.2.2.1
    exact ⟨h.1,hC,h.2.2.2.2.1,holds_mem ht.2.2.2.2 (by
      simp [cta,laterDrainTotalFrame,laterScanCarry,laterDrainCarry,firstGroupCarry,firstDrainTail,
        drainSchedulerFrame]),h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2.1,hC,h.2.2.2.2.2.2.2⟩
  obtain ⟨v,hv,hV⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hs hIn
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1847 _ hV hV.2.2.2.2.1 (by simp)
  have huAll := (loaderLinear (regs := []) (by decide) (by decide) hV.1
    (by simp) (by decide) hu).1
  refine ⟨u,(run_rtg hv).trans (run_rtg huAll),?_⟩
  have hBranchPc := hU.1
  change u.pc = (if decide (cutoff ≤ cta) = true then 1794 else 1847+1) at hBranchPc
  by_cases h : cutoff ≤ cta
  · have hPc : u.pc = 1794 := by simpa only [decide_eq_true h,ite_true] using hBranchPc
    rw [ite_eq_left (show drainGroupLimit p n ≤ g/l.block from h)]
    refine ⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩
    have hr := hU.2.2.2.2.2
    exact ⟨hr.2.2.2.2.2.1,hr.2.1,hr.2.2.2.2.2.2⟩
  · have hPc : u.pc = 1848 := by
      simpa only [decide_eq_false h,Bool.false_eq_true,ite_false,Nat.reduceAdd] using hBranchPc
    rw [ite_eq_right (show ¬ drainGroupLimit p n ≤ g/l.block from h)]
    refine ⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩
    have hr := hU.2.2.2.2.2
    exact ⟨hr.2.2.2.2.2.1,hr.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,
      hr.2.2.2.2.2.2.2⟩


private theorem laterDrainSelectionOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use votes : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    (hActive : g/l.block < tilePrefix p p.batch*p.heads)
    {first shuffles : Nat} (hMiss : drainGroupLimit p first ≤ g/l.block)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1794
      (fun lane => laterDrainStart p l (warpLane l g lane) first use) shuffles votes ends) :
    ∃ n < p.batch, tilePrefix p n*p.heads ≤ g/l.block ∧ g/l.block < drainGroupLimit p n ∧
      ∃ shuffles', Nonempty (SchedulerWarpReached l X g 1848
        (fun lane => drainSelectedFrame p l (warpLane l g lane) n use) shuffles' votes ends) := by
  let n := first+31
  have hn : n < p.batch := by
    by_contra! h
    have he : drainGroupLimit p first = tilePrefix p p.batch*p.heads := by
      simp [drainGroupLimit,Nat.min_eq_left h,n]
    omega
  have hLower : tilePrefix p n*p.heads ≤ g/l.block := by
    simpa [drainGroupLimit,Nat.min_eq_right hn.le,n] using hMiss
  obtain ⟨total⟩ := laterDrainGroupTotalOfMaximal hp hMax hg hn hCuQ cur
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  by_cases hUpper : drainGroupLimit p n ≤ g/l.block
  · obtain ⟨next⟩ := total.advanceLocal (pc' := 1794)
      (G := fun lane => laterDrainStart p l (warpLane l g lane) n use) (by
        intro lane hl
        have hw := (Step.sameWarp_lane hBlock hg hl).1
        obtain ⟨t,ht,hT⟩ := laterDrainGroupGate hp hw.1.2.1 hn.le (total.checkpoint lane hl)
        rw [ite_eq_left (hw.1.2.2 ▸ hUpper)] at hT
        exact ⟨t,ht,hT⟩)
    exact laterDrainSelectionOfMaximal hp hMax hg hCuQ hActive hUpper next
  · refine ⟨n,hn,hLower,Nat.lt_of_not_ge hUpper,shuffles+7,total.advanceLocal ?_⟩
    intro lane hl
    have hw := (Step.sameWarp_lane hBlock hg hl).1
    obtain ⟨t,ht,hT⟩ := laterDrainGroupGate hp hw.1.2.1 hn.le (total.checkpoint lane hl)
    rw [ite_eq_right (hw.1.2.2 ▸ hUpper)] at hT
    exact ⟨t,ht,hT⟩
termination_by p.batch-first
decreasing_by omega

/-- For any active CTA, the loader's actual drain scans reach its
selected request and consume the terminal release waits before exiting. -/
theorem CacheDrainNeighbors.exitOfScheduledCta {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (c : CacheDrainNeighbors p l X g use)
    (hCuQ : DrainCuQProtected p X) (hActive : g/l.block < tilePrefix p p.batch*p.heads)
    (hCache : CacheDrainReady l X g use)
    (hQuery : warpIndex l g = 14 → QueryDrainReady l X g 0) : Thread.Exited X g := by
  by_cases hFirst : g/l.block < drainGroupLimit p 0
  · exact c.exitOfFirstGroup hp hMax hg hw hFirst hCache hQuery
  obtain ⟨total⟩ := c.firstGroupTotalOfMaximal hp hMax hg
  obtain ⟨later⟩ := afterFirstDrainGroupMiss hp hg (Nat.le_of_not_gt hFirst) total
  obtain ⟨first,hFirst,hLo,hHi,_,⟨selected⟩⟩ :=
    laterDrainSelectionOfMaximal hp hMax hg hCuQ hActive (Nat.le_of_not_gt hFirst) later
  obtain ⟨n,hn,⟨entry⟩⟩ := drainSelectedBallotEntry hp hg hFirst hLo hHi selected
  obtain ⟨indices⟩ := drainSelectedIndicesOfMaximal hp hMax hg hn entry
  obtain ⟨ready⟩ := prepareSelectedDrain hp hg hw indices
  exact activeLoaderExitOfDrainReached hp hMax hg hw (by decide) hCache hQuery ready


/-- The recorded exit from the producer loop, with its next cache use and scheduler seeds. -/
abbrev CacheDrainEntry (p : Params) (l : Launch) (X : Execution) (g use : Nat) :=
  ∃ shuffles votes ends, Nonempty (SchedulerWarpReached l X g 1744
    (fun lane => firstDrainTail p l (warpLane l g lane) use) shuffles votes ends)

/-- A scheduled cache producer at the terminal loop boundary drains its release objects
and retires after its actual request-group rescan. -/
theorem cacheDrainExitOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) (hActive : g/l.block < tilePrefix p p.batch*p.heads)
    (hReached : CacheDrainEntry p l X g use) (hCache : CacheDrainReady l X g use)
    (hQuery : warpIndex l g = 14 → QueryDrainReady l X g 0) : Thread.Exited X g := by
  obtain ⟨_,_,_,⟨cur⟩⟩ := hReached
  obtain ⟨neighbors⟩ := cacheDrainNeighborsOfStart hp hMax hg hCuQ cur
  exact neighbors.exitOfScheduledCta hp hMax hg hw hCuQ hActive hCache hQuery

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
