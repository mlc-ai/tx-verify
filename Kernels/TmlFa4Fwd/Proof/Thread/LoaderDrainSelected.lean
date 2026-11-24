-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainFirstGroup
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotCursor
import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import Kernels.TmlFa4Fwd.Flow.Code.Part028
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

def drainIndexCarry (p : Params) (l : Launch) (g first use : Nat) : List (Nat × Value) :=
  [(7188,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g))),
    (7187,b32 (groupLaneTiles p first (laneOf l g))),(7192,b32 0)] ++ firstDrainTail p l g use

private theorem terminalBallotArgs (l : Launch) (g : Nat)
    {base count part heads cta : Nat} (hPrefix : part ≤ count) (hCount : count < 2^31)
    (hHead : heads < 2^31) (hCta : cta < 2^31) (hEnd : base+count*heads < 2^31) :
    Seg kernel [] l g 4 1851
      [(7189,b32 count),(7137,b32 heads),(7191,b32 (base+count*heads)),
        (7188,b32 part),(1072,b32 cta)] 1855
      [(256,.pred (decide (base+part*heads ≤ cta)))] := by
  have hMul := Nat.mul_le_mul_right heads hPrefix
  have hBase : base < 2^31 := by omega
  have hProd : count*heads < 2^31 := by omega
  have hPre : part < 2^31 := by omega
  have hPrefixWork : base+part*heads < 2^31 := by omega
  intro t ht
  seg_fp ht using
    first
    | norm_cmp
    | (simp only [compare,Option.getD_some,← BitVec.ofNat_mul,
        truncBits_ofNat (show count < 2^32 by omega) (by decide),
        truncBits_ofNat (show heads < 2^32 by omega) (by decide),
        truncBits_ofNat (show part < 2^32 by omega) (by decide),
        truncBits_ofNat (show cta < 2^32 by omega) (by decide)]
       norm_cmp)

private theorem selectedBallotLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use first : Nat} {t : TState} (hg : g < l.threads) (hFirst : first < p.batch)
    (ht : At t 1848 (drainSelectedFrame p l g first use)) :
    let part := prefixWindow (groupLaneTiles p first) 32 (laneOf l g)
    let base := tilePrefix p first*p.heads
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 1855 ((256,.pred (decide (base+part*p.heads ≤ g/l.block)))::
        drainIndexCarry p l g first use) := by
  let xs := groupLaneTiles p first
  let lane := laneOf l g
  let base := tilePrefix p first*p.heads
  let cta := g/l.block
  let part := prefixWindow xs 32 lane
  let group := drainGroupCount p first
  let limit := drainGroupLimit p first
  let frame := drainSelectedFrame p l g first use
  have hBatch : p.batch < 2^31 := hp.shape.2.1
  have hFirst32 : first < 2^32 := by omega
  have hBatch32 : p.batch < 2^32 := by omega
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hGroup := hp.groupWindow_signed hFirst.le (show 31 < 32 by decide) 32
  change group < 2^31 at hGroup
  have hPartGroup : part ≤ group := by
    rw [show group = ∑ i ∈ Finset.range 32, xs i from prefixWindow_warp _ (by decide)]
    exact prefixWindow_le_warp xs 32 hLane
  have hSum : base+group*p.heads = limit := drainGroupCount_eq p hFirst.le
  have hFit := hp.prefixWork_signed (Nat.min_le_left p.batch (first+31))
  change limit < 2^31 at hFit
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hGuard : Seg kernel [] l g 2 1848 [(7190,b32 first),(7145,b32 p.batch)]
      1850 [(255,.pred false),(7192,b32 0)] := by
    intro s hs
    seg_fp hs using
      first
      | rfl
      | simp only [compare,Option.getD_some,truncBits_ofNat hBatch32 (by decide),
          truncBits_ofNat hFirst32 (by decide),RowDrainRole.signedWord hBatch,
          RowDrainRole.signedWord (hFirst.trans hBatch),ge_iff_le,Int.ofNat_le,
          decide_eq_false (Nat.not_le_of_lt hFirst)]
  have ht' : At t 1848 ([(7190,b32 first),(7145,b32 p.batch)]++frame) :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,ht.2.2.2.2⟩
  obtain ⟨s,hs,hsAt⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hGuard ht'
  obtain ⟨v,hRun,hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1850 false hsAt hsAt.2.2.2.2.1 (by simp)
  have hPath := (Loader.loaderLinear (regs := []) (by decide) (by decide) hsAt.1
    (by simp) (by decide) hRun).1
  have hInputs : At v 1851
      ([(7189,b32 group),(7137,b32 p.heads),(7191,b32 limit),(7188,b32 part),(1072,b32 cta)] ++
        drainIndexCarry p l g first use) := by
    have hFrame : Holds v.regs frame := hv.2.2.2.2.2.2
    have hTail : Holds v.regs (firstDrainTail p l g use) := hFrame.2.2.2.2.2.2.2
    exact hv.mono ⟨hFrame.2.2.1,hFrame.2.2.2.2.2.1,hFrame.2.1,hFrame.2.2.2.1,
      holds_lookup hTail rfl,hFrame.2.2.2.1,hFrame.2.2.2.2.1,hv.2.2.2.2.2.1,hTail⟩
  have hSegment := terminalBallotArgs l g hPartGroup hGroup hp.heads_signed hCta (hSum.symm ▸ hFit)
  rw [hSum] at hSegment
  obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSegment hInputs
  exact ⟨u,(run_rtg hs).trans ((run_rtg hPath).trans (run_rtg hu)),hU⟩

/-- Each selected terminal group reaches the actual full-mask ballot for its
assigned request, with the ballot predicate true on its exact lane prefix. -/
theorem drainSelectedBallotEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g use first shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first < p.batch) (hLow : tilePrefix p first*p.heads ≤ g/l.block)
    (hHigh : g/l.block < drainGroupLimit p first) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1848
      (fun lane => drainSelectedFrame p l (warpLane l g lane) first use) shuffles votes ends) :
    ∃ n < 31, Nonempty (SchedulerWarpReached l X g 1855
      (fun lane => (256,.pred (decide (lane < n)))::
        drainIndexCarry p l (warpLane l g lane) first use) shuffles votes ends) := by
  obtain ⟨batch,⟨hStart,hGroup,hBatch,hLo,hHi⟩,_⟩ := groupContains_request p hLow hHigh
  let n := batch-first
  have hn : n < 31 := by dsimp [n]; omega
  refine ⟨n,hn,?_⟩
  apply cur.advanceLocal
  intro lane hl
  have hb : l.block%32 = 0 := by rw [hp.block]
  have hWarp := Step.sameWarp_lane hb hg hl
  obtain ⟨u,hu,hU⟩ := selectedBallotLocal hp hWarp.1.1.2.1 hFirst (cur.checkpoint lane hl)
  have hLane : laneOf l (warpLane l g lane) = lane := hWarp.2
  have hCta : warpLane l g lane/l.block = g/l.block := hWarp.1.1.2.2.symm
  change At u 1855 ((256,.pred (decide (tilePrefix p first*p.heads +
      prefixWindow (groupLaneTiles p first) 32 (laneOf l (warpLane l g lane))*p.heads ≤
        warpLane l g lane/l.block)))::drainIndexCarry p l (warpLane l g lane) first use) at hU
  have hPart : (tilePrefix p first*p.heads +
      prefixWindow (groupLaneTiles p first) 32 lane*p.heads ≤ g/l.block) ↔ lane < n := by
    rw [← Nat.add_mul,prefixWindow_warp _ hl]
    exact (groupBallot_iff p hStart hGroup hBatch hl hLo hHi).trans (by dsimp [n]; omega)
  have hBool : decide _ = decide (lane < n) := Bool.eq_iff_iff.mpr (by
    simpa only [decide_eq_true_eq] using hPart)
  rw [hLane,hCta,hBool] at hU
  exact ⟨u,hu,hU⟩

private theorem terminalBallotOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g n lane : Nat} {t : TState} (ht : At t 1855 [(256,.pred (decide (lane < n)))]) :
    out kernel Assumptions.all l g t = .ev (.vote (2^32-1) (decide (lane < n))
      (fun word => next (setReg t 2284 (b32 word.toNat)))) := by
  rw [Loader.loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_1855) rfl rfl]
  change Out.ev (voteTmpl l g t 2284 256 false (.imm (-1))) = _
  have hb : l.block%32 = 0 := by rw [hp.block]
  simp [voteTmpl,readPred,readReg,ht.2.2.2.2.1,hb,b32,readBits,pure,Except.pure]
  rfl

private theorem terminalBallotCount (l : Launch) (g : Nat) {n : Nat} (hn : n < 31) :
    Seg kernel [] l g 2 1856 [(2284,b32 (2^n-1))] 1858
      [(257,.pred (decide (n = 0))),(1177,b32 n)] := by
  have hPow : 2^n < 2^32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hWord : 2^n-1 < 2^32 := by omega
  let word := BitVec.ofNat 32 (2^n-1)
  have hNat : word.toNat = 2^n-1 := by
    dsimp only [word]
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hWord]
  have hBits (i : Nat) (hi : i < 32) : word.getLsbD i = decide (i < n) := by
    dsimp only [word]
    rw [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one]
    simp [hi]
  have hPop := ballot_popc_prefix (by omega : n ≤ 32) hBits
  rw [hNat] at hPop
  have hZero : 2^n-1 = 0 ↔ n = 0 := by
    constructor
    · intro h
      by_contra hn
      have hh : 2^0 < 2^n := Nat.pow_lt_pow_right (by decide) (by omega)
      change 1 < 2^n at hh
      omega
    · rintro rfl
      decide
  intro t ht
  seg_fp ht using
    (simp only [Value.pred.injEq,compare,b32,Option.getD_some,
       truncBits_ofNat hWord (by decide),toNat_ofNat_lt (show 2^n-1 < 2^64 by omega),
       show (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 from rfl,hPop,
       decide_eq_decide]
     all_goals omega)

private theorem terminalIndexOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g sel value : Nat} (hSel : sel < 32) (previous : Bool) {t : TState}
    (ht : At t (if previous then 1860 else 1861)
      [((if previous then 2285 else 1177),b32 sel),
        ((if previous then 7188 else 7187),b32 value)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 value) sel 31
      (fun v _ => next (setReg t (if previous then 2286 else 2287) v))) := by
  have hSel32 : sel < 2^32 := by omega
  have hSel64 : sel < 2^64 := by omega
  have hCore := Loader.loaderOutCore (l := l) (g := g) (t := t)
    (by rw [ht.1]; cases previous <;> decide) (by rw [ht.1]; cases previous <;> decide)
  have hb : l.block%32 = 0 := by rw [hp.block]
  have hMask : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hBound : readBits l g t 32 (.imm 31) = .ok (BitVec.ofNat 64 31) := rfl
  rw [hCore]
  cases previous
  · have hPc : t.pc = 1861 := ht.1
    rw [out_event ht.2.2.2.1 (hPc.symm ▸ Flow.code_1861) rfl rfl]
    change Out.ev (shflTmpl l g t .idx 2287 none (.reg 7187)
      (.reg 1177) (.imm 31) (.imm (-1))) = _
    have hReg : t.regs 7187 = some (b32 value) := ht.2.2.2.2.2.1
    have hIdx : t.regs 1177 = some (b32 sel) := ht.2.2.2.2.1
    have hBits : readBits l g t 32 (.reg 1177) = .ok (BitVec.ofNat 64 sel) :=
      readBits_b32 hIdx hSel32
    simp only [shflTmpl,hReg,hb,hMask,hBound,hBits,readValue,readReg,
      toNat_ofNat_lt hSel64,pure,Except.pure]
    rfl
  · have hPc : t.pc = 1860 := ht.1
    rw [out_event ht.2.2.2.1 (hPc.symm ▸ Flow.code_1860) rfl rfl]
    change Out.ev (shflTmpl l g t .idx 2286 none (.reg 7188)
      (.reg 2285) (.imm 31) (.imm (-1))) = _
    have hReg : t.regs 7188 = some (b32 value) := ht.2.2.2.2.2.1
    have hIdx : t.regs 2285 = some (b32 sel) := ht.2.2.2.2.1
    have hBits : readBits l g t 32 (.reg 2285) = .ok (BitVec.ofNat 64 sel) :=
      readBits_b32 hIdx hSel32
    simp only [shflTmpl,hReg,hb,hMask,hBound,hBits,readValue,readReg,
      toNat_ofNat_lt hSel64,pure,Except.pure]
    rfl

private theorem prepareDrainIndex {p : Params} {l : Launch}
    {g use first n : Nat} (hn : n < 31) {t : TState}
    (ht : At t 1856 ((2284,b32 (2^n-1))::drainIndexCarry p l g first use)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      if n = 0 then At u 1861 ((1177,b32 n)::drainIndexCarry p l g first use)
      else At u 1860 ((2285,b32 (n-1))::(1177,b32 n)::drainIndexCarry p l g first use) := by
  let frame := drainIndexCarry p l g first use
  have ht' : At t 1856 ([(2284,b32 (2^n-1))]++frame) := ht
  obtain ⟨s,hs,hS⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) (terminalBallotCount l g hn) ht'
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1858 (decide (n = 0)) hS hS.2.2.2.2.1 (by simp)
  have hvAll := (Loader.loaderLinear (regs := []) (by decide) (by decide) hS.1
    (by simp) (by decide) hv).1
  have hPath := (run_rtg hs).trans (run_rtg hvAll)
  by_cases hz : n=0
  · have hPc : v.pc = 1861 := by simpa [hz] using hV.1
    exact ⟨v,hPath,by rw [ite_eq_left hz]; exact
      ⟨hPc,hV.2.1,hV.2.2.1,hV.2.2.2.1,hV.2.2.2.2.2⟩⟩
  · have hPc : v.pc = 1859 := by simpa [hz] using hV.1
    have hAt : At v 1859 ([(1177,b32 n)]++(1177,b32 n)::frame) :=
      ⟨hPc,hV.2.1,hV.2.2.1,hV.2.2.2.1,hV.2.2.2.2.2.1,hV.2.2.2.2.2⟩
    have hSeg : Seg kernel [] l g 1 1859 [(1177,b32 n)] 1860 [(2285,b32 (n-1))] := by
      intro w hw
      seg_fp hw using norm_bits
    obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hSeg hAt
    exact ⟨u,hPath.trans (run_rtg hu),by rw [ite_eq_right hz]; exact hU⟩

private theorem indexCarryFresh (reg : Fin 3) {p : Params} {l : Launch} {g use first : Nat}
    {r : Nat × Value} (hr : r ∈ drainIndexCarry p l g first use) :
    r.1 ≠ [2284,2286,2287][reg.val] := by
  intro he
  have hm := List.mem_map_of_mem (f := Prod.fst) hr
  rw [he] at hm
  fin_cases reg <;>
    exact (of_decide_eq_true rfl : _ ∉ (drainIndexCarry p l g first use).map Prod.fst) hm

/-- The selected request's ballot and its two index paths reach the generation drain
with the exact query parity retained. -/
theorem drainSelectedIndicesOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use first n shuffles votes : Nat} (hg : g < l.threads) (hn : n < 31)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 1855
      (fun lane => (256,.pred (decide (lane < n))) ::
        drainIndexCarry p l (warpLane l g lane) first use) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1862 (fun lane =>
      (7192,b32 0)::firstDrainTail p l (warpLane l g lane) use)
      (shuffles+(if n=0 then 1 else 2)) (votes+1) ends) := by
  let thread := warpLane l g
  let carry := fun lane => drainIndexCarry p l (thread lane) first use
  let selected := fun lane => (1177,b32 n)::carry lane
  let prefixCount := fun lane => prefixWindow (groupLaneTiles p first) 32 (laneOf l (thread lane))
  let tiles := fun lane => groupLaneTiles p first (laneOf l (thread lane))
  obtain ⟨count⟩ := cur.consumePrefixBallot (dst := 2284) hp hMax hg (by omega : n ≤ 32) (by
    intro lane _ pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (by decide : (256 : Nat) ≠ 2284)
    · exact indexCarryFresh 0 hm)
    (fun lane hl => terminalBallotOut hp
      ((cur.checkpoint lane hl).mono ⟨(cur.checkpoint lane hl).2.2.2.2.1,trivial⟩))
  have consumeSelected {sh : Nat}
      (c : SchedulerWarpReached l X g 1861 selected sh (votes+1) ends) :
      Nonempty (SchedulerWarpReached l X g 1862
        (fun lane => (7192,b32 0)::firstDrainTail p l (thread lane) use)
        (sh+1) (votes+1) ends) := by
    obtain ⟨after⟩ := c.consumeShuffle (dst := 2287) hp hMax hg .idx
      (fun lane => b32 (tiles lane)) (fun _ => n) (fun _ => 31)
      (by
        intro lane _ pair hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact (by decide : (1177 : Nat) ≠ 2287)
        · exact indexCarryFresh 2 hm)
      (fun lane hl => terminalIndexOut hp (by omega) false
        ((c.checkpoint lane hl).mono
          ⟨(c.checkpoint lane hl).2.2.2.2.1,(c.checkpoint lane hl).2.2.2.2.2.2.1,trivial⟩))
    exact after.advanceLocal (fun lane hl => by
      have ht := after.checkpoint lane hl
      exact ⟨_,.refl,ht.mono ht.2.2.2.2.2.2.2.2⟩)
  have prep (lane : Nat) (hl : lane < 32) :=
    prepareDrainIndex (g := thread lane) hn ((count.checkpoint lane hl).mono
      ⟨(count.checkpoint lane hl).2.2.2.2.1,(count.checkpoint lane hl).2.2.2.2.2.2⟩)
  by_cases hz : n=0
  · obtain ⟨start⟩ := count.advanceLocal (pc' := 1861) (G := selected) (by
      intro lane hl
      obtain ⟨u,hu,hU⟩ := prep lane hl
      rw [ite_eq_left hz] at hU
      exact ⟨u,hu,hU⟩)
    simpa only [hz,ite_true] using consumeSelected start
  · let previous := fun lane => (2285,b32 (n-1))::selected lane
    obtain ⟨start⟩ := count.advanceLocal (pc' := 1860) (G := previous) (by
      intro lane hl
      obtain ⟨u,hu,hU⟩ := prep lane hl
      rw [ite_eq_right hz] at hU
      exact ⟨u,hu,hU⟩)
    obtain ⟨after⟩ := start.consumeShuffle (dst := 2286) hp hMax hg .idx
      (fun lane => b32 (prefixCount lane)) (fun _ => n-1) (fun _ => 31)
      (by
        intro lane _ pair hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact (by decide : (2285 : Nat) ≠ 2286)
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact (by decide : (1177 : Nat) ≠ 2286)
          · exact indexCarryFresh 1 hm)
      (fun lane hl => terminalIndexOut hp (by omega) true
        ((start.checkpoint lane hl).mono
          ⟨(start.checkpoint lane hl).2.2.2.2.1,
            (start.checkpoint lane hl).2.2.2.2.2.2.1,trivial⟩))
    obtain ⟨middle⟩ := after.advanceLocal (pc' := 1861) (G := selected) (by
      intro lane hl
      have ht := after.checkpoint lane hl
      exact ⟨_,.refl,ht.mono ht.2.2.2.2.2.2⟩)
    simpa only [hz,ite_false] using consumeSelected middle

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
