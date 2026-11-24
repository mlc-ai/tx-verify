-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainUpScan
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import Kernels.TmlFa4Fwd.Flow.Code.Part027

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

def drainGroupCount (p : Params) (first : Nat) : Nat :=
  prefixWindow (groupLaneTiles p first) 32 31

def drainGroupLimit (p : Params) (first : Nat) : Nat :=
  tilePrefix p (min p.batch (first+31))*p.heads

theorem drainGroupCount_eq (p : Params) {first : Nat} (hFirst : first ≤ p.batch) :
    tilePrefix p first*p.heads + drainGroupCount p first*p.heads = drainGroupLimit p first := by
  have hs := congrArg (·*p.heads) (groupTiles_eq p hFirst (by decide : 32 ≤ 32))
  rw [drainGroupCount,prefixWindow_warp _ (by decide : 31 < 32)]
  simpa only [drainGroupLimit,Nat.add_mul,show min 31 32 = 31 by decide] using hs

def drainSelectionCarry (p : Params) (l : Launch) (g first use : Nat) : List (Nat × Value) :=
  [(7188,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g))),
    (7187,b32 (groupLaneTiles p first (laneOf l g))),(7137,b32 p.heads)] ++
      firstGroupCarry p l g use

def drainSelectedFrame (p : Params) (l : Launch) (g first use : Nat) : List (Nat × Value) :=
  [(7190,b32 first),(7191,b32 (drainGroupLimit p first)),(7189,b32 (drainGroupCount p first))] ++
    drainSelectionCarry p l g first use

/-- The returned first group prefix is broadcast from the actual lane 31. -/
theorem CacheDrainNeighbors.firstGroupTotalOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use : Nat} (hg : g < l.threads) (c : CacheDrainNeighbors p l X g use) :
    Nonempty (SchedulerWarpReached l X g 1787
      (fun lane => (7189,b32 (drainGroupCount p 0))::
        drainSelectionCarry p l (warpLane l g lane) 0 use) (c.shuffles+6) c.votes c.ends) := by
  obtain ⟨cur⟩ := c.firstGroupOfMaximal hp hg
  let tail (lane : Nat) := let t := warpLane l g lane
    [(7187,b32 (groupLaneTiles p 0 (laneOf l t))),(7137,b32 p.heads)] ++ firstGroupCarry p l t use
  obtain ⟨ready⟩ := cur.advanceLocal (pc' := kvDrainScanPc false 0)
    (G := fun lane => cacheDrainScanFrame p l (warpLane l g lane) 0 false 0 (tail lane)) (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hReg := (holds_append ..).mp ht.2.2.2.2.2
      refine ⟨_,.refl,ht.mono ⟨?_,(holds_append ..).mpr ⟨hReg.1,ht.2.2.2.2.1,hReg.2⟩⟩⟩
      simpa only [kvDrainScanSrc,Fin.val_zero,ite_true,Nat.pow_zero,prefixWindow_one]
        using ht.2.2.2.2.1)
  have hSafe : ∀ lane < 32, ∀ x ∈ tail lane, ∀ stage,
      x.1 ∉ [kvDrainScanDst false stage,kvDrainScanDst false stage+1,
        kvDrainScanSrc false stage.succ] := by
    intro lane _ item hm stage hBad
    have hm' := List.mem_map_of_mem (f := Prod.fst) hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hBad
    rcases hBad with hBad | hBad | hBad <;> rw [hBad] at hm'
    all_goals
      fin_cases stage <;> exact (of_decide_eq_true rfl : _ ∉ (tail lane).map Prod.fst) hm'
  obtain ⟨scanned⟩ := cacheDrainUpScanOfMaximal hp hMax hg (Nat.zero_le p.batch) false hSafe ready
  let input (lane : Nat) :=
    b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l (warpLane l g lane)))
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨total⟩ := scanned.consumeShuffle (dst := 7189) hp hMax hg .idx input (fun _ => 31)
    (fun _ => 31) (by
      intro lane _ pair hm hEq
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [hEq] at hMem
      exact (of_decide_eq_true rfl : 7189 ∉ (7188::(tail lane).map Prod.fst)) hMem) (by
      intro lane hl
      have ht := scanned.checkpoint lane hl
      let t := scanned.state lane
      have hIn : t.regs 7188 = some (input lane) := ht.2.2.2.2.1
      have hPc : t.pc = 1786 := ht.1
      rw [Loader.loaderOutCore (by rw [hPc]; decide) (by rw [hPc]; decide),
        out_event ht.2.2.2.1 (hPc.symm ▸ Flow.code_1786) rfl rfl]
      change Out.ev (shflTmpl l (warpLane l g lane) t .idx 7189 none
        (.reg 7188) (.imm 31) (.imm 31) (.imm (-1))) = _
      simp [shflTmpl,readValue,readReg,hIn,hBlock,input,b32,Value.bytes,readBits,
        pure,Except.pure,t]
      rfl)
  apply total.advanceLocal (pc' := 1787)
  intro lane hl
  have h31 : laneOf l (warpLane l g 31) = 31 :=
    (Step.sameWarp_lane hBlock hg (by decide : 31 < 32)).2
  have hSource : (shflSource .idx lane 31 31).1 = 31 :=
    congrArg Prod.fst (shflSource_idx lane (by decide : 31 < 32))
  have ht := total.checkpoint lane hl
  change At _ 1787 _ at ht
  exact ⟨_,.refl,by simpa only [input,hSource,h31,drainGroupCount,drainSelectionCarry,tail,
    List.cons_append,List.nil_append] using ht⟩

private theorem firstGroupGateCore {l : Launch} {g count heads cta cutoff : Nat}
    (hCount : count < 2^31) (hHeads : heads < 2^31) (hCta : cta < 2^31)
    (hCutoff : cutoff < 2^31) (hProd : count*heads = cutoff) (hLt : cta < cutoff) :
    Seg kernel [] l g 3 1787 [(7189,b32 count),(7137,b32 heads),(1072,b32 cta)]
      1790 [(240,.pred true),(7190,b32 0),(7191,b32 cutoff)] := by
  have hSize1 : count < 2^32 := hCount.trans (by decide)
  have hSize2 : cutoff < 2^32 := hCutoff.trans (by decide)
  have hSize3 : heads < 2^32 := hHeads.trans (by decide)
  have hSize4 : cta < 2^32 := hCta.trans (by decide)
  intro s hs
  seg_fp hs using
    first
    | rfl
    | simp only [b32,← BitVec.ofNat_mul,hProd,compare,Option.getD_some,
        truncBits_ofNat hSize1 (by decide),truncBits_ofNat hSize2 (by decide),
        truncBits_ofNat hSize3 (by decide),truncBits_ofNat hSize4 (by decide),
        RowDrainRole.signedWord hCta,RowDrainRole.signedWord hCutoff,gt_iff_lt,Int.ofNat_lt,
        decide_eq_true hLt]

/-- In the first group the actual branch recognizes every scheduled CTA whose
request is in that group's interval. -/
theorem firstDrainGroupSelected {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g use shuffles votes : Nat} (hg : g < l.threads)
    (hSelected : g/l.block < drainGroupLimit p 0) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1787
      (fun lane => (7189,b32 (drainGroupCount p 0)) ::
        drainSelectionCarry p l (warpLane l g lane) 0 use) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1848
      (fun lane => drainSelectedFrame p l (warpLane l g lane) 0 use) shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  let t := warpLane l g lane
  let frame := (7189,b32 (drainGroupCount p 0))::drainSelectionCarry p l t 0 use
  have ht : At (cur.state lane) 1787 frame := cur.checkpoint lane hl
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hOwner : t/l.block = g/l.block := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  have hCta : t/l.block < 2^31 := by
    rw [hOwner]
    exact (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hBound := hp.prefixWork_signed (Nat.min_le_left p.batch (0+31))
  change drainGroupLimit p 0 < 2^31 at hBound
  have hGroup := hp.groupWindow_signed (Nat.zero_le p.batch) (by decide : 31 < 32) 32
  change drainGroupCount p 0 < 2^31 at hGroup
  have hProd : drainGroupCount p 0*p.heads = drainGroupLimit p 0 := by
    simpa [tilePrefix] using drainGroupCount_eq p (first := 0) (Nat.zero_le p.batch)
  have hLt : t/l.block < drainGroupLimit p 0 := by
    rw [hOwner]
    exact hSelected
  have hSeg := firstGroupGateCore (l := l) (g := t) hGroup hp.heads_signed hCta
    hBound hProd hLt

  have ht' : At (cur.state lane) 1787
      ([(7189,b32 (drainGroupCount p 0)),(7137,b32 p.heads),(1072,b32 (t/l.block))]++frame) :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
      holds_lookup ht.2.2.2.2 rfl,ht.2.2.2.2⟩
  obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSeg ht'
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t)
    Flow.code_1790 true hU hU.2.2.2.2.1 (by simp)
  have hvAll := (Loader.loaderLinear (regs := []) (by decide) (by decide) hU.1
    (by simp) (by decide) hv).1
  exact ⟨v,(run_rtg hu).trans (run_rtg hvAll),hV.mono hV.2.2.2.2.2⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
