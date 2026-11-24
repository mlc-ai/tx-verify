-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainLoopEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part120

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- Terminal statistics operands retained across all three request-selection collectives. -/
def terminalRetained (l : Launch) (warp : Fin 8) (parity : Nat) : List (Nat × Value) :=
  (7258,b32 parity)::idleCarry l warp

/-- The ballot's live prefix and request word and the terminal statistics operands. -/
def terminalIndexCarry (l : Launch) (warp : Fin 8) (parity prefixCount tiles : Nat) :
    List (Nat × Value) :=
  [(7263,b32 prefixCount),(7262,b32 tiles)] ++ terminalRetained l warp parity

private theorem terminalBallotArgs (l : Launch) (g : Nat)
    {base count part heads cta : Nat} (hPrefix : part ≤ count) (hCount : count < 2^31)
    (hHead : heads < 2^31) (hCta : cta < 2^31) (hEnd : base+count*heads < 2^31) :
    Seg kernel [] l g 4 7722
      [(7264,b32 count),(7141,b32 heads),(7266,b32 (base+count*heads)),
        (7263,b32 part),(1606,b32 cta)] 7726
      [(678,.pred (decide (base+part*heads ≤ cta)))] := by
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
    {g first parity : Nat} (warp : Fin 8) {t : TState} (hg : g < l.threads)
    (hFirst : first < p.batch)
    (ht : At t 7720 ((7262,b32 (groupLaneTiles p first (laneOf l g)))::
      (terminalSelectedGroup p l g first ++ terminalRetained l warp parity))) :
    let part := prefixWindow (groupLaneTiles p first) 32 (laneOf l g)
    let base := tilePrefix p first*p.heads
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 7726 ((678,.pred (decide (base+part*p.heads ≤ g/l.block)))::
        terminalIndexCarry l warp parity part (groupLaneTiles p first (laneOf l g))) := by
  let xs := groupLaneTiles p first
  let lane := laneOf l g
  let base := tilePrefix p first*p.heads
  let cta := g/l.block
  let part := prefixWindow xs 32 lane
  let group := prefixWindow xs 32 31
  let limit := tilePrefix p (min p.batch (first+31))*p.heads
  let frame := (7262,b32 (xs lane))::(terminalSelectedGroup p l g first ++
    terminalRetained l warp parity)
  have hBatch : p.batch < 2^31 := hp.shape.2.1
  have hFirst32 : first < 2^32 := by omega
  have hBatch32 : p.batch < 2^32 := by omega
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hGroup := hp.groupWindow_signed hFirst.le (show 31 < 32 by decide) 32
  change group < 2^31 at hGroup
  have hPartGroup : part ≤ group := by
    rw [show group = ∑ i ∈ Finset.range 32, xs i from prefixWindow_warp _ (by decide)]
    exact prefixWindow_le_warp xs 32 hLane
  have hSum : base+group*p.heads = limit := by
    have h := congrArg (·*p.heads) (groupTiles_eq p hFirst.le (by decide : 32 ≤ 32))
    have hCount : group = ∑ i ∈ Finset.range 32, xs i := prefixWindow_warp _ (by decide)
    rw [hCount]
    simpa only [show min 31 32 = 31 by decide,Nat.add_mul,base,limit,xs] using h
  have hFit := hp.prefixWork_signed (Nat.min_le_left p.batch (first+31))
  change limit < 2^31 at hFit
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have ht : At t 7720 frame := ht
  have hGuard : Seg kernel [] l g 1 7720 [(7265,b32 first),(7151,b32 p.batch)]
      7721 [(677,.pred false)] := by
    intro s hs
    seg_fp hs using
      simp only [compare,Option.getD_some,truncBits_ofNat hBatch32 (by decide),
        truncBits_ofNat hFirst32 (by decide),RowDrainRole.signedWord hBatch,
        RowDrainRole.signedWord (hFirst.trans hBatch),ge_iff_le,Int.ofNat_le,
        decide_eq_false (Nat.not_le_of_lt hFirst)]
  obtain ⟨s,hs,hsAt⟩ := hGuard.apply
    (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  obtain ⟨v,hRun,hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7721 false hsAt hsAt.2.2.2.2.1 (by simp)
  obtain ⟨hPath,hKeep⟩ := drainLocalKeep ht (by decide) (by decide)
    (by
      dsimp only [frame,terminalSelectedGroup,terminalSearchCommon,RowDrainRole.roots,
        RowDrainRole.frame,RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
        terminalRetained,idleCarry,List.cons_append,List.nil_append,List.map]
      decide +kernel) (by decide +kernel) (run_comp hs hRun)
  have hInputs : At v 7722
      [(7264,b32 group),(7141,b32 p.heads),(7266,b32 limit),(7263,b32 part),(1606,b32 cta)] :=
    hv.mono ⟨holds_lookup hKeep rfl,holds_lookup hKeep rfl,holds_lookup hKeep rfl,
      holds_lookup hKeep rfl,holds_lookup hKeep rfl,trivial⟩
  have hSegment := terminalBallotArgs l g hPartGroup hGroup hp.heads_signed hCta (hSum.symm ▸ hFit)
  rw [hSum] at hSegment
  obtain ⟨u,hu,hU⟩ := hSegment.apply hInputs
  have hSave : At v 7722 (terminalIndexCarry l warp parity part (xs lane)) :=
    hv.mono ⟨holds_lookup hKeep rfl,holds_lookup hKeep rfl,holds_lookup hKeep rfl,
      holds_lookup hKeep rfl,holds_lookup hKeep rfl,trivial⟩
  obtain ⟨hLocal,hRegs⟩ := drainLocalKeep hSave (by decide) (by decide)
    (by simp only [terminalIndexCarry,terminalRetained,idleCarry,List.cons_append,List.nil_append,
      List.map]; decide +kernel) (by decide +kernel) hu
  exact ⟨u,hPath.trans hLocal,hU.mono ⟨hU.2.2.2.2.1,hRegs⟩⟩

/-- After a group is selected, each lane advances to the full-warp request ballot. -/
theorem terminalSelectedGroupBallotEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first < p.batch) (hLow : tilePrefix p first*p.heads ≤ g/l.block)
    (hHigh : g/l.block < tilePrefix p (min p.batch (first+31))*p.heads)
    (warp : Fin 8) (parity : Nat → Nat) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7720
      (fun lane => let t := warpLane l g lane
        (7262,b32 (groupLaneTiles p first (laneOf l t)))::
          (terminalSelectedGroup p l t first ++ terminalRetained l warp (parity lane)))
      shuffles votes ends) :
    ∃ n < 31, Nonempty (SchedulerWarpReached l X g 7726
      (fun lane => (678,.pred (decide (lane < n)))::
        terminalIndexCarry l warp (parity lane)
          (prefixWindow (groupLaneTiles p first) 32 lane) (groupLaneTiles p first lane))
      shuffles votes ends) := by
  obtain ⟨batch,⟨hStart,hGroup,hBatch,hLo,hHi⟩,_⟩ := groupContains_request p hLow hHigh
  let n := batch-first
  have hn : n < 31 := by dsimp [n]; omega
  refine ⟨n,hn,?_⟩
  apply cur.advanceLocal
  intro lane hl
  have hb : l.block%32 = 0 := by rw [hp.block]
  have hWarp := Step.sameWarp_lane hb hg hl
  obtain ⟨u,hu,hU⟩ := selectedBallotLocal (g := warpLane l g lane) hp warp
    hWarp.1.1.2.1 hFirst (cur.checkpoint lane hl)
  have hLane : laneOf l (warpLane l g lane) = lane := hWarp.2
  have hCta : warpLane l g lane/l.block = g/l.block := hWarp.1.1.2.2.symm
  rw [hLane,hCta] at hU
  have hPart : (tilePrefix p first*p.heads +
      prefixWindow (groupLaneTiles p first) 32 lane*p.heads ≤ g/l.block) ↔ lane < n := by
    rw [← Nat.add_mul,prefixWindow_warp _ hl]
    exact (groupBallot_iff p hStart hGroup hBatch hl hLo hHi).trans (by dsimp [n]; omega)
  have hBool : decide _ = decide (lane < n) := Bool.eq_iff_iff.mpr (by
    simpa only [decide_eq_true_eq] using hPart)
  rw [hBool] at hU
  exact ⟨u,hu,hU⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
