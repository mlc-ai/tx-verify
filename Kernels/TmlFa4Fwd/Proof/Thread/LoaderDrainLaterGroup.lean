-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainLaterWords
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import Kernels.TmlFa4Fwd.Flow.Code.Part028

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Loader (loaderLinear)

def laterScanCarry (p : Params) (l : Launch) (g first use : Nat) : List (Nat × Value) :=
  (7190,b32 first)::laterDrainCarry p l g first use

private theorem laterDrainLaneCount {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use first : Nat} (hf : first ≤ p.batch) {t : TState}
    (ht : At t 1808 ([(2260,b32 (drainCuQ p (first+(shflSource .down (laneOf l g) 1 31).1))),
      (243,.pred (decide (laneOf l g = 31)))] ++ laterDrainWords p l g first use)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 1823
        ((7187,b32 (groupLaneTiles p first (laneOf l g)))::laterScanCarry p l g first use) := by
  let q := laneOf l g
  let lo := drainCuQ p (first+q)
  let hi := drainCuQ p (first+(shflSource .down q 1 31).1)
  let n := first+q
  let off := q = 31 ∨ p.batch ≤ n
  let E := laterScanCarry p l g first use
  let diff := truncBits 32 (BitVec.ofNat 64 hi - BitVec.ofNat 64 lo)
  obtain ⟨ha,hb,hMono,hLength,hTiles⟩ := drainWordTiles hp first q
  have hBound := hp.shape.2.2
  have hQ : q < 32 := Nat.mod_lt _ (by decide)
  have hIndex : n < 2^31 := by dsimp [n]; omega
  have hBatch : p.batch < 2^31 := by omega
  have hCalc : Seg kernel [] l g 4 1808
      [(2260,b32 hi),(7186,b32 lo),(1175,b32 n),(7145,b32 p.batch),(243,.pred (decide (q = 31)))]
      1812 [(245,.pred (decide off)),(1176,.bits 32 diff),(7187,b32 0)] := by
    intro s hs
    dsimp only [off,diff] at *
    have hI32 : n < 2^32 := hIndex.trans (by decide)
    have hB32 : p.batch < 2^32 := hBatch.trans (by decide)
    seg_fp hs using
      (simp [compare,truncBits_ofNat ha (by decide),truncBits_ofNat hb (by decide),
        truncBits_ofNat hI32 (by decide),truncBits_ofNat hB32 (by decide),
        RowDrainRole.signedWord hIndex,RowDrainRole.signedWord hBatch,ge_iff_le,lo,hi]; try rfl)
  have ht' : At t 1808
      ([(2260,b32 hi),(7186,b32 lo),(1175,b32 n),(7145,b32 p.batch),(243,.pred (decide (q=31)))]++
        E) := by
    apply ht.mono
    have h := ht.2.2.2.2
    exact ⟨h.1,h.2.2.1,h.2.2.2.1,
      holds_mem h (by simp [laterDrainWords,laterDrainCarry,firstGroupCarry]),
      h.2.1,h.2.2.2.2⟩
  obtain ⟨v,hv,hV⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hCalc ht'
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1812 _ hV hV.2.2.2.2.1 (by simp)
  have hwAll := (loaderLinear (regs := []) (by decide) (by decide) hV.1
    (by simp) (by decide) hw).1
  have hSteps := (run_rtg hv).trans (run_rtg hwAll)
  by_cases hOff : off
  · have hPc : w.pc = 1823 := by simpa only [decide_eq_true hOff,ite_true] using hW.1
    have hInactive : ¬ (first+q < p.batch ∧ q < 31) := by dsimp [off,n] at hOff; omega
    have hCount : 0 = groupLaneTiles p first q := by simpa [hInactive] using hTiles
    exact ⟨w,hSteps,⟨hPc,hW.2.1,hW.2.2.1,hW.2.2.2.1,by
      rw [← hCount]
      exact hW.2.2.2.2.2.2⟩⟩
  · have hPc : w.pc = 1813 := by
      simpa only [decide_eq_false hOff,Bool.false_eq_true,ite_false,Nat.reduceAdd] using hW.1
    have hActive : first+q < p.batch ∧ q < 31 := by dsimp [off,n] at hOff; omega
    have hDiff : diff = BitVec.ofNat 64 (hi-lo) := by
      dsimp only [diff]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show lo < 2^64 by omega) (hMono
        (decide_eq_true hActive)),
        truncBits_ofNat (show hi-lo < 2^32 by omega) (by decide)]
    have hAt : At w 1813 ((1176,b32 (hi-lo))::E) :=
      ⟨hPc,hW.2.1,hW.2.2.1,hW.2.2.2.1,by
        have h := hW.2.2.2.2.2.1
        rw [hDiff] at h
        exact ⟨h,hW.2.2.2.2.2.2.2⟩⟩
    obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (cacheDrainRoundUpTiles true l g hLength) hAt
    have hCount : (hi-lo+255)/256 = groupLaneTiles p first q := by simpa [hActive] using hTiles
    exact ⟨u,hSteps.trans (run_rtg hu),by rw [← hCount]; exact hU⟩


private theorem laterDrainLaneGuards {p : Params} {l : Launch} {g use first : Nat} {t : TState}
    (ht : At t 1823
      ((7187,b32 (groupLaneTiles p first (laneOf l g)))::laterScanCarry p l g first use)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 1828 (cacheDrainScanFrame p l g first true 0
        ((7187,b32 (groupLaneTiles p first (laneOf l g)))::laterScanCarry p l g first use)) := by
  let q := laneOf l g
  let E := (7187,b32 (groupLaneTiles p first q))::laterScanCarry p l g first use
  have h32 : q < 2^32 := (Nat.mod_lt _ (by decide : 0 < 32)).trans (by decide)
  have h64 : q < 2^64 := h32.trans (by decide)
  have hGuard : Seg kernel [] l g 5 1823 [(1073,b32 q)] 1828 (cacheDrainGuardFrame true q) := by
    intro s hs
    change ∃ w, run kernel [] l g 5 s = some w ∧ At w 1828
      [(253,.pred (decide (q = 0))),(252,.pred (decide (1 < q))),
       (251,.pred (decide (3 < q))),(250,.pred (decide (7 < q))),
       (249,.pred (decide (15 < q)))]
    seg_fp hs using simp [compare,truncBits_ofNat h32 (by decide),toNat_ofNat_lt h64,
      show (truncBits 32 15#64).toNat = 15 by decide,
      show (truncBits 32 7#64).toNat = 7 by decide,
      show (truncBits 32 3#64).toNat = 3 by decide,
      show (truncBits 32 1#64).toNat = 1 by decide,
      show (truncBits 32 0#64).toNat = 0 by decide]
  have ht' : At t 1823 ([(1073,b32 q)]++E) := ht.mono
    ⟨holds_mem ht.2.2.2.2 (by
      simp [q,laterScanCarry,laterDrainCarry,firstGroupCarry,firstDrainTail,
        drainSchedulerFrame]),
      ht.2.2.2.2⟩
  obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hGuard ht'
  obtain ⟨hPred,hRest⟩ := (holds_append ..).mp hU.2.2.2.2
  refine ⟨u,run_rtg hu,hU.mono ?_⟩
  change Holds u.regs ((kvDrainScanSrc true 0,
    b32 (prefixWindow (groupLaneTiles p first) (2^(0 : Fin 6).val) q)) ::
      cacheDrainGuardFrame true q ++ E)
  rw [show kvDrainScanSrc true 0 = 7187 by rfl,Fin.val_zero,Nat.pow_zero,prefixWindow_one]
  exact ⟨hRest.1,(holds_append ..).mpr ⟨hPred,hRest⟩⟩

def laterDrainTotalFrame (p : Params) (l : Launch) (g first use : Nat) : List (Nat × Value) :=
  [(7189,b32 (drainGroupCount p first)),
    (7188,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g))),
    (7187,b32 (groupLaneTiles p first (laneOf l g)))] ++ laterScanCarry p l g first use

/-- Each later group consumes its real six scan shuffles and the final broadcast. -/
theorem laterDrainGroupTotalOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use first shuffles votes : Nat} (hg : g < l.threads) (hf : first+31 < p.batch)
    (hCuQ : DrainCuQProtected p X)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 1794
      (fun lane => laterDrainStart p l (warpLane l g lane) first use) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1844
      (fun lane => laterDrainTotalFrame p l (warpLane l g lane) (first+31) use)
        (shuffles+7) votes ends) := by
  obtain ⟨neigh⟩ := laterDrainNeighborsOfMaximal hp hMax hg hf hCuQ cur
  let n := first+31
  let thread := warpLane l g
  let F (lane : Nat) :=
    (7187,b32 (groupLaneTiles p n (laneOf l (thread lane))))::laterScanCarry p l (thread lane) n use
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨ready⟩ := neigh.advanceLocal (pc' := kvDrainScanPc true 0)
    (G := fun lane => cacheDrainScanFrame p l (thread lane) n true 0 (F lane)) (by
      intro lane hl
      have hLane : laneOf l (thread lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      have hSrc := Step.shflSource_lt .down hl 1 31
      have hWord : laneOf l (warpLane l g (shflSource .down lane 1 31).1) =
          (shflSource .down lane 1 31).1 := (Step.sameWarp_lane hBlock hg hSrc).2
      have ht := neigh.checkpoint lane hl
      have hAt : At (neigh.state lane) 1808
          ([(2260,b32 (drainCuQ p (n+(shflSource .down (laneOf l (thread lane)) 1 31).1))),
            (243,.pred (decide (laneOf l (thread lane) = 31)))] ++
              laterDrainWords p l (thread lane) n use) := by
        simpa only [n,thread,hLane,hWord,List.cons_append,List.nil_append] using ht
      obtain ⟨u,hu,hU⟩ := laterDrainLaneCount hp hf.le hAt
      obtain ⟨v,hv,hV⟩ := laterDrainLaneGuards hU
      exact ⟨v,hu.trans hv,hV⟩)
  have hSafe : ∀ lane < 32, ∀ x ∈ F lane, ∀ stage,
      x.1 ∉ [kvDrainScanDst true stage,kvDrainScanDst true stage+1,
        kvDrainScanSrc true stage.succ] := by
    intro lane _ item hm stage hBad
    have hm' := List.mem_map_of_mem (f := Prod.fst) hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hBad
    rcases hBad with hBad | hBad | hBad <;> rw [hBad] at hm'
    all_goals
      fin_cases stage <;> exact (of_decide_eq_true rfl : _ ∉ (F lane).map Prod.fst) hm'
  obtain ⟨scanned⟩ := cacheDrainUpScanOfMaximal hp hMax hg hf.le true hSafe ready
  let input (lane : Nat) := b32 (prefixWindow (groupLaneTiles p n) 32 (laneOf l (thread lane)))
  obtain ⟨total⟩ := scanned.consumeShuffle (dst := 7189) hp hMax hg .idx input (fun _ => 31)
    (fun _ => 31) (by
      intro lane _ pair hm hEq
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [hEq] at hMem
      exact (of_decide_eq_true rfl : 7189 ∉ (7188::(F lane).map Prod.fst)) hMem) (by
      intro lane hl
      have ht := scanned.checkpoint lane hl
      let t := scanned.state lane
      have hIn : t.regs 7188 = some (input lane) := ht.2.2.2.2.1
      have hPc : t.pc = 1843 := ht.1
      rw [Loader.loaderOutCore (by rw [hPc]; decide) (by rw [hPc]; decide),
        out_event ht.2.2.2.1 (hPc.symm ▸ Flow.code_1843) rfl rfl]
      change Out.ev (shflTmpl l (thread lane) t .idx 7189 none
        (.reg 7188) (.imm 31) (.imm 31) (.imm (-1))) = _
      simp [shflTmpl,readValue,readReg,hIn,hBlock,input,b32,Value.bytes,readBits,
        pure,Except.pure,t]
      rfl)
  apply total.advanceLocal (pc' := 1844)
  intro lane hl
  have h31 : laneOf l (thread 31) = 31 :=
    (Step.sameWarp_lane hBlock hg (by decide : 31 < 32)).2
  have hSource : (shflSource .idx lane 31 31).1 = 31 :=
    congrArg Prod.fst (shflSource_idx lane (by decide : 31 < 32))
  have ht := total.checkpoint lane hl
  change At _ 1844 _ at ht
  exact ⟨_,.refl,by simpa only [input,hSource,h31,drainGroupCount,laterDrainTotalFrame,F,
    List.cons_append,List.nil_append] using ht⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
