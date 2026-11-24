-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainFirstGroup
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderLaterDrainWord
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Flow.Code.Part028
import Lemmas.Flow.MemTmpl
import Lemmas.Step.ProtectedReadProgress
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open Correction (OpeningTripCursor)
open PTX.Kernels.TmlFa4Fwd.Loader (loaderLinear)

def laterDrainCarry (p : Params) (l : Launch) (g first use : Nat) : List (Nat × Value) :=
  [(7185,b32 (tilePrefix p first*p.heads)),(1173,b32 (g/l.block+1)),(7137,b32 p.heads)] ++
    firstGroupCarry p l g use

def laterDrainStart (p : Params) (l : Launch) (g first use : Nat) : List (Nat × Value) :=
  (7190,b32 first) :: laterDrainCarry p l g (min p.batch (first+31)) use

def laterDrainWords (p : Params) (l : Launch) (g first use : Nat) : List (Nat × Value) :=
  [(7186,b32 (drainCuQ p (first+laneOf l g))),(1175,b32 (first+laneOf l g)),(7190,b32 first)] ++
    laterDrainCarry p l g first use

private theorem laterDrainWordGate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use first : Nat} (hf : first+31 < p.batch) {s : TState}
    (hs : At s 1794 (laterDrainStart p l g first use)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if p.batch < first+31+laneOf l g then 1806 else 1803)
        ([(1175,b32 (first+31+laneOf l g)),(7186,b32 0),(7190,b32 (first+31))] ++
          laterDrainCarry p l g (first+31) use) := by
  let n := first+31
  let E := laterDrainCarry p l g n use
  let cta := g/l.block
  have hmin : min p.batch (first+31) = n := Nat.min_eq_right hf.le
  have hAt : At s 1794 ([(7190,b32 first),(7145,b32 p.batch),(1173,b32 (cta+1))]++E) := by
    apply hs.mono
    have h := hs.2.2.2.2
    rw [laterDrainStart,hmin] at h
    exact ⟨h.1,holds_mem h (by simp [laterDrainCarry,firstGroupCarry]),
      holds_mem h (by simp [laterDrainCarry,cta]),h.2⟩
  obtain ⟨t,ht,hT⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (laterDrainGroup hp (g := g) (show first ≤ p.batch by omega)) hAt
  have hBranch : At t 1798 ((241,.pred false)::(1174,b32 n)::(7190,b32 n)::E) := by
    apply hT.mono
    have h := hT.2.2.2.2
    exact ⟨by simpa [decide_eq_false hf.not_ge] using h.2.1,
      h.1,by simpa [Nat.min_eq_left hf.le] using h.2.2.1,h.2.2.2.2⟩
  obtain ⟨a,ha,hA⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1798 false hBranch hBranch.2.2.2.2.1 (by simp)
  have haAll := (loaderLinear (regs := []) (by decide) (by decide) hBranch.1
    (by simp) (by decide) ha).1
  have hIn : At a 1799 ([(1174,b32 n),(1073,b32 (laneOf l g)),(7145,b32 p.batch)] ++
      (7190,b32 n)::E) := by
    apply hA.mono
    have h := hA.2.2.2.2.2
    exact ⟨h.1,holds_mem h (by
      simp [E,laterDrainCarry,firstGroupCarry,firstDrainTail,drainSchedulerFrame]),
      holds_mem h (by simp [E,laterDrainCarry,firstGroupCarry]),h.2⟩
  obtain ⟨b,hb,hB⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (laterDrainLaneGate hp hf) hIn
  have hBefore : At b 1802 ((242,.pred (decide (p.batch < n+laneOf l g))) ::
      [(1175,b32 (n+laneOf l g)),(7186,b32 0),(7190,b32 n)]++E) :=
    hB.mono ⟨hB.2.2.2.2.2.1,hB.2.2.2.2.1,hB.2.2.2.2.2.2⟩
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1802 _ hBefore hBefore.2.2.2.2.1 (by simp)
  have huAll := (loaderLinear (regs := []) (by decide) (by decide) hBefore.1
    (by simp) (by decide) hu).1
  refine ⟨u, (run_rtg ht).trans ((run_rtg haAll).trans ((run_rtg hb).trans (run_rtg huAll))),?_⟩
  change At u (if p.batch < n+laneOf l g then 1806 else 1803)
    ([(1175,b32 (n+laneOf l g)),(7186,b32 0),(7190,b32 n)]++E)
  refine ⟨?_,hU.2.1,hU.2.2.1,hU.2.2.2.1,hU.2.2.2.2.2⟩
  simpa only [decide_eq_true_eq,Nat.reduceAdd] using hU.1

set_option maxRecDepth 4096 in
private theorem readLaterDrainWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
    {g use first : Nat} (hg : g < l.threads) (hf : first+31 < p.batch)
    (c : OpeningTripCursor l X g 1794 (laterDrainStart p l g first use)) :
    ∃ d : OpeningTripCursor l X g 1806 (laterDrainWords p l g (first+31) use),
      d.ending = c.ending ∧
      ((X.tr g).take d.pos).countP Execution.isShfl =
        ((X.tr g).take c.pos).countP Execution.isShfl ∧
      ((X.tr g).take d.pos).countP isFullWarpVote =
        ((X.tr g).take c.pos).countP isFullWarpVote := by
  let n := first+31
  let q := n+laneOf l g
  let E := [(1175,b32 q),(7190,b32 n)] ++ laterDrainCarry p l g n use
  obtain ⟨t,ht,hT⟩ := laterDrainWordGate hp hf c.checkpoint
  by_cases hLane : q ≤ p.batch
  · have hPc : t.pc = 1803 := by simpa only [q,n,ite_eq_right (Nat.not_lt_of_ge hLane)] using hT.1
    have hIn : At t 1803 ([(1175,b32 q),(7506,b64 p.cuQBase)]++E) := by
      refine ⟨hPc,hT.2.1,hT.2.2.1,hT.2.2.2.1,?_⟩
      have h := hT.2.2.2.2
      exact ⟨h.1,holds_mem h (by
        simp [laterDrainCarry,firstGroupCarry,firstDrainTail,drainSchedulerFrame]),
        h.1,h.2.2⟩
    obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by decide) (laterDrainAddress hp hLane) hIn
    let a : Acc := {loc := globalLoc (p.cuQBase+4*q),size := 4}
    let word := b32 (p.qOffset q)
    have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hRange
    have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
    have hOut : out kernel Assumptions.all l g u = .ev (.read a (afterLoad u [7186])) := by
      rw [Loader.loaderOutCore (by rw [hU.1]; decide) (by rw [hU.1]; decide),
        out_event hU.2.2.2.1 (hU.1.symm ▸ Flow.code_1805) rfl rfl]
      change Out.ev (loadTmpl [] l g u .global false 32 [7186] 7860 0) = _
      exact congrArg Out.ev
        (loadTmpl_global hU.2.1 hU.2.2.2.2.1 (by omega) (by decide) (by omega))
    let hn : Next kernel Assumptions.all l g c.before u (.read a (afterLoad u [7186])) :=
      ⟨c.localSteps.trans (ht.trans (run_rtg hu)),hOut⟩
    obtain ⟨he,hPrefix,hTail⟩ := Step.protected_read_of_maximal hMax hg
      (a := a) (value := word) rfl (hp.cuQ q hLane) (hCuQ q hLane)
      hn c.recorded c.remaining c.positive c.bounded c.released
      (Assumptions.wf_snoc_initial hMax.1)
    have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hRead : afterLoad u [7186] (word.toBytes.map some) = next (setReg u 7186 word) := by
      rw [afterLoad_ok hU.2.1 hU.2.2.1 hRebuild]
      simp [next,setReg,hU.2.1,hU.2.2.1]
    have hReady : At (next (setReg u 7186 word)) 1806 ((7186,word)::E) :=
      (hU.mono hU.2.2.2.2.2).set (by
        simp [E,laterDrainCarry,firstGroupCarry,firstDrainTail,drainCarry,drainSchedulerFrame])
    rw [hRead] at hPrefix hTail
    refine ⟨⟨c.pos+1,_,_,c.ending,Nat.succ_pos _,len_of_get he,
      releasedIfLast he (by intro h; cases h),?_,hPrefix,hTail,.refl⟩,rfl,?_,?_⟩
    · simpa only [laterDrainWords,drainCuQ,ite_eq_left hLane,q,n,word,
        List.cons_append,List.nil_append,E] using hReady
    · exact countP_take_succ_false he rfl
    · exact countP_take_succ_false he rfl
  · have hPc : t.pc = 1806 := by simpa only [q,n,ite_eq_left (Nat.lt_of_not_ge hLane)] using hT.1
    have hReady : At t 1806 ((7186,b32 0)::E) :=
      ⟨hPc,hT.2.1,hT.2.2.1,hT.2.2.2.1,
        hT.2.2.2.2.2.1,hT.2.2.2.2.1,hT.2.2.2.2.2.2⟩
    refine ⟨⟨c.pos,c.before,t,c.ending,c.positive,c.bounded,c.released,?_,
      c.recorded,c.remaining,c.localSteps.trans ht⟩,rfl,rfl,rfl⟩
    simpa only [laterDrainWords,drainCuQ,ite_eq_right hLane,q,n,
      List.cons_append,List.nil_append,E] using hReady

private theorem laterDrainWordsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use first shuffles votes : Nat} (hg : g < l.threads) (hf : first+31 < p.batch)
    (hCuQ : DrainCuQProtected p X)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 1794
      (fun lane => laterDrainStart p l (warpLane l g lane) first use) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1806
      (fun lane => laterDrainWords p l (warpLane l g lane) (first+31) use)
        shuffles votes ends) := by
  let thread := warpLane l g
  have hLane (lane : Nat) (hl : lane < 32) :
      ∃ d : OpeningTripCursor l X (thread lane) 1806
        (laterDrainWords p l (thread lane) (first+31) use),
        d.ending = ends lane ∧
        ((X.tr (thread lane)).take d.pos).countP Execution.isShfl = shuffles ∧
        ((X.tr (thread lane)).take d.pos).countP isFullWarpVote = votes := by
    have hs := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
    obtain ⟨d,hEnd,hSh,hVote⟩ := readLaterDrainWord hp hMax hCuQ hs.1.2.1 hf
      ⟨cur.pos lane,cur.before lane,cur.state lane,ends lane,cur.positive lane hl,
        cur.bounded lane hl,cur.released lane hl,cur.checkpoint lane hl,cur.recorded lane hl,
        cur.continuation lane hl,cur.localSteps lane hl⟩
    exact ⟨d,hEnd,hSh.trans (cur.ordinals.shfl lane hl),hVote.trans (cur.ordinals.vote lane hl)⟩
  classical
  let d (i : Nat) (hi : i < 32) := Classical.choose (hLane i hi)
  let pos i := if hi : i < 32 then (d i hi).pos else cur.pos i
  let before i := if hi : i < 32 then (d i hi).before else cur.before i
  let ready i := if hi : i < 32 then (d i hi).ready else cur.state i
  refine ⟨⟨⟨pos,before,ready,⟨?_,?_⟩,?_,?_,?_⟩,?_,?_ ,?_,?_⟩⟩
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (Classical.choose_spec (hLane i hi)).2.1
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (Classical.choose_spec (hLane i hi)).2.2
  · intro i hi
    have hEnd : (d i hi).ending = ends i := (Classical.choose_spec (hLane i hi)).1
    simpa only [before,pos,dite_eq_left hi,hEnd] using (d i hi).remaining
  · intro i hi
    simpa only [before,ready,dite_eq_left hi] using (d i hi).localSteps
  · intro i hi
    simpa only [ready,dite_eq_left hi] using (d i hi).checkpoint
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (d i hi).positive
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (d i hi).bounded
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (d i hi).released
  · intro i hi
    simpa only [before,pos,dite_eq_left hi] using (d i hi).recorded


/-- Later request groups use the same protected table and one actual neighbor shuffle. -/
theorem laterDrainNeighborsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use first shuffles votes : Nat} (hg : g < l.threads) (hf : first+31 < p.batch)
    (hCuQ : DrainCuQProtected p X)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 1794
      (fun lane => laterDrainStart p l (warpLane l g lane) first use) shuffles votes ends) :
    let thread := warpLane l g
    let n := first+31
    let words := fun lane => b32 (drainCuQ p (n+laneOf l (thread lane)))
    Nonempty (SchedulerWarpReached l X g 1808
      (fun lane => (2260,words (shflSource .down lane 1 31).1) ::
        (243,.pred (decide (laneOf l (thread lane) = 31))) ::
        laterDrainWords p l (thread lane) n use) (shuffles+1) votes ends) := by
  dsimp only
  obtain ⟨read⟩ := laterDrainWordsOfMaximal hp hMax hg hf hCuQ cur
  let thread := warpLane l g
  let n := first+31
  let words := fun lane => b32 (drainCuQ p (n+laneOf l (thread lane)))
  let frame := fun lane => (243,.pred (decide (laneOf l (thread lane) = 31))) ::
    laterDrainWords p l (thread lane) n use
  obtain ⟨ready⟩ := read.advanceLocal (pc' := 1807) (G := frame) (by
    intro lane hl
    let g' := thread lane
    let q := laneOf l g'
    let E := laterDrainWords p l g' n use
    have hSeg : Seg kernel [] l g' 1 1806 [(1073,b32 q)] 1807
        [(243,.pred (decide (q = 31)))] := by
      intro s hs
      have hb : q < 2^32 := (Nat.mod_lt _ (by decide : 0 < 32)).trans (by decide)
      seg_fp hs using (simp [compare,truncBits_ofNat hb (by decide),
        show (truncBits 32 31#64).toNat = 31 by decide,
        toNat_ofNat_lt (show q < 2^64 by omega)]; exact_mod_cast (Iff.rfl : q = 31 ↔ q = 31))
    have ht : At (read.state lane) 1806 ([(1073,b32 q)]++E) :=
      (read.checkpoint lane hl).mono ⟨holds_mem (read.checkpoint lane hl).2.2.2.2 (by
        simp [q,g',thread,laterDrainWords,laterDrainCarry,firstGroupCarry,firstDrainTail,
          drainSchedulerFrame]),
        (read.checkpoint lane hl).2.2.2.2⟩
    obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl) (by decide) hSeg ht
    exact ⟨u,run_rtg hu,hU⟩)
  have hFresh : ∀ lane < 32, ∀ item ∈ frame lane, item.1 ≠ 2260 := by
    intro lane _ item hi hEq
    have hMem := List.mem_map_of_mem (f := Prod.fst) hi
    rw [hEq] at hMem
    exact (of_decide_eq_true rfl : 2260 ∉ (frame lane).map Prod.fst) hMem
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (thread lane) (ready.state lane) =
        .ev (.shfl .down (words lane) 1 31
          (fun word _ => next (setReg (ready.state lane) 2260 word))) := by
    let t := ready.state lane
    have ht := ready.checkpoint lane hl
    have hWord : t.regs 7186 = some (words lane) := ht.2.2.2.2.2.1
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    rw [Loader.loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide),
      out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_1807) rfl rfl]
    change Out.ev (shflTmpl l (thread lane) t .down 2260 none
      (.reg 7186) (.imm 1) (.imm 31) (.imm (-1))) = _
    simp [shflTmpl,readValue,readReg,hWord,hBlock,words,b32,Value.bytes,readBits,pure,Except.pure,t]
    rfl
  exact ready.consumeShuffle hp hMax hg .down words (fun _ => 1) (fun _ => 31) hFresh hOut

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
