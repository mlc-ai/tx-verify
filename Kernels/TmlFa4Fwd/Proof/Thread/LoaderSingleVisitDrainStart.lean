-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActiveExitProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Flow.MemTmpl
import Lemmas.Step.ProtectedReadProgress
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open Correction (OpeningTripCursor)
open PTX.Kernels.TmlFa4Fwd.Loader (loaderLinear loaderSteadyCounterGateWithFrame)

private theorem linearFramed {l : Launch} {g n pc pc' : Nat} {s : TState}
    {F G E : List (Nat × Value)} (hLo : 174 ≤ pc) (hHi : pc+n ≤ 1906)
    (hKeep : ((kernel.code.drop pc).take n).all
      (fun i => (E.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hStraight : ((kernel.code.drop pc).take (n-1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hSeg : Seg kernel [] l g n pc F pc' G) (hs : At s pc (F++E)) :
    ∃ u, run kernel Assumptions.all l g n s = some u ∧ At u pc' (G++E) := by
  have hRegs := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨u,hRun,hu⟩ := hSeg s (hs.mono hRegs.1)
  obtain ⟨hAll,hFrame⟩ := loaderLinear hLo hHi hs.1 hKeep hStraight hRun
  exact ⟨u,hAll,hu.mono ((holds_append ..).mpr ⟨hu.2.2.2.2,
    holdsSchedulerFrame hRegs.2 hFrame (fun _ hm => List.mem_map_of_mem hm)⟩)⟩

/-- Scheduler inputs retained while the selected single-visit tile skips the
warm and steady copy loops. -/
def drainSchedulerFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1073,b32 (laneOf l g)),(7506,b64 p.cuQBase),(1072,b32 (g/l.block)),
    (64,.pred (!decide (laneHasRequest (laneOf l g) p.batch)))]

private theorem singleVisitDrainLocal {p : Params} {l : Launch} {g : Nat} {s : TState}
    {rest : Bool} (hw : warpIndex l g = 14 ∨ warpIndex l g = 15)
    (hs : At s 905 ([(1088,b32 1),(1091,b32 0),(164,.pred rest),
      (1062,b32 (warpIndex l g)),(2535,b32 l.sharedBase)] ++ drainSchedulerFrame p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 1744 ((1062,b32 (warpIndex l g)) :: (drainCarry l 2 ++ drainSchedulerFrame p l g)) := by
  let F := drainSchedulerFrame p l g
  let warp := warpIndex l g
  let keep := [(1062,b32 warp),(2535,b32 l.sharedBase)] ++ F
  let core := [(7,.pred false),(166,.pred true),(7179,b32 2),(7180,b32 1),(1091,b32 0)]
  have hEntry : Seg kernel [] l g 6 905 [(1088,b32 1),(1091,b32 0),(164,.pred rest)] 911
      core := by
    intro t ht
    cases rest <;> dsimp only [core] <;> seg_fp ht using rfl
  have hs' : At s 905 ([(1088,b32 1),(1091,b32 0),(164,.pred rest)]++keep) := hs
  obtain ⟨t,hEntry,ht⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hEntry hs'
  obtain ⟨u,hJump,hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_911 true ht ht.2.2.2.2.2.1 (by simp)
  have hJumpAll := (loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by simp) (by decide) hJump).1
  let keep' := [(1091,b32 0),(1062,b32 warp),(2535,b32 l.sharedBase),
    (7179,b32 2),(7180,b32 1)] ++ F
  have hu' : At u 1353 ([(1091,b32 0),(1062,b32 warp),(7,.pred false)]++keep') := by
    have h := hu.2.2.2.2
    apply hu.mono
    simp only [core,keep,keep',List.cons_append,List.nil_append,Holds] at h ⊢
    exact ⟨h.2.2.2.2.1,h.2.2.2.2.2.1,h.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2⟩
  have hSteady : Seg kernel [] l g 5 1353
      [(1091,b32 0),(1062,b32 warp),(7,.pred false)] 1358
      [(202,.pred true),(7181,b32 0)] := by
    intro v hv
    rcases hw with h | h <;>
      simp only [warp,h] at hv <;> seg_fp hv using rfl
  obtain ⟨v,hSteady,hv⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSteady hu'
  obtain ⟨w,hSkip,hw'⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1358 true hv hv.2.2.2.2.1 (by simp)
  have hSkipAll := (loaderLinear (regs := []) (by decide) (by decide) hv.1
    (by simp) (by decide) hSkip).1
  let carry := (1062,b32 warp)::(drainCarry l 2 ++ F)
  have hw'' : At w 1384 ([(7181,b32 0),(1091,b32 0)]++carry) :=
    hw'.mono hw'.2.2.2.2.2
  obtain ⟨q,hGate,hq⟩ := loaderSteadyCounterGateWithFrame (l := l) (g := g)
    (by decide : 0 < 2^31) (by decide : 0 < 2^31)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) w hw''
  exact ⟨q,(run_rtg hEntry).trans ((run_rtg hJumpAll).trans ((run_rtg hSteady).trans
    ((run_rtg hSkipAll).trans (run_rtg hGate)))),hq.mono hq.2.2.2.2.2.2⟩

/-- For a single visit, both loader warps advance from their real V publication
to the terminal scheduler without requesting another cache packet. -/
theorem singleVisitDrainStartOfPublished {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) {ends : Nat → Option TState} {rest : Nat → Bool}
    (cur : SchedulerWarpReached l X g 905 (fun lane => let t := warpLane l g lane
      [(1088,b32 1),(1091,b32 0),(164,.pred (rest lane)),
        (1062,b32 (warpIndex l t)),(2535,b32 l.sharedBase)] ++ drainSchedulerFrame p l t)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1744 (fun lane => let t := warpLane l g lane
      (1062,b32 (warpIndex l t))::(drainCarry l 2 ++ drainSchedulerFrame p l t))
      shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hWarp := warpIndex_lt hp (warpLane l g lane)
  have hWarpEq : warpIndex l g = warpIndex l (warpLane l g lane) := hSame.2
  rw [hWarpEq] at hw
  exact singleVisitDrainLocal (by omega) (cur.checkpoint lane hl)

def firstDrainTail (p : Params) (l : Launch) (g use : Nat) : List (Nat × Value) :=
  (1062,b32 (warpIndex l g)) :: (drainCarry l use ++ drainSchedulerFrame p l g)

/-- The first request group's checked batch size and exact optional CuQ lane word. -/
def firstDrainWordsFrame (p : Params) (l : Launch) (g use : Nat) : List (Nat × Value) :=
  [(7184,b32 (drainCuQ p (laneOf l g))),(7145,b32 p.batch)] ++ firstDrainTail p l g use

private theorem prepareFirstDrainRead {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} {t : TState} (ht : At t 1744 (firstDrainTail p l g use)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if p.batch < laneOf l g then 1751 else 1748)
        ([(7184,b32 0),(7145,b32 p.batch)] ++ firstDrainTail p l g use) := by
  let F := firstDrainTail p l g use
  let lane := laneOf l g
  let batch := p.batch
  obtain ⟨hBatch32,hParam⟩ := hp.values (19,p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  let v := next (setReg t 7145 (b32 batch))
  have hLoad : run kernel [] l g 1 t = some v :=
    Loader.scalarLoad ht hParam hBatch32 (by rw [Loader.loaderParam19Name]; exact Flow.code_1744)
  have hV : At v 1745 ((7145,b32 batch)::F) :=
    ht.set (by simp [firstDrainTail,drainCarry,drainSchedulerFrame])
  have hLoadAll := (loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by simp) (by decide) hLoad).1
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hBatch := hp.shape.2.1
  have signed {n : Nat} (hn : n < 2^31) :
      toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    simp only [toSigned,toNat_ofNat_lt (show n < 2^64 by omega),
      Nat.mod_eq_of_lt (show n < 2^32 by omega),ite_eq_left hn]
  have hGate : Seg kernel [] l g 2 1745 [(7145,b32 batch),(1073,b32 lane)] 1747
      [(231,.pred (decide (batch < lane))),(7184,b32 0)] := by
    intro w hw
    seg_fp hw using
      first
      | rfl
      | simp only [truncBits_ofNat (show lane < 2^32 by omega) (by decide),
          truncBits_ofNat (show batch < 2^32 by omega) (by omega),compare,Option.getD_some,
          signed (show lane < 2^31 by omega),signed (show batch < 2^31 by omega),
          gt_iff_lt,Int.ofNat_lt]
  have hV' : At v 1745 ([(7145,b32 batch),(1073,b32 lane)] ++ (7145,b32 batch)::F) :=
    hV.mono ⟨hV.2.2.2.2.1,holds_mem hV.2.2.2.2
      (by simp [F,firstDrainTail,drainSchedulerFrame,lane]),hV.2.2.2.2⟩
  obtain ⟨w,hToGate,hw⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hGate hV'
  obtain ⟨u,hBranch,hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1747 _ hw hw.2.2.2.2.1 (by simp)
  have hBranchAll := (loaderLinear (regs := []) (by decide) (by decide) hw.1
    (by simp) (by decide) hBranch).1
  refine ⟨u,(run_rtg hLoadAll).trans ((run_rtg hToGate).trans (run_rtg hBranchAll)),?_⟩
  refine ⟨?_,hu.2.1,hu.2.2.1,hu.2.2.2.1,hu.2.2.2.2.2⟩
  simpa only [decide_eq_true_eq] using hu.1

private theorem readFirstDrainWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
    {g use : Nat} (hg : g < l.threads)
    (c : OpeningTripCursor l X g 1744 (firstDrainTail p l g use)) :
    ∃ d : OpeningTripCursor l X g 1751 (firstDrainWordsFrame p l g use),
      d.ending = c.ending ∧
      ((X.tr g).take d.pos).countP Execution.isShfl =
        ((X.tr g).take c.pos).countP Execution.isShfl ∧
      ((X.tr g).take d.pos).countP isFullWarpVote =
        ((X.tr g).take c.pos).countP isFullWarpVote := by
  let q := laneOf l g
  obtain ⟨t,ht,hT⟩ := prepareFirstDrainRead hp c.checkpoint
  by_cases hLane : q ≤ p.batch
  · have hT' : At t 1748 ((7145,b32 p.batch)::firstDrainTail p l g use) := by
      refine ⟨?_,hT.2.1,hT.2.2.1,hT.2.2.2.1,hT.2.2.2.2.2⟩
      simpa only [q,ite_eq_right (Nat.not_lt_of_ge hLane)] using hT.1
    have hFrame : At t 1748 (Thread.Loader.drainRootFrame p l g ++
        (7145,b32 p.batch)::firstDrainTail p l g use) := by
      apply hT'.mono
      refine (holds_append ..).mpr ⟨?_,hT'.2.2.2.2⟩
      refine ⟨?_,?_,?_,trivial⟩ <;>
        apply holds_mem hT'.2.2.2.2 <;> simp [firstDrainTail,drainSchedulerFrame]
    obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (Thread.Loader.loaderFirstDrainAddress hp hLane) hFrame
    let a : Acc := {loc := globalLoc (p.cuQBase+4*q),size := 4}
    let word := b32 (p.qOffset q)
    have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hRange
    have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
    have hOut : out kernel Assumptions.all l g u = .ev (.read a (afterLoad u [7184])) := by
      rw [Loader.loaderOutCore (by rw [hU.1]; decide) (by rw [hU.1]; decide),
        out_event hU.2.2.2.1 (hU.1.symm ▸ Flow.code_1750) rfl rfl]
      change Out.ev (loadTmpl [] l g u .global false 32 [7184] 7858 0) = _
      exact congrArg Out.ev (loadTmpl_global hU.2.1 hU.2.2.2.2.1 (by omega) (by decide) (by omega))
    let hn : Next kernel Assumptions.all l g c.before u (.read a (afterLoad u [7184])) :=
      ⟨c.localSteps.trans (ht.trans (run_rtg hu)),hOut⟩
    obtain ⟨he,hPrefix,hTail⟩ := Step.protected_read_of_maximal hMax hg
      (a := a) (value := word) rfl (hp.cuQ q hLane) (hCuQ q hLane)
      hn c.recorded c.remaining c.positive c.bounded c.released
      (Assumptions.wf_snoc_initial hMax.1)
    have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hRead : afterLoad u [7184] (word.toBytes.map some) = next (setReg u 7184 word) := by
      rw [afterLoad_ok hU.2.1 hU.2.2.1 hRebuild]
      simp [next,setReg,hU.2.1,hU.2.2.1]
    have hReady : At (next (setReg u 7184 word)) 1751
        ((7184,word)::(7145,b32 p.batch)::firstDrainTail p l g use) :=
      (hU.mono hU.2.2.2.2.2).set (by
        simp [firstDrainTail,drainCarry,drainSchedulerFrame])
    rw [hRead] at hPrefix hTail
    refine ⟨⟨c.pos+1,_,_,c.ending,Nat.succ_pos _,len_of_get he,
      releasedIfLast he (by intro h; cases h),?_,hPrefix,hTail,.refl⟩,rfl,?_,?_⟩
    · simpa only [firstDrainWordsFrame,drainCuQ,ite_eq_left hLane,q,word,
        List.cons_append,List.nil_append] using hReady
    · exact countP_take_succ_false he rfl
    · exact countP_take_succ_false he rfl
  · have hReady : At t 1751 (firstDrainWordsFrame p l g use) := by
      simpa only [firstDrainWordsFrame,drainCuQ,ite_eq_right hLane,
        ite_eq_left (Nat.lt_of_not_ge hLane),q] using hT
    exact ⟨⟨c.pos,c.before,t,c.ending,c.positive,c.bounded,c.released,hReady,
      c.recorded,c.remaining,c.localSteps.trans ht⟩,rfl,rfl,rfl⟩

/-- The loader's actual first drain group either loads its protected CuQ
word or bypasses an out-of-range lane with the decoded zero. -/
theorem firstDrainWordsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use shuffles votes : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 1744
      (fun lane => firstDrainTail p l (warpLane l g lane) use) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1751
      (fun lane => firstDrainWordsFrame p l (warpLane l g lane) use) shuffles votes ends) := by
  let thread := warpLane l g
  have hLane (lane : Nat) (hl : lane < 32) :
      ∃ d : OpeningTripCursor l X (thread lane) 1751 (firstDrainWordsFrame p l (thread lane) use),
        d.ending = ends lane ∧
        ((X.tr (thread lane)).take d.pos).countP Execution.isShfl = shuffles ∧
        ((X.tr (thread lane)).take d.pos).countP isFullWarpVote = votes := by
    have hs := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
    obtain ⟨d,hEnd,hSh,hVote⟩ := readFirstDrainWord hp hMax hCuQ hs.1.2.1
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

/-- The loader's drain performs the real full-warp down shuffle of the checked
CuQ words at the next common shuffle ordinal. -/
theorem firstDrainNeighborsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use shuffles votes : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 1744
      (fun lane => firstDrainTail p l (warpLane l g lane) use) shuffles votes ends) :
    let thread := warpLane l g
    let words := fun lane => b32 (drainCuQ p (laneOf l (thread lane)))
    Nonempty (SchedulerWarpReached l X g 1752
      (fun lane => (2239,words (shflSource .down lane 1 31).1)::
        firstDrainWordsFrame p l (thread lane) use) (shuffles+1) votes ends) := by
  dsimp only
  obtain ⟨ready⟩ := firstDrainWordsOfMaximal hp hMax hg hCuQ cur
  let thread := warpLane l g
  let words := fun lane => b32 (drainCuQ p (laneOf l (thread lane)))
  have hFresh : ∀ lane < 32,
      ∀ item ∈ firstDrainWordsFrame p l (thread lane) use, item.1 ≠ 2239 := by
    intro lane _ item hi hEq
    have hMem := List.mem_map_of_mem (f := Prod.fst) hi
    rw [hEq] at hMem
    have hn : 2239 ∉ (firstDrainWordsFrame p l (thread lane) use).map Prod.fst :=
      of_decide_eq_true rfl
    exact hn hMem
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (thread lane) (ready.state lane) =
        .ev (.shfl .down (words lane) 1 31
          (fun word _ => next (setReg (ready.state lane) 2239 word))) := by
    let t := ready.state lane
    have ht := ready.checkpoint lane hl
    have hWord : t.regs 7184 = some (words lane) := ht.2.2.2.2.1
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    rw [Loader.loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide),
      out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_1751) rfl rfl]
    change Out.ev (shflTmpl l (thread lane) t .down 2239 none
      (.reg 7184) (.imm 1) (.imm 31) (.imm (-1))) = _
    simp [shflTmpl,readValue,readReg,hWord,hBlock,words,b32,Value.bytes,readBits,pure,Except.pure,t]
    rfl
  exact ready.consumeShuffle hp hMax hg .down words (fun _ => 1) (fun _ => 31) hFresh hOut

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
