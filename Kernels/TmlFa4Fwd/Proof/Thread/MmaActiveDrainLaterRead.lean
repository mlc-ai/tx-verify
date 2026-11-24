-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainFirstRoute
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaGroupedCuQControl
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Flow.Code.Part042
import Lemmas.Step.ProtectedReadProgress
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread.Allocation (MmaCuQGroup drainRoots signedWord)
open Correction (OpeningTripCursor)

/-- A recurring lookup keeps the old cutoff until the next group is reduced. -/
def activeDrainGroupFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  (7215,b32 first)::(1196,b32 (g/l.block+1))::
    (7210,b32 (tilePrefix p first*p.heads))::activeDrainCommon p l g

private theorem laterWordGate {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first : Nat} (hf : first ≤ p.batch) {t : TState}
    (ht : At t 2701 ((1197,b32 first)::activeDrainGroupFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if p.batch < first+laneOf l g then 2708 else 2705)
        ((1198,b32 (first+laneOf l g))::(7211,b32 0)::activeDrainGroupFrame p l g first) := by
  let lane := laneOf l g
  let F := activeDrainGroupFrame p l g first
  let guard := decide (p.batch < first+lane)
  have hBatch := hp.shape.2.1
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hMargin := hp.shape.2.2.2.2.2
  have hIndex : first+lane < 2^31 := by omega
  have hInit : Seg kernel [] l g 3 2701
      [(1197,b32 first),(1180,b32 lane),(7149,b32 p.batch)] 2704
      [(421,.pred guard),(1198,b32 (first+lane)),(7211,b32 0)] := by
    intro s hs
    seg_fp hs using
      first
      | rfl
      | simp only [b32,← BitVec.ofNat_add,truncBits_ofNat (show first < 2^32 by omega) (by decide),
        truncBits_ofNat (show lane < 2^32 by omega) (by decide),
        truncBits_ofNat (show first+lane < 2^32 by omega) (by decide),
        truncBits_ofNat (show p.batch < 2^32 by omega) (by decide),compare,Option.getD_some,
        signedWord hIndex,signedWord hBatch,Int.ofNat_lt,gt_iff_lt,guard]
  have hMany := ht.2.2.2.2
  obtain ⟨u,hu,hU⟩ := hInit.apply (ht.mono ⟨hMany.1,holds_lookup hMany rfl,
    holds_lookup hMany rfl,trivial⟩)
  have hStable : At t 2701 F := ht.mono hMany.2
  obtain ⟨hPath,hF⟩ := activeDrainLocalKeep hStable (by decide) (by decide) (by
    change ((kernel.code.drop 2701).take 3).all
      (fun i => [7215,1196,7210,7149,7139,1180,7506,1072].all
        (fun r => !(writesRegs i.op).contains r)) = true
    decide +kernel) (by decide +kernel) hu
  have hEntry : At u 2704 ((1198,b32 (first+lane))::(7211,b32 0)::F) :=
    hU.mono ⟨hU.2.2.2.2.2.1,hU.2.2.2.2.2.2.1,hF⟩
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2704 guard hEntry hU.2.2.2.2.1
    (by simp)
  exact ⟨v,hPath.trans (run_rtg (localRun (by decide) (by decide) hU.1 rfl hv)),
    by simpa only [guard,decide_eq_true_eq] using hV⟩

/-- Each recurring-group CuQ word is read from the protected launch allocation,
or retains its zero when the initialized guard bypasses the load. -/
theorem activeDrainLaterWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g first : Nat} (hg : g < l.threads) (hf : first ≤ p.batch)
    (c : OpeningTripCursor l X g 2701 ((1197,b32 first)::activeDrainGroupFrame p l g first)) :
    ∃ d : OpeningTripCursor l X g 2708
      ((7211,b32 (drainCuQ p (first+laneOf l g)))::(1198,b32 (first+laneOf l g))::
        activeDrainGroupFrame p l g first),
      d.ending = c.ending ∧
      ((X.tr g).take d.pos).countP Execution.isShfl =
        ((X.tr g).take c.pos).countP Execution.isShfl ∧
      ((X.tr g).take d.pos).countP isFullWarpVote =
        ((X.tr g).take c.pos).countP isFullWarpVote := by
  let lane := laneOf l g
  let ix := first+lane
  let F := activeDrainGroupFrame p l g first
  obtain ⟨t,ht,hT⟩ := laterWordGate hp hf c.checkpoint
  by_cases hi : ix ≤ p.batch
  · have hPc : t.pc = 2705 := by
      simpa only [ix,lane,ite_eq_right (Nat.not_lt_of_ge hi)] using hT.1
    have hT' : At t 2705 ((1198,b32 ix)::F) :=
      ⟨hPc,hT.2.1,hT.2.2.1,hT.2.2.2.1,hT.2.2.2.2.1,hT.2.2.2.2.2.2⟩
    have hAddrAt : At t (MmaCuQGroup.drain.readSite-2)
        ((MmaCuQGroup.drain.ordReg,b32 ix)::MmaCuQGroup.drain.facts p l g first) :=
      hT'.mono ⟨hT'.2.2.2.2.1,holds_lookup hT'.2.2.2.2 rfl,
        holds_lookup hT'.2.2.2.2 rfl,holds_lookup hT'.2.2.2.2 rfl,
        holds_lookup hT'.2.2.2.2 rfl,holds_lookup hT'.2.2.2.2 rfl,
        holds_lookup hT'.2.2.2.2 rfl,holds_lookup hT'.2.2.2.2 rfl,trivial⟩
    obtain ⟨u,hRun,hU,hOut⟩ := MmaCuQGroup.drain.readAddress hp hi hAddrAt
    have hRegDef : MmaCuQGroup.drain.dstReg = 7211 := rfl
    let a : Acc := {loc := globalLoc (p.cuQBase+4*ix),size := 4}
    have hn : Next kernel Assumptions.all l g c.before u (.read a (afterLoad u [7211])) :=
      ⟨c.localSteps.trans (ht.trans (run_rtg hRun)),by simpa only [hRegDef] using hOut⟩
    let word := b32 (p.qOffset ix)
    obtain ⟨he,hPrefix,hTail⟩ := Step.protected_read_of_maximal hMax hg
      (a := a) (value := word) rfl (hp.cuQ ix hi) (hCuQ ix hi)
      hn c.recorded c.remaining c.positive c.bounded c.released
      (Assumptions.wf_snoc_initial hMax.1)
    have hArgs : At t 2705 [(1198,b32 ix),(7506,b64 p.cuQBase)] :=
      hT'.mono ⟨hT'.2.2.2.2.1,holds_lookup hT'.2.2.2.2 rfl,trivial⟩
    have hs : Seg kernel [] l g 2 2705 [(1198,b32 ix),(7506,b64 p.cuQBase)] 2707
        [(7886,b64 (p.cuQBase+4*ix))] := by
      -- Reuse the decoded address calculation that also checks recorded reads.
      exact MmaCuQGroup.drain.addressCore hp g hi
    obtain ⟨v,hv,_⟩ := hs.apply hArgs
    obtain ⟨_,hKeep⟩ := activeDrainLocalKeep hT' (by decide) (by decide) (by
      change ((kernel.code.drop 2705).take 2).all
        (fun i => [1198,7215,1196,7210,7149,7139,1180,7506,1072].all
          (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel) (by decide +kernel) hv
    have hv' : run kernel Assumptions.all l g 2 t = some v :=
      localRun (by decide) (by decide) hPc (by decide +kernel) hv
    have hSame := Option.some.inj (hv'.symm.trans hRun)
    subst v
    have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hRead : afterLoad u [7211] (word.toBytes.map some) = next (setReg u 7211 word) := by
      rw [afterLoad_ok hU.2.1 hU.2.2.1 hRebuild]
      simp [next,setReg,hU.2.1,hU.2.2.1]
    have hReady : At (next (setReg u 7211 word)) 2708 ((7211,word)::(1198,b32 ix)::F) :=
      (hU.mono hKeep).set (by simp [F,activeDrainGroupFrame,activeDrainCommon,drainRoots])
    rw [hRead] at hPrefix hTail
    refine ⟨⟨c.pos+1,_,_,c.ending,Nat.succ_pos _,len_of_get he,
      releasedIfLast he (by intro h; cases h),?_,hPrefix,hTail,.refl⟩,rfl,?_,?_⟩
    · simpa only [drainCuQ,ite_eq_left hi,ix,lane,word] using hReady
    · exact countP_take_succ_false he rfl
    · exact countP_take_succ_false he rfl
  · have hReady : At t 2708 ((7211,b32 (drainCuQ p ix))::(1198,b32 ix)::F) := by
      have hT' := hT.mono (show Holds t.regs ((7211,b32 0)::(1198,b32 ix)::F) from
        ⟨hT.2.2.2.2.2.1,hT.2.2.2.2.1,hT.2.2.2.2.2.2⟩)
      simpa only [drainCuQ,ite_eq_right hi,ite_eq_left (Nat.lt_of_not_ge hi),ix,lane] using hT'
    exact ⟨⟨c.pos,c.before,t,c.ending,c.positive,c.bounded,c.released,hReady,c.recorded,
      c.remaining,c.localSteps.trans ht⟩,rfl,rfl,rfl⟩

def activeDrainDownFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(7211,b32 (drainCuQ p (first+laneOf l g))),(1198,b32 (first+laneOf l g)),
    (422,.pred (decide (laneOf l g = 31)))] ++ activeDrainGroupFrame p l g first

private theorem prepareLaterDown {p : Params} {l : Launch} {g first : Nat} {t : TState}
    (ht : At t 2708 ((7211,b32 (drainCuQ p (first+laneOf l g)))::(1198,b32 (first+laneOf l g))::
      activeDrainGroupFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2709 (activeDrainDownFrame p l g first) := by
  let k := laneOf l g
  have hl : k < 32 := Nat.mod_lt _ (by decide)
  have hSeg : Seg kernel [] l g 1 2708 [(1180,b32 k)] 2709
      [(422,.pred (decide (k=31)))] := by
    intro s hs
    seg_fp hs using
      simp only [compare,Option.getD_some,truncBits_ofNat (show k < 2^32 by omega) (by decide),
        toNat_ofNat_lt (show k < 2^64 by omega),Int.ofNat_inj,
        show (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 by decide]
  obtain ⟨u,hu,hU⟩ := hSeg.apply (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep ht (by decide) (by decide) (by
    change ((kernel.code.drop 2708).take 1).all
      (fun i => [7211,1198,7215,1196,7210,7149,7139,1180,7506,1072].all
        (fun r => !(writesRegs i.op).contains r)) = true
    decide +kernel) (by decide +kernel) hu
  exact ⟨u,hPath,hU.mono ⟨hKeep.1,hKeep.2.1,hU.2.2.2.2.1,hKeep.2.2⟩⟩

/-- The recurring group completes its guarded CuQ reads before its first warp exchange. -/
theorem activeDrainLaterWordsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first ≤ p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2701
      (fun i => (1197,b32 first)::activeDrainGroupFrame p l (warpLane l g i) first)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2709
      (fun i => activeDrainDownFrame p l (warpLane l g i) first) shuffles votes ends) := by
  classical
  let thread := warpLane l g
  have hData (i : Nat) (hi : i < 32) : ∃ (pos : Nat) (before ready : TState),
      0 < pos ∧ pos ≤ (X.tr (thread i)).length ∧
      (pos = (X.tr (thread i)).length → Step.Released l X (thread i)) ∧
      ((X.tr (thread i)).take pos).countP Execution.isShfl = shuffles ∧
      ((X.tr (thread i)).take pos).countP isFullWarpVote = votes ∧
      Run kernel Assumptions.all l (thread i) {} ((X.tr (thread i)).take pos) (some before) ∧
      Run kernel Assumptions.all l (thread i) before ((X.tr (thread i)).drop pos) (ends i) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread i)) before ready ∧
      At ready 2709 (activeDrainDownFrame p l (thread i) first) := by
    let start : OpeningTripCursor l X (thread i) 2701
        ((1197,b32 first)::activeDrainGroupFrame p l (thread i) first) :=
      ⟨cur.pos i,cur.before i,cur.state i,ends i,cur.positive i hi,cur.bounded i hi,
        cur.released i hi,cur.checkpoint i hi,cur.recorded i hi,cur.continuation i hi,
        cur.localSteps i hi⟩
    have hWarp := Step.sameWarp_lane (show l.block%32 = 0 by rw [hp.block]) hg hi
    obtain ⟨u,hEnd,hSh,hV⟩ := activeDrainLaterWord hp hMax hCuQ hWarp.1.1.2.1 hf start
    obtain ⟨v,hLocal,hv⟩ := prepareLaterDown u.checkpoint
    have hEnd' : u.ending = ends i := hEnd
    exact ⟨u.pos,u.before,v,u.positive,u.bounded,u.released,
      hSh.trans (cur.ordinals.shfl i hi),hV.trans (cur.ordinals.vote i hi),
      u.recorded,hEnd' ▸ u.remaining,u.localSteps.trans hLocal,hv⟩
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! pos before ready hPos hBound hRel hSh hV hRec hTail hLocal hAt using hData
  exact ⟨⟨⟨pos,before,ready,⟨hSh,hV⟩,hTail,hLocal,hAt⟩,hPos,hBound,hRel,hRec⟩⟩

end PTX.Kernels.TmlFa4Fwd.Mma
