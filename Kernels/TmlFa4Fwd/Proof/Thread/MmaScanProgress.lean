-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaScanStartProgress
public import Kernels.TmlFa4Fwd.Proof.MmaFirstRoute
import Lemmas.Flow.WarpScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma (firstSchedulerPos scanReg scanPc scanSrc scanDst scanResult
  scanTemplate scanFold scanTotalTemplate roundInfo roundStraight localRun firstGroupRoute)

noncomputable section

private def scanPosition (p : Params) (l : Launch) (g round : Nat) : Nat :=
  firstSchedulerPos p (laneOf l g) + 1 + round

private def ScanCursor (p : Params) (l : Launch) (X : Execution) (g round : Nat) : Prop :=
  let pos := scanPosition p l g round
  ∃ s t o, pos ≤ (X.tr g).length ∧
    ((X.tr g).take pos).countP Execution.isShfl = 5 + round ∧
    (pos = (X.tr g).length → Step.Released l X g) ∧
    At t (1960 + 4 * round)
      [(scanReg round, b32 (prefixWindow (groupLaneTiles p 0) (2 ^ round) (laneOf l g))),
        (1180, b32 (laneOf l g)), (7139, b32 p.heads), (1072, b32 (g / l.block)),
        (7196, b32 (groupLaneTiles p 0 (laneOf l g)))] ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s) ∧
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧
    Run kernel Assumptions.all l g s ((X.tr g).drop pos) o

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem scanSeed (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X)
    : ScanCursor p l X g 0 := by
  obtain ⟨s, t, o, hBound, hCount, hReleased, ht, hPast, hLocal, hTail⟩ :=
    firstScanCursor hp hMax hg hw hProtected
  have hFacts : At t 1960
      [(7196, b32 (groupLaneTiles p 0 (laneOf l g))), (1180, b32 (laneOf l g)),
        (7139, b32 p.heads), (1072, b32 (g / l.block)),
        (7196, b32 (groupLaneTiles p 0 (laneOf l g)))] := by at_select ht
  refine ⟨s, t, o, hBound, hCount, hReleased, ?_, hPast, hLocal, hTail⟩
  simpa only [Nat.mul_zero, Nat.add_zero, pow_zero, prefixWindow_one,
    scanReg, dite_eq_left (by decide : 0 < 5), scanSrc] using hFacts

private theorem appendActualShuffle {l : Launch} {X : Execution} {g pos : Nat}
    {t u : TState} {o : Option TState} {dst : Value → Bool → TState}
    {mode : ShflMode} {sent recv : Value} {b c : Nat} {ok : Bool}
    (hr : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hn : Next kernel Assumptions.all l g t u (.shfl mode sent b c dst))
    (he : X.get (g,pos) = some ⟨u.pc, .shfl mode sent b c recv ok⟩) :
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1)) (some (dst recv ok)) ∧
      Run kernel Assumptions.all l g (dst recv ok) ((X.tr g).drop (pos+1)) o := by
  have hLt : pos < (X.tr g).length := len_of_get he
  obtain ⟨_, _, hGet, ⟨v, valid, rfl, hOut⟩, hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hOut
  have hEv := congrArg Event.kind (Option.some.inj (hGet.symm.trans he))
  obtain ⟨_, _, _, _, hv, hValid⟩ := Kind.shfl.inj hEv
  subst v
  subst valid
  refine ⟨?_, hRest⟩
  rw [List.take_succ_eq_append_getElem hLt]
  have hEq : (X.tr g)[pos] = ⟨u.pc, .shfl mode sent b c recv ok⟩ := by
    change (X.tr g)[pos]? = some _ at he
    rwa [List.getElem?_eq_getElem hLt, Option.some.injEq] at he
  rw [hEq]
  exact hr.snoc hn.steps ⟨_, hn.stop, recv, ok, rfl, rfl⟩

private theorem scanRoundFrame : ∀ stage : Fin 5,
    ((kernel.code.drop (scanPc stage + 1)).take 3).all
      (fun ins => [1180, 7139, 1072, 7196].all (fun r => !(writesRegs ins.op).contains r)) = true ∧
    1072 ≠ scanDst stage ∧ 7196 ≠ scanDst stage := by decide +kernel

private theorem scanRound (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g round : Nat} (hg : g < l.threads) (hRound : round < 5)
    (hCursor : ∀ h, SameWarp l g h → ScanCursor p l X h round) :
    ScanCursor p l X g (round + 1) := by
  let stage : Fin 5 := ⟨round,hRound⟩
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ round)
  let word (h : Nat) := b32 (part (laneOf l h))
  let advance (t : TState) (v : Value) := next (setReg t (scanDst stage) v)
  let pos (h : Nat) := scanPosition p l h round
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hShape (h : Nat) (hs : SameWarp l g h) :
      ∃ s t o, pos h ≤ (X.tr h).length ∧
        ((X.tr h).take (pos h)).countP Execution.isShfl = 5 + round ∧
        (pos h = (X.tr h).length → Step.Released l X h) ∧
        At t (scanPc stage) [(scanSrc stage, word h),
          (1180,b32 (laneOf l h)), (7139,b32 p.heads), (1072,b32 (h / l.block)),
          (7196, b32 (groupLaneTiles p 0 (laneOf l h)))] ∧
        Run kernel Assumptions.all l h {} ((X.tr h).take (pos h)) (some s) ∧
        Run kernel Assumptions.all l h s ((X.tr h).drop (pos h)) o ∧
        Next kernel Assumptions.all l h s t
          (.shfl .up (word h) (2^round) 0 (fun v _ => advance t v)) := by
    obtain ⟨s,t,o,hBound,hCount,hRel,hAt,hRun,hl,hTail⟩ := hCursor h hs
    have ht : At t (scanPc stage) [(scanSrc stage, word h),
        (1180,b32 (laneOf l h)), (7139,b32 p.heads), (1072,b32 (h / l.block)),
          (7196, b32 (groupLaneTiles p 0 (laneOf l h)))] := by
      simpa only [scanReg, dite_eq_left hRound, scanPc, stage, word, part] using hAt
    have hOut := scanTemplate hp h t stage (part (laneOf l h))
      ht.1 ht.2.2.2.1 ht.2.2.2.2.1
    exact ⟨s,t,o,hBound,hCount,hRel,ht,hRun,hTail,hl,hOut⟩
  have hIssued (h : Nat) (hs : SameWarp l g h) :
      ∃ recv ok, X.get (h,pos h) =
        some ⟨scanPc stage,.shfl .up (word h) (2^round) 0 recv ok⟩ ∧
        X.ShflK (h,pos h) (5+round) := by
    apply Step.shfl_occurs_of_maximal hMax hBlock hs.1.2.1 pos word (fun _ => 2^round) (fun _ => 0)
    · intro k hk
      obtain ⟨_,_,_,_,hCount,_,_,_,_,_⟩ := hShape k (Step.sameWarp_trans hs hk)
      exact .inl (fun hNil => by rw [hNil] at hCount; simp at hCount; omega)
    · intro k hk
      obtain ⟨s,t,o,hBound,hCount,hRel,hAt,hRun,hTail,hn⟩ := hShape k (Step.sameWarp_trans hs hk)
      exact ⟨s,t,o,_,hBound,hCount,hRel,hAt.1,hRun,hTail,hn⟩
    · intro ev h
      exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes h)
  have hgWarp : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨s,t,o,hBound,hCount,_,ht,hPast,hTail,hn⟩ := hShape g hgWarp
  obtain ⟨recv,ok,he,hOrdinal⟩ := hIssued g hgWarp
  let source := (shflSource .up (laneOf l g) (2^round) 0).1
  let peer := warpLane l g source
  have hlane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hSource : source < 32 := Step.shflSource_lt .up hlane _ _
  obtain ⟨hPeer,hLane⟩ := Step.sameWarp_lane hBlock hg hSource
  obtain ⟨v,flag,hGet,hK⟩ := hIssued peer hPeer
  obtain ⟨hRecv,_⟩ := shfl_source_value hMax.1 he hOrdinal hGet hK
    (ShflK.not_exited hMax.1 hPeer.1.2.1 hK)
  change laneOf l peer = source at hLane
  have hWord : recv = b32 (part source) := by simpa only [word, hLane] using hRecv
  have hStep : X.get (g,pos g) = some ⟨t.pc,.shfl .up (word g) (2^round) 0 recv ok⟩ :=
    ht.1.symm ▸ he
  obtain ⟨hRun,hRest⟩ := appendActualShuffle hPast hTail hn hStep
  have hInfo := roundInfo stage
  have hAt : At (advance t recv) (scanPc stage + 1)
      [(scanDst stage,recv),(scanSrc stage,word g),(1180,b32 (laneOf l g)),
        (7139,b32 p.heads), (1072,b32 (g / l.block)),
        (7196, b32 (groupLaneTiles p 0 (laneOf l g)))] := ht.set (by
    intro pair hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact hInfo.1.symm
    · exact hInfo.2.1.symm
    · exact hInfo.2.2.1.symm
    · exact (scanRoundFrame stage).2.1
    · exact (scanRoundFrame stage).2.2)
  have hArgs : At (advance t recv) (scanPc stage+1)
      [(1180,b32 (laneOf l g)),(scanSrc stage,word g),(scanDst stage,b32 (part source))] :=
    hAt.mono ⟨hAt.2.2.2.2.2.2.1,hAt.2.2.2.2.2.1,hWord ▸ hAt.2.2.2.2.1,trivial⟩
  obtain ⟨u,hCore,hu⟩ := scanFold stage l g (groupLaneTiles p 0) hlane
    (groupPrefixOperands_fit hp (Nat.zero_le p.batch) hlane stage) _ hArgs
  have hRange : 1904 ≤ scanPc stage + 1 ∧ scanPc stage + 1 + 3 ≤ 2768 := by
    have hs := stage.isLt
    unfold scanPc
    omega
  have hLocal := localRun hRange.1 hRange.2 hAt.1 (roundStraight stage) hCore
  have hFrame {r : Nat} (hr : r ∈ [1180,7139,1072,7196]) : u.regs r = (advance t recv).regs r :=
    schedulerLocalFrame (lo := scanPc stage+1) (len := 3) (scanRoundFrame stage).1
      (roundStraight stage) hCore hAt.1.ge (by rw [hAt.1]) hr
  have hPc : scanPc stage + 4 = 1960 + 4 * (round+1) := by
    simp [scanPc,stage,Nat.mul_add,Nat.add_assoc]
  have hWin : 2 * 2 ^ stage.val = 2^(round+1) := by
    simpa only [stage,Nat.pow_succ] using Nat.mul_comm 2 (2^round)
  have hOut : At u (scanPc stage+4)
      [(scanResult stage,b32 (prefixWindow (groupLaneTiles p 0) (2*2^stage.val) (laneOf l g))),
        (1180,b32 (laneOf l g)),(7139,b32 p.heads), (1072,b32 (g / l.block)),
        (7196, b32 (groupLaneTiles p 0 (laneOf l g)))] :=
    hu.mono ⟨hu.2.2.2.2.1,(hFrame (by decide)).trans hAt.2.2.2.2.2.2.1,
      (hFrame (by decide)).trans hAt.2.2.2.2.2.2.2.1,
      (hFrame (by decide)).trans hAt.2.2.2.2.2.2.2.2.1,
      (hFrame (by decide)).trans hAt.2.2.2.2.2.2.2.2.2.1, trivial⟩
  have hIndex : scanPosition p l g (round+1) = pos g + 1 := by
    simp [scanPosition, pos, Nat.add_assoc]
  unfold ScanCursor
  rw [hIndex]
  have hNextCount : ((X.tr g).take (pos g+1)).countP Execution.isShfl = 5+(round+1) := by
    rw [List.take_add_one, show (X.tr g)[pos g]? = _ from he]
    simp only [Option.toList_some,List.countP_append,List.countP_singleton]
    change ((X.tr g).take (pos g)).countP Execution.isShfl+1 = 5+(round+1)
    rw [hCount]
    omega
  exact ⟨_,_,o,len_of_get he,hNextCount,releasedIfLast he (by intro h; cases h),
    by simpa only [hPc,hWin,hInfo.2.2.2] using hOut,hRun,run_rtg hLocal,hRest⟩

private theorem completeScan (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hProtected : DrainCuQProtected p X) :
    ∀ round ≤ 5, ∀ g < l.threads, warpIndex l g = 12 → ScanCursor p l X g round := by
  intro round hRound
  induction round with
  | zero =>
    intro g hg hw
    exact scanSeed hp hMax hg hw hProtected
  | succ round ih =>
    intro g hg hw
    exact scanRound hp hMax hg (by omega) (fun h hs =>
      ih (by omega) h hs.1.2.1 (hs.2.symm.trans hw))

/-- Every lane in a maximal MMA warp obtains the first group's inclusive tile prefix
and the common total from the real full-warp broadcast. -/
theorem firstGroupScanTotalWithTiles (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X) :
    ∃ j e t o, X.get (g,j) = some e ∧ X.ShflK (g, j) 10 ∧ e.pc = 1980 ∧ e.kind = .shfl .idx
        (b32 (∑ k ∈ Finset.range (laneOf l g+1), groupLaneTiles p 0 k))
        31 31 (b32 (tilePrefix p (min p.batch 31))) true ∧
      At t 1981 [(7198,b32 (tilePrefix p (min p.batch 31))),
        (7197,b32 (∑ k ∈ Finset.range (laneOf l g+1), groupLaneTiles p 0 k)),
        (1180,b32 (laneOf l g)),(7139,b32 p.heads), (1072,b32 (g / l.block)),
        (7196, b32 (groupLaneTiles p 0 (laneOf l g)))] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  let word (h : Nat) := b32 (part (laneOf l h))
  let pos (h : Nat) := scanPosition p l h 5
  let advance (t : TState) (v : Value) := next (setReg t 7198 v)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hShape (h : Nat) (hs : SameWarp l g h) :
      ∃ s t o, pos h ≤ (X.tr h).length ∧ ((X.tr h).take (pos h)).countP Execution.isShfl = 10 ∧
        (pos h = (X.tr h).length → Step.Released l X h) ∧
        At t 1980 [(7197, word h), (1180, b32 (laneOf l h)), (7139, b32 p.heads),
          (1072, b32 (h / l.block)), (7196, b32 (groupLaneTiles p 0 (laneOf l h)))] ∧
        Run kernel Assumptions.all l h {} ((X.tr h).take (pos h)) (some s) ∧
        Run kernel Assumptions.all l h s ((X.tr h).drop (pos h)) o ∧
        Next kernel Assumptions.all l h s t
          (.shfl .idx (word h) 31 31 (fun v _ => advance t v)) := by
    obtain ⟨s,t,o,hBound,hCount,hRel,hAt,hRun,hl,hTail⟩ :=
      completeScan hp hMax hProtected 5 (by decide) h hs.1.2.1 (hs.2.symm.trans hw)
    have ht : At t 1980 [(7197, word h), (1180, b32 (laneOf l h)), (7139, b32 p.heads),
        (1072, b32 (h / l.block)), (7196, b32 (groupLaneTiles p 0 (laneOf l h)))] := hAt
    have ht' : At t 1980 [(7197,word h)] := ht.mono ⟨ht.2.2.2.2.1,trivial⟩
    exact ⟨s,t,o,hBound,hCount,hRel,ht,hRun,hTail,hl,scanTotalTemplate hp ht'⟩
  have hIssued (h : Nat) (hs : SameWarp l g h) :
      ∃ recv ok, X.get (h,pos h) = some ⟨1980,.shfl .idx (word h) 31 31 recv ok⟩ ∧
        X.ShflK (h,pos h) 10 := by
    apply Step.shfl_occurs_of_maximal hMax hBlock hs.1.2.1 pos word (fun _ => 31) (fun _ => 31)
    · intro k hk
      obtain ⟨_,_,_,_,hCount,_,_,_,_,_⟩ := hShape k (Step.sameWarp_trans hs hk)
      exact .inl (fun hNil => by rw [hNil] at hCount; simp at hCount)
    · intro k hk
      obtain ⟨s,t,o,hBound,hCount,hRel,hAt,hRun,hTail,hn⟩ := hShape k (Step.sameWarp_trans hs hk)
      exact ⟨s,t,o,_,hBound,hCount,hRel,hAt.1,hRun,hTail,hn⟩
    · intro ev h
      exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes h)
  have hgWarp : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨s,t,o,hBound,hCount,_,ht,hPast,hTail,hn⟩ := hShape g hgWarp
  obtain ⟨recv,ok,he,hOrdinal⟩ := hIssued g hgWarp
  let source := (shflSource .idx (laneOf l g) 31 31).1
  let peer := warpLane l g source
  have hlane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hSrc : shflSource .idx (laneOf l g) 31 31 = (31,true) :=
    shflSource_idx _ (by decide)
  have hBoundSrc : source < 32 := Step.shflSource_lt .idx hlane _ _
  obtain ⟨hPeer,hLane⟩ := Step.sameWarp_lane hBlock hg hBoundSrc
  obtain ⟨v,flag,hGet,hK⟩ := hIssued peer hPeer
  obtain ⟨hRecv,hOk⟩ := shfl_source_value hMax.1 he hOrdinal hGet hK
    (ShflK.not_exited hMax.1 hPeer.1.2.1 hK)
  have hLane' : laneOf l peer = 31 := by
    change laneOf l peer = source at hLane
    simpa only [source,hSrc] using hLane
  have hWord : recv = b32 (tilePrefix p (min p.batch 31)) := by
    have hFull : part 31 = tilePrefix p (min p.batch 31) := by
      unfold part
      rw [prefixWindow_warp _ (by decide : (31 : Nat) < 32)]
      have h := groupTiles_eq p (Nat.zero_le p.batch) (by decide : (32 : Nat) ≤ 32)
      simpa [tilePrefix,Nat.min_comm] using h
    simpa only [word,hLane',hFull] using hRecv
  have hFlag : ok = true := by simpa only [hSrc] using hOk
  rw [hWord, hFlag] at he
  have hStep : X.get (g,pos g) = some
      ⟨t.pc,.shfl .idx (word g) 31 31 (b32 (tilePrefix p (min p.batch 31))) true⟩ := ht.1.symm ▸ he
  obtain ⟨hRun,hRest⟩ := appendActualShuffle hPast hTail hn hStep
  have ht' : At t 1980
      [(7197,b32 (∑ k ∈ Finset.range (laneOf l g+1), groupLaneTiles p 0 k)),
        (1180,b32 (laneOf l g)),(7139,b32 p.heads), (1072,b32 (g / l.block)),
        (7196, b32 (groupLaneTiles p 0 (laneOf l g)))] := by
    simpa only [word,part,prefixWindow_warp _ hlane] using ht
  have hAfter := ht'.set (r := 7198) (v := b32 (tilePrefix p (min p.batch 31))) (by
    intro pair hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact (by decide : 7197 ≠ 7198)
    · exact (by decide : 1180 ≠ 7198)
    · exact (by decide : 7139 ≠ 7198)
    · exact (by decide : 1072 ≠ 7198)
    · exact (by decide : 7196 ≠ 7198))
  exact ⟨pos g,_,_,o,he,hOrdinal,rfl,by simp only [word,part,prefixWindow_warp _ hlane],
    hAfter,hRun,hRest⟩

/-- The first-group broadcast, with its decoded site and inclusive prefix. -/
theorem firstGroupScanTotalWithSite (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X) :
    ∃ j e t o, X.get (g,j) = some e ∧ e.pc = 1980 ∧ e.kind = .shfl .idx
        (b32 (∑ k ∈ Finset.range (laneOf l g+1), groupLaneTiles p 0 k))
        31 31 (b32 (tilePrefix p (min p.batch 31))) true ∧
      At t 1981 [(7198,b32 (tilePrefix p (min p.batch 31))),
        (7197,b32 (∑ k ∈ Finset.range (laneOf l g+1), groupLaneTiles p 0 k)),
        (1180,b32 (laneOf l g)),(7139,b32 p.heads), (1072,b32 (g / l.block))] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  obtain ⟨j, e, t, o, he, _, hs, hk, ht, hPrefix, hTail⟩ :=
    firstGroupScanTotalWithTiles hp hMax hg hw hProtected
  exact ⟨j, e, t, o, he, hs, hk, by at_select ht, hPrefix, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
