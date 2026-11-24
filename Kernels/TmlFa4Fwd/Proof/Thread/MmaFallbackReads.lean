-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstGroupOrdinal
import Lemmas.Step.ProtectedReadProgress
import Lemmas.Kernel.ReadValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma (fallbackAbi groupScanFacts fallbackCuQReadGate
  fallbackCuQReadAddress fallbackCuQReadOut localRun)

def fallbackReadFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  (1183, b32 first) :: groupScanFacts .select first p.batch (g / l.block) ++
    (7194, b32 (tilePrefix p first * p.heads)) :: fallbackAbi p l g

private theorem fallbackReadBranch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first : Nat} {t : TState} (hFirst : first ≤ p.batch)
    (ht : At t 1993 (fallbackReadFrame p l g first)) :
    let index := first + laneOf l g
    let F := (1184, b32 index) :: (7195, b32 0) :: fallbackReadFrame p l g first
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if p.batch < index then 2000 else 1997) F := by
  dsimp only
  let index := first + laneOf l g
  let F := (1184, b32 index) :: (7195, b32 0) :: fallbackReadFrame p l g first
  obtain ⟨v, hv, hV⟩ := fallbackCuQReadGate hp g hFirst (Nat.mod_lt _ (by decide)) t
    (by at_select ht)
  have hWrites : ((kernel.code.drop 1993).take 3).all
      (fun i => ((fallbackReadFrame p l g first).map Prod.fst).all
        (fun r => !(writesRegs i.op).contains r)) = true := by
    change ((kernel.code.drop 1993).take 3).all
      (fun i => [1183, 7199, 7203, 1182, 1072, 7194, 1180, 7139, 2535, 7502, 7506, 7503].all
        (fun r => !(writesRegs i.op).contains r)) = true
    decide +kernel
  have hStraight : ((kernel.code.drop 1993).take 2).all
      (fun i => schedulerFallsThrough i.op) = true := by decide +kernel
  have hKept := holdsSchedulerFrame ht.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hStraight hv ht.1.ge (by rw [ht.1]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  have hV' : At v 1996 F := hV.mono ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.2.1, hKept⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1996 (decide (p.batch < index)) hV' hV.2.2.2.2.2.1 (by simp)
  have hPrep := localRun (pc := 1993) (n := 3) (by decide) (by decide) ht.1 hStraight hv
  have hBranch := localRun (by decide) (by decide) hV'.1 (by decide) hu
  exact ⟨u, run_comp hPrep hBranch, by simpa only [decide_eq_true_eq] using hU⟩

/-- The real fallback lane either takes its protected launch read, or uses zero without an
event when its cumulative-offset index lies past the final sentinel. -/
theorem fallbackLaneCuQReadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first pos : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    (hProtected : DrainCuQProtected p X) {t u : TState} {o : Option TState}
    (ht : At u 1993 (fallbackReadFrame p l g first))
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hPos : 0 < pos) (hLen : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    let index := first + laneOf l g
    let advance := if index ≤ p.batch then pos + 1 else pos
    ∃ before ready, advance ≤ (X.tr g).length ∧
      (advance = (X.tr g).length → Step.Released l X g) ∧
      At ready 2000 ((7195, b32 (drainCuQ p index)) :: (1184, b32 index) ::
        fallbackReadFrame p l g first) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take advance) (some before) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready ∧
      Run kernel Assumptions.all l g before ((X.tr g).drop advance) o ∧
      (index ≤ p.batch → X.get (g, pos) = some
        ⟨1999, .rd {loc := globalLoc (p.cuQBase + 4 * index), size := 4}
          ((b32 (p.qOffset index)).toBytes.map some)⟩) := by
  dsimp only
  let index := first + laneOf l g
  let F := (1184, b32 index) :: fallbackReadFrame p l g first
  obtain ⟨s, hs, hS⟩ := fallbackReadBranch hp hFirst ht
  change At s (if p.batch < index then 2000 else 1997) _ at hS
  by_cases hi : index ≤ p.batch
  · have hSA : At s 1997 F := by
      exact ⟨by simpa only [ite_eq_right (Nat.not_lt_of_ge hi)] using hS.1,
        hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2.1, hS.2.2.2.2.2.2⟩
    obtain ⟨v, hv, hV⟩ := fallbackCuQReadAddress hp g hi s (by at_select hSA)
    have hCode : ((kernel.code.drop 1997).take 2).all
        (fun i => [1184, 1183, 7199, 7203, 1182, 1072, 7194, 1180, 7139, 2535, 7502, 7506, 7503].all
          (fun r => !(writesRegs i.op).contains r)) = true := by decide +kernel
    have hStraight : ((kernel.code.drop 1997).take 1).all
        (fun i => schedulerFallsThrough i.op) = true := by decide +kernel
    have hKept := holdsSchedulerFrame hSA.2.2.2.2
      (fun _ hr => schedulerLocalFrame hCode hStraight hv hSA.1.ge (by rw [hSA.1]) hr)
      (fun _ hm => List.mem_map_of_mem hm)
    let a : Acc := {loc := globalLoc (p.cuQBase + 4 * index), size := 4}
    let word := b32 (p.qOffset index)
    have hAddress := localRun (pc := 1997) (n := 2) (by decide) (by decide) hSA.1 hStraight hv
    have hNext : Next kernel Assumptions.all l g t v (.read a (afterLoad v [7195])) :=
      ⟨(hLocal.trans (run_rtg hs)).trans (run_rtg hAddress), fallbackCuQReadOut hp hi hV⟩
    obtain ⟨he, hPrefix, hRest⟩ := Step.protected_read_of_maximal hMax hg
      (show a.size = word.bytes from rfl) (hp.cuQ index hi) (hProtected index hi)
      hNext hPast hTail hPos hLen hRelease
      (Assumptions.wf_snoc_initial hMax.1)
    have hGet : X.get (g, pos) = some ⟨1999, .rd a (word.toBytes.map some)⟩ := by
      simpa only [hV.1] using he
    have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hRead : afterLoad v [7195] (word.toBytes.map some) = next (setReg v 7195 word) := by
      rw [afterLoad_ok hV.2.1 hV.2.2.1 hRebuild]
      simp [next, setReg, hV.2.1, hV.2.2.1]
    have hFresh : ∀ pair ∈ F, pair.1 ≠ 7195 := of_decide_eq_true rfl
    have hOut := (hV.mono hKept).set (v := word) hFresh
    rw [hRead] at hPrefix hRest
    simp only [ite_eq_left (show first + laneOf l g ≤ p.batch from hi)]
    exact ⟨_, _, len_of_get hGet, releasedIfLast hGet (by intro h; cases h),
      by
        change At (next (setReg v 7195 word)) 2000 ((7195, b32 (drainCuQ p index)) :: F)
        simpa only [drainCuQ, ite_eq_left hi] using hOut,
      hPrefix, .refl, hRest,
      fun _ => hGet⟩
  · have hU : At s 2000 ((7195, b32 (drainCuQ p index)) :: F) := by
      have hPc : s.pc = 2000 := by simpa only [ite_eq_left (Nat.lt_of_not_ge hi)] using hS.1
      have hWord : drainCuQ p index = 0 := by simp [drainCuQ, hi]
      exact ⟨hPc, hS.2.1, hS.2.2.1, hS.2.2.2.1,
        hWord.symm ▸ hS.2.2.2.2.2.1, hS.2.2.2.2.1, hS.2.2.2.2.2.2⟩
    simp only [ite_eq_right (show ¬first + laneOf l g ≤ p.batch from hi)]
    exact ⟨t, s, hLen, hRelease, hU, hPast, hLocal.trans (run_rtg hs), hTail, fun h => (hi h).elim⟩

/-- The first fallback read completes in every released lane and keeps the actual
shuffle and ballot ordinals for the next group's scan. -/
theorem firstFallbackLaneReadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) (hBatch : 31 < p.batch)
    (hCut : tilePrefix p 31 * p.heads ≤ g / l.block) :
    let index := 31 + laneOf l g
    ∃ pos before ready o, 0 < pos ∧ pos ≤ (X.tr g).length ∧
      ((X.tr g).take pos).countP Execution.isShfl = 11 ∧
      ((X.tr g).take pos).countP isFullWarpVote = 0 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At ready 2000 ((7195, b32 (drainCuQ p index)) :: (1184, b32 index) ::
        fallbackReadFrame p l g 31) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready ∧
      Run kernel Assumptions.all l g before ((X.tr g).drop pos) o := by
  dsimp only
  let index := 31 + laneOf l g
  obtain ⟨pos, e, t, u, o, hPos, hLen, he, hSite, hState, hShfl, hRel, hAt, hPast, hTau, hTail⟩ :=
    firstFallbackGroupReached hp hMax hg hw hProtected hBatch hCut
  have hIndex : pos - 1 + 1 = pos := by omega
  have hVote := firstGroupBroadcastBallotCount hp hMax.1 hg hw he hSite hState
    (hIndex.symm ▸ hPast)
  rw [hIndex] at hVote
  obtain ⟨before, ready, hBound, hRel', hReady, hPast', hTau', hTail', hRead⟩ :=
    fallbackLaneCuQReadOfMaximal hp hMax hg hBatch.le hProtected
      (by at_select hAt) hPast hTau hTail hPos hLen hRel
  let advance := if index ≤ p.batch then pos + 1 else pos
  have hCounts : ((X.tr g).take advance).countP Execution.isShfl = 11 ∧
      ((X.tr g).take advance).countP isFullWarpVote = 0 := by
    by_cases hi : index ≤ p.batch
    · rw [show advance = pos + 1 by simp [advance, hi], List.take_add_one,
        show (X.tr g)[pos]? = _ from hRead hi]
      exact ⟨by simpa [Execution.isShfl] using hShfl,
        by simpa [isWarpVote, voteClass] using hVote⟩
    · simpa only [advance, ite_eq_right hi] using And.intro hShfl hVote
  have hPositive : 0 < advance := by
    dsimp only [advance]
    split_ifs <;> omega
  exact ⟨advance, before, ready, o, hPositive, hBound, hCounts.1, hCounts.2, hRel',
    hReady, hPast', hTau', hTail'⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
