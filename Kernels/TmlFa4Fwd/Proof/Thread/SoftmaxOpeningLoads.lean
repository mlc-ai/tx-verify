-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningScore
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningCollective
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreTrace
import Kernels.TmlFa4Fwd.Proof.Safety.TmemWordSizes
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.TcMma Prologue Epilogue

private theorem holdsOpeningScoreFrame {R S : Nat → Option Value} {F : List (Nat × Value)}
    (h : Holds R F) (keep : ∀ r, firstScoreKeeps r → S r = R r)
    (hRegs : ∀ pair ∈ F, firstScoreKeeps pair.1) : Holds S F := by
  exact holdsSchedulerFrame h (fun r hr => by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact keep p.1 (hRegs p hp)) (fun _ h => List.mem_map_of_mem (f := Prod.fst) h)

/-- Every lane issues a selected score quarter, and the returned cursors have one more
Tensor Memory collective of exactly the same ordinal. The frame excludes destination registers. -/
theorem openingScoreQuarterWarpOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : LayoutInjective X) {g ordinal : Nat}
    (hg : g < l.threads) (stage : Fin 2) (quarter : Fin 4)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : ∀ lane < 32, OpeningLaneCursor l X (warpLane l g lane) (scorePc .first quarter)
      (F lane) (ends lane))
    (hCount : ∀ lane (hl : lane < 32),
      ((X.tr (warpLane l g lane)).take (cur lane hl).pos).countP isTcColl = ordinal)
    (hKeep : ∀ lane < 32, ∀ pair ∈ F lane, firstScoreKeeps pair.1)
    (hAddr : ∀ lane (hl : lane < 32), (cur lane hl).ready.regs (scoreReg .first quarter) =
      some (b32 (scoreAddress l (warpLane l g lane) stage quarter)))
    (hBytes : ∀ lane < 32, ∀ j vals, X.get (warpLane l g lane,j) = some
      ⟨scorePc .first quarter,.tc (.ld (scoreAddress l (warpLane l g lane) stage quarter)
        vals .s32x32b)⟩ →
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4) :
    ∃ after : ∀ lane < 32, OpeningLaneCursor l X (warpLane l g lane)
        (scorePc .first quarter+17) (F lane) (ends lane),
      ∀ lane (hl : lane < 32), (after lane hl).pos = (cur lane hl).pos + 1 ∧
        ((X.tr (warpLane l g lane)).take (after lane hl).pos).countP isTcColl = ordinal+1 ∧
        ∃ vals, vals.length = 32 ∧
          X.get (warpLane l g lane,(cur lane hl).pos) =
            some ⟨scorePc .first quarter,.tc (.ld
              (scoreAddress l (warpLane l g lane) stage quarter) vals .s32x32b)⟩ ∧
          (∀ k < 16, (after lane hl).ready.regs (firstScorePairReg quarter k) =
            some (joinValue (vals.getD (2*k) (b32 0)) (vals.getD (2*k+1) (b32 0)))) ∧
          (∀ r, (r < scoreWordBase quarter ∨ scoreWordBase quarter+32 ≤ r) →
            (r < firstScorePairReg quarter 0 ∨ firstScorePairReg quarter 16 ≤ r) →
            (after lane hl).ready.regs r = (cur lane hl).ready.regs r) := by
  classical
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hOccur (lane : Nat) (hl : lane < 32) :=
    firstScoreQuarterOfMaximal hp hMax hGuard hLayout (Step.sameWarp_lane hBlock hg hl).1.1.2.1
      quarter stage
      ((cur lane hl).checkpoint.mono ⟨hAddr lane hl,trivial⟩)
      (fun _ _ _ ⟨_,hw,_⟩ => Safety.tensorWroteWordBytes hp hMax.1 hw)
      (hBytes lane hl (cur lane hl).pos) (cur lane hl).recorded (cur lane hl).continuation
      (cur lane hl).localSteps (cur lane hl).positive (cur lane hl).bounded (cur lane hl).released
  choose returned ready vals hLength hEvents hReady hPack hFrame hPrefix hTail hLocal using hOccur
  have hPeer (lane : Nat) (hl : lane < 32) (peer : Nat) (hm : peer ∈ warpLanes l (thread lane)) :
      ∃ pos, X.TcK (peer,pos) ordinal := by
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm
    have hk32 : k < 32 := by
      have hk := List.mem_range.mp hk
      exact hk.trans_le (Nat.min_le_left ..)
    have hOwn := (Step.sameWarp_lane hBlock hg hl).1
    have hOther := Step.sameWarp_lane hBlock hOwn.1.2.1 hk32
    have hEq := Step.warpLane_of_sameWarp (Step.sameWarp_trans hOwn hOther.1)
    change thread (laneOf l (warpLane l (thread lane) k)) = warpLane l (thread lane) k at hEq
    rw [show laneOf l (warpLane l (thread lane) k) = k from hOther.2] at hEq
    have hTc : X.TcK (thread k,(cur k hk32).pos) ordinal :=
      ⟨⟨_,hEvents k hk32,rfl⟩,hCount k hk32⟩
    exact ⟨_,hEq ▸ hTc⟩
  let finish (lane : Nat) (hl : lane < 32) :
      OpeningLaneCursor l X (thread lane) (scorePc .first quarter+17) (F lane) (ends lane) := by
    have keep (r : Nat) (hr : firstScoreKeeps r) :
        (ready lane hl).regs r = (cur lane hl).ready.regs r := by
      have hWord : 2881 ≤ scoreWordBase quarter ∧ scoreWordBase quarter+32 ≤ 3011 := by
        fin_cases quarter <;> decide
      have hPair : 7303 ≤ firstScorePairReg quarter 0 ∧ firstScorePairReg quarter 16 ≤ 7367 := by
        fin_cases quarter <;> decide
      apply hFrame lane hl r
      · rcases hr.1 with h | h
        · exact .inl (h.trans_le hWord.1)
        · exact .inr (hWord.2.trans h)
      · rcases hr.2 with h | h
        · exact .inl (h.trans_le hPair.1)
        · exact .inr (hPair.2.trans h)
    let c := cur lane hl
    exact ⟨c.pos+1,returned lane hl,ready lane hl,Nat.succ_pos _,len_of_get (hEvents lane hl),
      openingScoreCollectiveReleased (hEvents lane hl) (hCount lane hl) (hPeer lane hl),
      hPrefix lane hl,hTail lane hl,hLocal lane hl,
      (hReady lane hl).mono (holdsOpeningScoreFrame c.checkpoint.2.2.2.2 keep (hKeep lane hl))⟩
  refine ⟨finish,fun lane hl =>
    ⟨rfl,?_,vals lane hl,hLength lane hl,hEvents lane hl,hPack lane hl,hFrame lane hl⟩⟩
  change ((X.tr (thread lane)).take ((cur lane hl).pos+1)).countP isTcColl = _
  have he : X.get (thread lane,(cur lane hl).pos) = _ := hEvents lane hl
  exact (countP_take_succ (p := isTcColl) he rfl).trans
    (congrArg (· + 1) (hCount lane hl))

private theorem openingOtherQuarterWarp {l : Launch} {X : Execution}
    {g : Nat} (stage : Fin 2) (site : Fin 2)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : ∀ lane < 32, OpeningLaneCursor l X (warpLane l g lane)
      (nextScoreOrPc site) (F lane) (ends lane))
    (hAddr : ∀ lane < 32, (2788,b32 (scoreAddress l (warpLane l g lane) stage 0)) ∈ F lane)
    (hKeep : ∀ lane < 32, ∀ pair ∈ F lane, firstScoreKeeps pair.1) :
    ∃ after : ∀ lane < 32, OpeningLaneCursor l X (warpLane l g lane)
        (scorePc .first (nextScoreOrQuarter site)) (F lane) (ends lane),
      ∀ lane (hl : lane < 32), (after lane hl).pos = (cur lane hl).pos ∧
        (after lane hl).ready.regs (scoreReg .first (nextScoreOrQuarter site)) =
          some (b32 (scoreAddress l (warpLane l g lane) stage (nextScoreOrQuarter site))) ∧
        ∀ r, r ≠ scoreReg .first (nextScoreOrQuarter site) →
          (after lane hl).ready.regs r = (cur lane hl).ready.regs r := by
  classical
  have laneStep (lane : Nat) (hl : lane < 32) :
      ∃ after : OpeningLaneCursor l X (warpLane l g lane)
          (scorePc .first (nextScoreOrQuarter site)) (F lane) (ends lane),
        after.pos = (cur lane hl).pos ∧
          after.ready.regs (scoreReg .first (nextScoreOrQuarter site)) =
            some (b32 (scoreAddress l (warpLane l g lane) stage (nextScoreOrQuarter site))) ∧
          ∀ r, r ≠ scoreReg .first (nextScoreOrQuarter site) →
            after.ready.regs r = (cur lane hl).ready.regs r := by
    let c := cur lane hl
    have hBase : At c.ready (nextScoreOrPc site)
        [(2788,b32 (scoreAddress l (warpLane l g lane) stage 0))] :=
      c.checkpoint.mono ⟨holds_mem c.checkpoint.2.2.2.2 (hAddr lane hl),trivial⟩
    obtain ⟨u,hu,hU,hFrame⟩ := nextScoreOrTrace stage site hBase
    have hReg : 2881 ≤ scoreReg .first (nextScoreOrQuarter site) ∧
        scoreReg .first (nextScoreOrQuarter site) < 3011 := by
      fin_cases site <;> decide
    have hKeepFrame (r : Nat) (hr : firstScoreKeeps r) : u.regs r = c.ready.regs r := by
      apply hFrame
      rcases hr.1 with hr | hr <;> omega
    have hFacts := holdsOpeningScoreFrame c.checkpoint.2.2.2.2 hKeepFrame (hKeep lane hl)
    let next : OpeningLaneCursor l X (warpLane l g lane)
        (scorePc .first (nextScoreOrQuarter site)) (F lane) (ends lane) :=
      ⟨c.pos,c.before,u,c.positive,c.bounded,c.released,c.recorded,c.continuation,
        c.localSteps.trans (run_rtg hu),hU.mono hFacts⟩
    exact ⟨next,rfl,hU.2.2.2.2.1,hFrame⟩
  choose after hBoundary hReg hFrame using laneStep
  exact ⟨after,fun lane hl => ⟨hBoundary lane hl,hReg lane hl,hFrame lane hl⟩⟩

/-- The four actual opening score loads and the packed registers they leave live. -/
def OpeningScoreTileLoaded (l : Launch) (X : Execution) (stage : Fin 2)
    (g start : Nat) (t : TState) : Prop :=
  ∀ quarter : Fin 4, ∃ vals : List Value, vals.length = 32 ∧
    X.get (g,start+quarter.val) = some
      ⟨scorePc .first quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
    ∀ k < 16, t.regs (firstScorePairReg quarter k) =
      some (joinValue (vals.getD (2*k) (b32 0)) (vals.getD (2*k+1) (b32 0)))

private theorem keepsEarlierScorePair (q other : Fin 4) (hOrder : q.val < other.val)
    {k : Nat} (hk : k < 16) :
    (firstScorePairReg q k < scoreWordBase other ∨
      scoreWordBase other+32 ≤ firstScorePairReg q k) ∧
    (firstScorePairReg q k < firstScorePairReg other 0 ∨
      firstScorePairReg other 16 ≤ firstScorePairReg q k) := by
  have hWord : scoreWordBase other+32 ≤ 3011 := by fin_cases other <;> decide
  unfold firstScorePairReg
  omega

private theorem scorePairOtherQuarterAddress (q : Fin 4) (k : Nat) (site : Fin 2) :
    firstScorePairReg q k ≠ scoreReg .first (nextScoreOrQuarter site) := by
  have hAddr : scoreReg .first (nextScoreOrQuarter site) < 3011 := by fin_cases site <;> decide
  unfold firstScorePairReg
  omega

/-- The successful opening score returns lead to all four recorded score loads and
the actual cursor at the first Bias poll, with the stable register frame still live. -/
theorem openingBiasPollCursorOfScoreWarp {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : LayoutInjective X)
    {g : Nat} (hg : g < l.threads) (stage : Fin 2)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : ∀ lane < 32, OpeningLaneCursor l X (warpLane l g lane) 3428 (F lane) (ends lane))
    (hCount : ∀ lane (hl : lane < 32),
      ((X.tr (warpLane l g lane)).take (cur lane hl).pos).countP isTcColl = 0)
    (hKeep : ∀ lane < 32, ∀ pair ∈ F lane, firstScoreKeeps pair.1)
    (hAddr0 : ∀ lane < 32, (2788,b32 (scoreAddress l (warpLane l g lane) stage 0)) ∈ F lane)
    (hAddr2 : ∀ lane < 32, (2789,b32 (scoreAddress l (warpLane l g lane) stage 2)) ∈ F lane)
    (hBytes : ∀ quarter : Fin 4, ∀ lane < 32, ∀ j vals, X.get (warpLane l g lane,j) = some
      ⟨scorePc .first quarter,.tc (.ld (scoreAddress l (warpLane l g lane) stage quarter)
        vals .s32x32b)⟩ →
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4) :
    ∃ after : ∀ lane < 32, OpeningLaneCursor l X (warpLane l g lane) 3498 (F lane) (ends lane),
      ∀ lane (hl : lane < 32), (after lane hl).pos = (cur lane hl).pos+4 ∧
        ((X.tr (warpLane l g lane)).take (after lane hl).pos).countP isTcColl = 4 ∧
        OpeningScoreTileLoaded l X stage (warpLane l g lane) (cur lane hl).pos
          (after lane hl).ready := by
  obtain ⟨after0,h0⟩ := openingScoreQuarterWarpOfMaximal hp hMax hGuard hLayout hg stage 0
    cur hCount hKeep
    (fun lane hl => holds_mem (cur lane hl).checkpoint.2.2.2.2 (hAddr0 lane hl)) (hBytes 0)
  obtain ⟨enter1,hEnter1⟩ := openingOtherQuarterWarp stage 0 after0 hAddr0 hKeep
  have hCount1 lane (hl : lane < 32) :
      ((X.tr (warpLane l g lane)).take (enter1 lane hl).pos).countP isTcColl = 1 := by
    rw [(hEnter1 lane hl).1]
    exact (h0 lane hl).2.1
  obtain ⟨after1,h1⟩ := openingScoreQuarterWarpOfMaximal hp hMax hGuard hLayout hg stage 1
    enter1 hCount1 hKeep (fun lane hl => (hEnter1 lane hl).2.1) (hBytes 1)
  obtain ⟨after2,h2⟩ := openingScoreQuarterWarpOfMaximal hp hMax hGuard hLayout hg stage 2
    after1 (fun lane hl => (h1 lane hl).2.1) hKeep
    (fun lane hl => holds_mem (after1 lane hl).checkpoint.2.2.2.2 (hAddr2 lane hl)) (hBytes 2)
  obtain ⟨enter3,hEnter3⟩ := openingOtherQuarterWarp stage 1 after2 hAddr0 hKeep
  have hCount3 lane (hl : lane < 32) :
      ((X.tr (warpLane l g lane)).take (enter3 lane hl).pos).countP isTcColl = 3 := by
    rw [(hEnter3 lane hl).1]
    exact (h2 lane hl).2.1
  obtain ⟨after3,h3⟩ := openingScoreQuarterWarpOfMaximal hp hMax hGuard hLayout hg stage 3
    enter3 hCount3 hKeep (fun lane hl => (hEnter3 lane hl).2.1) (hBytes 3)
  refine ⟨after3,fun lane hl => ⟨?_,(h3 lane hl).2.1,?_⟩⟩
  · rw [(h3 lane hl).1,(hEnter3 lane hl).1,(h2 lane hl).1,(h1 lane hl).1,
      (hEnter1 lane hl).1,(h0 lane hl).1]
  · intro q
    obtain ⟨vals0,hLen0,hRead0,hPack0,hKeep0⟩ := (h0 lane hl).2.2
    obtain ⟨vals1,hLen1,hRead1,hPack1,hKeep1⟩ := (h1 lane hl).2.2
    obtain ⟨vals2,hLen2,hRead2,hPack2,hKeep2⟩ := (h2 lane hl).2.2
    obtain ⟨vals3,hLen3,hRead3,hPack3,hKeep3⟩ := (h3 lane hl).2.2
    rw [(hEnter1 lane hl).1,(h0 lane hl).1] at hRead1
    rw [(h1 lane hl).1,(hEnter1 lane hl).1,(h0 lane hl).1] at hRead2
    rw [(hEnter3 lane hl).1,(h2 lane hl).1,(h1 lane hl).1,(hEnter1 lane hl).1,
      (h0 lane hl).1] at hRead3
    have keep3 (q : Fin 4) (hQ : q.val < 3) (k : Nat) (hk : k < 16) :
        (after3 lane hl).ready.regs (firstScorePairReg q k) =
          (after2 lane hl).ready.regs (firstScorePairReg q k) := by
      obtain ⟨hW,hP⟩ := keepsEarlierScorePair q 3 hQ hk
      exact (hKeep3 _ hW hP).trans
        ((hEnter3 lane hl).2.2 _ (scorePairOtherQuarterAddress q k 1))
    have keep2 (q : Fin 4) (hQ : q.val < 2) (k : Nat) (hk : k < 16) :
        (after2 lane hl).ready.regs (firstScorePairReg q k) =
          (after1 lane hl).ready.regs (firstScorePairReg q k) := by
      obtain ⟨hW,hP⟩ := keepsEarlierScorePair q 2 hQ hk
      exact hKeep2 _ hW hP
    have keep1 (k : Nat) (hk : k < 16) :
        (after1 lane hl).ready.regs (firstScorePairReg 0 k) =
          (after0 lane hl).ready.regs (firstScorePairReg 0 k) := by
      obtain ⟨hW,hP⟩ := keepsEarlierScorePair 0 1 (by decide) hk
      exact (hKeep1 _ hW hP).trans
        ((hEnter1 lane hl).2.2 _ (scorePairOtherQuarterAddress 0 k 0))
    fin_cases q
    · exact ⟨vals0,hLen0,hRead0,fun k hk =>
        (keep3 0 (by decide) k hk).trans ((keep2 0 (by decide) k hk).trans
          ((keep1 k hk).trans (hPack0 k hk)))⟩
    · exact ⟨vals1,hLen1,hRead1,fun k hk =>
        (keep3 1 (by decide) k hk).trans ((keep2 1 (by decide) k hk).trans (hPack1 k hk))⟩
    · exact ⟨vals2,hLen2,hRead2,fun k hk => (keep3 2 (by decide) k hk).trans (hPack2 k hk)⟩
    · exact ⟨vals3,hLen3,hRead3,hPack3⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
