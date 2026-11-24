-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotProgress
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainFinish
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainGroup
import Kernels.TmlFa4Fwd.Flow.Code.Part048
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

def finalDrainBallotFrame (n lane lanePrefix tiles : Nat) : List (Nat × Value) :=
  [(332,.pred (decide (lane < n))),(7233,b32 lanePrefix),(7232,b32 tiles),(1062,b32 13)]

def finalDrainIndexFrame (n lanePrefix tiles : Nat) : List (Nat × Value) :=
  [(1214,b32 n),(333,.pred (decide (n = 0))),(7233,b32 lanePrefix),(7232,b32 tiles),(1062,b32 13)]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

/-- The final full-mask ballot occurs in every lane and supplies the same selected index. -/
theorem SchedulerWarpReached.finalDrainBallotOfMaximal {g n shuffles votes : Nat}
    (hg : g < l.threads) (hn : n < 32) {lanePrefix tiles : Nat → Nat} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3092
      (fun lane => finalDrainBallotFrame n lane (lanePrefix lane) (tiles lane))
        shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 3095
      (fun lane => finalDrainIndexFrame n (lanePrefix lane) (tiles lane))
        shuffles (votes+1) ends) := by
  let thread := warpLane l g
  let hit := fun lane => decide (lane < n)
  let post := fun lane (word : BitVec 32) => next (setReg (cur.state lane) 2446 (b32 word.toNat))
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel Assumptions.all l (thread lane) (cur.before lane) (cur.state lane)
        (.vote (2^32-1) (hit lane) (post lane)) := by
    have ht := cur.checkpoint lane hl
    have hEq : out kernel Assumptions.all l (thread lane) (cur.state lane) =
        out kernel [] l (thread lane) (cur.state lane) :=
      epilogue_out_all_eq_nil (.inl (by rw [ht.1]; decide))
    exact ⟨cur.localSteps lane hl,hEq.trans
      (drainBallotTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1)⟩
  have hSuffix := cur.ballotSuffix hp hMax hg hit post hNext
  have hRecorded (lane : Nat) : ∃ word, lane < 32 →
      X.get (thread lane,cur.pos lane) = some ⟨3092,.vote (2^32-1) (hit lane) word⟩ ∧
      Run kernel Assumptions.all l (thread lane) (post lane word)
        ((X.tr (thread lane)).drop (cur.pos lane+1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨word,he,_,hr⟩ := (hNext lane hl).ballot_at_nonempty
        (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.vote lane hl)
      exact ⟨word,fun _ => ⟨by rwa [(cur.checkpoint lane hl).1] at he,hr⟩⟩
    · exact ⟨0,fun hh => (hl hh).elim⟩
  choose word seen using hRecorded
  obtain ⟨hK,_,hOrdinal⟩ := cur.ordinals.ballot (fun _ => 3092) hit word
    (fun lane hl => (seen lane hl).1)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hAdvance (lane : Nat) : ∃ u, lane < 32 →
      At u 3095 (finalDrainIndexFrame n (lanePrefix lane) (tiles lane)) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane))
        (post lane (word lane)) u := by
    by_cases hl : lane < 32
    · have hSame := Step.sameWarp_lane hBlock hg hl
      obtain ⟨u,hu,hLocal⟩ := drainBallotLocal hMax.1 hn (cur.checkpoint lane hl)
        (seen lane hl).1 (hK lane hl) (by
          intro peer hp
          refine ⟨cur.pos peer,word peer,?_⟩
          have heq : thread lane - laneOf l (thread lane) + peer = thread peer := by
            rw [show laneOf l (thread lane) = lane from hSame.2]
            unfold thread warpLane
            omega
          rw [heq]
          exact ⟨(seen peer hp).1,hK peer hp⟩)
      exact ⟨u,fun _ => ⟨hu,hLocal⟩⟩
    · exact ⟨cur.state lane,fun hh => (hl hh).elim⟩
  choose arrived hArrived using hAdvance
  let result : SchedulerWarpAt l X g 3095
      (fun lane => finalDrainIndexFrame n (lanePrefix lane) (tiles lane)) shuffles (votes+1) ends :=
    ⟨fun lane => cur.pos lane+1,fun lane => post lane (word lane),arrived,hOrdinal,
      fun lane hl => (seen lane hl).2,fun lane hl => (hArrived lane hl).2,
      fun lane hl => (hArrived lane hl).1⟩
  refine ⟨⟨result,fun _ _ => Nat.succ_pos _,fun lane hl => len_of_get (seen lane hl).1,
    fun lane hl => releasedIfLast (seen lane hl).1 (by intro h; cases h),?_⟩⟩
  intro lane hl
  have he := (seen lane hl).1
  have hLen : cur.pos lane < (X.tr (thread lane)).length := len_of_get he
  change Run kernel Assumptions.all l (thread lane) {}
    ((X.tr (thread lane)).take (cur.pos lane+1)) (some (post lane (word lane)))
  rw [List.take_succ_eq_append_getElem hLen,(List.getElem?_eq_some_iff.mp he).2]
  exact (cur.recorded lane hl).snoc (cur.localSteps lane hl)
    ⟨_,(hNext lane hl).stop,word lane,by rw [(cur.checkpoint lane hl).1],rfl⟩

/-- The final selected-index exchange is followed by the actual output lane exit. -/
private theorem selectedIndexExits {g n shuffles votes : Nat} (hg : g < l.threads) (hn : n < 32)
    {tiles : Nat → Nat} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3098
      (fun lane => [(7232,b32 (tiles lane)),(1214,b32 n),(1062,b32 13)])
      shuffles votes ends) :
    ∀ lane < 32, Thread.Exited X (warpLane l g lane) := by
  obtain ⟨after⟩ := cur.consumeShuffle (dst := 2449) hp hMax hg .idx
    (fun lane => b32 (tiles lane)) (fun _ => n) (fun _ => 31)
    (by
      intro lane _ item hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact of_decide_eq_true rfl)
    (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hModel : out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
          out kernel [] l (warpLane l g lane) (cur.state lane) :=
        epilogue_out_all_eq_nil (.inl (by rw [ht.1]; decide))
      exact hModel.trans (drainTailShuffle hp false _ _ _ _ hn
        ht.1 ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2.1))
  intro lane hl
  have ht := after.checkpoint lane hl
  obtain ⟨u,hU,hn⟩ := tailExitNext l (warpLane l g lane) (after.state lane)
    ht.1 ht.2.2.2.1 ht.2.2.2.2.2.2.2.1
  have hLane := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.1
  have hNext : Next kernel Assumptions.all l (warpLane l g lane) (after.before lane) u .exit :=
    ⟨(after.localSteps lane hl).trans hn.steps,hn.stop⟩
  have he := Thread.exitAtMaximalCursor hMax hLane
    (after.positive lane hl) (after.bounded lane hl) (after.recorded lane hl)
    (after.continuation lane hl) hNext (after.released lane hl)
  rw [hU] at he
  exact ⟨after.pos lane,⟨9205,.exit⟩,he,rfl⟩

/-- The selected request's optional previous-index exchange and final selected exchange return
every lane of the output warp. -/
theorem SchedulerWarpReached.finalDrainIndexExits {g n shuffles votes : Nat} (hg : g < l.threads)
    (hn : n < 32) {lanePrefix tiles : Nat → Nat} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3095
      (fun lane => finalDrainIndexFrame n (lanePrefix lane) (tiles lane)) shuffles votes ends) :
    ∀ lane < 32, Thread.Exited X (warpLane l g lane) := by
  let selected := fun lane => [(7232,b32 (tiles lane)),(1214,b32 n),(1062,b32 13)]
  have hBranch (lane : Nat) (hl : lane < 32) :=
    let t := cur.state lane
    let ht := cur.checkpoint lane hl
    epilogueLocalStep (by rw [ht.1]; decide) (by rw [ht.1]; decide)
      (drainBallotBranch l (warpLane l g lane) t _ ht.1 ht.2.2.2.1 ht.2.2.2.2.2.1)
  by_cases hZero : n = 0
  · obtain ⟨next⟩ := cur.advanceLocal (pc' := 3098) (G := selected) (by
      intro lane hl
      let t := cur.state lane
      let u := { t with pc := 3098 }
      have ht := cur.checkpoint lane hl
      have hTau : Tau kernel Assumptions.all l (warpLane l g lane) t u := by
        apply tauStep_iff.mp
        simpa only [u,hZero,decide_true,ite_true] using hBranch lane hl
      exact ⟨u,.single hTau,rfl,ht.2.1,ht.2.2.1,ht.2.2.2.1,
        ht.2.2.2.2.2.2.2.1,ht.2.2.2.2.1,ht.2.2.2.2.2.2.2.2.1,trivial⟩)
    exact selectedIndexExits hp hMax hg hn next
  · let nPrev := n - 1
    let carry := fun lane => [(2447,b32 nPrev),(7233,b32 (lanePrefix lane))] ++ selected lane
    obtain ⟨before⟩ := cur.advanceLocal (pc' := 3097) (G := carry) (by
      intro lane hl
      let thread := warpLane l g lane
      let t := cur.state lane
      let u := skip t
      have ht := cur.checkpoint lane hl
      have hTau : Tau kernel Assumptions.all l thread t u := by
        apply tauStep_iff.mp
        simpa only [u,hZero,decide_false,Bool.false_eq_true,ite_false] using hBranch lane hl
      have hPc : u.pc = 3096 := by simp [u,skip,t,ht.1]
      have hU : At u 3096 [(1214,b32 n)] :=
        ⟨hPc,rfl,rfl,ht.2.2.2.1,ht.2.2.2.2.1,trivial⟩
      obtain ⟨v,hvRun,hV⟩ := drainPreviousLane l thread (by omega) hn u hU
      obtain ⟨hvAll,hFrame,_,_⟩ := epilogueLinearRun (F := [2447]) (t := u) (n := 1)
        (by omega) (by omega) (by omega) (by
          intro _
          rw [hPc]
          exact ⟨_,Flow.code_3096,by simp [writesRegs]⟩) hU.2.1 hU.2.2.1 hvRun
      refine ⟨v,(Relation.ReflTransGen.single hTau).trans (run_rtg hvAll),hV.mono ?_⟩
      exact ⟨hV.2.2.2.2.1,
        (hFrame 7233 (by decide)).trans ht.2.2.2.2.2.2.1,
        (hFrame 7232 (by decide)).trans ht.2.2.2.2.2.2.2.1,
        (hFrame 1214 (by decide)).trans ht.2.2.2.2.1,
        (hFrame 1062 (by decide)).trans ht.2.2.2.2.2.2.2.2.1,trivial⟩)
    obtain ⟨after⟩ := before.consumeShuffle (dst := 2448) hp hMax hg .idx
      (fun lane => b32 (lanePrefix lane)) (fun _ => nPrev) (fun _ => 31)
      (by
        intro lane _ item hi
        simp only [carry,selected,List.cons_append,List.nil_append,List.mem_cons,
          List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl)
      (by
        intro lane hl
        have ht := before.checkpoint lane hl
        have hModel : out kernel Assumptions.all l (warpLane l g lane) (before.state lane) =
            out kernel [] l (warpLane l g lane) (before.state lane) :=
          epilogue_out_all_eq_nil (.inl (by rw [ht.1]; decide))
        exact hModel.trans (drainTailShuffle hp true _ _ _ _ (by omega)
          ht.1 ht.2.2.2.1 ht.2.2.2.2.2.1 ht.2.2.2.2.1))
    obtain ⟨next⟩ := after.advanceLocal (G := selected) (pc' := 3098) (by
      intro lane hl
      have ht := after.checkpoint lane hl
      exact ⟨_,.refl,ht.mono ht.2.2.2.2.2.2.2⟩)
    exact selectedIndexExits hp hMax hg hn next

/-- A nonempty drain group containing the CTA issues the terminal ballot and exits in all lanes. -/
theorem SchedulerWarpReached.selectedDrainGroupExits {g first cta shuffles votes : Nat}
    (hg : g < l.threads) (hc : cta < l.grid) (hFirst : first < p.batch)
    (hLow : tilePrefix p first * p.heads ≤ cta)
    (hHigh : cta < tilePrefix p (min p.batch (first + 31)) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3086 (drainFinishFacts p first cta) shuffles votes ends) :
    ∀ lane < 32, Thread.Exited X (warpLane l g lane) := by
  let tiles := groupLaneTiles p first
  let lanePrefix := drainPrefix p first
  let count := lanePrefix 31
  let base := tilePrefix p first * p.heads
  have hBound (lane : Nat) (hl : lane < 32) : lanePrefix lane ≤ count := by
    have h := prefixWindow_le_warp tiles 32 hl
    simpa only [prefixWindow_warp _ hl,lanePrefix,count,drainPrefix] using h
  have hCount : count < 2^31 := by
    have h := hp.groupWindow_signed hFirst.le (show 31 < 32 by decide) 32
    simpa only [prefixWindow_warp _ (show 31 < 32 by decide),count,lanePrefix,drainPrefix] using h
  have hEndEq : base + count * p.heads =
      tilePrefix p (min p.batch (first + 31)) * p.heads := by
    have hSum := groupTiles_eq p hFirst.le (show 32 ≤ 32 by decide)
    change tilePrefix p first + count = tilePrefix p (min p.batch (first + 31)) at hSum
    change tilePrefix p first * p.heads + count * p.heads = _
    rw [← Nat.add_mul,hSum]
  have hEnd : base + count * p.heads < 2^31 := by
    rw [hEndEq]
    exact hp.prefixWork_signed (Nat.min_le_left _ _)
  obtain ⟨batch,⟨hStart,hGroup,hBatch,hLo,hHi⟩,_⟩ := groupContains_request p hLow hHigh
  let n := batch-first
  have hn : n < 32 := by dsimp [n]; omega
  have hThreshold (lane : Nat) (hl : lane < 32) :
      base + lanePrefix lane * p.heads ≤ cta ↔ lane < n := by
    change tilePrefix p first * p.heads + lanePrefix lane * p.heads ≤ cta ↔ _
    rw [← Nat.add_mul]
    change (tilePrefix p first + ∑ i ∈ Finset.range (lane+1), groupLaneTiles p first i) *
      p.heads ≤ cta ↔ _
    exact (groupBallot_iff p hStart hGroup hBatch hl hLo hHi).trans (by dsimp [n]; omega)
  obtain ⟨atBallot⟩ := cur.advanceLocal (pc' := 3092)
    (G := fun lane => finalDrainBallotFrame n lane (lanePrefix lane) (tiles lane)) (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have ht' : At (cur.state lane) 3086 [(7235,b32 first),(7147,b32 p.batch),
          (7234,b32 count),(7138,b32 p.heads),(7236,b32 (base+count*p.heads)),
          (7233,b32 (lanePrefix lane)),(1072,b32 cta),(7232,b32 (tiles lane)),(1062,b32 13)] := by
        rw [hEndEq]
        exact ht
      obtain ⟨u,hu,hSteps⟩ := drainGroupToBallot hp hFirst (hBound lane hl)
        hCount (hc.trans hp.grid.2.2) hEnd ht'
      have hDec : decide (base + lanePrefix lane * p.heads ≤ cta) = decide (lane < n) := by
        by_cases h : lane < n
        · simp [h,(hThreshold lane hl).2 h]
        · have hNot : ¬ base + lanePrefix lane * p.heads ≤ cta := h ∘ (hThreshold lane hl).1
          simp [h,hNot]
      rw [hDec] at hu
      exact ⟨u,hSteps,hu⟩)
  obtain ⟨atIndex⟩ := atBallot.finalDrainBallotOfMaximal hp hMax hg hn
  exact atIndex.finalDrainIndexExits hp hMax hg hn

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
