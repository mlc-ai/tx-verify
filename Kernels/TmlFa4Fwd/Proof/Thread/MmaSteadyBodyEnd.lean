-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadySecondPv
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyBackedge
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseOrdinal
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadySecondPv
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyFirstQk
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Kernels.TmlFa4Fwd.Flow.Code.Part038
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread (actualFullElectionMask keyDescriptorLow)
open Thread.Mma (ReleaseIssue)

noncomputable section

private theorem bodyRegisterNot {l : Launch} {visit remaining r : Nat} {stage : Fin 2}
    (h : r ∉ secondPvRootRegs) (hq : r < 9624 ∨ 9631 < r) :
    ∀ pair ∈ steadyKeyBroadcastFrame l visit remaining ++ qDescriptorFacts l stage,
      pair.1 ≠ r := by
  intro pair hm
  rcases List.mem_append.mp hm with hm | hm
  · have hReg := List.mem_map_of_mem (f := Prod.fst) hm
    exact fun he => h (List.mem_cons_of_mem _ (he ▸ hReg))
  · exact qWordNot hq pair hm

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g visit remaining shuffles votes count : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState}
include hp hMax hg

private theorem steadyVReleaseWithPolls
    (cur : SchedulerWarpReached l X g 2459
      (fun _ => steadySecondPvFrame l visit remaining) shuffles votes ends)
    (hOrd : ElectOrdinal l X)
    (hCut : ∀ lane < 32, elections X (warpLane l g lane) (cur.pos lane) = count) :
    ∃ next : SchedulerWarpReached l X g 2463
      (fun _ => steadySecondPvFrame l visit remaining) shuffles votes ends,
      (∀ lane < 32, cur.pos lane < next.pos lane ∧
        elections X (warpLane l g lane) (next.pos lane) = count+1 ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
      ∃ issuer idx, SameWarp l g issuer ∧ ReleaseIssue X issuer idx .loopValue
        (commitSpec l issuer (l.sharedBase+8*(readyStage (2*visit+1)).val+56)) ∧
        idx+1 = next.pos (laneOf l issuer) := by
  let base := l.sharedBase+8*(readyStage (2*visit+1)).val
  have hSlot := (readyStage (2*visit+1)).isLt
  have hWidth : base+56 < 2^32 := by dsimp only [base]; have := hp.shared.2.1; omega
  have hAlign : (base+56)%8 = 0 := by dsimp only [base]; have := hp.shared.1; omega
  obtain ⟨next,hCount,issuer,idx,hWarp,hEvent,hIndex⟩ :=
    commitWarpFromOrdinalElectionWithPollCounts hp hMax hg 4 (base := base) cur hOrd count hCut
      (secondPvRegNot (by decide) (.inl (by decide)))
      (secondPvRegNot (by decide) (.inl (by decide)))
      (fun pair hm => by
        change pair.1 ∉ [2599]
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using
          secondPvRegNot (by decide) (.inl (by decide)) pair hm)
      (by
        simp [base,commitSite,steadySecondPvFrame,steadyKeyBroadcastFrame,steadyKeyFrame,
          steadyKeyRing,steadyValueFrame]) hWidth hAlign
  exact ⟨next,hCount,issuer,idx,hWarp,hEvent,hIndex⟩

private theorem steadySecondQkElectWithPolls
    (cur : SchedulerWarpReached l X g 2463
      (fun _ => steadySecondPvFrame l visit remaining) shuffles votes ends)
    (hOrd : ElectOrdinal l X)
    (hCut : ∀ lane < 32, elections X (warpLane l g lane) (cur.pos lane) = count) :
    ∃ leader : Fin 32, ∃ next : SchedulerWarpReached l X g 2465
      (fun lane => recurringQkEntry l 1 (2*visit+2) (laneOf l (warpLane l g lane) == leader) ++
        steadyKeyBroadcastFrame l visit remaining) shuffles votes ends,
      ∀ lane < 32, cur.pos lane < next.pos lane ∧
        elections X (warpLane l g lane) (next.pos lane) = count+1 ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) := by
  let F := steadyKeyBroadcastFrame l visit remaining
  let H := (2601,b32 0)::F ++ qDescriptorFacts l 0
  obtain ⟨a,hA⟩ := cur.advanceLocalWithPosition (pc' := 2464) (G := fun _ => H) (by
    intro lane hl
    have ht := cur.checkpoint lane hl
    have h := ht.mono ht.2.2.2.2.2
    let t := next (setReg (cur.state lane) 2601 (b32 0))
    have hRun : run kernel [] l (warpLane l g lane) 1 (cur.state lane) = some t := by
      apply run_local Flow.code_2463 rfl ht
      rfl
    exact ⟨t,run_rtg (localRun (by decide) (by decide) ht.1 rfl hRun),
      h.set (bodyRegisterNot (by decide) (.inl (by decide)))⟩)
  have hPred : ∀ pair ∈ H, pair.1 ≠ 9709 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · decide
    · exact bodyRegisterNot (by decide) (.inr (by decide)) pair hm
  obtain ⟨leader,b,hE⟩ := a.consumeElectionAtOrdinal hp hMax hg
    (fun lane => electState l (warpLane l g lane) (a.state lane) 10)
    (fun lane lead => (9709,.pred (laneOf l (warpLane l g lane) == lead))::H)
    hOrd count (fun lane hl => by rw [hA]; exact hCut lane hl)
    (fun lane hl => electTemplate 10 (a.checkpoint lane hl))
    (fun lane hl lead => electStateFrame 10 (a.checkpoint lane hl) lead hPred (by simp [electSite]))
  obtain ⟨out,hOut⟩ := b.advanceLocalWithPosition (pc' := 2465)
      (G := fun lane =>
        recurringQkEntry l 1 (2*visit+2) (laneOf l (warpLane l g lane) == leader) ++ F) (by
    intro lane hl
    have ht := b.checkpoint lane hl
    have hh := ht.2.2.2.2
    have hs := (holds_append ..).mp hh.2.2
    refine ⟨_,.refl,ht.mono ((holds_append ..).mpr ⟨?_,hs.1⟩)⟩
    exact ⟨hh.1,holds_lookup hs.1 rfl,holds_lookup hs.1 rfl,holds_lookup hs.1 rfl,
      hh.2.1,hs.2⟩)
  refine ⟨leader,out,fun lane hl => ?_⟩
  obtain ⟨hi,inst,he⟩ := hE lane hl
  refine ⟨by rw [hOut,hi,hA]; omega,?_,?_⟩
  · rw [hOut,hi]
    unfold elections
    rw [List.take_add_one,show (X.tr (warpLane l g lane))[a.pos lane]? = _ from he]
    simp only [Option.toList_some,List.countP_append,List.countP_cons,isElectEv,↓reduceIte,
      List.countP_nil,Nat.zero_add]
    have hCount : elections X (warpLane l g lane) (a.pos lane) = count := by
      rw [hA]
      exact hCut lane hl
    exact congrArg (·+1) hCount
  · intro other
    rw [hOut,hi]
    unfold okPolls
    rw [countP_take_succ_false (p := okPoll other) he rfl,hA]

private theorem steadySecondQkScoreWithPolls (leader : Fin 32)
    (cur : SchedulerWarpReached l X g 2465
      (fun lane => recurringQkEntry l 1 (2*visit+2) (laneOf l (warpLane l g lane) == leader) ++
        steadyKeyBroadcastFrame l visit remaining) shuffles votes ends) (hOrd : ElectOrdinal l X)
    (hCut : ∀ lane < 32, elections X (warpLane l g lane) (cur.pos lane) = count) :
    ∃ next : SchedulerWarpReached l X g 2520
      (fun _ => steadyKeyBroadcastFrame l visit remaining ++ qDescriptorFacts l 1)
      shuffles votes ends,
      (∀ lane < 32, cur.pos lane < next.pos lane ∧
        elections X (warpLane l g lane) (next.pos lane) = count+1 ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
        ∃ issuer idx, SameWarp l g issuer ∧ X.Commit (issuer,idx)
          (commitSpec l issuer (l.sharedBase+88)) ∧ idx+1 = next.pos (laneOf l issuer) := by
  obtain ⟨next,hCount,_,issuer,idx,hWarp,hCommit,hIndex⟩ :=
    recurringQkPacketAndCommitWithPollCounts hp hMax hg 1 leader
      (base := l.sharedBase+88) cur (by
        change ((kernel.code.drop 2465).take 43).all
          (fun ins =>
            ([2600,2571,1193,1192,2572,2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,
              2615,2618,1190,1062,2574,2602,9632,1188] : List Nat).all
              fun r => !(writesRegs ins.op).contains r) = true
        decide +kernel) hOrd count hCut
      (bodyRegisterNot (by decide) (.inl (by decide)))
      (bodyRegisterNot (by decide) (.inl (by decide)))
      (fun pair hm => by
        change pair.1 ∉ [2603]
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using
          bodyRegisterNot (by decide) (.inl (by decide)) pair hm)
      (by
        simp [steadyKeyBroadcastFrame,steadyKeyFrame,steadyKeyRing,steadyValueFrame,
          steadyFrame,steadyPorts,recurringKeyBlock,qkCommitSite,commitSite])
      (by change l.sharedBase+88+0 < 2^32; have := hp.shared.2.1; omega)
      (by change (l.sharedBase+88+0)%8 = 0; have := hp.shared.1; omega)
  exact ⟨next,hCount,issuer,idx,hWarp,⟨2519,hCommit⟩,hIndex⟩

private theorem steadyKReleaseWithPolls
    (cur : SchedulerWarpReached l X g 2520
      (fun _ => steadyKeyBroadcastFrame l visit remaining ++ qDescriptorFacts l 1)
      shuffles votes ends) (hOrd : ElectOrdinal l X)
    (hCut : ∀ lane < 32, elections X (warpLane l g lane) (cur.pos lane) = count) :
    ∃ done : SchedulerWarpReached l X g 2524
      (fun _ => steadyBackedgeFrame l visit remaining ++ steadyIterationRoots l)
      shuffles votes ends,
      (∀ lane < 32, cur.pos lane < done.pos lane ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (done.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
      ∃ issuer idx, SameWarp l g issuer ∧ ReleaseIssue X issuer idx .loopKey
        (commitSpec l issuer (l.sharedBase+8*(readyStage (2*visit+2)).val+56)) ∧
        idx+1 = done.pos (laneOf l issuer) := by
  let base := l.sharedBase+8*(readyStage (2*visit+2)).val
  have hSlot := (readyStage (2*visit+2)).isLt
  have hWidth : base+56 < 2^32 := by dsimp only [base]; have := hp.shared.2.1; omega
  have hAlign : (base+56)%8 = 0 := by dsimp only [base]; have := hp.shared.1; omega
  obtain ⟨next,hCount,issuer,idx,hWarp,hEvent,hIndex⟩ :=
    commitWarpFromOrdinalElectionWithPollCounts hp hMax hg 6 (base := base) cur hOrd count hCut
      (bodyRegisterNot (by decide) (.inl (by decide)))
      (bodyRegisterNot (by decide) (.inl (by decide)))
      (fun pair hm => by
        change pair.1 ∉ [2604]
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using
          bodyRegisterNot (by decide) (.inl (by decide)) pair hm)
      (by
        simp [base,commitSite,steadyKeyBroadcastFrame,steadyKeyFrame]) hWidth hAlign
  have hLocal : ∃ done : SchedulerWarpReached l X g 2524
      (fun _ => steadyBackedgeFrame l visit remaining ++ steadyIterationRoots l)
      shuffles votes ends, done.pos = next.pos := by
    apply next.advanceLocalWithPosition
    intro lane hl
    have ht := next.checkpoint lane hl
    have H := (holds_append ..).mp ht.2.2.2.2
    have hScalars : Holds (next.state lane).regs (steadyQkScalars l) :=
      ⟨holds_lookup H.1 rfl,holds_lookup H.1 rfl,holds_lookup H.1 rfl,holds_lookup H.1 rfl,
        holds_lookup H.1 rfl,trivial⟩
    have hControl : Holds (next.state lane).regs (steadyBackedgeFrame l visit remaining) :=
      ⟨holds_lookup H.1 rfl,holds_lookup H.1 rfl,holds_lookup H.1 rfl,
        holds_lookup H.1 rfl,holds_lookup H.1 rfl,holds_lookup H.1 rfl,holds_lookup H.1 rfl,
        holds_lookup H.1 rfl,holds_lookup H.1 rfl,holds_lookup H.1 rfl,trivial⟩
    exact ⟨_,.refl,ht.mono ((holds_append ..).mpr
      ⟨hControl,(holds_append ..).mpr ⟨hScalars,H.2⟩⟩)⟩
  obtain ⟨done,hDone⟩ := hLocal
  refine ⟨done,?_,issuer,idx,hWarp,hEvent,by rw [hDone]; exact hIndex⟩
  intro lane hl
  rw [hDone]
  exact ⟨(hCount lane hl).1,(hCount lane hl).2.2⟩

variable (hRemaining : 2 ≤ remaining) (hBound : remaining < 2^32)
    (cur : SchedulerWarpReached l X g 2459
      (fun _ => steadySecondPvFrame l visit remaining) shuffles votes ends)
    (hCut : ∀ lane < 32, elections X (warpLane l g lane) (cur.pos lane) = count)
include hRemaining hBound cur hCut

/-- From the second PV packet, the steady MMA body returns the V slot, issues the
second QK score, returns the K slot, then selects its repeating or terminal successor. -/
theorem steadyBodyEndWithPollCounts :
    ∃ done : SchedulerWarpReached l X g (if 2 < remaining then 2291 else 2534)
      (fun _ => steadyFrame l (visit+1) (remaining-1) ++ steadyIterationRoots l)
      shuffles votes ends,
    (∀ lane < 32, cur.pos lane < done.pos lane ∧
      ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (done.pos lane)) =
        okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
    (∃ issuer idx, SameWarp l g issuer ∧ ReleaseIssue X issuer idx .loopValue
      (commitSpec l issuer (l.sharedBase+8*(readyStage (2*visit+1)).val+56)) ∧
      cur.pos (laneOf l issuer) ≤ idx ∧ idx < done.pos (laneOf l issuer)) ∧
    (∃ issuer idx, SameWarp l g issuer ∧ X.Commit (issuer,idx)
      (commitSpec l issuer (l.sharedBase+88)) ∧ idx < done.pos (laneOf l issuer)) ∧
    (∃ issuer idx, SameWarp l g issuer ∧ ReleaseIssue X issuer idx .loopKey
      (commitSpec l issuer (l.sharedBase+8*(readyStage (2*visit+2)).val+56)) ∧
      idx+1 = done.pos (laneOf l issuer)) := by
  have hOrd : ElectOrdinal l X := electOrdinal hMax.1
    (ElectMutual.of_full (fun e => actualFullElectionMask hMax.1 e))
  obtain ⟨v,hV,vi,vj,hVs,hVe,hVi⟩ := steadyVReleaseWithPolls hp hMax hg cur hOrd hCut
  obtain ⟨leader,a,hA⟩ := steadySecondQkElectWithPolls hp hMax hg v hOrd
    (fun lane hl => (hV lane hl).2.1)
  obtain ⟨b,hB,si,sj,hSs,hSe,hSi⟩ := steadySecondQkScoreWithPolls hp hMax hg leader a hOrd
    (fun lane hl => (hA lane hl).2.1)
  obtain ⟨next,hK,ki,kj,hKs,hKe,hKi⟩ := steadyKReleaseWithPolls hp hMax hg b hOrd
    (fun lane hl => (hB lane hl).2.1)
  obtain ⟨done,hDone⟩ := steadyBackedgeReachedFramedWithPosition hRemaining hBound next (by
    rw [steadyIterationRoots_regs]
    decide +kernel)
  refine ⟨done,?_,⟨vi,vj,hVs,hVe,?_⟩,⟨si,sj,hSs,hSe,?_⟩,ki,kj,hKs,hKe,?_⟩
  · intro lane hl
    rw [hDone]
    refine ⟨(hV lane hl).1.trans ((hA lane hl).1.trans ((hB lane hl).1.trans (hK lane hl).1)),?_⟩
    intro other
    rw [(hK lane hl).2 other,(hB lane hl).2.2 other,(hA lane hl).2.2 other,(hV lane hl).2.2 other]
  · rw [hDone]
    let lane := laneOf l vi
    have hl : lane < 32 := Nat.mod_lt _ (by decide)
    have hv : vj+1 = v.pos lane := hVi
    refine ⟨?_,?_⟩
    · have h := (hV lane hl).1
      change cur.pos lane ≤ vj
      omega
    · exact (show vj < v.pos lane by omega).trans
        ((hA lane hl).1.trans ((hB lane hl).1.trans (hK lane hl).1))
  · rw [hDone]
    let lane := laneOf l si
    have hl : lane < 32 := Nat.mod_lt _ (by decide)
    exact (show sj < b.pos lane by change sj < b.pos (laneOf l si); omega).trans (hK lane hl).1
  · rw [hDone]
    exact hKi

end
end PTX.Kernels.TmlFa4Fwd.Mma
