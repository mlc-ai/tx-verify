-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyKeyWait
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyRoots
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyQkCommit
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondScoreIssue
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Kernels.TmlFa4Fwd.Proof.MmaQkBroadcast
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Flow.Code.Part036

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread (keyDescriptorLow electionCountAtMatchedShuffle actualFullElectionMask)

noncomputable section

def steadyValueCarry (l : Launch) (visit : Nat) (keep : Bool) : List (Nat × Value) :=
  if keep then [(2595,b32 (valueDescriptorLow l (2*visit+1)))] else []

private def steadyValueCarryRegs (keep : Bool) : List Nat := if keep then [2595] else []

def steadyFirstQkFrame (l : Launch) (visit remaining : Nat) (keepValue : Bool := false) :
    List (Nat × Value) :=
  steadyKeyFrame l visit remaining ++ steadyQkScalars l ++ steadyValueCarry l visit keepValue ++
    qDescriptorFacts l 1

def steadyKeyBroadcastFrame (l : Launch) (visit remaining : Nat) (keepValue : Bool := false) :
    List (Nat × Value) :=
  (2600,b32 (keyDescriptorLow l (2*visit+2))) ::
    (steadyKeyFrame l visit remaining ++ steadyQkScalars l ++ steadyValueCarry l visit keepValue)

private theorem steadyKeyDescriptorSetup {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g visit remaining : Nat} {keep : Bool} {t : TState}
    (ht : At t 2355 (steadyFirstQkFrame l visit remaining keep)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2361 ((2592,b32 (keyDescriptorLow l (2*visit+2)))::
        steadyFirstQkFrame l visit remaining keep) := by
  let use := 2*visit+2
  have hInput : At t 2355
      [(1192,b32 (kvSlot use)),(2535,b32 l.sharedBase),(1062,b32 12)] :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
      holds_lookup ht.2.2.2.2 rfl,trivial⟩
  obtain ⟨u,hu,hU⟩ := (Thread.keyDescriptorLocal hp g use).apply hInput
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep ht (by decide) (by decide) (by
    have hRegs : (steadyFirstQkFrame l visit remaining keep).map Prod.fst =
        [2571,1193,1192,2572,2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,2615,
          2618,1190,1062,2574,2602,9632,1188] ++ steadyValueCarryRegs keep ++
          [9624,9625,9626,9627,9628,9629,9630,9631] := by
      cases keep <;> rfl
    rw [hRegs]
    cases keep <;> decide +kernel) (by decide +kernel) hu
  exact ⟨u,hPath,hU.mono ⟨hU.2.2.2.2.1,hKeep⟩⟩

private theorem qWordNot {l : Launch} {stage : Fin 2} {r : Nat} (hr : r < 9624 ∨ 9631 < r) :
    ∀ pair ∈ qDescriptorFacts l stage, pair.1 ≠ r := by
  intro pair hm
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
  change 9624+i.val ≠ r
  have := i.isLt
  omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g visit remaining shuffles votes : Nat}
    {keep : Bool} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2355 (fun _ => steadyFirstQkFrame l visit remaining keep)
      shuffles votes ends)
include hp hMax hg cur

private theorem firstQkReadyWithPolls :
    ∃ leader : Fin 32, ∃ count : Nat, ∃ out : SchedulerWarpReached l X g 2364
      (fun lane => recurringQkEntry l 0 (2*visit+2) (laneOf l (warpLane l g lane) == leader) ++
        steadyKeyBroadcastFrame l visit remaining keep) (shuffles+1) votes ends,
      ∀ lane < 32, cur.pos lane ≤ out.pos lane ∧
        elections X (warpLane l g lane) (out.pos lane) = count ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (out.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) := by
  let use := 2*visit+2
  let word := keyDescriptorLow l use
  let F := steadyFirstQkFrame l visit remaining keep
  obtain ⟨s,hStartPos⟩ := cur.advanceLocalWithPosition
    (G := fun _ => (2592,b32 word)::F)
    (fun lane hl => steadyKeyDescriptorSetup hp (g := warpLane l g lane) (cur.checkpoint lane hl))
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hDistinct (r : Nat) (hr : r ∉ [2592,2571,1193,1192,2572,2568,1191,7207,7208,7205,7206,7204,
      2535,2610,2614,2615,2618,1190,1062,2574,2602,9632,1188] ++ steadyValueCarryRegs keep)
      (hWord : r < 9624 ∨ 9631 < r) :
      ∀ pair ∈ (2592,b32 word)::F, pair.1 ≠ r := by
    intro pair hm
    have h : pair ∈ (2592,b32 word) ::
        (steadyKeyFrame l visit remaining ++ steadyQkScalars l ++ steadyValueCarry l visit keep) ∨
        pair ∈ qDescriptorFacts l 1 := by
      change pair ∈ ((2592,b32 word)::(steadyKeyFrame l visit remaining ++ steadyQkScalars l ++
        steadyValueCarry l visit keep)) ++ qDescriptorFacts l 1 at hm
      exact List.mem_append.mp hm
    rcases h with h | h
    · have hReg := List.mem_map_of_mem (f := Prod.fst) h
      exact fun he => hr (by cases keep <;> exact he ▸ hReg)
    · exact qWordNot hWord pair h
  obtain ⟨broadcast,hEvents⟩ := s.consumeShuffleWithEvents (dst := 2600) hp hMax hg .idx
    (fun _ => b32 word) (fun _ => 0) (fun _ => 31)
    (fun _ _ => hDistinct 2600 (by cases keep <;> decide) (.inl (by decide))) (by
      intro lane hl
      exact laneZeroBroadcast hp (by decide)
        ((s.checkpoint lane hl).mono ⟨(s.checkpoint lane hl).2.2.2.2.1,trivial⟩) Flow.code_2361)
  let G := (2600,b32 word)::(2592,b32 word)::F
  let H := (2573,b32 0)::G
  obtain ⟨before,hBefore⟩ := broadcast.advanceLocalWithPosition (pc' := 2363) (G := fun _ => H) (by
    intro lane hl
    have ht := broadcast.checkpoint lane hl
    let t := next (setReg (broadcast.state lane) 2573 (b32 0))
    have hRun : run kernel [] l (warpLane l g lane) 1 (broadcast.state lane) = some t := by
      apply run_local Flow.code_2362 rfl ht
      rfl
    have hLocal := localRun (by decide) (by decide) ht.1 rfl hRun
    refine ⟨t,run_rtg hLocal,ht.set ?_⟩
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hz
    · change (2600 : Nat) ≠ 2573; decide
    · exact hDistinct 2573 (by cases keep <;> decide) (.inl (by decide)) pair hz)
  let n := elections X (warpLane l g 0) (s.pos 0)
  have hCut (lane : Nat) (hl : lane < 32) :
      elections X (warpLane l g lane) (before.pos lane) = n := by
    obtain ⟨hi,recv,ok,he,hk⟩ := hEvents lane hl
    obtain ⟨_,recv',ok',he',hk'⟩ := hEvents 0 (by decide)
    have hSame := Step.sameWarp_trans (sameWarp_symm (Step.sameWarp_lane hBlock hg hl).1)
      (Step.sameWarp_lane hBlock hg (show 0 < 32 by decide)).1
    have hCounts := electionCountAtMatchedShuffle hMax.1 hSame he hk he' hk'
    rw [hBefore,hi]
    unfold elections
    rw [countP_take_succ_false he rfl]
    exact hCounts
  have hFresh : ∀ pair ∈ H, pair.1 ≠ 9682 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | h
    · change (2573 : Nat) ≠ 9682; decide
    · rcases List.mem_cons.mp h with rfl | h
      · change (2600 : Nat) ≠ 9682; decide
      · exact hDistinct 9682 (by cases keep <;> decide) (.inr (by decide)) pair h
  have hOrd : ElectOrdinal l X := electOrdinal hMax.1
    (ElectMutual.of_full (fun e => actualFullElectionMask hMax.1 e))
  obtain ⟨leader,after,hElect⟩ := before.consumeElectionAtOrdinal hp hMax hg
    (fun lane => electState l (warpLane l g lane) (before.state lane) 6)
    (fun lane lead => (9682,.pred (laneOf l (warpLane l g lane) == lead))::H)
    hOrd n hCut (fun lane hl => electTemplate 6 (before.checkpoint lane hl))
    (fun lane hl lead => electStateFrame 6 (before.checkpoint lane hl) lead hFresh
      (by simp [electSite]))
  obtain ⟨out,hOutPos⟩ := after.advanceLocalWithPosition (pc' := 2364)
    (G := fun lane => recurringQkEntry l 0 use (laneOf l (warpLane l g lane) == leader) ++
      steadyKeyBroadcastFrame l visit remaining keep) (by
    intro lane hl
    have ht := after.checkpoint lane hl
    let hs := ht.2.2.2.2
    have hLive : Holds (after.state lane).regs
        (steadyKeyFrame l visit remaining ++ steadyQkScalars l ++ steadyValueCarry l visit keep ++
          qDescriptorFacts l 1) :=
      hs.2.2.2.2
    have hParts := (holds_append ..).mp hLive
    refine ⟨_,.refl,ht.mono ((holds_append ..).mpr ⟨?_,?_⟩)⟩
    · exact ⟨hs.1,holds_lookup hParts.1 rfl,hs.2.2.1,holds_lookup hParts.1 rfl,hs.2.1,hParts.2⟩
    · exact ⟨hs.2.2.1,hParts.1⟩)
  refine ⟨leader,n+1,out,fun lane hl => ?_⟩
  obtain ⟨hi,inst,he⟩ := hElect lane hl
  obtain ⟨hShflPos,_,_,hShfl,_⟩ := hEvents lane hl
  refine ⟨by rw [hOutPos,hi,hBefore,hShflPos,hStartPos]; omega,?_,?_⟩
  · rw [hOutPos,hi]
    unfold elections
    rw [List.take_add_one,show (X.tr (warpLane l g lane))[before.pos lane]? = _ from he]
    simp only [Option.toList_some,List.countP_append,List.countP_cons,isElectEv,↓reduceIte,
      List.countP_nil,Nat.zero_add]
    exact congrArg (·+1) (hCut lane hl)

  · intro other
    unfold okPolls
    rw [hOutPos,hi,countP_take_succ_false he rfl,hBefore,hShflPos,
      countP_take_succ_false hShfl rfl,hStartPos]

/-- The first recurring K acquire leads to the actual key descriptor shuffle,
all eight stage-zero QK issues, and the first recurring score commit. -/
theorem steadyFirstQkScoreWithPollCounts :
    ∃ next : SchedulerWarpReached l X g 2419
      (fun _ => steadyKeyBroadcastFrame l visit remaining keep ++ qDescriptorFacts l 0)
      (shuffles+1) votes ends,
      (∀ lane < 32, cur.pos lane < next.pos lane ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
      ∃ issuer idx, SameWarp l g issuer ∧ X.Commit (issuer,idx)
        (commitSpec l issuer (l.sharedBase+80)) ∧ idx+1 = next.pos (laneOf l issuer) := by
  obtain ⟨leader,count,ready,hCut⟩ := firstQkReadyWithPolls hp hMax hg cur
  let F := steadyKeyBroadcastFrame l visit remaining keep
  have hDistinct (r : Nat)
      (h : r ∉ [2600,2571,1193,1192,2572,2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,
        2615,2618,1190,1062,2574,2602,9632,1188] ++ steadyValueCarryRegs keep)
      (hWord : r < 9624 ∨ 9631 < r) :
      ∀ pair ∈ F ++ qDescriptorFacts l 0, pair.1 ≠ r := by
    intro pair hm
    rcases List.mem_append.mp hm with hm | hm
    · have hReg := List.mem_map_of_mem (f := Prod.fst) hm
      exact fun he => h (by cases keep <;> exact he ▸ hReg)
    · exact qWordNot hWord pair hm
  have hOrd : ElectOrdinal l X := electOrdinal hMax.1
    (ElectMutual.of_full (fun e => actualFullElectionMask hMax.1 e))
  obtain ⟨done,hAdvance,_,issuer,idx,hWarp,hCommit,hIndex⟩ :=
    recurringQkPacketAndCommitWithPollCounts hp hMax hg 0 leader
      (F := F) (base := l.sharedBase+80) ready (by
        have hRegs : F.map Prod.fst =
            [2600,2571,1193,1192,2572,2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,
              2615,2618,1190,1062,2574,2602,9632,1188] ++ steadyValueCarryRegs keep := by
          cases keep <;> rfl
        rw [hRegs]
        cases keep <;> decide +kernel) hOrd count (fun lane hl => (hCut lane hl).2.1)
      (hDistinct 390 (by cases keep <;> decide) (.inl (by decide)))
      (hDistinct 391 (by cases keep <;> decide) (.inl (by decide)))
      (fun pair hm => by
        change pair.1 ∉ [2593]
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using
          hDistinct 2593 (by cases keep <;> decide) (.inl (by decide)) pair hm)
      (by
        simp [F,steadyKeyBroadcastFrame,steadyQkScalars,recurringKeyBlock,qkCommitSite,commitSite])
      (by change l.sharedBase+80+0 < 2^32; have := hp.shared.2.1; omega)
      (by change (l.sharedBase+80+0)%8 = 0; have := hp.shared.1; omega)
  refine ⟨done,?_,issuer,idx,hWarp,⟨2418,hCommit⟩,hIndex⟩
  intro lane hl
  exact ⟨(hCut lane hl).1.trans_lt (hAdvance lane hl).1,
    fun other => ((hAdvance lane hl).2.2 other).trans ((hCut lane hl).2.2 other)⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Mma
