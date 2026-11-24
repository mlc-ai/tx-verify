-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCohortPolls
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyFirstQk
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpPvPacket
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyFirstQk
import Kernels.TmlFa4Fwd.Proof.MmaQkBroadcast
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Kernels.TmlFa4Fwd.Flow.Code.Part037
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread (actualFullElectionMask electionCountAtMatchedShuffle)

noncomputable section

def steadySecondPvFrame (l : Launch) (visit remaining : Nat) : List (Nat × Value) :=
  (2595,b32 (valueDescriptorLow l (2*visit+1))) ::
    (steadyKeyBroadcastFrame l visit remaining ++ qDescriptorFacts l 0)

private def secondPvRootRegs : List Nat :=
  [2595,2600,2571,1193,1192,2572,2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,
    2615,2618,1190,1062,2574,2602,9632,1188]

private theorem secondPvRegNot {l : Launch} {visit remaining r : Nat}
    (h : r ∉ secondPvRootRegs) (hq : r < 9624 ∨ 9631 < r) :
    ∀ pair ∈ steadySecondPvFrame l visit remaining, pair.1 ≠ r := by
  intro pair hm
  change pair ∈ (((2595,b32 (valueDescriptorLow l (2*visit+1))) ::
    steadyKeyBroadcastFrame l visit remaining) ++ qDescriptorFacts l 0) at hm
  rcases List.mem_append.mp hm with hm | hm
  · have hh := List.mem_map_of_mem (f := Prod.fst) hm
    exact fun he => h (he ▸ hh)
  · exact qWordNot hq pair hm

/-- A recorded stage-one main cohort supplies this visit's successful acquire. -/
theorem steadySecondMainOfCohort {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : Protocol.Scores.CorrectionJointGuards l X)
    {g visit remaining shuffles votes : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 12)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2419
      (fun _ => steadySecondPvFrame l visit remaining) shuffles votes ends)
    (hOrdinal : ∀ lane < 32, okPolls (Thread.Scores.probabilityObject l (g/l.block) 1 0)
      ((X.tr (warpLane l g lane)).take (cur.pos lane)) = visit)
    (hCohort : Protocol.Scores.ProbabilityCohort l X (g/l.block) 1 0 visit) :
    WarpOrdinalPollAdvance l X g 7 (l.sharedBase+104) (visit%2) shuffles votes
      (fun _ => steadySecondPvFrame l visit remaining) ends cur := by
  exact mmaWarpProbabilityPollOfCohort hp hMax hGuard hg hWarp 7 1 0
    cur (fun _ _ => ⟨secondPvRegNot (by decide) (.inr (by decide)),by
      simp [waitSite,steadySecondPvFrame,steadyKeyBroadcastFrame,steadyKeyFrame,steadyKeyRing,
        steadyValueFrame,steadyFrame,steadyPorts],by
      simp [waitSite,steadySecondPvFrame,steadyKeyBroadcastFrame,steadyKeyFrame,steadyKeyRing,
        steadyValueFrame,steadyFrame,steadyPorts]⟩) hOrdinal hCohort

private theorem secondPvConstBroadcast {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pc shuffles votes src dst value : Nat} (hg : g < l.threads)
    {F : List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g pc (fun _ => F) shuffles votes ends)
    (hLo : 1904 ≤ pc) (hHi : pc+1 < 2768)
    (hMov : kernel.code[pc]? = some ⟨none,.move ⟨.scalar,.int .b 32,[some src],[.imm value]⟩⟩)
    (hCode : kernel.code[pc+1]? = some ⟨none,.warp ⟨.shfl .idx,some (.int .b 32),[some dst],
      [.reg src,.imm 0,.imm 31],some (.imm (-1))⟩⟩)
    (hValue : value < 2^32) (hSrc : ∀ pair ∈ F, pair.1 ≠ src)
    (hDst : ∀ pair ∈ F, pair.1 ≠ dst) (hNe : src ≠ dst) :
    ∃ result : SchedulerWarpReached l X g (pc+2) (fun _ => (dst,b32 value)::(src,b32 value)::F)
      (shuffles+1) votes ends,
      ∀ lane < 32, result.pos lane = cur.pos lane+1 ∧
        ∃ recv ok, X.get (warpLane l g lane,cur.pos lane) =
          some ⟨pc+1,.shfl .idx (b32 value) 0 31 recv ok⟩ ∧
          X.ShflK (warpLane l g lane,cur.pos lane) shuffles := by
  obtain ⟨mid,hMid⟩ := cur.advanceLocalWithPosition (pc' := pc+1)
    (G := fun _ => (src,b32 value)::F) (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      let u := next (setReg (cur.state lane) src (b32 value))
      have hr : run kernel [] l (warpLane l g lane) 1 (cur.state lane) = some u := by
        apply run_local hMov rfl ht
        rw [execLocalA_nil,execLocal_move (m :=
          ⟨.scalar,.int .b 32,[some src],[.imm value]⟩) rfl]
        simp [execMove,DType.width,readValue,readBits,b32,pure,Except.pure,bind,Except.bind,
          BitVec.ofInt_natCast,truncBits_ofNat hValue (by decide),Value.bytes,u]
      exact ⟨u,run_rtg (localRun hLo (by omega) ht.1 rfl hr),ht.set hSrc⟩)
  obtain ⟨result,hEvents⟩ := mid.consumeShuffleWithEvents hp hMax hg .idx (fun _ => b32 value)
    (fun _ => 0) (fun _ => 31) (by
      intro _ _ pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hNe
      · exact hDst pair hm) (by
        intro lane hl
        exact laneZeroBroadcast hp (by omega) ((mid.checkpoint lane hl).mono
          ⟨(mid.checkpoint lane hl).2.2.2.2.1,trivial⟩) hCode)
  refine ⟨result,fun lane hl => ?_⟩
  simpa only [hMid] using hEvents lane hl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g visit remaining shuffles votes : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2422
      (fun _ => steadySecondPvFrame l visit remaining) shuffles votes ends)
include hp hMax hg cur

private theorem secondPvElectedWithPolls :
    ∃ leader count, ∃ ready : SchedulerWarpReached l X g 2427
      (fun lane => pvElectedFrame l g 1 (2*visit+1) (visit%2) (decide (0<visit))
        (steadySecondPvFrame l visit remaining) lane leader) (shuffles+2) votes ends,
      ∀ lane < 32, cur.pos lane < ready.pos lane ∧
        elections X (warpLane l g lane) (ready.pos lane) = count ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (ready.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) := by
  let F := steadySecondPvFrame l visit remaining
  obtain ⟨a,hFirst⟩ := secondPvConstBroadcast hp hMax hg cur (by decide) (by decide)
    Flow.code_2422 Flow.code_2423 (by decide)
    (secondPvRegNot (by decide) (.inl (by decide)))
    (secondPvRegNot (by decide) (.inl (by decide))) (by decide)
  have hUnused (r : Nat) (hr : r ∉ [2594,2597] ++ secondPvRootRegs)
      (hq : r < 9624 ∨ 9631 < r) :
      ∀ item ∈ (2594,b32 192)::(2597,b32 192)::F, item.1 ≠ r := by
    intro item hm
    have hR : r ∉ secondPvRootRegs := fun h => hr (List.mem_append_right _ h)
    rcases List.mem_cons.mp hm with rfl | hm
    · exact fun he => hr (List.mem_append_left _ (by simp [← he]))
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact fun he => hr (List.mem_append_left _ (by simp [← he]))
      · exact secondPvRegNot hR hq item hm
  obtain ⟨b,hBroadcast⟩ := secondPvConstBroadcast hp hMax hg a (by decide) (by decide)
    Flow.code_2424 Flow.code_2425 (by decide)
    (hUnused 2598 (by decide) (.inl (by decide)))
    (hUnused 2596 (by decide) (.inl (by decide))) (by decide)
  let E := pvEntryFacts l 1 (2*visit+1) (visit%2) (decide (0<visit)) ++ F
  obtain ⟨c,hC⟩ := b.advanceLocalWithPosition (pc' := 2426) (G := fun _ => E) (by
    intro lane hl
    have ht := b.checkpoint lane hl
    let h := ht.2.2.2.2
    refine ⟨_,.refl,ht.mono ((holds_append ..).mpr ⟨?_,h.2.2.2.2⟩)⟩
    have hAcc : (if decide (0<visit) = true then 1 else 0) =
        (if 0<visit then 1 else 0) := by simp
    change Holds (b.state lane).regs
      [(2596,b32 384),(2594,b32 192),(2595,b32 (valueDescriptorLow l (2*visit+1))),
        (7206,b32 (if decide (0<visit) = true then 1 else 0)),
        (2618,b32 (l.sharedBase+120)),(7205,b32 (visit%2))]
    rw [hAcc]
    exact ⟨holds_lookup h rfl,holds_lookup h rfl,holds_lookup h rfl,holds_lookup h rfl,
      holds_lookup h rfl,holds_lookup h rfl,trivial⟩)
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  let n := elections X (warpLane l g 0) (a.pos 0)
  have hCut (lane : Nat) (hl : lane < 32) :
      elections X (warpLane l g lane) (c.pos lane) = n := by
    obtain ⟨hi,_,_,he,hk⟩ := hBroadcast lane hl
    obtain ⟨_,_,_,he',hk'⟩ := hBroadcast 0 (by decide)
    have hw := Step.sameWarp_trans (sameWarp_symm (Step.sameWarp_lane hBlock hg hl).1)
      (Step.sameWarp_lane hBlock hg (show 0<32 by decide)).1
    have hCount := electionCountAtMatchedShuffle hMax.1 hw he hk he' hk'
    rw [hC,hi]
    unfold elections
    rw [countP_take_succ_false he rfl]
    exact hCount
  have hPred : ∀ pair ∈ E, pair.1 ≠ 9699 := by
    intro pair hm
    rcases List.mem_append.mp hm with hm | hm
    · have hReg := List.mem_map_of_mem (f := Prod.fst) hm
      have hNe : 9699 ∉ ([2596,2594,2595,7206,2618,7205] : List Nat) := by decide
      exact fun he => hNe (he ▸ hReg)
    · exact secondPvRegNot (by decide) (.inr (by decide)) pair hm
  have hOrd : ElectOrdinal l X := electOrdinal hMax.1
    (ElectMutual.of_full (fun e => actualFullElectionMask hMax.1 e))
  obtain ⟨leader,new,hElect⟩ := c.consumeElectionAtOrdinal hp hMax hg
    (fun lane => electState l (warpLane l g lane) (c.state lane) 8)
    (fun lane lead => (9699,.pred (laneOf l (warpLane l g lane) == lead))::E)
    hOrd n hCut (fun lane hl => electTemplate 8 (c.checkpoint lane hl))
    (fun lane hl lead => electStateFrame 8 (c.checkpoint lane hl) lead hPred (by simp [electSite]))
  refine ⟨leader,n+1,new,fun lane hl => ?_⟩
  obtain ⟨hi,inst,he⟩ := hElect lane hl
  obtain ⟨hPosA,_,_,heA,_⟩ := hFirst lane hl
  obtain ⟨hPosB,_,_,heB,_⟩ := hBroadcast lane hl
  refine ⟨by rw [hi,hC,hPosB,hPosA]; omega,?_,?_⟩
  · rw [hi]
    unfold elections
    rw [List.take_add_one,show (X.tr (warpLane l g lane))[c.pos lane]? = _ from he]
    simp only [Option.toList_some,List.countP_append,List.countP_cons,isElectEv,↓reduceIte,
      List.countP_nil,Nat.zero_add]
    exact congrArg (·+1) (hCut lane hl)
  · intro other
    unfold okPolls
    rw [hi,countP_take_succ_false he rfl,hC,hPosB,countP_take_succ_false heB rfl,
      hPosA,countP_take_succ_false heA rfl]

/-- The second recurring PV packet records all fragments and reaches the V release election. -/
theorem steadySecondPvPacketWithPollCounts
    (hTail : ∀ lane < 32, PvTailReadyWithOrdinal l X (warpLane l g lane) 1 (visit%2)
      (steadySecondPvFrame l visit remaining) (cur.pos lane)) :
    ∃ newEnds count, ∃ next : SchedulerWarpReached l X g 2459
      (fun _ => steadySecondPvFrame l visit remaining) (shuffles+2) votes newEnds,
      PvPacketIssues l X g 1 (2*visit+1) (decide (0<visit)) ∧
      ∀ lane < 32, cur.pos lane < next.pos lane ∧
        elections X (warpLane l g lane) (next.pos lane) = count ∧
        PvPollDelta X (warpLane l g lane) (cur.pos lane) (next.pos lane)
          (Thread.Scores.probabilityObject l (g/l.block) 1 1) true := by
  obtain ⟨leader,count,ready,hCut⟩ := secondPvElectedWithPolls hp hMax hg cur
  have hFresh : ∀ pair ∈ steadySecondPvFrame l visit remaining,
      pair.1 ≠ (pvSite 1).b-2 ∧ pair.1 ≠ (pvSite 1).b ∧ pair.1 ≠ (waitSite (pvTailWait 1)).result :=
    fun pair hm => ⟨secondPvRegNot (by decide) (.inr (by decide)) pair hm,
      secondPvRegNot (by decide) (.inr (by decide)) pair hm,
      secondPvRegNot (by decide) (.inr (by decide)) pair hm⟩
  obtain ⟨newEnds,next,hIssue,hCount⟩ := pvWarpPacketWithPollCounts hp hMax hg 1
    (2*visit+1) (visit%2) (decide (0<visit)) (Nat.mod_lt _ (by decide)) leader hFresh (by
      set_option maxRecDepth 100000 in
      change ((kernel.code.drop 2427).take 7).all
        (fun ins => (secondPvRootRegs ++ [9624,9625,9626,9627,9628,9629,9630,9631]).all
          (fun r => !(writesRegs ins.op).contains r)) = true
      decide +kernel) ready (fun lane hl => by
        unfold PvTailReadyWithOrdinal
        dsimp only
        rw [(hCut lane hl).2.2]
        exact hTail lane hl)
  refine ⟨newEnds,count,next,hIssue,?_⟩
  intro lane hl
  have hCta : (warpLane l g lane)/l.block = g/l.block :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.2.symm
  have hDelta := (hCount lane hl).2.2
  rw [hCta] at hDelta
  refine ⟨(hCut lane hl).1.trans_le (hCount lane hl).2.1,
    (hCount lane hl).1.trans (hCut lane hl).2.1,?_⟩
  intro other
  exact (hDelta other).trans
    (congrArg (· + if true = true ∧ other = _ then 1 else 0) ((hCut lane hl).2.2 other))

end
end PTX.Kernels.TmlFa4Fwd.Mma
