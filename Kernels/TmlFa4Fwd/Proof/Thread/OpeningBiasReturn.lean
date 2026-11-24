-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasRendezvousProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasSignalProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasFmaEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue

/-- The selected lane has returned from its opening Bias rendezvous and read the
actual launch scales. Its score pairs and Bias operands remain available to the FMAs. -/
structure OpeningFmaLane (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) (stage : Fin 2) (wait : Nat) where
  arrival : OpeningBiasArrivalLane p l X g batch stage wait
  pos : Nat
  position : pos = if laneOf l g = 0 then wait+68 else wait+67
  releasedBias : laneOf l g = 0 → X.get (g,wait+67) = some
    ⟨3590,.arrive (signalLoc l g stage 0) 0 1 true .cta⟩
  before : TState
  ready : TState
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  continuation : Run kernel Assumptions.all l g before ((X.tr g).drop pos)
    arrival.loaded.opening.ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready
  checkpoint : At ready 3593 [(7135,b32 p.invScaleBits),(7132,b32 p.scaleLog2Bits)]
  scores : OpeningScoreBeforeBias l X g stage ready
  unpacked : ∀ i, BiasUnpacked false i ready (openingBiasWord p l g batch stage i)
  frame : ∀ r ∉ firstBiasEntryWritten, ready.regs r = arrival.loaded.cursor.ready.regs r

/-- A released Bias rendezvous leads to the actual first FMA inputs. The chosen
warp lane records the Bias-empty arrival, while the other lanes take the local branch. -/
theorem OpeningBiasArrivalLane.firstFmaOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m)
    {g batch wait : Nat} {stage : Fin 2} (hg : g < l.threads)
    (arrival : OpeningBiasArrivalLane p l X g batch stage wait)
    (hReturn : wait+67 < (X.tr g).length ∨
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g) :
    Nonempty (OpeningFmaLane p l X g batch stage wait) := by
  let warp := arrival.loaded.opening.warp
  have hStage : stageOf warp = stage := arrival.loaded.opening.selectedStage
  obtain ⟨u,hBranch,hStart,hBranchFrame⟩ := biasReleaseBranchFrame warp false arrival.ready
  have hBound : wait+67 ≤ (X.tr g).length := len_of_get arrival.arrival
  have hReleased (hEnd : wait+67 = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
    rcases hReturn with h | h
    · omega
    · exact h
  have finish (pos : Nat) (hPos : pos = if laneOf l g = 0 then wait+68 else wait+67)
      (hSignal : laneOf l g = 0 → X.get (g,wait+67) = some
        ⟨3590,.arrive (signalLoc l g stage 0) 0 1 true .cta⟩)
      (before seed : TState) (hSeed : At seed 3591 [])
      (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before))
      (hTail : Run kernel Assumptions.all l g before ((X.tr g).drop pos)
        arrival.loaded.opening.ending)
      (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before seed)
      (hFrame : ∀ r ∉ biasReleaseWritten false, seed.regs r = arrival.state.regs r) :
      Nonempty (OpeningFmaLane p l X g batch stage wait) := by
    obtain ⟨t,hAt,hScales,hRegs⟩ := firstBiasFmaScaleLoads hp (g := g) hSeed
    have hWritten : biasReleaseWritten false = [7894,492,1046,3076,3077,3078] := rfl
    have hScore (q : Fin 4) (k : Nat) (hk : k < 16) :
        t.regs (firstScorePairReg q k) = arrival.state.regs (firstScorePairReg q k) := by
      have hIdx : 7303 ≤ firstScorePairReg q k ∧ firstScorePairReg q k < 7367 := by
        have hQ := q.isLt
        unfold firstScorePairReg
        omega
      refine (hRegs _ (by omega) (by omega)).trans (hFrame _ ?_)
      simp only [hWritten,List.mem_cons,List.not_mem_nil,or_false]
      intro hr
      rcases hr with h | h | h | h | h | h <;> omega
    have hBias (i : Fin 16) (k : Nat) (hk : k < 4) (r : Nat)
        (hReg : r = (biasUnpackRegs false i k).1 ∨ r = (biasUnpackRegs false i k).2) :
        t.regs r = arrival.state.regs r := by
      have hI := i.isLt
      simp only [biasUnpackRegs,biasUnpackTop,Bool.false_eq_true,ite_false] at hReg
      have hRange : 786 ≤ r ∧ r < 922 := by omega
      refine (hRegs _ (by omega) (by omega)).trans (hFrame _ ?_)
      simp only [hWritten,List.mem_cons,List.not_mem_nil,or_false]
      intro hr
      rcases hr with h | h | h | h | h | h <;> omega
    refine ⟨⟨arrival,pos,hPos,hSignal,before,t,hPast,hTail,
      hLocal.trans (run_rtg hScales),hAt,arrival.scores.withFrame hScore,?_,?_⟩⟩
    · intro i k hk
      exact ⟨(hBias i k hk _ (.inl rfl)).trans (arrival.unpacked i k hk).1,
        (hBias i k hk _ (.inr rfl)).trans (arrival.unpacked i k hk).2⟩
    · intro r hr
      simp only [firstBiasEntryWritten,biasFenceWritten,List.mem_cons,not_or] at hr
      exact (hRegs r hr.1 hr.2.1).trans ((hFrame r hr.2.2.2).trans (arrival.frame r hr.2.2.1))
  by_cases hLane : laneOf l g = 0
  · rw [ite_eq_left hLane] at hStart
    obtain ⟨v,hSetup,hV⟩ := (biasReleaseSetup hp g warp false).apply hStart
    have hBase := hV.2.2.2.2.1
    have hCount := hV.2.2.2.2.2.1
    let after := next (mbarStateDest v (some (signalSite 0).state))
    have hSteps := (run_rtg hBranch).trans (run_rtg hSetup)
    obtain ⟨hGet,hPast,hTail⟩ := signalOfMaximal hp hg (stageOf warp) 0
      hV.1 hV.2.2.2.1 hBase hCount arrival.recorded arrival.continuation
      hSteps (by omega) hBound hReleased
    have hPos : wait+67+1 = wait+68 := by omega
    have hReady : At after 3591 [] := by
      refine ⟨?_,hV.2.1,hV.2.2.1,hV.2.2.2.1,trivial⟩
      change v.pc + 1 = 3591
      rw [hV.1]
      rfl
    rw [hStage] at hGet
    apply finish (wait+68) (by rw [ite_eq_left hLane])
      (fun _ => hGet)
      after after hReady (hPos ▸ hPast) (hPos ▸ hTail) .refl
    intro r hr
    have hState : r ≠ (signalSite 0).state := by
      intro h
      exact hr (h ▸ List.mem_cons_self)
    have hScratch : r ∉ biasReleaseSetupRegs false :=
      fun h => hr (List.mem_cons_of_mem _ h)
    have hFrame := biasReleaseSetupFrame false hStart.1 hSetup r hScratch
    simpa only [after,next,mbarStateDest,Function.update_of_ne hState] using
      (hFrame.trans (hBranchFrame r))
  · rw [ite_eq_right hLane] at hStart
    refine finish (wait+67) (by rw [ite_eq_right hLane]) (fun h => (hLane h).elim)
      arrival.state u (hStart.mono trivial) arrival.recorded arrival.continuation
      (run_rtg hBranch) (fun r _ => hBranchFrame r)

/-- The start-of-round Bias synchronization represented by the recorded arrival cursor. -/
theorem OpeningBiasArrivalLane.observed {p : Params} {l : Launch} {X : Execution}
    {g batch wait : Nat} {stage : Fin 2} (lane : OpeningBiasArrivalLane p l X g batch stage wait) :
    FirstBiasArrival X g (wait+66) stage := lane.arrival

/-- The observed Bias event has the stage's named-barrier shape. -/
theorem FirstBiasArrival.barrier {X : Execution} {g i : Nat} {stage : Fin 2}
    (h : FirstBiasArrival X g i stage) :
    Thread.BarrierArrival X (g,i) (11+stage.val) (some 128) .sync :=
  ⟨_,h,rfl⟩

/-- A recorded Bias event is part of the existing lane trace. -/
theorem FirstBiasArrival.bound {X : Execution} {g i : Nat} {stage : Fin 2}
    (h : FirstBiasArrival X g i stage) : i+1 ≤ (X.tr g).length :=
  len_of_get h

/-- The first Bias arrival has ordinal zero for its named barrier. -/
theorem FirstBiasArrival.ordinalZero {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i : Nat} {stage : Fin 2} (h : FirstBiasArrival X g i stage) :
    Thread.observedBarrierOrdinal X (g,i) (11+stage.val) = 0 :=
  Thread.Scores.firstBiasBarrierOrdinal hp hX stage h

/-- The actual opening leader's release is a unit credit for its Bias stage. -/
theorem OpeningFmaLane.biasEmptyCredit {p : Params} {l : Launch} {X : Execution}
    {g batch wait : Nat} {stage : Fin 2} (lane : OpeningFmaLane p l X g batch stage wait)
    (hLeader : laneOf l g = 0) :
    X.get (g,wait+67) =
      some ⟨3590,.arrive (Thread.Loader.biasEmptyObject l (g/l.block) stage) 0 1 true .cta⟩ := by
  have he := lane.releasedBias hLeader
  have hLoc : signalLoc l g stage 0 = Thread.Loader.biasEmptyObject l (g/l.block) stage := by
    change Loc.mk .shared (g/l.block) (l.sharedBase+8*stage.val+336) =
      Loc.mk .shared (g/l.block) (l.sharedBase+(336+8*stage.val))
    congr 1
    omega
  rw [hLoc] at he
  exact he

end PTX.Kernels.TmlFa4Fwd.Softmax
