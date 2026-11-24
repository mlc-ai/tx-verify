-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedRoundScoreOrigin
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedDenominatorCarry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedBiasedScores
import Lemmas.Flow.RecordedCheckpointPath
import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasVectorTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Thread.Scores

theorem betweenRecordedBiasedCheckpoints {l : Launch} {g i j : Nat}
    {events : List Event} {s t : TState} (hi : i < j) (hj : j ≤ events.length)
    (hFirst : TraceReach kernel Assumptions.all l g {} (events.take i) s)
    (hSecond : TraceReach kernel Assumptions.all l g {} (events.take j) t) :
    TraceReach kernel Assumptions.all l g s ((events.drop i).take (j-i)) t := by
  obtain ⟨u,hU,hInitial⟩ := hFirst.returnedPrefix
  obtain ⟨v,hV,hAfter⟩ := hSecond.returnedPrefix
  have hs : events.take j = events.take i ++ (events.drop i).take (j-i) := by
    rw [← List.take_add,Nat.add_sub_of_le hi.le]
  have hRun := hU.after_returned_prefix (hs ▸ hV)
  have hMore : ((events.drop i).take (j-i)) ≠ [] := by
    intro hEmpty
    have hLengths := congrArg List.length hs
    simp only [hEmpty,List.append_nil,List.length_take,Nat.min_eq_left hj,
      Nat.min_eq_left (hi.le.trans hj)] at hLengths
    omega
  simpa only [List.append_nil] using
    (hRun.after_local_nonempty hInitial hMore).returning_reach.append (.of_local hAfter)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g start last pc batch : Nat} {s : TState} (hs : At s 5032 [])
    (hTrace : TraceReach kernel Assumptions.all l g {} ((X.tr g).take start) s)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop start) none)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLast : start ≤ last) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : let co := assignedCoordinates p batch (g/l.block)
      256*co.1+128*(warpIndex l g/4)+(g%l.block)%128 < p.qLength batch)
include hp hX hFrame hs hTrace hr hExit hLast hb hLo hHi hRow

/-- The first score load of this recorded biased round determines its actual
launch logits. The incoming maximum, denominator and phase survive to that same cursor. -/
theorem biasedDenominatorEntryOfHeadWithOrdinal :
    ∃ stage : Fin 2, stage.val = warpIndex l g/4 ∧ ∃ pos u,
      let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*stage.val+(g%l.block)%128
      let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,start)
      let logit := fun col => maskedLogit p batch co.2 row
        (visitKey (Mma.trips p batch co.1) visit col)
      start < pos ∧ 0 < visit ∧ visit < Mma.trips p batch co.1 ∧
      At u (biasBodyStart true+4*biasBodyPairs true) [] ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take pos) u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) none ∧
      (∀ i ∈ biasBodyItems true,
        u.regs i.result = some (.pair
          (scoreValue (logit (2*(i.qk-7367))))
          (scoreValue (logit (2*(i.qk-7367)+1))))) ∧
      (∀ r ∈ biasedCarryRegisters, u.regs r = s.regs r) ∧
      (∀ block < 2^32, s.regs 7249 = some (b32 block) →
        u.regs 7249 = some (b32 ((block+(2^32-1))%2^32))) ∧
      probabilityOrdinal l X (g/l.block) stage 0 (g,pos) = visit := by
  obtain ⟨load,address,values,t,out,hLoadAfter,hLoad,hScorePath,hScore,hSame,hFirstEvents⟩ :=
    biasedScoreLoadPathOfHead hX hs hr hExit hLast
  have hLoadBefore : load < last := by
    have hExitLen := X.exit_last hX (event_thread_lt hX hExit) hExit
    have hLen := len_of_get hLoad
    change load < (X.tr g).length at hLen
    change last+1 = (X.tr g).length at hExitLen
    have hNe : load ≠ last := by
      rintro rfl
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hLoad.symm.trans hExit)))
    omega
  obtain ⟨stage,hStage,wait,phase,u,hWait,hVisit,hTrips,hu,hRun,hLogits,hBefore,hRank,hWindow,
      pre,hPc,hStop,hBeforeWait,hToBody,hKeep⟩ :=
    observedBiasedAffineScoresOfFootprintWithPath hp hX hFrame hLoad hExit hLoadBefore hb
      hLo hHi hRow
  let pos := if laneOf l g = 0 then wait+1+64+3 else wait+1+64+2
  have hVisitRank : observedBarrierOrdinal X (g,wait) (11+stage.val) =
      probabilityOrdinal l X (g/l.block) stage 0 (g,start) :=
    hRank.symm.trans (hSame (probabilityObject l (g/l.block) stage 0))
  have hStartWait : start < wait := by omega
  have hPath := betweenRecordedBiasedCheckpoints hStartWait (len_of_get hWait).le
    hTrace hBeforeWait
  have hEventRange (e : Event) (he : e ∈ ((X.tr g).drop start).take (wait-start)) :
      e.pc < 5189 := by
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp he
    have hi' := (List.getElem?_eq_some_iff.mp hi).1
    have hOff : i < wait-start := hi'.trans_le (by simp)
    have hActual : X.get (g,start+i) = some e := by
      rwa [List.getElem?_take_of_lt hOff,List.getElem?_drop] at hi
    by_cases h : start+i < load
    · have hFirst : e ∈ ((X.tr g).drop start).take (load-start) := by
        apply List.mem_of_getElem? (i := i)
        rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop]
      rw [hFirstEvents e hFirst]
      decide
    · exact hWindow _ _ (by omega) (by omega) hActual
  have hBase := biasedCarryBeforeVectorRead hPath hs.1.ge (by rw [hs.1]; decide)
    (by rw [hs.2.1]; decide) hEventRange
  have hSpace : ∀ r ∈ biasedCarryRegisters,
      r ∉ [9755,4166,4167,4168,4169,4170] ∧
      (∀ i, biasVectorKeeps true i r) ∧ r ∉ biasFenceWritten true ∧
      r ∉ (biasBodyItems true).flatMap BiasAffineItem.writes := by
    intro r hr
    simp only [biasedCarryRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> refine ⟨by decide,?_,by decide,by decide +kernel⟩ <;>
      intro i <;> unfold biasVectorKeeps <;> fin_cases i <;> decide
  refine ⟨stage,hStage,pos,u,?_,hVisitRank ▸ hVisit,hVisitRank ▸ hTrips,hu,?_,hRun,?_,?_,?_,?_⟩
  · unfold pos
    split <;> omega
  · have hPos : wait ≤ pos := by
      unfold pos
      split <;> omega
    have hAppend := hBeforeWait.append hToBody
    rw [← List.take_add,Nat.add_sub_of_le hPos] at hAppend
    exact hAppend
  · simpa only [hVisitRank] using hLogits
  · intro r hr
    obtain ⟨hA,hB,hC,hD⟩ := hSpace r hr
    exact (hKeep r hA hB hC hD).trans (hBase r hr)
  · intro block hb hWord
    have hBlock := biasedBlockWordBeforeVectorRead hb hPath hs.1 hPc
      (by rw [hs.2.1]; decide) hEventRange hWord
    exact (hKeep 7249 (by decide) (by intro i; unfold biasVectorKeeps; fin_cases i <;> decide)
      (by decide) (by decide +kernel)).trans hBlock
  · have hLength := X.exit_last hX (event_thread_lt hX hExit) hExit
    change last+1 = (X.tr g).length at hLength
    have hwLen : wait < (X.tr g).length := len_of_get hWait
    have hDifferent : wait ≠ last := by
      rintro rfl
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hWait.symm.trans hExit)))
    have hLater : wait < last := by omega
    have hpLen : pos < (X.tr g).length := by
      by_contra! h
      rw [List.drop_eq_nil_iff.mpr h] at hRun
      cases hRun
    have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
    have hQuiet := repeatedBiasAffineEarlyRank hp hX hFrame hWait hExit hLater hb hLo hHi
    change ((X.tr g).take pos).countP earlyProbabilityMark =
      ((X.tr g).take wait).countP earlyProbabilityMark at hQuiet
    rw [earlyProbabilityCount hp hX stage hWarp hStage.symm hpLen,
      earlyProbabilityCount hp hX stage hWarp hStage.symm hwLen] at hQuiet
    have hWaitRank := biasedVisitEqualsProbabilityOrdinal hp hX stage hWarp hStage.symm hWait
    exact hQuiet.trans (hWaitRank.symm.trans hVisitRank)

end PTX.Kernels.TmlFa4Fwd.Softmax
