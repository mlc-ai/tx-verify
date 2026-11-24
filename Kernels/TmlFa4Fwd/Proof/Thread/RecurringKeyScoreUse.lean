-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaObservedCacheBank
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Kernels.TmlFa4Fwd.Mma

/-- Each fragment contributing to an actual recurring score commit uses the key
generation at twice that score commit's ordinal within its query stage. -/
theorem ScoreCommit.recurringKeyUse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hCommit : ScoreCommit l X (g,index) cta stage spec rank)
    (hPositive : 0 < scoreCommitOrdinal l X cta stage (g,index)) :
    ∃ start, start + 9 = index ∧ ∀ step : Fin 8, ∃ d operands accum mask,
      QkInstruction X (g,start+step.val) (recurringKeyBlock stage) step d operands accum mask ∧
      let frame := Thread.Mma.atPrefix l X g (start+step.val)
      let use := frame.kvAcquires 0 + frame.kvAcquires 1 + frame.kvAcquires 2 - 1
      use = 2 * scoreCommitOrdinal l X cta stage (g,index) ∧
      operands.b = sharedDescriptor (kvStart l use + qkFragment step) 16 := by
  obtain ⟨start,hStart,hBank⟩ := hCommit.recurringCacheBankOccurrence hp hX hPositive
  refine ⟨start,hStart,fun step => ?_⟩
  obtain ⟨d,operands,accum,mask,hIssue,hElect⟩ := hBank step
  obtain ⟨hB,_,_,hRank⟩ := hIssue.recurringKeyOperandOfReadyOrdinal hp hX stage
  have hGate : (slotWait 2).pc + 3 ≤ qkPc (recurringKeyBlock stage) + step.val ∧
      qkPc (recurringKeyBlock stage) + step.val ≤ (slotElect 2).pc := by
    fin_cases stage <;> fin_cases step <;> decide
  have hCount := pendingReadyBalance hp hX 2 hIssue.decoded hGate
  change Thread.Mma.readyOccurrence X g (start+step.val) .loopKey =
    1 + Thread.Mma.releaseElections X g (start+step.val) .loopKey at hCount
  dsimp only at hRank
  rw [hCount,hElect] at hRank
  exact ⟨d,operands,accum,mask,hIssue,hRank,hB⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
