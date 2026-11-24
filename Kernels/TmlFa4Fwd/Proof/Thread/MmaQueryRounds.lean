-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaObservedCacheBank
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringProbabilityAcquire
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem countConstant {X : Execution} {g first last : Nat}
    (mark : Event → Bool) (hOrder : first ≤ last)
    (hFalse : ∀ i e, first ≤ i → i < last → X.get (g,i) = some e → mark e = false) :
    ((X.tr g).take first).countP mark = ((X.tr g).take last).countP mark := by
  have hTake : (X.tr g).take last =
      (X.tr g).take first ++ ((X.tr g).drop first).take (last-first) := by
    conv_lhs => rw [← Nat.add_sub_of_le hOrder, List.take_add]
  have hZero : (((X.tr g).drop first).take (last-first)).countP mark = 0 := by
    apply List.countP_eq_zero.mpr
    intro event hIn
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hIn
    have hLen := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at hLen
    have hBound : i < last-first := by omega
    rw [List.getElem?_take_of_lt hBound, List.getElem?_drop] at hi
    intro hMark
    rw [hFalse (first+i) event (by omega) (by omega) hi] at hMark
    cases hMark
  rw [hTake,List.countP_append,hZero,Nat.add_zero]

/-- The QK observation records a performed MMA issue. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.QkInstruction.mmaIssue
    {X : Execution} {i : EvId} {b : Fin 4} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : QkInstruction X i b step d op accum mask) : X.MmaIssue i d op accum mask :=
  ⟨_,h.decoded⟩

/-- A recurring score commit identifies each actual QK fragment of the same round.
The preceding score cursor equals that round's ordinal. -/
theorem scoreCommitRecurringQueryBank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hCommit : ScoreCommit l X (g,index) cta stage spec rank)
    (hPos : 0 < scoreCommitOrdinal l X cta stage (g,index)) :
    ∃ start, start + 9 = index ∧ ∀ step : Fin 8, ∃ d op accum mask,
      QkInstruction X (g,start+step.val) (recurringKeyBlock stage) step d op accum mask ∧
      TraceBefore X (g,start+step.val) (g,index) ∧
      scoreCommitOrdinal l X cta stage (g,start+step.val) =
        scoreCommitOrdinal l X cta stage (g,index) := by
  obtain ⟨block,hStage,hRepeat,he⟩ := positiveScoreCommitRepeats hp hX hCommit hPos
  have hBlock : block = recurringKeyBlock stage := by
    apply Fin.ext
    revert hStage hRepeat
    fin_cases block <;> fin_cases stage <;> decide
  subst block
  obtain ⟨start,hStart,hBank⟩ := hCommit.recurringCacheBankOccurrence hp hX hPos
  obtain ⟨_,_,_,hElect,_⟩ := scoreCommitLeader hp hX (recurringKeyBlock stage) he
  refine ⟨start,hStart,?_⟩
  intro step
  obtain ⟨dd,ops,acc,flags,hIssue,_⟩ := hBank step
  have hSlice (mark : Event → Bool)
      (hMma : ∀ (pc d : Nat) (op : TcMma.OperandSpec) (acc : Bool) (mask : List Nat),
        mark ⟨pc,.tc (.mma d op acc mask)⟩ = false)
      (hVote : ∀ (pc mask inst leader : Nat), mark ⟨pc,.elect mask inst leader⟩ = false) :
      ((X.tr g).take (start+step.val)).countP mark = ((X.tr g).take index).countP mark := by
    apply countConstant mark (by have := step.isLt; omega)
    intro i e hFirst hLast hGet
    by_cases hAt : i = index-1
    · subst i
      have hEq := Option.some.inj (hGet.symm.trans hElect)
      rw [hEq]
      apply hVote
    · have hStep : i-start < 8 := by omega
      obtain ⟨_,_,_,_,hFrag,_⟩ := hBank ⟨i-start,hStep⟩
      have hf : start+(⟨i-start,hStep⟩ : Fin 8).val = i := by dsimp; omega
      have hDecoded := hFrag.decoded
      rw [hf] at hDecoded
      rw [Option.some.inj (hGet.symm.trans hDecoded)]
      apply hMma
  have hScore := hSlice (scoreCommitOn (scoreReadyObject l cta stage))
    (by intros; rfl) (by intros; rfl)
  exact ⟨dd,ops,acc,flags,hIssue,⟨rfl,by have := step.isLt; omega,len_of_get he⟩,hScore⟩

/-- The issue transition of an observed QK fragment is ordered after its trace predecessors. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.QkInstruction.baseCausalityOfTrace
    {l : Launch} {X : Execution} {earlier mma : EvId} {block : Fin 4} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : QkInstruction X mma block step d op accum mask) (hTrace : TraceBefore X earlier mma) :
    baseCausality l X earlier mma := by
  exact .single (.inl (po_of_not_access hTrace.1 hTrace.2.1 hTrace.2.2 (by rw [h.decoded]; rfl)))

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
