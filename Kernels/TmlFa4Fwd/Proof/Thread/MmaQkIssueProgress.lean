-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkIssue
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.TcIssueProgress
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g pos : Nat} (hg : g < l.threads) (block : Fin 4)
    (kvUse : Nat) {F : List (Nat × Value)} {s t : TState} {ending : Option TState}
    (ht : At t (qkPc block) F) (hFacts : ∀ step, Holds t.regs (qkIssueFacts l block step kvUse))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t) (hPos : 0 < pos)
    (hBound : pos ≤ (X.tr g).length)
include hp hMax hg block kvUse ht hFacts hPrefix hTail hLocal hPos hBound

/-- Replay the full QK packet and retain the recorded cursor for its following commit. -/
theorem qkPacketOfMaximal (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    ∃ before ready, At ready (qkPc block + 8) F ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 8)) (some before) ∧
      Run kernel Assumptions.all l g before ((X.tr g).drop (pos + 8)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready ∧
      (∀ test, (∀ j : Fin 8, test (qkIssueEvent l g block j kvUse) = false) →
        ((X.tr g).take (pos + 8)).countP test = ((X.tr g).take pos).countP test) ∧
      ∀ j : Fin 8, X.get (g,pos+j.val) = some (qkIssueEvent l g block j kvUse) := by
  have segment (n start i : Nat) (hLen : start+n ≤ 8) {a b : TState}
      (hb : At b (qkPc block+start) F)
      (hWords : ∀ step, Holds b.regs (qkIssueFacts l block step kvUse))
      (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some a))
      (hRun : Run kernel Assumptions.all l g a ((X.tr g).drop i) ending)
      (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) a b)
      (hPositive : 0 < i) (hLimit : i ≤ (X.tr g).length)
      (hReleased : i = (X.tr g).length → Step.Released l X g) :
      ∃ before ready, At ready (qkPc block + (start + n)) F ∧
        Run kernel Assumptions.all l g {} ((X.tr g).take (i + n)) (some before) ∧
        Run kernel Assumptions.all l g before ((X.tr g).drop (i + n)) ending ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready ∧
        (∀ test, (∀ j : Fin 8, test (qkIssueEvent l g block j kvUse) = false) →
          ((X.tr g).take (i + n)).countP test = ((X.tr g).take i).countP test) ∧
        ∀ j (hj : j < n), X.get (g,i+j) =
          some (qkIssueEvent l g block ⟨start+j,by omega⟩ kvUse) := by
    induction n generalizing start i a b with
    | zero =>
      refine ⟨a,b,?_,?_,?_,hSteps,?_,?_⟩
      · simpa only [Nat.add_zero] using hb
      · simpa only [Nat.add_zero] using hPast
      · simpa only [Nat.add_zero] using hRun
      · simp only [Nat.add_zero,implies_true]
      · exact fun j hj => (Nat.not_lt_zero _ hj).elim
    | succ n ih =>
      let step : Fin 8 := ⟨start,by omega⟩
      let kind := TcKind.mma (scoreColumn (qkStage block)) (qkOperands l g block step kvUse)
        (decide (step.val ≠ 0)) (List.replicate 4 0)
      have hn : Next kernel Assumptions.all l g a b (.tc kind (next b)) :=
        ⟨hSteps,qkIssueOut hp hg block step kvUse (hb.mono (hWords step))⟩
      obtain ⟨hGet,hPast',hRest⟩ := Step.tc_issue_of_maximal hMax hg hn rfl
        hPast hRun hPositive hLimit hReleased
        (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
      have hEvent : X.get (g,i) = some (qkIssueEvent l g block step kvUse) :=
        by rw [hGet,hb.1]; rfl
      have hNext : At (next b) (qkPc block+(start+1)) F := by
        simpa only [Nat.add_assoc] using hb.next
      obtain ⟨before,ready,hAt,hPrefix,hTail,hLocal,hCounts,hEvents⟩ :=
        ih (start+1) (i+1) (by omega) hNext hWords hPast' hRest .refl
          (Nat.succ_pos _) (len_of_get hEvent)
          (Prologue.releasedIfLast hEvent (by intro h; cases h))
      have hEnd : i + 1 + n = i + n.succ := by omega
      have hFinish : start + 1 + n = start + n.succ := by omega
      refine ⟨before,ready,hFinish ▸ hAt,hEnd ▸ hPrefix,hEnd ▸ hTail,hLocal,?_,?_⟩
      · intro test hTest
        rw [← hEnd,hCounts test hTest]
        exact countP_take_succ_false hEvent (hTest step)
      · intro j hj
        cases j with
        | zero => exact hEvent
        | succ j =>
          simpa only [Nat.add_assoc,Nat.add_comm 1] using hEvents j (by omega)
  obtain ⟨before,ready,hAt,hPast,hRun,hSteps,hCounts,hEvents⟩ :=
    segment 8 0 pos (by decide) ht hFacts hPrefix hTail hLocal hPos hBound hRelease
  exact ⟨before,ready,hAt,hPast,hRun,hSteps,hCounts,fun j => by
    simpa only [Nat.zero_add,Fin.eta] using hEvents j.val j.isLt⟩

end PTX.Kernels.TmlFa4Fwd.Mma
