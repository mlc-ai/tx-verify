-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasGuard
public import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader (biasExpectationGuarded biasExpectationGuardedAfterCredit)

/-- Each Bias expectation is guarded by at least its matching ordinal of successful
return-object acquires along the actual issuing lane. -/
theorem biasExpectationPollBudget {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {cta g j : Nat}
    (stage : Fin 2) (hIssue : X.Arrive (g,j) (biasReadyObject l cta stage) 32768 1 true .cta) :
    arrivals (biasReadyObject l cta stage) ((X.tr g).take j) + 1 ≤
      okPolls (biasEmptyObject l cta stage) ((X.tr g).take j) := by
  let ready := biasReadyObject l cta stage
  let empty := biasEmptyObject l cta stage
  let traceTake := (X.tr g).take
  have grows {k : Nat} {e : Event} {phase : Nat} {scope : MbarScope}
      (he : X.get (g,k) = some e) (hw : e.kind = .wait empty phase true true scope) :
      okPolls empty (traceTake (k + 1)) = okPolls empty (traceTake k) + 1 := by
    obtain ⟨pc, kind⟩ := e
    change kind = _ at hw
    subst kind
    exact MbarRing.Poll.okPoll_get he
  induction j using Nat.strong_induction_on with
  | h j ih =>
    change arrivals ready (traceTake j) + 1 ≤ okPolls empty (traceTake j)
    rcases Nat.eq_zero_or_pos (arrivals ready (traceTake j)) with hz | hPos
    · obtain ⟨⟨other, k⟩, e, q, scope, he, hKind, hResume⟩ :=
        biasExpectationGuarded hp hX stage hIssue
      have hEq : other = g := hResume.1.1
      subst other
      have hBefore : k < j := hResume.1.2.1
      have hGrow := grows he hKind
      have hLe := MbarRing.Poll.okPolls_mono empty (X.tr g) (show k + 1 ≤ j by omega)
      change okPolls empty (traceTake (k + 1)) ≤ okPolls empty (traceTake j) at hLe
      omega
    · let prev := arrivals ready (traceTake j) - 1
      have hPrev : prev + 1 ≤ (traceTake j).countP (arrivesOn ready) := by
        change prev + 1 ≤ arrivals ready (traceTake j)
        dsimp only [prev]
        omega
      obtain ⟨a, e, ha, hLabel, hCount⟩ := MbarRing.Slot.exists_nth_countP
        (arrivesOn ready) hPrev
      have hOrder : a < j := by
        have hLen := (List.getElem?_eq_some_iff.mp ha).1
        simp only [traceTake, List.length_take] at hLen
        omega
      have hEarlier : X.get (g,a) = some e := by
        change (X.tr g)[a]? = some e
        rw [List.getElem?_take_of_lt hOrder] at ha
        exact ha
      rw [List.take_take, Nat.min_eq_left hOrder.le] at hCount
      change arrivals ready (traceTake a) = prev at hCount
      have hCredit : X.Arrive (g,a) ready 32768 1 true .cta := by
        obtain ⟨pc, kind⟩ := e
        cases kind <;> simp [arrivesOn, sourceArrive] at hLabel
        case arrive target tx n rel scope =>
          subst target
          obtain ⟨rfl, rfl, rfl, rfl⟩ := biasOrdinaryCredit hp hX stage ⟨_, hEarlier⟩
          exact ⟨_, hEarlier⟩
      obtain ⟨k, f, q, scope, hak, hf, hKind, hResume⟩ :=
        biasExpectationGuardedAfterCredit hp hX hCredit hIssue hOrder
      have hkj : k < j := hResume.1.2.1
      have hInd := ih a hOrder hCredit
      change arrivals ready (traceTake a) + 1 ≤ okPolls empty (traceTake a) at hInd
      have hMono := MbarRing.Poll.okPolls_mono empty (X.tr g) hak.le
      have hNext := MbarRing.Poll.okPolls_mono empty (X.tr g) (show k + 1 ≤ j by omega)
      have hGrow := grows hf hKind
      change okPolls empty (traceTake a) ≤ okPolls empty (traceTake k) at hMono
      change okPolls empty (traceTake (k + 1)) ≤ okPolls empty (traceTake j) at hNext
      dsimp only [prev] at hCount
      omega

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
