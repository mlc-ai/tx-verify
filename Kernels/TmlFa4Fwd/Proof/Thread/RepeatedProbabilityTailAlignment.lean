-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityMainPacket
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityTailElection
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

private theorem repeatedProbabilityCount
    {l : Launch} {X : Execution} {g start : Nat} {test : Event → Bool}
    (hTc : ∀ pc kind, test ⟨pc,.tc kind⟩ = false)
    (hArrive : ∀ pc loc tx n release scope, test ⟨pc,.arrive loc tx n release scope⟩ = false)
    (mode : Repeated) (stage : Fin 2) (weights : Nat → ℝ)
    (hStores : ∀ q : Fin 4, X.get (g,start+mode.probabilityStoreOffset q) =
      some (repeatedStoreEvent l g stage mode.round q weights))
    (hDelayed : mode = .biased →
      X.get (g,start) = some ⟨probabilityPc mode.round 0,.tc .waitLd⟩)
    (hWait : X.get (g,start+(if mode = .biased then 1 else 0)+3) =
      some ⟨probabilityWaitPc mode.round false,.tc .waitSt⟩)
    (hCredit : Thread.Scores.ProbabilityCredit l X
      (g,start+(if mode = .biased then 1 else 0)+4) (g/l.block) stage 0)
    (hTail : X.get (g,start+(if mode = .biased then 1 else 0)+6) =
      some ⟨probabilityWaitPc mode.round true,.tc .waitSt⟩) :
    ((X.tr g).take (start+(if mode = .biased then 1 else 0)+7)).countP test =
      ((X.tr g).take start).countP test := by
  let delay := if mode = .biased then 1 else 0
  let base := start+delay
  let count n := ((X.tr g).take n).countP test
  have store (q : Fin 4) :
      count (base+(if q.val = 3 then 5 else q.val)+1) =
        count (base+(if q.val = 3 then 5 else q.val)) := by
    have hPos : start+mode.probabilityStoreOffset q =
        base+(if q.val = 3 then 5 else q.val) := by
      cases mode <;> fin_cases q <;> simp [Repeated.probabilityStoreOffset,base,delay,Nat.add_assoc]
    have he := hStores q
    rw [hPos] at he
    exact countP_take_succ_false he (hTc _ _)
  obtain ⟨pc,hC⟩ := hCredit
  change X.get (g,base+4) = some ⟨pc,.arrive _ 0 1 true .cta⟩ at hC
  have hBase : count base = count start := by
    by_cases h : mode = .biased
    · have hc := countP_take_succ_false (hDelayed h) (hTc _ _)
      simpa only [base,delay,ite_eq_left h] using hc
    · simp only [base,delay,ite_eq_right h,Nat.add_zero]
  change count (base+7) = count start
  calc
    _ = count (base+6) := countP_take_succ_false hTail (hTc _ _)
    _ = count (base+5) := store 3
    _ = count (base+4) := countP_take_succ_false hC (hArrive ..)
    _ = count (base+3) := countP_take_succ_false hWait (hTc _ _)
    _ = count (base+2) := store 2
    _ = count (base+1) := store 1
    _ = count base := store 0
    _ = count start := hBase

/-- The four stores, two store waits, main credit and optional delayed load wait
do not change either warp-rendezvous ordinal before the tail. -/
theorem repeatedProbabilityTailOrdinals
    {l : Launch} {X : Execution} {g start : Nat}
    (mode : Repeated) (stage : Fin 2) (weights : Nat → ℝ)
    (hStores : ∀ q : Fin 4, X.get (g,start+mode.probabilityStoreOffset q) =
      some (repeatedStoreEvent l g stage mode.round q weights))
    (hDelayed : mode = .biased →
      X.get (g,start) = some ⟨probabilityPc mode.round 0,.tc .waitLd⟩)
    (hWait : X.get (g,start+(if mode = .biased then 1 else 0)+3) =
      some ⟨probabilityWaitPc mode.round false,.tc .waitSt⟩)
    (hCredit : Thread.Scores.ProbabilityCredit l X
      (g,start+(if mode = .biased then 1 else 0)+4) (g/l.block) stage 0)
    (hTail : X.get (g,start+(if mode = .biased then 1 else 0)+6) =
      some ⟨probabilityWaitPc mode.round true,.tc .waitSt⟩) :
    let stop := start+(if mode = .biased then 1 else 0)+7
    warpBars X g stop = warpBars X g start ∧ elections X g stop = elections X g start :=
  ⟨repeatedProbabilityCount (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    mode stage weights hStores hDelayed hWait hCredit hTail,
   repeatedProbabilityCount (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    mode stage weights hStores hDelayed hWait hCredit hTail⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
