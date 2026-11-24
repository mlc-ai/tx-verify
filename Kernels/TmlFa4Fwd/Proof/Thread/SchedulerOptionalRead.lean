-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

/-- Optional scalar reads advance just the participating lanes and keep both scheduler
collective ordinals. The resulting cursor retains each real prefix and release state. -/
theorem SchedulerWarpReached.afterOptionalRead {l : Launch} {X : Execution}
    {g site nextSite readSite shuffles votes : Nat} {F G : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g site F shuffles votes ends)
    (reads : Nat → Prop) [DecidablePred reads] (access : Nat → Acc)
    (bytes : Nat → List (Option Byte)) :
    let thread := warpLane l g
    let pos := fun lane => if reads lane then cur.pos lane + 1 else cur.pos lane
    (∀ lane < 32, ∃ before ready,
      pos lane ≤ (X.tr (thread lane)).length ∧
      (pos lane = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      At ready nextSite (G lane) ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take (pos lane))
        (some before) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before ready ∧
      Run kernel Assumptions.all l (thread lane) before ((X.tr (thread lane)).drop (pos lane))
        (ends lane) ∧
      (reads lane → X.get (thread lane, cur.pos lane) =
        some ⟨readSite, .rd (access lane) (bytes lane)⟩)) →
    Nonempty (SchedulerWarpReached l X g nextSite G shuffles votes ends) := by
  dsimp only
  intro hLane
  let thread := warpLane l g
  let pos := fun lane => if reads lane then cur.pos lane + 1 else cur.pos lane
  let read := fun lane => Event.mk readSite (.rd (access lane) (bytes lane))
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! before state hBound hRelease hAt hPast hLocal hRun hEvent using hLane
  have hOrd : WarpOrdinals l X g pos shuffles votes := by
    have keep (test : Event → Bool) (n : Nat)
        (hc : ∀ lane < 32, ((X.tr (thread lane)).take (cur.pos lane)).countP test = n)
        (hPlain : ∀ lane, test (read lane) = false) :
        ∀ lane < 32, ((X.tr (thread lane)).take (pos lane)).countP test = n := by
      intro lane hl
      by_cases h : reads lane
      · rw [show pos lane = cur.pos lane + 1 by simp only [pos, ite_eq_left h], List.take_add_one,
          show (X.tr (thread lane))[cur.pos lane]? = _ from hEvent lane hl h]
        have hPlain' : test ⟨readSite, .rd (access lane) (bytes lane)⟩ = false := hPlain lane
        simpa only [List.countP_append, Option.toList_some, List.countP_singleton, hPlain',
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hc lane hl
      · simpa only [pos, ite_eq_right h] using hc lane hl
    exact ⟨keep _ _ cur.ordinals.shfl (fun _ => rfl), keep _ _ cur.ordinals.vote (fun _ => rfl)⟩
  have hPositive (lane : Nat) (hl : lane < 32) : 0 < pos lane := by
    have h := cur.positive lane hl
    dsimp only [pos]
    split_ifs <;> omega
  exact ⟨⟨⟨pos,before,state,hOrd,hRun,hLocal,hAt⟩,hPositive,hBound,hRelease,hPast⟩⟩

end PTX.Kernels.TmlFa4Fwd.Epilogue
