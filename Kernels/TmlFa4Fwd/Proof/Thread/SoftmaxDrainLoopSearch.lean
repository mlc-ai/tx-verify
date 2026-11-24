-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainLoopRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- Reached terminal search in either case of the runtime branch, in the same execution. -/
def LaterTerminalSearch (p : Params) (l : Launch) (X : Execution) (g first shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  (tilePrefix p p.batch*p.heads ≤ g/l.block ∧ ∃ steps, Nonempty (SchedulerWarpReached l X g 7720
    (fun lane => terminalExhaustedSearch p l (warpLane l g lane)) (shuffles+7*steps) votes ends)) ∨
  ∃ chosen steps, first < chosen ∧ chosen < p.batch ∧
    tilePrefix p chosen*p.heads ≤ g/l.block ∧
    g/l.block < tilePrefix p (min p.batch (chosen+31))*p.heads ∧
    Nonempty (SchedulerWarpReached l X g 7720
      (fun lane => let t := warpLane l g lane
        (7262,b32 (groupLaneTiles p chosen (laneOf l t)))::terminalSelectedGroup p l t chosen)
      (shuffles+7*steps) votes ends)

/-- Traverse an arbitrary number of remaining groups by replaying each actual scan round. -/
theorem terminalDrainSearchOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads) {first shuffles votes : Nat}
    (hFirst : first ≤ p.batch)
    (hPast : tilePrefix p (min p.batch (first+31))*p.heads ≤ g/l.block) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7666
      (fun lane => terminalSearchLoop p l (warpLane l g lane) first) shuffles votes ends) :
    LaterTerminalSearch p l X g first shuffles votes ends := by
  have hNext := terminalDrainAdvanceGroup hp hg hFirst cur
  by_cases h : p.batch ≤ first+31
  · rw [ite_eq_left h] at hNext
    exact .inl ⟨by simpa [Nat.min_eq_left h] using hPast,0,by simpa using hNext⟩
  · rw [ite_eq_right h] at hNext
    obtain ⟨reads⟩ := hNext
    obtain ⟨down⟩ := terminalDrainReadsNextGroup hp hMax hCuQ hg reads
    have hf : first+31 ≤ p.batch := by omega
    obtain ⟨next⟩ := terminalDrainLaterWindowOfMaximal hp hMax hg hf down
    have hRoute := terminalDrainLaterRouteOfMaximal hp hMax hg hf next
    by_cases hMore : tilePrefix p (min p.batch (first+31+31))*p.heads ≤ g/l.block
    · rw [ite_eq_left hMore] at hRoute
      obtain ⟨edge⟩ := hRoute
      rcases terminalDrainSearchOfMaximal hp hMax hCuQ hg hf hMore edge with hEnd | hFound
      · obtain ⟨hCut,steps,hEnd⟩ := hEnd
        have hCount : (shuffles+6+1)+7*steps = shuffles+7*(steps+1) := by omega
        exact .inl ⟨hCut,steps+1,by simpa only [hCount] using hEnd⟩
      · obtain ⟨chosen,steps,hBefore,hAfter,hLo,hHi,hChosen⟩ := hFound
        have hCount : (shuffles+6+1)+7*steps = shuffles+7*(steps+1) := by omega
        exact .inr ⟨chosen,steps+1,by omega,hAfter,hLo,hHi,by
          simpa only [hCount] using hChosen⟩
    · rw [ite_eq_right hMore] at hRoute
      exact .inr ⟨first+31,1,by omega,by omega,
        by simpa only [Nat.min_eq_right hf] using hPast,Nat.lt_of_not_ge hMore,
        by simpa using hRoute⟩
termination_by p.batch-first
decreasing_by omega

end PTX.Kernels.TmlFa4Fwd.Softmax
