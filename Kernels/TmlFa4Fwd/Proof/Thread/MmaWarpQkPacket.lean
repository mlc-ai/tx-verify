-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkIssueProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Kernels.TmlFa4Fwd.Proof.MmaQkCommit
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    (block : Fin 4) (use : Nat) (leader : Fin 32) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (qkPc block)
      (fun lane => (qkGuard block,.pred (laneOf l (warpLane l g lane) == leader)) :: F lane)
      shuffles votes ends)
    (hOperands : ∀ step, Holds (cur.state leader.val).regs (qkIssueFacts l block step use))
include hp hMax hg block use leader cur hOperands

/-- Run the entire recorded elected QK packet. The selected lane issues exactly eight fragments,
while the other lanes advance locally and all collective counts remain intact. -/
theorem qkWarpPacketWithPollCounts :
    ∃ next : SchedulerWarpReached l X g (qkPc block+8) F shuffles votes ends,
      (∀ lane < 32, next.pos lane = cur.pos lane+(if lane = leader.val then 8 else 0)) ∧
      (∀ lane < 32, elections X (warpLane l g lane) (next.pos lane) =
        elections X (warpLane l g lane) (cur.pos lane)) ∧
      (∀ lane < 32, ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
        okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
      ∀ step : Fin 8, X.get (warpLane l g leader.val,cur.pos leader.val+step.val) =
        some (qkIssueEvent l (warpLane l g leader.val) block step use) := by
  let th := warpLane l g
  let pos := fun lane => cur.pos lane+(if lane = leader.val then 8 else 0)
  let _ : Nonempty TState := ⟨cur.state 0⟩
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hEach (lane : Nat) (hl : lane < 32) : ∃ before state,
      At state (qkPc block+8) (F lane) ∧
      Run kernel Assumptions.all l (th lane) before ((X.tr (th lane)).drop (pos lane))
        (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (th lane)) before state ∧
      Run kernel Assumptions.all l (th lane) {} ((X.tr (th lane)).take (pos lane))
        (some before) ∧
      pos lane ≤ (X.tr (th lane)).length ∧
      (pos lane = (X.tr (th lane)).length → Step.Released l X (th lane)) ∧
      ((X.tr (th lane)).take (pos lane)).countP Execution.isShfl = shuffles ∧
      ((X.tr (th lane)).take (pos lane)).countP isFullWarpVote = votes ∧
      elections X (th lane) (pos lane) = elections X (th lane) (cur.pos lane) ∧
      (∀ other, okPolls other ((X.tr (th lane)).take (pos lane)) =
        okPolls other ((X.tr (th lane)).take (cur.pos lane))) ∧
      (lane = leader.val → ∀ step : Fin 8, X.get (th lane,cur.pos lane+step.val) =
        some (qkIssueEvent l (th lane) block step use)) := by
    obtain ⟨hWarp,hLane⟩ := Step.sameWarp_lane hBlock hg hl
    have ht := cur.checkpoint lane hl
    by_cases hLead : lane = leader.val
    · subst lane
      obtain ⟨before,ready,hAt,hPast,hRun,hLocal,hCounts,hEvents⟩ :=
        qkPacketOfMaximal hp hMax hWarp.1.2.1 block use (ht.mono ht.2.2.2.2.2) hOperands
          (cur.recorded leader.val hl) (cur.continuation leader.val hl)
          (cur.localSteps leader.val hl)
          (cur.positive leader.val hl) (cur.bounded leader.val hl) (cur.released leader.val hl)
      have hLen : cur.pos leader.val+8 = cur.pos leader.val+(7 : Fin 8).val+1 := by omega
      have he := hEvents 7
      have hBound : cur.pos leader.val+8 ≤ (X.tr (th leader.val)).length :=
        hLen.symm ▸ Nat.succ_le_of_lt (len_of_get he)
      have hRelease : cur.pos leader.val+8 = (X.tr (th leader.val)).length →
          Step.Released l X (th leader.val) :=
        hLen.symm ▸ releasedIfLast he (by intro h; cases h)
      have hS := (hCounts Execution.isShfl (fun _ => rfl)).trans (cur.ordinals.shfl leader.val hl)
      have hV := (hCounts isFullWarpVote (fun _ => rfl)).trans (cur.ordinals.vote leader.val hl)
      have hE : elections X (th leader.val) (cur.pos leader.val+8) =
          elections X (th leader.val) (cur.pos leader.val) :=
        hCounts isElectEv (fun _ => rfl)
      simpa only [pos,↓reduceIte] using
        ⟨before,ready,hAt,hRun,hLocal,hPast,hBound,hRelease,hS,hV,hE,
          fun other => hCounts (okPoll other) (fun _ => rfl),fun _ => hEvents⟩
    · have hPred : (laneOf l (th lane) == leader.val) = false :=
        beq_eq_false_iff_ne.mpr (fun h => hLead (hLane.symm.trans h))
      rw [hPred] at ht
      obtain ⟨ready,hAt,hLocal⟩ := skipQK (l := l) (g := th lane) block ht
      have hNoPoll : ∀ other, okPolls other ((X.tr (th lane)).take (cur.pos lane)) =
          okPolls other ((X.tr (th lane)).take (cur.pos lane)) := fun _ => rfl
      rw [show pos lane = cur.pos lane by simp [pos,hLead]]
      exact ⟨cur.before lane,ready,hAt,cur.continuation lane hl,
          (cur.localSteps lane hl).trans hLocal,
          cur.recorded lane hl,cur.bounded lane hl,cur.released lane hl,cur.ordinals.shfl lane hl,
          cur.ordinals.vote lane hl,rfl,hNoPoll,fun h => (hLead h).elim⟩
  choose! before state hAt hRun hLocal hPast hBound hRelease hS hV hE hPoll hEvents using hEach
  let next : SchedulerWarpReached l X g (qkPc block+8) F shuffles votes ends :=
    ⟨⟨pos,before,state,⟨hS,hV⟩,hRun,hLocal,hAt⟩,
      fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right ..),
      hBound,hRelease,hPast⟩
  exact ⟨next,fun _ _ => rfl,hE,hPoll,hEvents leader.val leader.isLt rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
