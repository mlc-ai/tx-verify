-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Kernels.InklingRelDecode.Proof.Mma.NoUbSite
import Kernels.InklingRelDecode.Proof.Mma.Steps
import Kernels.InklingRelDecode.Proof.Mma.StepsRead
import Kernels.InklingRelDecode.Proof.Mma.StepsIssue
import Kernels.InklingRelDecode.Proof.Mma.StepsStart
import Kernels.InklingRelDecode.Proof.Mma.StepsElect
import Kernels.InklingRelDecode.Proof.Mma.StepsPrepare
import Kernels.InklingRelDecode.Proof.Mma.Broadcast
import Kernels.InklingRelDecode.Gen.StepDispatch

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

/-- Every normal event reaches its predicted successor or reaches a final fault in
the intervening scalar code. The role takes the recorded allocation word verbatim. -/
theorem stepsU {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {regs : Nat → Value}
    (hp : Pre Q L m) (w : Value) (d : D) : (code L g regs w).StepAtU d := by
  obtain ⟨s,i,v⟩ := d
  cases s with
  | setMaxReg => exact (dec_step ..).toStepAtU
  | ldNum => exact (iter_read_step ..).toStepAtU
  | bar0 => exact start_bar_step hp i v
  | qkBar => exact (kv_bar_step ..).toStepAtU
  | kvWait => exact (kv_poll_step ..).toStepAtU
  | qkShfl => exact qk_broadcast_step i v
  | qkBar2 => exact qk_prepare_step hp i v
  | qkSkip => exact qk_skip_step hp i v
  | qkElect => exact qk_election hp i v
  | qk j => exact (qk_issue_step hp j i v).toStepAtU
  | qkCommit => exact qk_notify_step hp i v
  | pvBar => exact (p_bar_step ..).toStepAtU
  | pWait => exact (p_poll_step ..).toStepAtU
  | pvShfl => exact pv_broadcast_step i v
  | pvBar2 => exact pv_prepare_step hp i v
  | pvSkip => exact pv_skip_step hp i v
  | pvElect => exact pv_election hp i v
  | pv j => exact (pv_issue_step hp j i v).toStepAtU
  | pvCommit1 => exact (pv_notify_step hp i v).toStepAtU
  | pvCommit2 => exact pv_done_step hp i v
  | finBar => exact (final_bar_step ..).toStepAtU
  | finElect => exact (final_elect_step hp i v).toStepAtU
  | finCommit => exact (final_commit_step ..).toStepAtU
  | bar1 => exact (return_bar_step ..).toStepAtU
  | setMaxRegInc => exact (inc_step ..).toStepAtU
  | dispatch =>
    exact ⟨fun _ => ⟨_, Flow.code_2337, rfl, trivial⟩, fun _ _ _ _ _ => .inl (.inl rfl)⟩

end PTX.Kernels.InklingRelDecode.Proof.Mma
