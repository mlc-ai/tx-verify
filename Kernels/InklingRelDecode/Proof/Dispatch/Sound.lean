-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
public import Kernels.InklingRelDecode.Proof.Dispatch.NoUbSite
import Kernels.InklingRelDecode.Proof.Dispatch.Read
import Kernels.InklingRelDecode.Proof.Dispatch.Steps

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX.Flow

theorem steps {L : Launch} {g first : Nat} {regs : Nat → Value} {x : BitVec 64} (d : D) :
    (code L g regs x first).StepAt d := by
  obtain ⟨site, round⟩ := d
  cases site with
  | head => exact head_step
  | sync => exact sync_step
  | read => exact read_step
  | idleDec => exact idleDec_step
  | idleSync => exact idleSync_step
  | idleSyncAgain => exact idleSyncAgain_step
  | idleInc => exact idleInc_step
  | badSync => exact badSync_step
  | badSyncAgain => exact badSyncAgain_step
  | loaderEntry => exact loaderEntry_step
  | mmaEntry => exact mmaEntry_step
  | exitSync => exact exitSync_step
  | exitDealloc => exact exitDealloc_step
  | ret => exact ret_step

theorem stepsU {L : Launch} {g first : Nat} {regs : Nat → Value} {x : BitVec 64} (d : D) :
    (code L g regs x first).StepAtU d := (steps d).toStepAtU

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
