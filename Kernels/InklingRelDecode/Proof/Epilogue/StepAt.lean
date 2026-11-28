-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Wait
public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Load
public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Exit

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof

theorem stepAt {e L g} (d : D) : (code e L g).StepAtU d := by
  obtain ⟨s,v⟩ := d
  cases s with
  | wait => exact step_wait
  | shfl => exact step_shfl
  | load => exact step_load
  | waitLd => exact step_waitLd
  | lse => exact step_lse
  | store j => exact step_store j
  | join => exact step_join
  | setMax => exact step_setMax
  | roleWord => exact step_roleWord
  | sync1 => exact step_sync1
  | sync0 => exact step_sync0
  | dealloc => exact step_dealloc
  | exit => exact step_exit

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
