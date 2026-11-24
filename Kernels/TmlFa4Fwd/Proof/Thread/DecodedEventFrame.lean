-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.EventFrame

/-- Event opcodes with no implicit read of a changing special register. -/
def ordinaryEvent (op : Op) : Bool :=
  match op with
  | .int .. | .move .. | .cvt .. => false
  | _ => true

/-- Ordinary returning events retain the program counter or advance one instruction. -/
theorem ordinaryEventFrame {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {op : Op} (hOp : ordinaryEvent op = true) :
    ReturnedFrame s.pc (eventTmpl A l g s op) := by
  cases op <;> simp only [ordinaryEvent, Bool.false_eq_true] at hOp
  all_goals simp only [eventTmpl]
  case mem => exact mem_frame
  case warp => exact warp_frame
  case matrix => exact matrix_frame
  case barSync | barSyncN | barArrive => exact bar_frame
  case cluster => exact Or.inr rfl
  case setMaxReg => exact setMaxNReg_frame
  case cpTensor => exact tensor_frame
  case prefetchTensor | prefetchBulk => exact tensorPrefetch_frame
  case cpAsync | cpAsyncCommit | cpAsyncWait | cpAsyncArrive => exact cpAsync_frame
  case asyncStore => exact asyncStore_frame
  case cpTensorStore | bulkCommit | bulkWait => exact tensorStore_frame
  case clcTryCancel | clcQuery => exact clc_frame
  case fence => exact fence_frame
  case mbarInit | mbarInval | fenceMbarInit | mbarArrive | mbarWait | cpBulk =>
    exact widen_frame tma_frame
  case tcCommit => exact tcCommit_frame
  case tcLd => exact tcLd_frame
  case tcSt => exact tcSt_frame
  case tcAlloc | tcDealloc | tcRelinquish | tcMma | tcFenceBefore | tcFenceAfter |
      tcWaitLd | tcWaitSt | tcCp | tcShift => exact tc_frame
  all_goals exact True.intro

end PTX.Kernels.TmlFa4Fwd.Epilogue
