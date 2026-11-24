-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopyQuietSlice
import Kernels.TmlFa4Fwd.Flow.Code.Part015

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Epilogue

noncomputable section

set_option maxRecDepth 100000 in
private theorem warmValueQuietAudit : CopyQuietAudit 1004 1341 := by
  refine ⟨by decide, ⟨_, Flow.code_1004, rfl, rfl⟩, ?_, ?_⟩
  · kernel_rfl
  · kernel_rfl

variable {l : Launch}

/-- A warm copy with no intervening shuffle belongs to the current packet slice,
including its final pair before the packet commit. -/
theorem warmValueQuietSlice {g start : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hStart : 174 ≤ start)
    (hAudit : ∀ bound, ((kernel.code.drop start).take (1341 - start)).all
      (fun ins => loaderPipelineCutOp start 1341 bound [] ins.op) = true)
    (hWalk : Walk kernel Assumptions.all l g s events visits) (hPc : start ≤ s.pc ∧ s.pc ≤ 1341)
    (hShape : RingShape s) {j : Nat} {e : Event} (he : events[j]? = some e)
    (hWarm : 1004 < e.pc ∧ e.pc < 1341) (hQuiet : (events.take j).countP Execution.isShfl = 0) :
    e ∈ loaderSliceEvents start 1341 visits :=
  copyQuietSlice warmValueQuietAudit hStart hAudit hWalk hPc hShape he hWarm hQuiet

end
end PTX.Kernels.TmlFa4Fwd.Loader
