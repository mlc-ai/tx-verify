-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Epi.StepAt

@[expose] public section

/-! # Warpgroup 0's step obligations

`Wg0.Control.stepAt`: every state of warpgroup 0's control machine steps (UB-tolerant), under
`Pre` only: the Loop half (`Wg0.Loop.stepAt`) and the epilogue (`Wg0.Epi.stepAt`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- **Warpgroup 0's step obligations.** -/
theorem stepAt (hp : Pre P L m) (d : D) : (code P L g w).StepAtU d := by
  cases hl : d.site.inLoop
  · exact Epi.stepAt hp d hl
  · exact Loop.stepAt hp d hl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
