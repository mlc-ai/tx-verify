-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepTma

@[expose] public section

/-! # The TMA warp's obligations at the two length loads

The row's two lengths, read by `ld.global.nc` where their pointers are set: a 32-bit word
continues, any other value stops the machine. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

theorem stepAt_loadTopk (d : D) (hs : d.site = .loadTopk) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

theorem stepAt_loadExtra (d : D) (hs : d.site = .loadExtra) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
