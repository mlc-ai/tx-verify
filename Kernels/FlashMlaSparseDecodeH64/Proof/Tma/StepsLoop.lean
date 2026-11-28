-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepTma

@[expose] public section

/-! # The TMA warp's obligations at its waits and arrivals

The waits on `bar_q_utccp` and `bar_last_store_done` and the loop's entry; per block the waits on
`valid_coord_ready` and `raw_free`, the arrivals on `raw_ready` and `valid_coord_free` and the
loop's end; then the CTA barrier and the `ret`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_qWait (d : D) (hs : d.site = .qWait) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

theorem stepAt_storeWait (d : D) (hs : d.site = .storeWait) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

theorem stepAt_coordWait (d : D) (hs : d.site = .coordWait) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

theorem stepAt_rawWait (d : D) (hs : d.site = .rawWait) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

theorem stepAt_rawArrive (d : D) (hs : d.site = .rawArrive) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

theorem stepAt_coordFree (d : D) (hs : d.site = .coordFree) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

theorem stepAt_outBar (d : D) (hs : d.site = .outBar) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

theorem stepAt_exit (d : D) (hs : d.site = .exit) : (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
