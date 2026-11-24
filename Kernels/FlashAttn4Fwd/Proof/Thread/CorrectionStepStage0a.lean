-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepEntryF

@[expose] public section

/-! # Stage 0's staging addresses (chunks 1 to 4)

The swizzled address of chunk `c` of the thread's row: the address of chunk `c - 2^k`
(bit `k` of `c` the highest set) plus the selected `±16 · 2^k` (`stage_flip`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Stage 0's staging addresses, from pc 3823 to 3827. -/
theorem entry_s0a (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 4 3823
      (factsX L g 3823 (dS aw a o)
        [(2721, b32 (trips L)), (2723, b32 0), (2727, b32 (selN (bit2 L g) 64 4294967232)),
          (2729, b32 (selN (bit1 L g) 32 4294967264)),
          (2731, b32 (selN (bit0 L g) 4294967280 16))]) 3827
      (factsX L g 3827 (dS aw a o)
        [(2721, b32 (trips L)), (2723, b32 0), (2727, b32 (selN (bit2 L g) 64 4294967232)),
          (2729, b32 (selN (bit1 L g) 32 4294967264)),
          (2731, b32 (selN (bit0 L g) 4294967280 16))]) := by
  intro t h
  stage_facts hpre L g 0
  corr_segx h hpre [selN]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
