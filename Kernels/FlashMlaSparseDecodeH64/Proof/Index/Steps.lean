-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StepsLen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StepsMain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StepsExtra

@[expose] public section

/-! # The index warp's obligations

Every state of the index warp's control machine obeys its UB-tolerant step obligation
(`Index.stepAt`); one theorem per site, in the three files. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {g : Nat}

/-- **Every state of the index warp steps.** -/
theorem stepAt (d : D) : (code P L g).StepAtU d := by
  cases hs : d.site
  · exact stepAt_lenA d hs
  · exact stepAt_lenB d hs
  · exact stepAt_pre d hs
  · exact stepAt_pf d hs
  · exact stepAt_wA d hs
  · exact stepAt_sA1 d hs
  · exact stepAt_sA2 d hs
  · exact stepAt_stA d hs
  · exact stepAt_bA d hs
  · exact stepAt_arrA d hs
  · exact stepAt_xpre d hs
  · exact stepAt_xpf d hs
  · exact stepAt_wB d hs
  · exact stepAt_sB1 d hs
  · exact stepAt_sB2 d hs
  · exact stepAt_stB d hs
  · exact stepAt_bB d hs
  · exact stepAt_arrB d hs
  · exact stepAt_bar d hs
  · exact stepAt_exit d hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
