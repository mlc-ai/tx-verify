-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.ReqOnce
import Lemmas.Kernel.Safety.Schedule

@[expose] public section

/-! # ERR-SETMAXNREG: setmaxnreg requests are legal

The safety class of Core's `Unsafe` this file owns (`SetMaxNReg.UnsafeAt`). Every thread makes
one request, its first (`request_first`), at its warpgroup's pc (`request_pc`): `dec`/`inc`
and the count are the instruction's there, the same for the lanes of a warpgroup
(`regCount`, `Frame.noSetMaxNReg_of_first`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Proof MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-SETMAXNREG**: setmaxnreg requests are legal. -/
theorem Safe.noRegister (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ SetMaxNReg.UnsafeAt Assumptions.all L X :=
  Frame.noSetMaxNReg_of_first ⟨by rw [hp.block]; decide, by rw [hp.block]⟩
    (fun g => regCount (warp L g))
    (fun g k pc inc n inst he => request_value hp hX hFw hnu he)
    (fun g h hs => regCount_group hp hs)
    (fun ⟨g, k⟩ pc inc n inst he => request_first hp hX hFw hnu he)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
