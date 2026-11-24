-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.KkRdv
public import Kernels.InklingRelDecode.Proof.Result.KkPRead

@[expose] public section

/-!
# The rendezvous premises of `InputsRest` by the barrier-0 counts: umbrella

`KkRdv.lean`: `Kk.oRdv_of` (`Rd.ORdv`) and `Kk.sPstAfter_of` (`Rd.SPstAfter`), from the counts of
`Interface/KkBar.lean` (two default threads of a CTA at `bar20` of one iteration are at one
barrier-0 ordinal when the decisions of every iteration agree).

`KkPRead.lean`: `Kk.pReadSrc_of` (`Rs.PReadSrc`), from the package's `P` stores (whose coordinate
is the thread's iteration, `Kk.pst_iter`) and `Interface/KkTmemSt.lean` (one `P` store per
iteration of a thread, in the order of the iterations).
-/
