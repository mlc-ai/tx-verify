-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Protocol.Bar.CtaMismatch

@[expose] public section

/-! # ERR-CTA-BARRIER

A fault is a count mismatch with an arrival of the open generation or a second arrival of a warp in
one generation (`NamedBar.Multi.no_fault_of_mismatch`). `Protocol.Bar.bar_no_mismatch` excludes the
mismatch: barrier 0 serves the two startup rendezvous (all warps), the half-CTA rendezvous of the
four data warps, and the final full rendezvous, which follows all of them. It takes race freedom
for the lockstep of the data lanes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noCtaBar (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (safe : ¬ Race L X) : ¬ CtaBarFault L X :=
  Protocol.Bar.no_cta_bar_fault hp hX hf words safe

end PTX.Kernels.InklingRelDecode.Proof.Top
