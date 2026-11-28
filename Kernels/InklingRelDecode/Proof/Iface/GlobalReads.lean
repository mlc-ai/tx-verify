-- SPDX-License-Identifier: Apache-2.0
-- iface: GlobalReads producer=W status=proved domain=consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.Regions

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

/-- A footprint of global input bytes. -/
def InputAcc (Q : Params) (a : Acc) : Prop :=
  a.loc.space = .global ∧ a.loc.cta = 0 ∧ ∀ j < a.size, Q.reads (a.loc.addr + j)

/-- **Global reads**: every global byte that an access reads is an input byte. The reading
sites are the 203 of `Assumptions.inputReadSites` and the tensor loads. -/
def GlobalReads (Q : Params) (X : Execution) : Prop :=
  ∀ e a l, X.Intent e a false → a.Covers l → l.space = .global → InInput Q l

end PTX.Kernels.InklingRelDecode.Proof.Iface
