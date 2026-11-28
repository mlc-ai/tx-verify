-- SPDX-License-Identifier: Apache-2.0
-- iface: KvCopyForm producer=W status=proved domain=consistent
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

/-- **The form of the tensor loads**: every tensor load of the kernel copies a 64 by 64 box of
the K or V columns of a slab of a block that exists (`kvh`, `isV` and the half `hh` name the 64
columns, the slab's page and head fix the row), into the issuer's CTA. -/
def KvCopyForm (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a sp}, X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ →
    ∃ r sl kvh isV hh dst bar, r < Q.b ∧ sl < 2 * Q.blocks r ∧ kvh < kvHeads ∧ isV ≤ 1 ∧
      hh ≤ 1 ∧ dst % 1024 = 0 ∧ sp = ⟨⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass,
        ![(BitVec.ofNat 32 (kvh * Q.headCols + 128 * isV + 64 * hh)).toInt,
          (BitVec.ofNat 32 (Q.page r sl * Q.pageRows + kvh * Q.headRows)).toInt],
        ⟨.shared, g / L.block, dst⟩, none⟩, bar, false, .one⟩

end PTX.Kernels.InklingRelDecode.Proof.Iface
