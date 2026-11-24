-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
public import Lemmas.Flow.Arith32Word

@[expose] public section

/-! # The tile count's division

Every role's `afterTiles` divides the batch's tile count by the two coordinate divisions of its own
`coords`, and dies (`none`) when a division has no rule. The roles' coordinate divisions are the
output warp's, so a role's `afterTiles` dies only where the output warp's does. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

/-- **Two tile counts die together**: `afterTiles` of a scan record whose coordinates agree on the
two divisions dies only where the other's does, whatever the record after the divisions. -/
theorem afterTiles_none_of {co co' : Epilogue.Coords} (h1 : co.n1 = co'.n1) (h2 : co.d1 = co'.d1)
    (h3 : co.n2 = co'.n2) (h4 : co.d2 = co'.d2) {α β : Type} {f : α} {g : β}
    (h : (if divOk co.n1 co.d1 then (if divOk co.n2 co.d2 then some f else none) else none) =
      none) :
    (if divOk co'.n1 co'.d1 then (if divOk co'.n2 co'.d2 then some g else none) else none) =
      none := by
  simp only [h1, h2, h3, h4] at h ⊢
  split_ifs at h ⊢ <;> simp_all

end PTX.Kernels.TmlFa4Fwd.Proof
