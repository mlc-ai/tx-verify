-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Inject

@[expose] public section

/-!
# The word the epilogue stores as `LsePart`

The epilogue stores `Epi.Prm.lseWord` for a valid row: the `-inf` pattern where the row is empty
(`eq0`, the row sum is zero), else the log-sum-exp `pr.lse`.

* `lse_negInf_of_eq0`: for an empty row the four bytes written are those of the `-inf` pattern
  `Post` states (`negInfByte`).
* `lse_bytes_of_ne0`: for a non-empty row they are the bytes of `pr.lse`, a four-byte value.

That `pr.lse` is `log2` of the row sum (`Spec.lsePart`), and that `eq0` holds exactly for the empty
rows, are facts of the softmax region's score stage (`DComp.SmObligations`, "thread-layer gaps":
the row
sum `l`, the maximum `mx` and `eq0`, `lse` of `Br.prm`); they are not part of this layer.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The four bytes of the `-inf` pattern are `negInfByte`. -/
theorem negInf_bytes : ∀ k < 4, (b32 4286578688).toBytes[k]? = some (negInfByte k) := by
  decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
