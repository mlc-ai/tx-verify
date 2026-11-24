-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # The `+inf` LSE pattern

An empty row writes the f32 `+inf` pattern `0f7F800000` (`kernel.cuh:298`). `Post` states the
same bytes through `infByte`; this file proves the two spellings equal. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
open PTX

/-- The four bytes of the `+inf` pattern that `infByte` names are the four bytes of
`0f7F800000`. -/
theorem infByte_eq (k : Nat) :
    infByte k = (Value.bits 32 (BitVec.ofNat 64 0x7F800000), k) := by
  rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
