-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Execution.NoBarArrive

@[expose] public section

/-! # The kernel has no `bar.arrive`

A static check of the code, for the named-barrier tools that need every arrival to be a
`bar.sync` (`Fact kernel.NoBarArrive`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- **No instruction of the kernel is a `bar.arrive`.** -/
theorem kernel_noBarArrive : kernel.NoBarArrive := by
  unfold Kernel.NoBarArrive
  decide +kernel

instance : Fact kernel.NoBarArrive := ⟨kernel_noBarArrive⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
