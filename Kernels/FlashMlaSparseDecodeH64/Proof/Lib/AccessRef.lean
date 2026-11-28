-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

/-! # The two kinds of access reference

A reference to an access of the trace: a thread's own access, or the part of an asynchronous
operation (`AsyncCopy.Ref`). Named once here for the statements above the roles. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

/-- An access of a thread, or a part of an asynchronous operation of one. -/
abbrev AccessRef : Type := PTX.AsyncCopy.Ref

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
