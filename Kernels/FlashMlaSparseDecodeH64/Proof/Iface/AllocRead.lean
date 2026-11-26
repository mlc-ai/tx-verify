-- SPDX-License-Identifier: Apache-2.0
-- iface: AllocRead producer=R status=proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.Regs

@[expose] public section

/-! # The startup's read-back of the allocated address reads `0`

The startup (`Startup/Machine.lean`) allocates the CTA's 512 Tensor Memory columns in warp 0
(`tcgen05.alloc`, pc 91), whose second step is lane 0's store of the allocated column to the
shared allocation word; every lane of warp 0 then reads the word back (pc 92) and traps (pc 95)
unless it is `0` (no other warp reaches pc 92). `AllocRead` is that read's value, stated as
bytes ("reads as", lane rules, rule 10): the read of every launched lane at pc 92 reads the bytes
of the 32-bit word `0`.

It is a cross-lane fact: the bytes are those of the store the read reads from (lane 0's store at
pc 91, the allocation's second step, in the same warp), and the column is the allocator's result,
`0` for the CTA's only allocation of all its columns. Proved from `Follow` by `allocRead`
(`Protocol/Shared/AllocRead.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof

/-- **Row `AllocRead`**: the read at pc 92 of every launched lane reads the bytes of `b32 0`. -/
def AllocRead (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
    X.get (g, k) = some ⟨92, .rd a bs⟩ → bs = (b32 0).toBytes.map some

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
