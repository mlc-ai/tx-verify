-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingLoaderExec
public import Lemmas.Tcgen05.TcSharedAddress
public import Lemmas.Tensor.BoxWrite
public import Kernels.InklingRelDecode.Proof2.Lib.MmaFoot

@[expose] public section

/-!
# The shared bytes of the KV ring's copies and MMA operands

The bytes of a ring slot `s` are the K region `[sharedBase + 32768 s, + 32768)` and the V region
`[sharedBase + 98304 + 32768 s, + 32768)`.

* `copy_foot`: a tensor copy of the loader (`kvCopySpec`, a `(64, 64)` bf16 box of the `kv_rows`
  map, 128-byte swizzle) writes only bytes of its destination box `[dst, dst + 8192)`: the byte
  at row `y`, column `x` is `dst + offset .b128 dst (128 y + 2 x + z)`, below `128 · 64`
  (`TensorCopy.box_offset_lt`).
* `qk_b_foot`: a QK MMA's B operand (the K tile, K-major, `kMajorDesc`) reads only bytes of the
  16384-byte half `hh` of the slot's K region: the 128-byte swizzle permutes the 16-byte chunks of
  a 128-byte row (`TensorSwizzle.offset_row`), so the address stays in the row of its unswizzled
  address `start + 128 (r % 8) + 1024 (r / 8) + 2 k + z`.
* `pv_b_foot`: a PV MMA's B operand (the V tile, MN-major, leading offset 16384, stride 1024)
  reads only bytes of the slot's V region: the unswizzled address is
  `start + 2 (n % 8) + 16 (n / 8 % 8) + 16384 (n / 64) + 128 (k % 8) + 1024 (k / 8)`.

Together with the copies' destination boxes (`ldDst`: K slab `a`, half `hh` at
`32768 s + 8192 a + 16384 hh`, V at `+ 98304`) these say that the K tile of a slot is written by
the four K copies and read by the eight QK MMAs through exactly the same 32768 bytes, and likewise
for V.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Foot
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec)

noncomputable section

/-! ### The loader's copies -/

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Foot
