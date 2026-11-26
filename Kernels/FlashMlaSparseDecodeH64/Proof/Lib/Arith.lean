-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32Wide

@[expose] public section

/-! # Integer forms of the code the library vocabulary does not have

The wide, 64-bit and 16-bit forms are the library's (`Lemmas/Flow/Arith32Wide.lean`). One form
stays here, the term Core's rule evaluates to, so that a table entry closes its segment by `rfl`:
`setp.eq.b64` against `0` as the walk writes it (D-P2-GAPS, G7). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow.Arith32

/-- `setp.eq.b64` against the immediate `0`. -/
abbrev eqz64 (x : BitVec 64) : Bool :=
  PTX.compare .eq .b 64 (r64 x) (truncBits 64 (BitVec.ofInt 64 0))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
