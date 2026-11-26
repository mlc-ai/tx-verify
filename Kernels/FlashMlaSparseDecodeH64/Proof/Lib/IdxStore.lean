-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # The index warp's shared writes

`idxWr e`: `e` is a write at a pc of the index warp's code (pcs 2332 to 2586). Per block a lane
makes two such writes (the coordinate pair) and, on lanes `0 mod 4`, a third (the validity byte);
a prefix's count of them is read off the reference invariant (`Index/Export/Store.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- An event is a write at a pc of the index warp's code. -/
def idxWr (e : Event) : Bool :=
  decide (2332 ≤ e.pc ∧ e.pc ≤ 2586) && match e.kind with | .wr .. => true | _ => false

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
