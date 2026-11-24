-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine

@[expose] public section

/-! # The loader warps' fragment

The definitions of `Loader/Handoff.lean`, which proves the step obligations and the hand-off. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The warp of the fragment: 15 for `true`, 14 for `false`. -/
def wOf (b : Bool) : Nat := if b then 15 else 14

/-- The startup's values of the registers live at pc 179 that the loader never reads: four
shared-memory barrier addresses and the LSE pointer and stride. -/
def ent (p : Params) (L : Launch) (r : Nat) : Value :=
  if r = 1069 then b32 (L.sharedBase + 192) else if r = 2390 then b32 (L.sharedBase + 208)
  else if r = 6495 then b32 (L.sharedBase + 144) else if r = 6497 then b32 (L.sharedBase + 224)
  else if r = 7500 then b64 p.lseBase else if r = 7501 then b64 p.lseStride else .pred false

/-- **The loader warps' fragment** (warp `wOf b`). -/
abbrev F (p : Params) (L : Launch) (g : Nat) (b : Bool) : Flow.Code kernel Assumptions.all L g :=
  code p L g (wOf b) (ent p L)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
