-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.IterRange

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- The number of KV blocks assigned to this CTA, including its preload.
The request and the split are launch coordinates shared by all eight warps. -/
def blocksOf (Q : Params) (L : Launch) (cta : Nat) :=
  Q.numIters ((L.ctaidOf cta).get .z) ((L.ctaidOf cta).get .x)

theorem blocksOf_lt {Q L m g} (hp : Pre Q L m) (hg : g < L.threads) :
    blocksOf Q L (g/L.block) < 2^31 := iter_range hp hg

end PTX.Kernels.InklingRelDecode.Proof.Lib
