-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Regs

@[expose] public section

/-! # The registers at the first shuffle

`abiFacts` states the registers the ABI prefix leaves (`Startup/Abi.lean` proves that it does). The
thread machine reads only this definition. -/

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Proof

noncomputable section

/-- Parameter words and address registers live at the first shuffle. -/
def abiFacts (p : Params) (l : Launch) : List (Nat × Value) :=
  [(1, b64 l.localBase),
   (7492, b64 p.kLayout.base), (7493, b64 p.kLayout.rowStride),
   (7494, b64 p.kLayout.headStride), (7495, b64 p.kLayout.pageStride),
   (1663, b32 16), (1664, b32 p.kvHeads),
   (7496, b64 p.vLayout.base), (7497, b64 p.vLayout.rowStride),
   (7498, b64 p.vLayout.headStride), (7499, b64 p.vLayout.pageStride),
   (7500, b64 p.lseBase), (7501, b64 p.lseStride),
   (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
   (7504, b64 p.pageTableBase), (7505, b64 p.pageTableStride),
   (7291, .ptr 64 false (.param (param 9)) 0),
   (7290, .ptr 64 false (.param (param 10)) 0),
   (7289, .ptr 64 false (.param (param 11)) 0),
   (7506, b64 p.cuQBase),
   (7292, b64 (l.localBase + 0)), (7293, b64 (l.localBase + 32)),
   (7294, b64 (l.localBase + 64)), (7295, b64 (l.localBase + 96)),
   (1665, b32 l.sharedBase)]

end
end PTX.Kernels.TmlFa4Fwd.Prologue
