-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- A reached affine state whose preceding publication may still need its
warp record to return. Its local instructions and trace do not change on release. -/
structure AffineCursor (l : Launch) (X : Execution) (g pc : Nat) where
  pos : Nat
  before : TState
  ready : TState
  ending : Option TState
  positive : 0 < pos
  bounded : pos ≤ (X.tr g).length
  checkpoint : At ready pc []
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  remaining : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready

/-- Register replay transfers the reached state into a history with the same
trace once its final publication has been released. -/
def AffineCursor.resume {l : Launch} {X Y : Execution} {g pc : Nat}
    (c : AffineCursor l X g pc) (hTrace : Y.tr = X.tr)
    (hReleased : c.pos = (X.tr g).length → Step.Released l Y g) :
    OpeningTripCursor l Y g pc [] :=
  ⟨c.pos,c.before,c.ready,c.ending,c.positive,by simpa only [hTrace] using c.bounded,
    fun h => hReleased (by simpa only [hTrace] using h),c.checkpoint,
    by simpa only [hTrace] using c.recorded,by simpa only [hTrace] using c.remaining,c.localSteps⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
