-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.RescaleSkip
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- **The evidence that lane `h`, at index `t`, is past the rescale decision of its round**: its
last barrier-zero event is the optional rendezvous, or it skipped the rescale with no barrier-zero
event since. -/
def PostVisit (L : Launch) (X : Execution) (h t : Nat) : Prop :=
  (∃ u kd, X.get (h, u) = some ⟨2326, kd⟩ ∧ ((X.tr h).take u).countP (Execution.isBarId 0) + 1 =
    ((X.tr h).take t).countP (Execution.isBarId 0)) ∨
  ∃ v a b c r ok, X.get (h, v) = some ⟨2255, .shfl .bfly a b c r ok⟩ ∧
    rescaleSkip L a r = true ∧ ((X.tr h).take v).countP (Execution.isBarId 0) =
      ((X.tr h).take t).countP (Execution.isBarId 0)

end PTX.Kernels.InklingRelDecode.Proof.Lib
