-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.RescaleSkip
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- **The evidence that lane `h`, at index `t`, took the rescale decision the other way** from the
lane at index `j` of lane `g`: its skipping shuffle at the same barrier ordinal, or its store wait
as its last collective event. -/
def Dissent (L : Launch) (X : Execution) (g j h t : Nat) : Prop :=
  (∃ v a b c r ok, X.get (h, v) = some ⟨2255, .shfl .bfly a b c r ok⟩ ∧
    rescaleSkip L a r = true ∧ ((X.tr h).take v).countP (Execution.isBarId 0) =
      ((X.tr g).take j).countP (Execution.isBarId 0)) ∨
  ∃ u kd, X.get (h, u) = some ⟨2329, kd⟩ ∧
    ((X.tr h).take u).countP isTcColl + 1 = ((X.tr h).take t).countP isTcColl

end PTX.Kernels.InklingRelDecode.Proof.Lib
