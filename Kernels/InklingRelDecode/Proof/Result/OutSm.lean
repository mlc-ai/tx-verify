-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutEpi
public import Kernels.InklingRelDecode.Proof.Result.OutProb
public import Kernels.InklingRelDecode.Proof.Interface.All

@[expose] public section

/-!
# The softmax region's side of the epilogue's registers

The epilogue's registers are the bridge's input at the loop's exit (`DComp.exitIn`). The softmax
region proves its running maximum and sum are those of the blocks it has processed (`Sm.Corr`,
`SmBridge.corr_step`, one block at a time); `rowIn_of_corr` is the last step from there: at the
state that leaves the loop, once `Sm.Corr` holds for all `num_iters` blocks of the row (`blocks0`)
and the scale register is the parameter, the bridge's input is a `RowIn` (`OutEpi.lean`).
`Inputs.smExit` (`OutPremises.lean`) is that statement for every softmax state that goes into the
epilogue.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- **The bridge's input at the loop's exit is a `RowIn`** when the region's running maximum and
sum are those of the row's blocks and its scale is the launch's. -/
theorem rowIn_of_corr {P : Params} {L : Launch} {g : Nat} {d : Sm.D} {r s tok head : Nat}
    (hsc : d.e.sc = P.scale) (hc : Sm.Corr (sl P) (blocks0 P r s tok head) d) :
    RowIn P (DComp.exitIn L g d) r s tok head where
  sc := by
    show Value.float FloatFmt.f32 (d.e.sc * log2eF32) = _
    rw [hsc]
    rfl
  l := hc.2
  mx := hc.1

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
