-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlockLib

@[expose] public section

/-! # The exchange word of a closed block reads as its extended real

At the closing event of a block the block's words are valid (`W0Valid`), so its exchange word `pm`
reads as the extended real `w0FE pm` (`w0_pm_rd`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {P : Params} {X : Execution} {g : Nat}

/-- **The exchange word of a closed block** reads as `w0FE` of itself. -/
theorem w0_pm_rd {K0 : Nat}
    (hv : W0Valid P.scale ((X.tr g).take (K0 + 1))) {c0 : Event}
    (hK : X.get (g, K0) = some c0) (hc : c0.pc = 1122) :
    Rd (w0Words (w0Fin ((X.tr g).take K0)).2).pm
      (w0FE (w0Words (w0Fin ((X.tr g).take K0)).2).pm) := by
  have hpre : (X.tr g).take (K0 + 1) = (X.tr g).take K0 ++ [c0] := by
    have : (X.tr g)[K0]? = some c0 := hK
    rw [List.take_add_one, this]; rfl
  have hfin : w0Fin ((X.tr g).take K0 ++ [c0]) =
      ((w0Fin ((X.tr g).take K0)).1 ++ [(w0Fin ((X.tr g).take K0)).2], []) := by
    rw [w0Fin_snoc]; simp [hc, w0ArrSPc]
  have hwok : W0Ok P.scale (w0Words (w0Fin ((X.tr g).take K0)).2) := by
    have hvK := hv
    rw [hpre] at hvK
    exact hvK.now.1 _ (by rw [hfin]; simp)
  exact Wg0.Data.w0_rd_pm hwok

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
