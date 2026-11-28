-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ShapeBase
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # Warpgroup 2's events by state: the rows' reads and chunk stores -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

theorem shapeAt_scale (d : D) (hs : ∃ r, d.site = .scale r) :
    (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨r, hs⟩ := hs
  cases hs
  fin_cases r <;> dq_open <;>
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact fires_load_ev (regs_of_factsFrom hF (by decide +kernel)) (by decide) rfl hsub hf

theorem shapeAt_raw (d : D) (hs : ∃ r i, d.site = .raw r i) :
    (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨r, i, hs⟩ := hs
  cases hs
  fin_cases r <;> fin_cases i <;> dq_open <;>
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact fires_load_ev (regs_of_factsFrom hF (by decide +kernel)) (by decide) rfl
      (hsub.trans (by change el < 1 at hi; omega)) hf

theorem shapeAt_store (d : D) (hs : ∃ r i, d.site = .store r i) :
    (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨r, i, hs⟩ := hs
  cases hs
  fin_cases r <;> fin_cases i <;> dq_open <;>
  · have h0 : t.sub = 0 := hsub.trans (by change el < 1 at hi; omega)
    change Fires _ (storeTmpl L g t .shared _ _ 0 _) e o at hf
    refine fires_store_reg (regs_of_factsFrom hF ?_) h0 hf
    decide +kernel

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
