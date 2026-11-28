-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Stage
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollElect
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # Warpgroup 0's elections wait with the full mask (`w0_elect_tmpl`) -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

set_option hygiene false in
/-- A site's election with the full mask in register `r`, as a template. -/
macro "w0_elect_t " r:num : tactic => `(tactic| (
  intro t ins hat _ hc
  obtain ⟨hpc, -, -, -, hF⟩ := hat
  w0_body
  exact elect_tmpl_shape (readBits_reg (rg $r)) (by decide)))

/-- **Warpgroup 0's output election sites** wait with the full mask. -/
theorem w0_elect_tmpl (d : D) (hs : ∃ c, d.site = .oel c) :
    ∀ t ins, (code P L g w).AtD d t → (code P L g w).inv d → kernel.code[(code P L g w).pc d]? =
      some ins → Sched.tmplShape (eventTmpl Assumptions.all L g t ins.op) =
        some (.elect 4294967295) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c
  · w0_elect_t 1912
  · w0_elect_t 2081
  · w0_elect_t 2250
  · w0_elect_t 2420

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
