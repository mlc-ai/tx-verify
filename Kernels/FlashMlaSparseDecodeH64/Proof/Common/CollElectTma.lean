-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollElect
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # The TMA warp's election waits with the full mask (`tma_elect_tmpl`) -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- **The TMA warp's election site** waits with the full mask. -/
theorem tma_elect_tmpl (d : D) (hs : d.site = .elect) :
    ∀ t ins, (code P L g).AtD d t → kernel.code[(code P L g).pc d]? =
      some ins → Sched.tmplShape (eventTmpl Assumptions.all L g t ins.op) =
        some (.elect 4294967295) := by
  tma_state d
  cases hs
  intro t ins hat hc
  obtain ⟨hpc, -, -, -, hF⟩ := hat
  try dsimp only [Flow.Code.AtD, code, facts, Site.pc, coordPc, Fin.isValue, Fin.val_zero,
    Fin.val_one, Fin.val_two] at hpc hc hF ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  exact elect_tmpl_shape (readBits_reg (rg 663)) (by decide)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
