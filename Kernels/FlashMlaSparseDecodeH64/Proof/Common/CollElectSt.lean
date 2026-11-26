-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollElect
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.Step.ShapeNc

@[expose] public section

/-! # The startup's elections wait with the full mask (`startup_elect_tmpl`) -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- **The startup's election sites** (pcs 16 and 31) wait with the full mask. -/
theorem startup_elect_tmpl (j : Fin 2) (x1 x2 : BitVec 64) :
    ∀ t ins, (code L g).AtD ⟨.elect j, x1, x2⟩ t → (code L g).inv ⟨.elect j, x1, x2⟩ →
      kernel.code[(code L g).pc ⟨.elect j, x1, x2⟩]? = some ins →
      Sched.tmplShape (eventTmpl Assumptions.all L g t ins.op) = some (.elect 4294967295) := by
  intro t ins hat _ hc
  fin_cases j
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_16)
    exact elect_tmpl_shape (readBits_reg (holds_mem (atD_holds hat) (mem_factsFrom (by lit_mem))))
      (by decide)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_31)
    exact elect_tmpl_shape (readBits_reg (holds_mem (atD_holds hat) (mem_factsFrom (by lit_mem))))
      (by decide)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
