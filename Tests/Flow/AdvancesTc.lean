-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.AdvancesTc
public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part030
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part031

@[expose] public section

/-! # `advances` at FlashMLA's `tcgen05.cp` (pc 1936) and `tcgen05.mma.ws` (pc 2027) -/

namespace PTX.Tests.AdvancesTc
open PTX PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

variable {L : Launch} {g : Nat}

theorem cp_1936 {ins : Instr} (h : kernel.code[1936]? = some ins) :
    ∀ {t : TState} {e : Event} {u : TState},
      Fires 1936 (eventTmpl Assumptions.all L g t ins.op) e (some u) → u = PTX.next t := by
  rw [Flow.code_1936] at h
  cases h
  advances

theorem mma_2027 {ins : Instr} (h : kernel.code[2027]? = some ins) :
    ∀ {t : TState} {e : Event} {u : TState},
      Fires 2027 (eventTmpl Assumptions.all L g t ins.op) e (some u) → u = PTX.next t := by
  rw [Flow.code_2027] at h
  cases h
  advances

end PTX.Tests.AdvancesTc
