-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.ElectFull
public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part000

@[expose] public section

/-! # FlashMLA's startup election with the full mask fires its event -/

namespace PTX.Tests.ElectFull
open PTX PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

variable {L : Launch} {g : Nat}

theorem elect_startup {pc : Nat} {ins : Instr} {t : TState} {e : Event} {o : Option TState}
    (h : kernel.code[16]? = some ins) {bits : BitVec 64}
    (hm : readBits L g t 32 (.reg 522) = .ok bits) (hb : bits.toNat = 2 ^ 32 - 1)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ inst ld, e.pc = pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld := by
  rw [Flow.code_16] at h
  cases h
  exact fires_elect_full hm hb hf

end PTX.Tests.ElectFull
