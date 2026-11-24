-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
import Kernels.TmlFa4Fwd.Flow.Code.Part131

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Shape

@[expose] public section

/-! # A correction lane's rescale load is followed by its implicit wait

A rescale load (`rld st c`, a `tcLdWait` site of the kernel's assumptions) continues at the same
instruction at sub-step 1 (`rldw st c`, `k = 1`), whose template is the implicit `wait::ld`
(Core's `tcLdTmpl`): the event fired there is a `wait::ld` (`rldw_wait`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g : Nat}

theorem rld_tcLdWait : ∀ (st : Fin 2) (c : Fin 8),
    Assumptions.all.any (·.tcLdWait (rldPc st c)) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The event at an implicit-wait state of a rescale load is its `wait::ld`.** -/
theorem rldw_wait {st : Fin 2} {c : Fin 8} {v : Control.V} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (Control.code p L g).AtD ⟨.rldw st c, v, 1⟩ t)
    (hc : kernel.code[(Site.rldw st c).pc]? = some ins)
    (hf : Fires (Site.rldw st c).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    e.kind = .tc .waitLd := by
  have hsub : t.sub = 1 := hat.2.1
  have hw : Assumptions.all.any (·.tcLdWait t.pc) = true := by
    rw [hat.1]; exact rld_tcLdWait st c
  fin_cases st <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢ <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
    simp only [eventTmpl, tcLdTmpl, hw, hsub, ite_true, Nat.one_ne_zero, ite_false] at hf <;>
    simp only [Fires] at hf <;>
    rw [hf.1]

end PTX.Kernels.TmlFa4Fwd.Proof.Correction
