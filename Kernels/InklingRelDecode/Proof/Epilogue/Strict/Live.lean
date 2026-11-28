-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Flow.NotObject
import Lemmas.Flow.ShflKind

@[expose] public section

/-! # The epilogue is not lost on an event that is not undefined behaviour

The successor of a state of the epilogue is `none` only at the exit, on a poll site fired by
something that is no poll, or on the shuffle site fired by something that is no shuffle. The
template of a poll fires a poll or undefined behaviour, and that of a shuffle a shuffle or
undefined behaviour. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat}

/-- **The successor of a state of the epilogue but the exit on an event that is not undefined
behaviour is not `none`.** -/
theorem live_epi {d : D} {t : TState} {ins : Instr} {v : Event} {o : Option TState}
    (hs : d.site ≠ .exit) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) v o)
    (hu : ∀ f, v.kind ≠ .ub f) : Control.next e L g d v ≠ none := by
  obtain ⟨s, r⟩ := d
  cases s with
  | wait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2565)
    rcases fires_mbarWait_kind hf with ⟨m, q, ok, acq, sc, hk⟩ | ⟨f, hk⟩
    · cases ok <;> simp [Control.next, hk]
    · exact absurd hk (hu f)
  | shfl =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2603)
    simp only [eventTmpl, warpTmpl] at hf
    rcases fires_shflTmpl_kind hf with ⟨av, bv, cv, recv, ok, hk⟩ | ⟨f, hk⟩
    · simp [Control.next, hk]
    · exact absurd hk (hu f)
  | exit => exact absurd rfl hs
  | _ => simp [Control.next]

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
