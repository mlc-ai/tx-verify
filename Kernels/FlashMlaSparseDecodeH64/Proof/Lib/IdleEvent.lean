-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Idle
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The idle code's events are unguarded event instructions

A role that hands a lane back to warpgroup 1 stops at an event of the idle code
(`IdleSite`); `idle_event` gives the site obligation there. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

/-- **An event of the idle code** is an unguarded event instruction. -/
theorem idle_event (s : IdleSite) : ∃ ins, kernel.code[s.pc]? = some ins ∧
    ins.op.isLocal = false ∧ ∀ F, Code.GuardTrue F ins.guard := by
  cases s
  · exact ⟨_, Flow.code_2596, rfl, fun _ => trivial⟩
  · exact ⟨_, Flow.code_2601, rfl, fun _ => trivial⟩
  · exact ⟨_, Flow.code_2604, rfl, fun _ => trivial⟩
  · exact ⟨_, Flow.code_3611, rfl, fun _ => trivial⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
