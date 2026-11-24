-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Correction
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # The value table at the destinations of a load

Destination `p` of each rescale and final load holds value `p` of the chunk `o`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
theorem rld_value (L : Launch) (g : Nat) (d : D) (c : Fin 16) (p : Nat) (hp : p < 16) :
    valueOf L g d ((rldRegs c.val).getD p 0) = d.o.getD p (b32 0) := by
  fin_cases c <;> interval_cases p <;>
    simp only [rldRegs, List.getD_cons_zero, List.getD_cons_succ, valueOf, chunkValues,
      loadValues, PTX.Flow.lookupLit, Option.getD_some]

set_option maxHeartbeats 8000000 in
theorem fld_value (L : Launch) (g : Nat) (d : D) (c : Fin 16) (p : Nat) (hp : p < 16) :
    valueOf L g d ((fldRegs c.val).getD p 0) = d.o.getD p (b32 0) := by
  fin_cases c <;> interval_cases p <;>
    simp only [fldRegs, List.getD_cons_zero, List.getD_cons_succ, valueOf, chunkValues,
      loadValues, PTX.Flow.lookupLit, Option.getD_some]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
