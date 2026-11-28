-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.WinSet

@[expose] public section

/-! # The sum register from pc 2562 to the epilogue's wait

The three local instructions from 2562 to the wait of pc 2565 do not write register 1915. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

def emS : List (Nat × Nat) := [(2562, 2565)]

theorem em_fwd : fwdOk emS [1915] = true := by decide +kernel

/-- **A state at pc 2562 and the wait's state agree on register 1915.** -/
theorem em_keep {t s : TState} (ht : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t s)
    (hpc : t.pc = 2562) : s.regs 1915 = t.regs 1915 :=
  (win_keep em_fwd ht (by rw [hpc]; decide)).2 1915 (by simp)

end PTX.Kernels.InklingRelDecode.Proof.Lib
