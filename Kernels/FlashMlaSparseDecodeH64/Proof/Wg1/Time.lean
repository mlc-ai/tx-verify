-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Machine

@[expose] public section

/-! # Warpgroup 1's local times

The head's sites in order (`time`: the `setmaxnreg` `0`, the shuffle `1`, an exit `2`) and the
idle code's (`itime`: the two length loads `0` and `1`, named barrier 12 `2`, the return `3`).
The glued table (`Common/Time.lean`) places them after the startup: the head at `headBase`, the
idle code at `idleBase`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1

/-- **The head's local time.** -/
def time : Site → Nat
  | .smr => 0
  | .hsh => 1
  | _ => 2

/-- **The idle code's local time.** -/
def itime : IdleSite → Nat
  | .ldA => 0
  | .ldB => 1
  | .bar => 2
  | .ret => 3

theorem time_le (s : Site) : time s ≤ 2 := by cases s <;> decide

theorem itime_le (s : IdleSite) : itime s ≤ 3 := by cases s <;> decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
