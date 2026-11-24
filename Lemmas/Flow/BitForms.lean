-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Events
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Integer forms of small bit operations

Proof tools for the integer arithmetic of descriptor and ring code:

* `land16383`, `lor65536`: `and.b32 d, a, 16383` is `a % 2^14`, and `or.b32` of such a value with
  `65536` (bit 16) is a sum;
* `xor_one_lt2`, `xor_bit_zero`, `xor_bit_one`: `xor.b32` of a parity bit with the literal 1 or
  with a selected wrap bit 0 or 1;
* `mbarClusterLoc_off`: an mbarrier of the thread's own CTA addressed by a 32-bit integer register
  plus a constant offset, as a cluster address.
-/

namespace PTX.Proof
open PTX

theorem land16383 (a : Nat) : a &&& 16383 = a % 16384 := Nat.and_two_pow_sub_one_eq_mod a 14

theorem lor65536 (a : Nat) : a % 16384 % 4294967296 ||| 65536 = a % 16384 + 65536 := by
  have h : a % 16384 % 4294967296 < 2 ^ 16 := by omega
  rw [Nat.or_comm, show (65536 : Nat) = 2 ^ 16 * 1 by rfl,
    ← Nat.two_pow_add_eq_or_of_lt h]
  omega

/-- `xor.b32 d, a, 1` of a bit. -/
theorem xor_one_lt2 {r : Nat} (hr : r < 2) :
    truncBits 32 (BitVec.ofNat 64 r) ^^^ truncBits 32 (BitVec.ofInt 64 1) =
      BitVec.ofNat 64 (1 - r) := by
  interval_cases r <;> decide

/-- `xor.b32` of a bit with the selected wrap bit 0 or 1. -/
theorem xor_bit_zero {r : Nat} (hr : r < 2) :
    truncBits 32 (BitVec.ofNat 64 r) ^^^ truncBits 32 (truncBits 32 (BitVec.ofInt 64 0)) =
      BitVec.ofNat 64 r := by
  interval_cases r <;> decide

theorem xor_bit_one {r : Nat} (hr : r < 2) :
    truncBits 32 (BitVec.ofNat 64 r) ^^^ truncBits 32 (truncBits 32 (BitVec.ofInt 64 1)) =
      BitVec.ofNat 64 (1 - r) := by
  interval_cases r <;> decide

end PTX.Proof

namespace PTX.Flow
open PTX PTX.Proof

/-- An mbarrier of the thread's own CTA at a 32-bit integer register's address plus a constant
offset, as a cluster address. -/
theorem mbarClusterLoc_off {L : Launch} {g : Nat} {t : TState} {base a off : Nat}
    (hr : t.regs base = some (b32 a)) (ha : a + off < 2 ^ 32) (h8 : (a + off) % 8 = 0) :
    mbarClusterLoc L g t base (off : Int) = .ok ⟨.shared, g / L.block, a + off⟩ := by
  have h64 : a < 18446744073709551616 := by omega
  have h32 : a < 4294967296 := by omega
  have ho : off < 18446744073709551616 := by omega
  simp [mbarClusterLoc, sharedEffAddr, readReg, hr, b32, readBits, truncBits,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, bind, Except.bind,
    pure, Except.pure, BitVec.toNat_add, h8]
  omega

end PTX.Flow
