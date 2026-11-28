-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- At a poll, the 32-bit counter can wrap before reaching the limit. The distance
in the register's arithmetic decreases even across that wrap. -/
def iterationsLeft (i n : Value) : Nat :=
  ((bits n).toNat + 2 ^ 32 - (bits i).toNat) % 2 ^ 32

theorem bits_lt (v : Value) : (bits v).toNat < 2 ^ 32 := by
  simp only [bits, truncBits, BitVec.toNat_ofNat]
  omega

theorem iterationsLeft_inc (i n : Value) (h : bits i ≠ bits n) :
    iterationsLeft (.bits 32 (truncBits 32 (bits i + 1))) n + 1 = iterationsLeft i n := by
  have hi := bits_lt i
  have hn := bits_lt n
  have hne : (bits i).toNat ≠ (bits n).toNat := fun he => h (BitVec.eq_of_toNat_eq he)
  have hinc : (bits (.bits 32 (truncBits 32 (bits i + 1)))).toNat =
      ((bits i).toNat + 1) % 2 ^ 32 := by
    generalize bits i = x
    change (truncBits 32 (truncBits 32 (x + 1))).toNat = _
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
      show (1 : BitVec 64).toNat = 1 by rfl]
    omega
  simp only [iterationsLeft, hinc]
  omega

/-- Positions within an iteration. A failed poll is the only self edge. -/
def Site.position : Site → Nat
  | .poll => 0 | .readyBar => 1 | .arrive => 2 | .page false => 3 | .page true => 12
  | .warpBar p => 4 + 4 * p.val + p.val / 2
  | .elect p => 5 + 4 * p.val + p.val / 2
  | .copy p s => 6 + 4 * p.val + p.val / 2 + (if s then 1 else 0)
  | _ => 0

theorem position_bound (s : Site) : s.position < 21 := by
  cases s with
  | warpBar p | elect p => fin_cases p <;> decide
  | copy p b => fin_cases p <;> cases b <;> decide
  | page b => cases b <;> decide
  | _ => decide

def measure (d : D) : Nat :=
  match d.site with
  | .dec => 22 * 2 ^ 32 + 6 | .first => 22 * 2 ^ 32 + 5
  | .second => 22 * 2 ^ 32 + 4 | .beginBar => 22 * 2 ^ 32 + 3
  | .endBar => 2 | .inc => 1 | .dispatch => 0
  | s => 22 * iterationsLeft d.counter d.limit + (21 - s.position)

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
