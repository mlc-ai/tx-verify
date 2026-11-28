-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal2

@[expose] public section

/-! # Rewriting lemmas of the exponent window

The input registers of the sixteen software instances, the exponential of a shifted score, the sum
of two `f32` words and the halves of a pair of them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- The input registers of the sixteen software instances. -/
def swTab (i : Nat) : Nat :=
  [1312, 1314, 1316, 1318, 1344, 1346, 1348, 1350, 1376, 1378, 1380, 1382, 1408, 1410, 1412,
    1414].getD i 0

theorem xRegs_eq : xRegs = (List.range 64).map (1288 + 2 * ·) := by decide +kernel

theorem addF {fz : Bool} {d : Value} {a b : ℝ} :
    okVal d (floatE (addI fz) [.float .f32 a, .float .f32 b]) = .float .f32 (a + b) := by
  rw [(ev_add (fz := fz) (d := d) (ev_real a) (ev_real b)).1, erealValue_coe]

theorem split_pair (a b : ℝ) : splitValue 64 (joinValue (.float .f32 a) (.float .f32 b)) =
    (.float .f32 a, .float .f32 b) := rfl

theorem ex2_val {W : Nat → Value} {X : Nat → EReal} (hx : ∀ r ∈ xRegs, Ev (W r) (X r)) {r : Nat}
    (hr : r ∈ xRegs) (fz : Bool) (d : Value) :
    okVal d (ex2E fz (W r)) = .float .f32 (pw2 (X r)) := by
  rw [(ev_ex2 (fz := fz) (d := d) (hx r hr)).1, erealValue_coe]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
