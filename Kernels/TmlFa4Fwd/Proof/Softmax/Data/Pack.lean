-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Exponent
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Def

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Assumption
noncomputable section

def pack (lo hi : Value) := okVal (.bits 32 0) (Gen.packE [hi, lo])
def packed (x y : ℝ) := Value.pair (.float .bf16 x) (.float .bf16 y)

theorem pack_float (x y : ℝ) :
    pack (.float .f32 x) (.float .f32 y) = packed x y := by
  simp only [pack, Gen.packE, Gen.finV_real (reads_float x).read,
    Gen.finV_real (reads_float y).read, bindRead, Option.getD_some]
  rfl

theorem packed_bytes (x y : ℝ) : Values.Bf16Pair (packed x y) x y := by
  refine ⟨rfl, fun z hz => ?_⟩
  change (if z < 2 then _ else _) = _ ∧ (if 2 + z < 2 then _ else _) = _
  simp only [hz, ite_true, Nat.not_lt_of_ge (Nat.le_add_right 2 z), ite_false,
    show (Value.float .bf16 x).bytes = 2 from rfl, Nat.add_sub_cancel_left, and_self]

/-- Each group of four probabilities passes through two conversions, a join and a split. -/
def packFour (W : Nat → Value) (j : Nat) : Value × Value :=
  splitValue 64 (joinValue (pack (W (4*j)) (W (4*j+1)))
    (pack (W (4*j+2)) (W (4*j+3))))

theorem packFour_eq {W : Nat → Value} {w : Nat → ℝ} (j : Nat)
    (h : ∀ i < 128, W i = .float .f32 (w i)) (hj : j < 32) :
    packFour W j = (packed (w (4*j)) (w (4*j+1)), packed (w (4*j+2)) (w (4*j+3))) := by
  simp only [packFour, h _ (show 4*j < 128 by omega), h _ (show 4*j+1 < 128 by omega),
    h _ (show 4*j+2 < 128 by omega), h _ (show 4*j+3 < 128 by omega), pack_float]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
