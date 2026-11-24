-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Pack

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
noncomputable section

def column (pairs : Nat → Value × Value) (i : Nat) :=
  if i % 2 = 0 then (pairs (i/2)).1 else (pairs (i/2)).2

theorem column_eq {pairs : Nat → Value × Value} {w : Nat → ℝ}
    (h : ∀ j < 64, pairs j = (.float .f32 (w (2*j)), .float .f32 (w (2*j+1))))
    (i : Nat) (hi : i < 128) : column pairs i = .float .f32 (w i) := by
  unfold column
  rw [h _ (by omega)]
  split
  · rw [show 2*(i/2) = i by omega]
  · rw [show 2*(i/2)+1 = i by omega]

theorem store_of_quads (W : Nat → Value) (words : Nat → Value) (w : Nat → ℝ)
    (hw : ∀ i < 128, W i = .float .f32 (w i))
    (h : ∀ j < 32, (words (2*j), words (2*j+1)) = packFour W j) {i : Nat} (hi : i < 64) :
    Values.Bf16Pair (words i) (w (2*i)) (w (2*i+1)) := by
  have hj : i/2 < 32 := by omega
  have e := Prod.mk.inj ((h _ hj).trans (packFour_eq (i/2) hw hj))
  by_cases he : i%2 = 0
  · rw [show words i = packed (w (2*i)) (w (2*i+1)) from by
      simpa only [show 2*(i/2) = i by omega, show 4*(i/2) = 2*i by omega] using e.1]
    exact packed_bytes _ _
  · rw [show words i = packed (w (2*i)) (w (2*i+1)) from by
      simpa only [show 2*(i/2)+1 = i by omega, show 4*(i/2)+2 = 2*i by omega,
        show 4*(i/2)+3 = 2*i+1 by omega] using e.2]
    exact packed_bytes _ _

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
