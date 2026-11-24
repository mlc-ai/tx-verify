-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormProducts

/-! On the sign-reversal witness every subtotal of the four nonzero bfloat16 products is
exactly representable in binary32. This removes the reduction-order dependency for this cell. -/
namespace FlashKda.Binary.Dot
open PTX OneToken
noncomputable section

def queryPart (i : Fin 4) : ℚ := [37/64,37/64,-37/64,-37/2048][i.val]!
def keyPart (i : Fin 4) : ℚ := [137/512,137/256,205/256,137/4096][i.val]!

abbrev Mask := BitVec 4

def subtotal (mask : Mask) : ℚ :=
  ([0,1,2,3] : List (Fin 4)).foldl (fun s i =>
    if mask.getLsbD i.val then s + queryPart i * keyPart i else s) 0

def exactBits (mask : Mask) : Nat :=
  [0,0x3e1e6800,0x3e9e6800,0x3eed9c00,0x3eed0800,0x3e9dd400,0x3e1d4000,0x3a940000,
   0x3a1e6800,0x3e1dc998,0x3e9e18cc,0x3eed4ccc,0x3eed5734,0x3e9e2334,0x3e1dde68,
   0x3a099800][mask.toNat]!

def roundNumber (m : FloatRound) (z : Bool) (v : ℚ) : Option ℚ := do
  let result ← binary32.round m.mode .inf v z
  result.num

theorem round_certified (value : ℚ) (field : Nat)
    (check : value = 0 ∨ exactProductField value field) (m : FloatRound) (z : Bool) :
    roundNumber m z value = some value := by
  have applies : ∀ x, m.mode.applies binary32 x := by intro x; cases m <;> trivial
  unfold roundNumber
  rcases check with hz | ⟨hw,ht,heq,_⟩
  · rw [hz, Rat.cast_zero, Layout.round_zero (applies 0)]
    rfl
  · have h : |(value : ℝ)| = (mag field : ℚ) := by exact_mod_cast heq
    rw [Layout.round_exact (m := m.mode) (F := field) (applies _) hw ht h (by simp)]
    by_cases hn : value < 0
    · have hr : (value : ℝ) < 0 := by exact_mod_cast hn
      rw [abs_of_neg hn] at heq
      simp [Layout.fieldVal, Nat.ne_of_gt hw, hr, ← heq, FVal.num]
    · have hr : ¬(value : ℝ) < 0 := by exact_mod_cast hn
      rw [abs_of_nonneg (le_of_not_gt hn)] at heq
      simp [Layout.fieldVal, Nat.ne_of_gt hw, hr, ← heq, FVal.num]

theorem round_subtotal (mask : Mask) (m : FloatRound) (z : Bool) :
    roundNumber m z (subtotal mask) = some (subtotal mask) := by
  have check : ∀ s : Mask, subtotal s = 0 ∨ exactProductField (subtotal s) (exactBits s) :=
    by decide +kernel
  exact round_certified _ _ (check mask) m z

def singleton (i : Fin 4) : Mask := (1 : Mask) <<< i.val

/-- A reduction may insert any number of zero terms, permute the four nonzero products and
choose a different IEEE rounding direction at each node. The mask records which products it used. -/
inductive Tree : Mask → Type
  | zero (mode : FloatRound) (sign : Bool) : Tree 0
  | product (i : Fin 4) (mode : FloatRound) : Tree (singleton i)
  | add {l r} (left : Tree l) (right : Tree r) (disjoint : l &&& r = 0)
      (mode : FloatRound) (sign : Bool) : Tree (l ||| r)

def evaluateWith (product : Fin 4 → ℚ) {s : Mask} : Tree s → Option ℚ
  | .zero m sign => roundNumber m sign 0
  | .product i m => roundNumber m false (product i)
  | .add a b _ m z => do
    roundNumber m z ((← evaluateWith product a) + (← evaluateWith product b))

theorem reduction_exact (product : Fin 4 → ℚ) (total : Mask → ℚ) (empty : total 0 = 0)
    (one : ∀ i, product i = total (singleton i))
    (join : ∀ x y : Mask, x &&& y = 0 → total x + total y = total (x ||| y))
    (rounds : ∀ s m z, roundNumber m z (total s) = some (total s))
    {mask : Mask} (t : Tree mask) : evaluateWith product t = some (total mask) := by
  induction t with
  | zero m z =>
    change roundNumber m z 0 = _
    rw [← empty]
    exact rounds _ _ _
  | product i m =>
    change roundNumber m false _ = _
    rw [one]
    exact rounds _ _ _
  | @add l r a b disjoint m z ha hb =>
    simp [evaluateWith,ha,hb,join _ _ disjoint,rounds]

def evaluate {s : Mask} (t : Tree s) := evaluateWith (fun i => queryPart i * keyPart i) t

theorem tree_exact {mask : Mask} (t : Tree mask) : evaluate t = some (subtotal mask) :=
  reduction_exact _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) round_subtotal t

/-- Every reduction covering all four active coordinates gives the same accumulator word and
the same bfloat16 dot as the production tensor-core register trace. -/
theorem full_cell (t : Tree 15) :
    evaluate t = some (4403/8388608) ∧
    binary32.decode 0x3a099800 = some (.fin (4403/8388608)) ∧
    brainFloat.round .rn .inf (4403/8388608 : ℝ) false = some (.fin (69/131072)) := by
  exact ⟨(tree_exact t).trans (by decide +kernel), by decide +kernel, rounded_dot⟩

end
end FlashKda.Binary.Dot
