-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.DotOrder
import Kernels.FlashKdaFwd.Audit.GateWindow

/-! All binary32 reduction orders on the two orthogonal gate inputs, including zeros.
The four nonzero terms and all 16 possible subtotals are exactly representable. -/
namespace FlashKda.Orthogonal
open PTX Binary Binary.Dot
noncomputable section

def term (changed : Bool) (i : Fin 4) : ℚ :=
  let active := changed && i == 0
  queryValue active * keyValue active (decide (2 ≤ i.val))

def partialDot (changed : Bool) (s : Mask) : ℚ :=
  ([0,1,2,3] : List (Fin 4)).foldl (fun acc i =>
    if s.getLsbD i.val then acc + term changed i else acc) 0

private def fields (changed : Bool) (s : Mask) : Nat :=
  (if changed then
    [0,0x3cb48100,0x3cb54a00,0x3d34e580,0x3cb54a00,0x38c90000,0,0x3cb48100,
     0x3cb54a00,0x38c90000,0,0x3cb48100,0x3d354a00,0x3cb61300,0x3cb54a00,0x38c90000]
   else
    [0,0x3cb54a00,0x3cb54a00,0x3d354a00,0x3cb54a00,0,0,0x3cb54a00,
     0x3cb54a00,0,0,0x3cb54a00,0x3d354a00,0x3cb54a00,0x3cb54a00,0])[s.toNat]!

theorem rounded_partial (changed : Bool) (s : Mask) (m : FloatRound) (z : Bool) :
    roundNumber m z (partialDot changed s) = some (partialDot changed s) := by
  have all : ∀ c : Bool, ∀ x : Mask, partialDot c x = 0 ∨
      exactProductField (partialDot c x) (fields c x) := by decide +kernel
  exact round_certified _ _ (all changed s) m z

theorem cell_in_any_order {s : Mask} (changed : Bool) (t : Tree s) :
    evaluateWith (term changed) t = some (partialDot changed s) := by
  cases changed <;> apply reduction_exact <;>
    first | exact rounded_partial _ | decide +kernel

/-- The caller can choose an independent rounding direction at every product and sum,
permute the nonzero coordinates and insert zero leaves anywhere in the reduction. -/
theorem readout_in_any_order (changed : Bool) (t : Tree 15) (terms : Fin 4 → ℚ)
    (a b : Fin 4 → ℝ)
    (ha : ∀ i, GatePair.allowed (-(negPrefix (changed && i == 0):ℝ)) (a i))
    (hb : ∀ i, GatePair.allowed (negPrefix (changed && i == 0):ℝ) (b i))
    (inputs : ∀ i, (do
      let (q,k) ← stored (decide (2 ≤ i.val)) (a i) (b i)
      return (← q.num)*(← k.num)) = some (terms i)) :
    evaluateWith terms t = decoded OneToken.binary32 (accWord changed) ∧
      (do
        let x ← evaluateWith terms t
        let d ← (OneToken.brainFloat.round .rn .inf (x:ℝ) false).bind FVal.num
        (OneToken.brainFloat.round .rn .inf ((d:ℝ)/2) false).bind FVal.num) =
        decoded OneToken.brainFloat (publicWord changed) := by
  have eq : terms = term changed := by
    funext i
    have v := inputs i
    rw [stored_words _ _ (ha i) (hb i)] at v
    simpa [term,FVal.num] using v.symm
  have full : partialDot changed 15 = Orthogonal.score changed := by
    cases changed <;> decide +kernel
  rw [eq,cell_in_any_order,full]
  obtain ⟨_,acc,_,out⟩ := contraction changed
  simp [acc,out,(conversions changed).1,(conversions changed).2]

end
end FlashKda.Orthogonal
