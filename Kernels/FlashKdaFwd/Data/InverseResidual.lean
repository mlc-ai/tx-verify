-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Audit.ResidualSample
import Mathlib.Tactic

/-! Check the rational matrix residuals from all 768 recorded inverse words. -/
@[expose] public section
namespace FlashKda.Sample.InverseCheck
open Chunk Block Inverse Sequence Stability Algorithm Finset Matrix
def offset (b : Fin 3) (i : Nat) := 16*b.val + i
def sourceKey (b : Fin 3) (i : Nat) : Triple :=
  if offset b i < 33 then (measurement (offset b i)).key else ⟨0,0,0⟩

def coefficientQ (b : Fin 3) : Matrix Full Full ℚ := fun i j =>
  if j < i then (normalized (sourceKey b j)).inner (normalized (sourceKey b i))/2
  else if i=j then 1 else 0
def word (b : Fin 3) (i j : Full) :=
  inverseWords.getD (256*b.val+16*i.val+j.val) 0
def stored (b : Fin 3) : Matrix Full Full ℚ := fun i j =>
  (PTX.FloatFmt.bf16.decode (word b i j)).getD 0
def cap (b : Fin 3) : ℚ := (if b=0 then 23358 else if b=1 then 22586 else 0)/1000000

set_option maxRecDepth 80000
set_option maxHeartbeats 10000000

theorem finite_words : inverseWords.size = 768 ∧ ∀ b i j,
    PTX.FloatFmt.bf16.decode (word b i j) = some (stored b i j) := by decide +kernel

def tested (b : Fin 3) : Prop :=
  31 * (∑ c, ∑ i, ((coefficientQ b * stored b - 1) i c)^2) ≤ (cap b)^2
instance (b : Fin 3) : Decidable (tested b) := inferInstanceAs (Decidable (_ ≤ (_ : ℚ)))
theorem first : tested 0 := by decide +kernel
theorem second : tested 1 := by decide +kernel
theorem tail_tile : tested 2 := by decide +kernel

end FlashKda.Sample.InverseCheck
