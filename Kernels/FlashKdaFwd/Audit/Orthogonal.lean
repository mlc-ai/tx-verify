-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.OneTokenRound
import Kernels.FlashKdaFwd.Audit.OneTokenNormalize

/-! A gate-only perturbation with orthogonal unit query and key in the stateless public call.
All 128 value coordinates are one, so each output has the same scalar derivation. -/
namespace FlashKda.Orthogonal
open PTX Chunk Algorithm Sequence OneToken
noncomputable section

def queryVec := four (1/2) (1/2) (1/2) (1/2)
def keyVec := four (1/2) (1/2) (-1/2) (-1/2)

theorem unit_perpendicular :
    dot queryVec queryVec = 1 ∧ dot keyVec keyVec = 1 ∧ dot keyVec queryVec = 0 := by
  unfold queryVec keyVec
  simp only [dot_four]
  norm_num [four]

def tokens (gate : ℕ → Row 128) :=
  activate (fun _ => queryVec) (fun _ => keyVec) gate (fun _ => 1) (fun _ => 0)
    (-5) 0 (fun _ => 0)

/-- At the first token all gates act on the zero entering state. This output is zero
for *every* possible choice of the gate coordinates and every real output scale. -/
theorem real_output (gate : ℕ → Row 128) (scale : ℝ) :
    output (tokens gate) (fun _ => 0) 1 scale 0 = 0 := by
  rw [single]
  simp [tokens,activate,normalize_dot,unit_perpendicular.2.2]

theorem first_state (gate : ℕ → Row 128) (i : Fin 128) :
    tokenState (tokens gate) (fun _ => 0) 1 i = (1/2)*normalize keyVec i := by
  norm_num [tokenState,sequential,step,tokens,activate,sigmoid,dot]

/-- Only coordinate zero in the public gate row changes between the two calls. -/
def gateWord (changed : Bool) (i : Fin 128) : Nat := if changed && i == 0 then 0xbf00 else 0

theorem single_word (i : Fin 128) : gateWord true i ≠ gateWord false i ↔ i = 0 := by
  by_cases h : i = 0 <;> simp [gateWord,h]

def queryWords (changed : Bool) : Fin 4 → Nat :=
  fun i => if changed && i == 0 then 0x3bdb else 0x3b6e
def keyWords (changed : Bool) : Fin 4 → Nat := fun i =>
  if i.val ≥ 2 then 0xc0c3 else if changed && i == 0 then 0x4053 else 0x40c3

def decoded (width : Layout) (word : Nat) := (width.decode word).bind FVal.num
def exactDot (numbers : Fin 4 → Option (Option ℚ × Option ℚ)) : Option ℚ := do
  let terms ← ([0,1,2,3] : List (Fin 4)).mapM fun i => do
    let (q,k) ← numbers i
    return (← q) * (← k)
  return terms.sum

def cell (changed : Bool) : Option ℚ :=
  exactDot fun i => some (decoded brainFloat (queryWords changed i),
    decoded brainFloat (keyWords changed i))

def accWord (changed : Bool) : Nat := if changed then 0xb8c90000 else 0
def dotWord (changed : Bool) : Nat := if changed then 0xb8c9 else 0
def publicWord (changed : Bool) : Nat := if changed then 0xb849 else 0
def score (changed : Bool) : ℚ := if changed then -201/2097152 else 0

/-- The exact contraction of the four measured pairs equals the live binary32 accumulator.
Both subsequent outputs are exactly representable in their storage types. -/
theorem contraction (changed : Bool) :
    cell changed = some (score changed) ∧
    decoded binary32 (accWord changed) = some (score changed) ∧
    decoded brainFloat (dotWord changed) = some (score changed) ∧
    decoded brainFloat (publicWord changed) = some (score changed/2) := by
  cases changed <;> decide +kernel

theorem conversions (changed : Bool) :
    (brainFloat.round .rn .inf (score changed:ℝ) false).bind FVal.num = some (score changed) ∧
    (brainFloat.round .rn .inf ((score changed:ℝ)/2) false).bind FVal.num =
      some (score changed/2) := by
  cases changed
  · norm_num [score,Layout.round_zero (by trivial : RoundMode.rn.applies brainFloat 0),FVal.num]
  · constructor
    · rw [Layout.round_exact (m := .rn) (F := 0x38c9) (by trivial) (by decide) (by decide) (by
        norm_num [score,Layout.magnitude,Layout.bias]) (by simp)]
      norm_num [score,Layout.fieldVal,Layout.magnitude,Layout.bias,FVal.num]
    · rw [Layout.round_exact (m := .rn) (F := 0x3849) (by trivial) (by decide) (by decide) (by
        norm_num [score,Layout.magnitude,Layout.bias]) (by simp)]
      norm_num [score,Layout.fieldVal,Layout.magnitude,Layout.bias,FVal.num]

theorem observed_error (gate : ℕ → Row 128) (scale : ℝ) :
    |((score true/2 : ℚ):ℝ)-output (tokens gate) (fun _ => 0) 1 scale 0| = 201/4194304 := by
  rw [real_output]; norm_num [score]

end
end FlashKda.Orthogonal
