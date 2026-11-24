-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormChoices
import Kernels.FlashKdaFwd.Audit.OneTokenRound

/-! A one-word change to the next sequence changes a public output of a finite first
sequence. The input class of the second call includes a quiet NaN. -/
namespace FlashKda.TailIsolation
open PTX FlashKda Chunk Algorithm Sequence OneToken Normalize
noncomputable section

/-- The two-token key buffer in both public calls. Only channel seven of token one
changes. Both queries and values are the first unit vector; both gate logits are zero. -/
def keyWord (following : Nat) (token : Fin 2) (channel : Fin 128) : Nat :=
  if channel = 0 then 0x3f80 else if token = 1 ∧ channel = 7 then following else 0

theorem single_difference (t : Fin 2) (i : Fin 128) :
    keyWord 0 t i ≠ keyWord 0x7fc1 t i ↔ t = 1 ∧ i = 7 := by
  by_cases h : i = 0 <;> simp [keyWord,h]

/-- The first sequence has one token, unit query, key and value coordinate, zero
initial state, unit output scale and an update strength of one half. -/
def firstToken := activate (fun _ => four 1 0 0 0) (fun _ => four 1 0 0 0)
    (fun _ _ => 0) (fun _ => 1) (fun _ => 0) 0 0 (fun _ => 0)

theorem first_exact : output firstToken (fun _ => 0) 1 1 0 = 500000/1000001 := by
  rw [single]
  simp only [firstToken, activate, sigmoid, neg_zero, Real.exp_zero, normalize_dot]
  rw [dot_four]
  norm_num [four, ← sq, div_pow, Real.sq_sqrt (show 0 ≤ (1000001:ℝ) by norm_num)]

local macro "fields" : tactic => `(tactic|
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, RoundMode.away])

theorem first_rounded : brainFloat.round .rn .inf (output firstToken (fun _ => 0) 1 1 0) false =
    some (.fin (1/2)) := by
  rw [first_exact, Layout.round_between (m := .rn) (F := 0x3eff) (by trivial) (by decide)
    (by fields) (by fields) (by simp)]
  fields

/-- A NaN in the last of a thread's eight key coordinates poisons the fused square,
whatever value the first seven coordinates accumulated. -/
theorem square_nan (acc : FVal) (payload : Option Nat) :
    squareStep acc (.nan payload) = some (.nan none) := by
  cases acc <;> rfl

/-- Each butterfly addition keeps an existing NaN in the writer's lane. The other
lane can supply any finite number, signed zero, infinity or NaN. -/
theorem add_nan (peer : FVal) :
    sumStep (.nan none) peer = some (.nan none) := by
  cases peer <;> rfl

theorem reduction (acc : FVal) (payload : Option Nat) (peers : List FVal) :
    (squareStep acc (.nan payload)).bind (fun a => peers.foldlM sumStep a) =
      some (.nan none) := by
  rw [square_nan]
  change peers.foldlM sumStep (.nan none) = some (.nan none)
  induction peers with
  | nil => rfl
  | cons p ps ih => simp [List.foldlM_cons, add_nan, ih]

/-- The reciprocal square root returns NaN for a NaN argument. Multiplication of
the cleared key by that inverse length also returns NaN, at any rounding mode. -/
theorem cleared_key (payload : Option Nat) (m : RoundMode) :
    invRoot.lane [.nan payload] = some (.val (.nan none)) ∧
    FloatFmt.f32.layout.roundVal m true ((FVal.zero false).mul (.nan payload)) =
      some (.nan none) := by constructor <;> rfl

theorem observed_words :
    brainFloat.decode 0x7fc1 = some (.nan (some 0x7fc1)) ∧
    brainFloat.decode 0x3f00 = some (.fin (1/2)) ∧
    brainFloat.decode 0x7fff = some (.nan (some 0x7fff)) ∧
    binary32.decode 0x7fffffff = some (.nan (some 0x7fffffff)) := by decide +kernel

/-- Holding every other argument fixed, no function of the first key row alone can
return both public output words observed on the unmodified extension. -/
theorem no_isolated_result (f : (Fin 128 → Nat) → Nat) :
    ¬ (f (keyWord 0 0) = 0x3f00 ∧ f (keyWord 0x7fc1 0) = 0x7fff) := by
  have same : keyWord 0 0 = keyWord 0x7fc1 0 := by funext i; simp [keyWord]
  rw [same]
  omega

end
end FlashKda.TailIsolation
