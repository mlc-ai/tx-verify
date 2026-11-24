-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormMachine

/-! Numerical meaning of the square-root arguments extracted from both production binaries. -/
namespace FlashKda.Binary
open PTX Normalize OneToken Expr
noncomputable section

/-- Interpret the floating part of the symbolic register graph up to the reciprocal square root.
The input leaf is one widened bfloat16 coordinate from the lane's shared-memory packet. -/
def evaluate : Expr → Nat → Option FVal
  | .zero, _ => some (.zero false)
  | .epsilon, _ => binary32.decode 0x358637bd
  | .word .zero (.input key index), lane => do widened (← (rawPacket key lane)[index]?)
  | .fma a b c, lane => do
    let acc ← evaluate c lane
    guard (a = b)
    squareStep acc (← evaluate a lane)
  | .add a b, lane => do sumStep (← evaluate a lane) (← evaluate b lane)
  | .shuffle d a, lane => do
    let (peer, valid) := shflSource .bfly lane d 31
    guard valid
    evaluate a peer
  | _, _ => none

def localTree (key : Bool) (indices : List Nat) (initial : Expr) :=
  indices.foldl (fun acc i =>
    let x := word .zero (input key i)
    fma x x acc) initial

def localInput (key : Bool) (lane : Nat) (acc : FVal) (i : Nat) : Option FVal := do
  squareStep acc (← widened (← (rawPacket key lane)[i]?))

theorem eval_localTree (key : Bool) (lane : Nat) (indices : List Nat) (initial : Expr) :
    evaluate (localTree key indices initial) lane =
      (evaluate initial lane).bind (indices.foldlM (localInput key lane) ·) := by
  induction indices generalizing initial with
  | nil => simp [localTree]
  | cons i rest ih =>
    unfold localTree at *
    rw [List.foldl_cons, ih]
    cases ha : evaluate initial lane with
    | none => simp [evaluate, ha]
    | some a =>
      cases hr : (rawPacket key lane)[i]? with
      | none => simp [evaluate, localInput, List.foldlM_cons, ha, hr]
      | some raw =>
        cases hx : widened raw <;> simp [evaluate, localInput, List.foldlM_cons, ha, hr, hx]

def mergedTree (key : Bool) (distances : List Nat) : Expr :=
  match distances with
  | [] => localTree key (List.range 8) .zero
  | d::ds => let previous := mergedTree key ds; add previous (shuffle d previous)

theorem eval_mergedTree (key : Bool) (distances : List Nat) (lane : Nat) :
    evaluate (mergedTree key distances) lane = warpSum key distances lane := by
  induction distances generalizing lane with
  | nil =>
    rw [mergedTree, eval_localTree]
    cases key <;> by_cases h : lane = 0 <;>
      simp [warpSum, rawPacket, localInput, laneSum, h, evaluate, List.range_succ,
        List.foldlM_cons, Option.bind_assoc]
  | cons d ds ih =>
    rw [mergedTree, evaluate, evaluate, warpSum, ih]
    cases h : shflSource .bfly lane d 31 with
    | mk peer valid =>
      cases valid <;> simp [ih]

def inputValue (key : Bool) : ℚ := if key then 14696465/16777216 else 3146753/1048576
def inputWord (key : Bool) : Nat := if key then 0x3f604011 else 0x40401004
def energy (key : Bool) : ℚ := if key then 7/8+1/1024 else 3+1/1024

theorem final_add (key : Bool) : sumStep (wordValue (squaredWord key)) (.fin epsilon32) =
    some (.fin (inputValue key)) := by
  apply sum_of_round
  · cases key <;> decide +kernel
  have exactSum : (wordValue (squaredWord key)).add .rn (.fin epsilon32) =
      .fin (energy key + epsilon32) := by cases key <;> decide +kernel
  rw [exactSum]
  change binary32.roundFtz .rn true _ = _
  unfold Layout.roundFtz
  have rounded : binary32.round .rn .inf ((energy key + epsilon32 : ℚ) : ℝ) false =
      some (.fin (inputValue key)) := by
    cases key
    · simpa [energy, inputValue] using squared_norm_inputs.1
    · simpa [energy, inputValue] using squared_norm_inputs.2
  rw [rounded]
  have hn : ¬ |((energy key + epsilon32 : ℚ) : ℝ)| < (binary32.minNormal : ℚ) := by
    cases key <;> norm_num [energy, epsilon32, Layout.minNormal, Layout.bias]
  have hf : binary32.flush (.fin (inputValue key)) = .fin (inputValue key) :=
    by cases key <;> decide +kernel
  push_cast at hn
  simp [hn, hf]

def rootArgument (expression : Expr) : Option FVal :=
  match expression with | root a => evaluate a 0 | _ => none

theorem expected_argument (key : Bool) :
    rootArgument (expected key) = some (.fin (inputValue key)) := by
  change (do sumStep (← evaluate (mergedTree key [1,2,4,8]) 0) (← binary32.decode 0x358637bd)) = _
  rw [eval_mergedTree, checked_sums, epsilon_value]
  exact final_add key

/-- Evaluate both expressions from the disassembled device binaries on the first row.
The words are the actual operands of the two reciprocal square roots in this slice model. -/
theorem binary_arguments : (do
    let (q,k) ← result
    return (← rootArgument q, ← rootArgument k)) =
      some (.fin (3146753/1048576), .fin (14696465/16777216)) ∧
    (∀ key, binary32.decode (inputWord key) = some (.fin (inputValue key))) := by
  constructor
  · rw [binary_routes]
    change (do return (← rootArgument (expected false), ← rootArgument (expected true))) = _
    rw [expected_argument,expected_argument]
    rfl
  · intro key; cases key <;> decide +kernel

end
end FlashKda.Binary
