-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Proof.CheckForward
import Lean.Data.Json

/-! Read a raw-word capture. Validate every dimension, decode every field, run the
independent rational checker and report outward bounds for the maximum absolute errors. -/
open Lean PTX FlashKda.Enclosure

namespace PublicCheck

structure TokenWords where
  q : Array Nat
  k : Array Nat
  gate : Array Nat
  logit : Nat
  deriving FromJson

structure RowWords where
  members : List Nat
  initial : Option (Array Nat)
  values : Array Nat
  outputs : Array Nat
  finalState : Option (Array Nat)
  deriving FromJson

structure Sample where
  label : String
  scale64 : Nat
  scale32 : Option Nat := none
  lower64 : Nat
  parameter32 : Nat
  bias32 : Array Nat
  stateBits : Nat
  tokens : Array TokenWords
  rows : Array RowWords
  deriving FromJson

structure Capture where
  cases : Array Sample
  deriving FromJson

private def finite (fmt : Layout) (bits w : Nat) : Except String ℚ := do
  unless w < 2^bits do throw s!"word {w} does not fit in {bits} bits"
  ((fmt.decode w).bind FVal.num).elim (throw s!"nonfinite or undefined {bits}-bit word {w}") pure

private def bf := finite FloatFmt.bf16.layout 16
private def single := finite FloatFmt.f32.layout 32
private def double := finite (.binary 11 52 true .ieee) 64

/-- The binding narrows the submitted Python double to a C++ float. Earlier captures
supply only the double. Check the candidate against exact midpoints, including ties
at zero and at the end of the finite range. -/
def scaleAtEntry (submitted : Nat) (captured : Option Nat) : Except String ℚ := do
  let x ← double submitted
  let word := captured.getD (Float.ofBits submitted.toUInt64).toFloat32.toBits.toNat
  let y ← single word
  let field := word % 2^31
  let center := 2*|x|
  let magnitude := Layout.magnitude 8 23
  let low := magnitude (field-1) + magnitude field
  let high := magnitude field + magnitude (field+1)
  let even := field % 2 == 0
  unless submitted / 2^63 == word / 2^31 &&
      (low < center || (low == center && even)) &&
      (center < high || (center == high && even)) do
    throw "binary32 scale disagrees with rounding the submitted binary64 word"
  return y

private def row (decode : Nat → Except String ℚ) (words : Array Nat) :
    Except String (Rationals 128) := do
  let values ← words.mapM decode
  if h : values.size = 128 then return ⟨values,h⟩
  else throw s!"expected 128 words, got {values.size}"

private def prepareToken (bits splits : Nat) (floor : ℚ) (parameter : Ball) (bias : Rationals 128)
    (r : TokenWords) : Except String (Prepared 128) := do
  let raw : Raw 128 := ⟨← row bf r.q,← row bf r.k,← row bf r.gate,← bf r.logit⟩
  (prepare bits splits floor parameter bias raw).elim
    (throw "activation enclosure unavailable at the requested precision or exponent range") pure

instance : ToJson Maximum where
  toJson m := Json.mkObj [
    ("lowerMillionths",toJson m.lowerMillionths),("upperMillionths",toJson m.upperMillionths)]

structure Report where
  sample : String
  outputCount : Nat
  stateCount : Nat
  outputError : Maximum
  stateError : Maximum
  deriving ToJson

def check (bits splits : Nat) (s : Sample) : Except String Report := do
  let n := s.tokens.size
  let scale ← scaleAtEntry s.scale64 s.scale32
  let floor ← double s.lower64
  let param ← single s.parameter32
  let bias ← row single s.bias32
  let state ← match s.stateBits with
    | 16 => pure bf
    | 32 => pure single
    | _ => throw "expected bfloat16 or binary32 state"
  let p ← (expAt bits splits param).elim (throw "log-gate parameter outside exponent range") pure
  let prepared ← s.tokens.mapM (prepareToken bits splits floor p bias)
  let channels := s.rows.toList.flatMap (·.members)
  unless channels.mergeSort = List.range 128 do throw "value channels must partition 0 through 127"
  let mut outputError : Maximum := {}
  let mut stateError : Maximum := {}
  let mut stateCount := 0
  let hasFinal := s.rows[0]?.any fun w => w.finalState.isSome
  let hasInitial := s.rows[0]?.any fun w => w.initial.isSome
  for group in s.rows do
    unless !group.members.isEmpty && group.finalState.isSome == hasFinal &&
        group.initial.isSome == hasInitial do throw "inconsistent channel groups or optional state"
    unless group.values.size == n && group.outputs.size == n do throw "inconsistent token count"
    let initial ← match group.initial with
      | none => pure (Vector.replicate 128 0)
      | some ws => row state ws
    let values ← group.values.mapM bf
    let r := run bits scale (fun t => prepared[t]!) (fun t => values[t]!) initial n
    unless r.outputs.size == group.outputs.size do throw "inconsistent readout length"
    outputError ← (scan .bf16 16 outputError (r.outputs.zip group.outputs).toList).elim
      (throw "nonfinite or invalid bfloat16 output word") pure
    if let some finalWords := group.finalState then
      unless finalWords.size == 128 do throw "inconsistent final-state width"
      let fmt := if s.stateBits == 16 then FloatFmt.bf16 else .f32
      stateError ← (scan fmt s.stateBits stateError (r.state.toArray.zip finalWords).toList).elim
        (throw "nonfinite or invalid final-state word") pure
      stateCount := stateCount+128*group.members.length
  return ⟨s.label,n*128,stateCount,outputError,stateError⟩

end PublicCheck

def main (args : List String) : IO Unit := do
  let (file,bits,splits) ← match args with
    | [f] => pure (f,48,4)
    | [f,b,s] =>
      match b.toNat?, s.toNat? with
      | some precision, some halves => pure (f,precision,halves)
      | _,_ => throw (IO.userError "precision and halving count must be natural numbers")
    | _ => throw (IO.userError "usage: check_public.lean capture.json [fractionalBits halvings]")
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let inputs : PublicCheck.Capture ← IO.ofExcept (fromJson? raw)
  for s in inputs.cases do
    match PublicCheck.check bits splits s with
    | .error e => throw (IO.userError s!"{s.label}: {e}")
    | .ok report => IO.println (toJson report).compress
