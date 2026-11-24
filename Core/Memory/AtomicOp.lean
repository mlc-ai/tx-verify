-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

/-!
# The values of atomic operations

The operations of `atom` and `red` and of the tensor reductions, one definition for all of them.
-/

namespace PTX

noncomputable section

/-! ## THREAD-ATOMIC-OP — the values of atomic operations
Statement: An integer or bit operation of `atom`, `red` or a tensor reduction computes the result of
  the Semantics section of `atom` exactly at the element width, from the bit patterns of the old
  value in memory and of the operands, comparing as two's complement numbers for the signed types. A
  floating operation takes its value from a kernel assumption, and without one the operation has no
  rule.

Defs: AtomOp.apply, Value.ofWidth, rmwValue

Source:
- §9.7.15.5 (atom): "atomic { d = *a; *a = (operation == cas) ? operation(*a, b, c) : operation(*a,
    b); }"
- §9.7.15.5 (atom): "inc(r, s) = (r >= s) ? 0 : r+1; dec(r, s) = (r==0 || r > s) ? s : r-1; exch(r,
    s) = s; cas(r,s,t) = (r == s) ? t : r;"
- §9.7.15.5 (atom): "The .inc and .dec operations return a result in the range [0..b] ."
- §9.7.15.5 (atom): "The .add operation rounds to nearest even."
- §9.7.15.5 (atom): "The .min and .max operations implement the exact same floating-point
    instructions as the non-atomic min and max instructions, but perform them atomically."
- §9.7.15.6 (red): "*a = operation(*a, b);"
- §9.7.1.13 (min): "d = (a < b) ? a : b; // Integer (signed and unsigned)"
- §9.7.1.14 (max): "d = (a > b) ? a : b; // Integer (signed and unsigned)"
- §9.7.9.1: "Compute the bit-wise and operation for the bits in a and b"
- THREAD-INT (an integer result wraps at its width)
- THREAD-BITS (bit patterns)
- ASM-INTERFACE (`rmwRule`)

Direction: stricter

Applies: The write half of every `atom` and `red` element with a rule (THREAD-ATOMIC) and every
  tensor reduction element (DEP-REDUCTION-VALUES)

Premises: The element type is an integer, bit or floating type; for an integer or bit type the old
  value and each operand has a bit pattern of the element's size.

Effect: Local value of the bytes an atomic read-modify-write writes; `noRule` and `typeMismatch` are
  faults (ERR-FAULT-REASON). The integer and bit operations work on the bit patterns of the old
  value `r` and the operand `s` taken modulo `2 ^ w` for the element width `w` (`AtomOp.apply`):
  `add` wraps at the width as the integer `add` does (THREAD-INT), `min` and `max` compare as two's
  complement numbers for the `.s` types and as unsigned numbers otherwise, `and`, `or` and `xor` are
  bitwise, `inc`, `dec` and `exch` are the quoted formulas, and `cas` compares `r` with the compare
  operand and writes the swap operand when they are equal. A result of at most 64 bits is a bit
  vector; a 128-bit result is two 64-bit halves, low half first (`Value.ofWidth`, THREAD-BYTES). A
  floating operation (`add`, `min` and `max` of a floating element) has no Core rule: the first
  assumption whose `rmwRule` gives a value supplies it, and without one the operation is `noRule`,
  as for every floating instruction.
-/

/-- Operation `op` at width `w` on the bit patterns `r` (the old value) and `s` (the operand),
both taken modulo `2 ^ w`; `signed` compares `min` and `max` as two's complement numbers. `cas`
has a third operand and is computed by `rmwValue`; here it leaves `r` unchanged. -/
def AtomOp.apply (op : AtomOp) (signed : Bool) (w : Nat) (r s : Nat) : Nat :=
  let m := 2 ^ w
  let r := r % m
  let s := s % m
  let int (n : Nat) : Int := if signed ∧ m ≤ 2 * n then (n : Int) - m else n
  match op with
  | .add => (r + s) % m
  | .min => if int r ≤ int s then r else s
  | .max => if int s ≤ int r then r else s
  | .inc => if s ≤ r then 0 else r + 1
  | .dec => if r = 0 ∨ s < r then s else r - 1
  | .and => r &&& s
  | .or => r ||| s
  | .xor => r ^^^ s
  | .exch => s
  | .cas => r

/-- The `w`-bit integer value with bit pattern `n`: a bit vector for at most 64 bits, and two 64-bit
halves, low half first, for more. -/
def Value.ofWidth (w n : Nat) : Value :=
  if w ≤ 64 then .bits w (BitVec.ofNat 64 n)
  else .pair (.bits 64 (BitVec.ofNat 64 n)) (.bits 64 (BitVec.ofNat 64 (n / 2 ^ 64)))

/-- The value an atomic operation `op` on an element of type `ty` writes, from the old value `r`
and the operands `srcs` (`[b]`, or `[b, c]` for `cas`). An integer or bit type computes on bit
patterns of exactly `ty.width` bits; a floating type takes the first value an assumption's
`rmwRule` gives, and is `noRule` without one. -/
def rmwValue (A : List Assumption) (op : AtomOp) (ty : DType) (r : Value) (srcs : List Value) :
    Exec Value :=
  match ty with
  | .float _ =>
    match op, srcs with
    | .cas, _ => throw .noRule
    | _, [s] => (A.findSome? fun asm => asm.rmwRule op ty r s).getD (.error .noRule)
    | _, _ => throw .noRule
  | .int k w =>
    let pat (v : Value) : Exec Nat :=
      match v.bitPattern with
      | some n => if 8 * v.bytes = w then pure n else throw .typeMismatch
      | none => throw .typeMismatch
    match op, srcs with
    | .cas, [b, c] => do
      let x ← pat r
      let y ← pat b
      let z ← pat c
      pure (Value.ofWidth w (if x % 2 ^ w = y % 2 ^ w then z % 2 ^ w else x % 2 ^ w))
    | .cas, _ => throw .noRule
    | _, [s] => do
      let x ← pat r
      let y ← pat s
      pure (Value.ofWidth w (op.apply (k == .s) w x y))
    | _, _ => throw .noRule
  | _ => throw .noRule

end

end PTX
