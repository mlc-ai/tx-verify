-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaValue

/-! Exact kind::i8 arithmetic (DEP-TC-MMA-VALUE): signedness per operand, 32-bit
wraparound of the accumulation, and no value from unknown bytes. -/
namespace PTX.Tests.TcMmaIntValue
open TcMma

private def b8 (x : Nat) : Option Byte := some (.bits 8 (BitVec.ofNat 64 x), 0)
private def row (x : Nat) : List (Option Byte) := List.replicate 32 (b8 x)

-- Byte interpretation: 0xFF is 255 unsigned and -1 signed; 0x80 is -128 signed.
example : byteInt false (b8 255) = some 255 := rfl
example : byteInt true (b8 255) = some (-1) := rfl
example : byteInt true (b8 128) = some (-128) := rfl
example : byteInt true (b8 127) = some 127 := rfl
-- Byte k of a wider register value is its k-th little-endian byte; past the width, none.
example : byteInt false (some (.bits 32 (BitVec.ofNat 64 0x11223344), 2)) = some 0x22 := rfl
example : byteInt false (some (.bits 32 (BitVec.ofNat 64 0x11223344), 4)) = none := rfl
example : byteInt false none = none := rfl
example : byteInt true (some (.pred true, 0)) = none := rfl

-- One dot product of length 32, for every signedness combination.
example : (mmaTerms (.i8 false false false) (row 255) (row 2) 0 0).map List.sum =
    some (32 * 255 * 2) := rfl
example : (mmaTerms (.i8 true false false) (row 255) (row 2) 0 0).map List.sum = some (-64) := rfl
example : (mmaTerms (.i8 true true false) (row 255) (row 255) 0 0).map List.sum = some 32 := rfl
example : (mmaTerms (.i8 false true false) (row 255) (row 255) 0 0).map List.sum =
    some (-(32 * 255)) := rfl
-- Extreme magnitudes: 32 * (-128) * (-128) and 32 * 255 * 255 fit easily in 32 bits.
example : (mmaTerms (.i8 true true false) (row 128) (row 128) 0 0).map List.sum = some 524288 := rfl
example : (mmaTerms (.i8 false false false) (row 255) (row 255) 0 0).map List.sum = some 2080800 :=
    rfl
-- Rows of A and columns of B are selected by index.
example : (mmaTerms (.i8 false false false) (row 0 ++ row 1) (row 0 ++ row 0 ++
    row 3) 1 2).map List.sum = some 96 := rfl
example : (mmaTerms (.i8 false false false) (row 0 ++ row 1) (row 0 ++ row 0 ++
    row 3) 0 2).map List.sum = some 0 := rfl
-- One unknown byte anywhere in the dot product leaves the element undetermined.
example : (mmaTerms (.i8 false false false) (row 1 |>.set 17 none) (row 1) 0 0).map List.sum =
    none := rfl
example : (mmaTerms (.i8 false false false) (row 1) (row 1) 1 0).map List.sum = none := rfl

-- Results are 32-bit two's complement: -64 is 2^32 - 64.
example : intEval true false false false (row 255) (row 2) none 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 (2 ^ 32 - 64))) := rfl
-- Overwrite ignores the old D, even an unknown one.
example : intEval false false false false (row 1) (row 1) (some (.pred true)) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 32)) := rfl
-- Accumulation adds the old word modulo 2^32.
example : intEval false false false true (row 1) (row 1) (some (.bits 32 (BitVec.ofNat 64 10))) 0 0
    =
    .ok (.bits 32 (BitVec.ofNat 64 42)) := rfl
example : intEval false false false true (row 1) (row 1)
    (some (.bits 32 (BitVec.ofNat 64 (2 ^ 32 - 32)))) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 0)) := rfl
example : intEval true false false true (row 255) (row 1)
    (some (.bits 32 (BitVec.ofNat 64 0))) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 (2 ^ 32 - 32))) := rfl
-- Accumulation needs a 32-bit old D; none or another width is not invented as zero.
example : intEval false false false true (row 1) (row 1) none 0 0 = .error .uninitialized := rfl
example : intEval false false false true (row 1) (row 1) (some (.bits 16 (BitVec.ofNat 64 0))) 0 0 =
    .error .uninitialized := rfl
example : intEval false false false false (row 1 |>.set 0 none) (row 1) none 0 0 =
    .error .uninitialized := rfl

-- `eval` dispatches on the kind: i8 needs no profile, f16 has no Core rule.
private def i8d : Descriptor := ⟨.one, .i8 true false false, 128, 8, false, false, false, false,
    false⟩
private def f16d : Descriptor := ⟨.one, .f16 .f16 .f32, 128, 8, false, false, false, false, false⟩
example : eval [] i8d false (row 255) (row 2) none 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 (2 ^ 32 - 64))) := rfl
example : eval [] f16d false (row 1) (row 1) none 0 0 = .error .noRule := rfl

/-! ## Saturation (descriptor bit 3)

The products of one element never overflow s32 (|Σ| ≤ 32·128·128), so only adding the old D
can. The accumulation order is unspecified, so a value is derived only when no partial sum, in
any order, leaves the range; then it equals the wrapping result. -/

private def w (x : Int) : Value := .bits 32 (BitVec.ofNat 64 ((BitVec.ofInt 32 x).toNat))

-- Overwrite: saturation cannot change the product sum.
example : intEval true true true false (row 128) (row 128) none 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 524288)) := rfl
-- Accumulation far from the bounds equals the wrapping result.
example : intEval false false true true (row 1) (row 1) (some (w 10)) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 42)) := rfl
example : intEval true false true true (row 255) (row 1) (some (w 0)) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 (2 ^ 32 - 32))) := rfl
-- Negative old D is read as a signed 32-bit value.
example : intEval false false true true (row 1) (row 1) (some (w (-40))) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 (2 ^ 32 - 8))) := rfl
-- Overflow above MAX_INT32: without saturation it wraps; with it no value is derived.
example : intEval false false false true (row 1) (row 1) (some (w (2 ^ 31 - 10))) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 (2 ^ 31 + 22))) := rfl
example : intEval false false true true (row 1) (row 1) (some (w (2 ^ 31 - 10))) 0 0 =
    .error .noRule := rfl
-- Below MIN_INT32 likewise.
example : intEval true false true true (row 255) (row 1) (some (w (-(2 ^ 31) + 5))) 0 0 =
    .error .noRule := rfl
-- Even when the final sum fits, a partial sum could overflow in some order: no value.
private def mixed : List (Option Byte) := List.replicate 16 (b8 1) ++ List.replicate 16 (b8 255)
example : (mmaTerms (.i8 false true false) (row 1) mixed 0 0).map List.sum = some 0 := rfl
example : intEval false true true true (row 1) mixed (some (w (2 ^ 31 - 10))) 0 0 =
    .error .noRule := rfl
example : intEval false true false true (row 1) mixed (some (w (2 ^ 31 - 10))) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 (2 ^ 31 - 10))) := rfl
-- Exactly at the bound is still determined.
example : intEval false false true true (row 1) (row 1) (some (w (2 ^ 31 - 33))) 0 0 =
    .ok (.bits 32 (BitVec.ofNat 64 (2 ^ 31 - 1))) := rfl

end PTX.Tests.TcMmaIntValue
