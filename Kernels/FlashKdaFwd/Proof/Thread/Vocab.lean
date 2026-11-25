-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32Wide

@[expose] public section

/-! # Integer forms of the kernel that the library's vocabulary does not have

The transition functions of the thread machine are written in the vocabulary of
`Lemmas/Flow/Arith32.lean` and `Arith32Wide.lean`: one reducible abbreviation per integer
instruction form, equal by unfolding to the term Core computes, so that the value equations of
a segment close by `rfl`. This file adds the forms this kernel uses and those files lack: a
64-bit immediate, `cvt.u32.u64` of a word, `max`, `min`, `mul.lo` and `mad.lo` with an immediate,
`and.b32` of two registers, and the 16-bit instructions of the conversion loop's block count. -/

namespace PTX.Flow.Arith32
open PTX

/-- The bits of a 64-bit immediate. -/
abbrev i64 (n : Int) : BitVec 64 := truncBits 64 (BitVec.ofInt 64 n)
/-- `cvt.u32.u64` of a 64-bit word. -/
abbrev low32 (x : BitVec 64) : BitVec 64 := truncBits 32 (truncBits 64 x)
/-- `max.s32` with an immediate. -/
abbrev maxi (x : BitVec 64) (n : Int) : BitVec 64 :=
  if PTX.compare .gt .s 32 (r32 x) (i32 n) then r32 x else i32 n
/-- `min.s32` with an immediate. -/
abbrev mini (x : BitVec 64) (n : Int) : BitVec 64 :=
  if PTX.compare .lt .s 32 (r32 x) (i32 n) then r32 x else i32 n
/-- `mul.lo.s32` with an immediate. -/
abbrev muli (x : BitVec 64) (n : Int) : BitVec 64 := truncBits 32 (r32 x * i32 n)
/-- `mad.lo.s32 d, x, <immediate>, z`. -/
abbrev madi (x : BitVec 64) (n : Int) (z : BitVec 64) : BitVec 64 :=
  truncBits 32 (r32 x * i32 n + r32 z)
/-- `and.b32` of two registers. -/
abbrev and32 (x y : BitVec 64) : BitVec 64 := r32 x &&& r32 y
/-- The bits a 16-bit operand reads. -/
abbrev r16 (x : BitVec 64) : BitVec 64 := truncBits 16 x
abbrev sub16 (x y : BitVec 64) : BitVec 64 := truncBits 16 (r16 x - r16 y)
abbrev and16 (x y : BitVec 64) : BitVec 64 := r16 x &&& r16 y
abbrev mul16 (x y : BitVec 64) : BitVec 64 := truncBits 16 (r16 x * r16 y)
abbrev shru16 (x y : BitVec 64) : BitVec 64 :=
  if (r16 y).toNat ≥ 16 then 0 else r16 x >>> (r16 y).toNat
abbrev scmp16 (c : Cmp) (x y : BitVec 64) : Bool := compare c .b 16 (r16 x) (r16 y)

/-! 16-bit forms as Core computes them, where the two-register forms above are not the code's:
`cvt.u16.u32` reads its source at 32 bits; an immediate operand is truncated once (`i16 n`, not
`r16 (i16 n)`), and a shift amount is read at 32 bits. The walk of a segment decides a branch
from a hypothesis up to reducible unfolding only, so a predicate computed from such terms must
be Core's term exactly. -/

abbrev low16 (x : BitVec 64) : BitVec 64 := truncBits 16 (truncBits 32 x)
abbrev subi16 (x : BitVec 64) (n : Int) : BitVec 64 := truncBits 16 (r16 x - i16 n)
abbrev isub16 (n : Int) (y : BitVec 64) : BitVec 64 := truncBits 16 (i16 n - r16 y)
abbrev andi16 (x : BitVec 64) (n : Int) : BitVec 64 := r16 x &&& i16 n
abbrev muli16 (x : BitVec 64) (n : Int) : BitVec 64 := truncBits 16 (r16 x * i16 n)
abbrev shrui16 (x : BitVec 64) (n : Int) : BitVec 64 :=
  if (i32 n).toNat ≥ 16 then 0 else r16 x >>> (i32 n).toNat
abbrev scmpi16 (c : Cmp) (x : BitVec 64) (n : Int) : Bool := compare c .b 16 (r16 x) (i16 n)

end PTX.Flow.Arith32
