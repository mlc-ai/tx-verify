-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-! # The 32-bit integer arithmetic of the code, on the bits registers hold

A proof tool. The value-table generator (`Tools/machine_gen.py`) writes the value of a register
as the term the code computes, in this vocabulary: each abbreviation is the result of one integer
instruction on 32-bit operands read from registers that hold `.bits _ x`, as the core's rules
compute it. A table in this form mirrors the code, so the segments of `site_cases` close it by
`rfl` (rule M2 of the role-machine plan). -/

namespace PTX.Flow.Arith32
open PTX

/-- The bits a 32-bit operand reads from a register holding `.bits _ x`. -/
abbrev r32 (x : BitVec 64) : BitVec 64 := truncBits 32 x
/-- The bits of a 32-bit immediate. -/
abbrev i32 (n : Int) : BitVec 64 := truncBits 32 (BitVec.ofInt 64 n)
abbrev add32 (x y : BitVec 64) : BitVec 64 := truncBits 32 (r32 x + r32 y)
abbrev addi (x : BitVec 64) (n : Int) : BitVec 64 := truncBits 32 (r32 x + i32 n)
abbrev sub32 (x y : BitVec 64) : BitVec 64 := truncBits 32 (r32 x - r32 y)
abbrev mul32 (x y : BitVec 64) : BitVec 64 := truncBits 32 (r32 x * r32 y)
abbrev mad32 (x y z : BitVec 64) : BitVec 64 := truncBits 32 (r32 x * r32 y + r32 z)
abbrev min32 (x y : BitVec 64) : BitVec 64 :=
  if compare .lt .s 32 (r32 x) (r32 y) then r32 x else r32 y
abbrev shrs (x : BitVec 64) (n : Int) : BitVec 64 :=
  truncBits 32 (BitVec.ofInt 64 (toSigned 32 (r32 x) / 2 ^ min (i32 n).toNat 32))
abbrev shru (x : BitVec 64) (n : Int) : BitVec 64 :=
  if (i32 n).toNat ≥ 32 then 0 else r32 x >>> (i32 n).toNat
abbrev shl (x : BitVec 64) (n : Int) : BitVec 64 :=
  if (i32 n).toNat ≥ 32 then 0 else truncBits 32 (r32 x <<< (i32 n).toNat)
abbrev andi (x : BitVec 64) (n : Int) : BitVec 64 := r32 x &&& i32 n
abbrev xor32 (x y : BitVec 64) : BitVec 64 := r32 x ^^^ r32 y
abbrev not32 (x : BitVec 64) : BitVec 64 := truncBits 32 (~~~ r32 x)
/-- The population count of a 32-bit word. -/
abbrev popc (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 32).filter (r32 x).toNat.testBit).length
abbrev scmp (c : Cmp) (k : IType) (x y : BitVec 64) : Bool := compare c k 32 (r32 x) (r32 y)
abbrev scmpi (c : Cmp) (k : IType) (x : BitVec 64) (n : Int) : Bool :=
  compare c k 32 (r32 x) (i32 n)
/-- `scmpi` in the form the code's `setp.<c>.<k> %p, %x, <immediate>` has: the walk of a segment
recomputes the comparison by Core's rule, which writes `truncBits` out, so a `scmpi` in a machine's
abbreviation and the walk's term differ only by the expansion of `r32`/`i32`. `cheapDefEq` can time
out on the `BitVec.ofInt` of a large immediate, so a role rewrites by this equation instead. -/
theorem scmpi_eq_setp (c : Cmp) (k : IType) (x : BitVec 64) (n : Int) :
    scmpi c k x n
      = compare c k 32 (truncBits 32 x) (truncBits 32 (BitVec.ofInt 64 n)) := rfl
/-- A `selp` on a predicate that holds `c`. -/
abbrev sel (c : Bool) (x y : BitVec 64) : BitVec 64 := if c = true then x else y

end PTX.Flow.Arith32
