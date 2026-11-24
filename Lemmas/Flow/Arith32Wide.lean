-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32
public import Lemmas.Flow.Step.SegSym

@[expose] public section

/-! # Wide and 64-bit integer forms, as Core's rules compute them

A proof tool, generic over the kernel (promoted from FlashMLA's pilot, `Proof2/Lib/Arith.lean`,
which took the 64-bit forms of tml-fa4's loader machine). The terms a value table writes for the
instructions `Lemmas/Flow/Arith32.lean` does not name: 64-bit arithmetic, wide multiplications,
shifts by a register, `cvt` between widths, `neg.s32`, `or`/`max` of words, unsigned division and
16-bit parity words. Each is the term Core's rule evaluates to (as `seg_fp` evaluates it), so a
table entry closes its segment by `rfl`.

No library module imports it, because a kernel that opens `PTX.Flow.Arith32` and keeps its own
form of one of these names (tml-fa4's MMA warp has its own `neg32`, the `sub.s32 0, x` form; its
loader machine has `r64`, `add64`, `sext`, `mulhi`, `mulWide`) would see two candidates; such a
kernel deletes its copy and imports this module. -/

namespace PTX.Flow.Arith32
open PTX

abbrev or32 (x y : BitVec 64) : BitVec 64 := r32 x ||| r32 y
abbrev max32 (x y : BitVec 64) : BitVec 64 :=
  if PTX.compare .gt .s 32 (r32 x) (r32 y) then r32 x else r32 y
abbrev neg32 (x : BitVec 64) : BitVec 64 := truncBits 32 (-r32 x)
/-- `shl.b32` by a register. -/
abbrev shlr (x y : BitVec 64) : BitVec 64 :=
  if (r32 y).toNat ≥ 32 then 0 else truncBits 32 (r32 x <<< (r32 y).toNat)
/-- `cvt.s32.s8`. -/
abbrev cvts8 (x : BitVec 64) : Value :=
  MemExt.same.extendBits 32 (cvtIntBits false .s 32 .s 8 (truncBits 8 x))
/-- The word `cvts8` writes. -/
abbrev cvts8w (x : BitVec 64) : BitVec 64 :=
  truncBits 32 (cvtIntBits false .s 32 .s 8 (truncBits 8 x))

abbrev r64 (x : BitVec 64) : BitVec 64 := truncBits 64 x
abbrev mul64 (x y : BitVec 64) : BitVec 64 := truncBits 64 (r64 x * r64 y)
abbrev add64 (x y : BitVec 64) : BitVec 64 := truncBits 64 (r64 x + r64 y)
abbrev addi64 (x : BitVec 64) (n : Int) : BitVec 64 :=
  truncBits 64 (r64 x + truncBits 64 (BitVec.ofInt 64 n))
abbrev shl64 (x : BitVec 64) (n : Int) : BitVec 64 :=
  if (i32 n).toNat ≥ 64 then 0 else truncBits 64 (r64 x <<< (i32 n).toNat)
/-- `cvt.s64.s32` and `cvt.u64.u32` of a 32-bit word (Core writes the unsigned case as
`truncBits`). -/
abbrev sext (x : BitVec 64) : BitVec 64 := truncBits 64 (cvtIntBits false .s 64 .s 32 (r32 x))
abbrev zext (x : BitVec 64) : BitVec 64 := truncBits 64 (r32 x)
/-- `mul.hi.s32` by an immediate. -/
abbrev mulhi (x : BitVec 64) (n : Int) : BitVec 64 :=
  truncBits 32 (BitVec.ofInt 64 ((if (some IType.s == some IType.s) = true then
    toSigned 32 (r32 x) * toSigned 32 (i32 n) else ↑(r32 x).toNat * ↑(i32 n).toNat) / 2 ^ 32))
/-- `shr.u32` by a register. -/
abbrev shrur (x y : BitVec 64) : BitVec 64 :=
  if (r32 y).toNat ≥ 32 then 0 else r32 x >>> (r32 y).toNat
/-- `mul.wide` of kind `k` by an immediate. -/
abbrev mulWide (k : IType) (x : BitVec 64) (n : Int) : BitVec 64 :=
  if (some k == some IType.s) = true then
    truncBits (2 * 32) (BitVec.ofInt 64 (toSigned 32 (r32 x) * toSigned 32 (i32 n)))
  else BitVec.ofNat 64 ((r32 x).toNat * (i32 n).toNat)
/-- `mul.wide` of kind `k` of two registers. -/
abbrev mulWideR (k : IType) (x y : BitVec 64) : BitVec 64 :=
  if (some k == some IType.s) = true then
    truncBits (2 * 32) (BitVec.ofInt 64 (toSigned 32 (r32 x) * toSigned 32 (r32 y)))
  else BitVec.ofNat 64 ((r32 x).toNat * (r32 y).toNat)
/-- `div.u32` with a rule, its quotient. -/
abbrev divu (x y : BitVec 64) : BitVec 64 := PTX.Flow.divQ .u 32 (r32 x) (r32 y)
/-- Whether `div.u32` has a rule. -/
abbrev divuOk (x y : BitVec 64) : Bool := PTX.Flow.divOk .u 32 (r32 x) (r32 y)

/-- 16-bit forms of the parity register: a literal, `xor` with `1`, and `cvt.u32.u16`. -/
abbrev i16 (n : Int) : BitVec 64 := truncBits 16 (BitVec.ofInt 64 n)
abbrev xor16 (x : BitVec 64) : BitVec 64 := truncBits 16 (truncBits 16 x ^^^ i16 1)
abbrev zext16 (x : BitVec 64) : BitVec 64 := truncBits 32 (truncBits 16 x)
/-- `cvt.u32.u16` of a register that already holds a 16-bit word, as Core evaluates it there (no
16-bit truncation). -/
abbrev zext16w (x : BitVec 64) : BitVec 64 := truncBits 32 x

/-- **On a 16-bit word the two forms of `cvt.u32.u16` agree.** -/
theorem zext16_eq_zext16w {x : BitVec 64} (h : x.toNat < 2 ^ 16) : zext16 x = zext16w x := by
  apply BitVec.eq_of_toNat_eq
  simp only [zext16, zext16w, truncBits, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := x.toNat % 2 ^ 16) (by omega), Nat.mod_eq_of_lt (a := x.toNat) h]

end PTX.Flow.Arith32
