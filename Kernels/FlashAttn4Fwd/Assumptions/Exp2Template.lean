-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.SegmentExact

@[expose] public section

/-!
# The software `exp2` template of the FlashAttention-4 forward kernel

The FlashAttention-4 forward kernel's assumption `swExp2` (`Assumption.segmentExact`, ASM-SEGMENT)
reads the instances of this template as the exact `2 ^ x`. The template is part of the kernel's
assumptions and is reviewed with its `Assumptions.lean`.

`cuteExp2` is CuTeDSL's software `exp2` of two `f32` lanes: clamp each input below at -127
(`max.f32 x, x, 0fC2FE0000`), pack the two, round down to an integer with `add.rm.f32x2`
against `1.5·2^23`, recover the fraction with two `sub.rn.f32x2`, evaluate a degree-3
polynomial in the fraction with three `fma.rn.f32x2` (coefficients `0f3D9DF09D`,
`0f3E6906A4`, `0f3F31F519`, `0f3F800000`), and add the integer part, shifted left by 23, to
the polynomial's bit pattern with `shl.b32` and `add.s32`. It computes approximately
`2 ^ max(x, -127)`. The template reads it as the exact `2 ^ x` (`Real.rpow`): the clamp at
-127 (which gives about `2^-127` where `2 ^ x` is smaller) and the polynomial's error are
approximations recorded in OPEN-NUM, not part of the exact reading. The 31-instruction
shape defines the five packed constants (and their scalar halves); the 21-instruction shape
reuses them, so its constant registers must hold exactly the values the defining shape writes.
-/

namespace PTX.Assumption
noncomputable section

/-- The slots of the software `exp2` of two lanes. -/
inductive CuteSlot where
  | x0 | x1 | m0 | m1 | a | kM | cM | r | ri0 | ri1 | s | f | k2 | c2 | k3 | c3 | p1 | k1 | c1
  | p2 | k0 | c0 | p3 | q0 | q1 | xr0 | fe0 | xe0 | o0 | y0 | xr1 | fe1 | xe1 | o1 | y1
  deriving DecidableEq

/-- The value Core's `mov.b32 d, 0f<c>` writes. -/
def cuteBits (c : Nat) : Value := .bits 32 (BitVec.ofNat 64 c)

/-- The value Core's `mov.b64 d, {k, k}` writes for `k` holding `cuteBits c`. -/
def cutePair (c : Nat) : Value := joinValue (cuteBits c) (cuteBits c)

/-- The exponent step of both lanes: `{ mov.b32 xr, ri; mov.b32 fe, q; shl.b32 xe, xr, 23;
add.s32 o, xe, fe; mov.b32 y, o; }` per lane. -/
def cuteTail : List (SegInstr CuteSlot) :=
  [.mov32 .xr0 .ri0, .mov32 .fe0 .q0, .shl32 .xe0 .xr0 23, .addS32 .o0 .xe0 .fe0, .mov32 .y0 .o0,
   .mov32 .xr1 .ri1, .mov32 .fe1 .q1, .shl32 .xe1 .xr1 23, .addS32 .o1 .xe1 .fe1, .mov32 .y1 .o1]

/-- The 31-instruction shape, which defines the constants. -/
def cuteExp2Define : SegShape CuteSlot where
  body := [.maxF32 .m0 .x0 0xC2FE0000, .maxF32 .m1 .x1 0xC2FE0000, .pack64 .a .m0 .m1,
    .movF32 .kM 0x4B400000, .pack64 .cM .kM .kM, .addRmF32x2 .r .a .cM, .unpack64 .ri0 .ri1 .r,
    .subRnF32x2 .s .r .cM, .subRnF32x2 .f .a .s, .movF32 .k2 0x3E6906A4, .pack64 .c2 .k2 .k2,
    .movF32 .k3 0x3D9DF09D, .pack64 .c3 .k3 .k3, .fmaRnF32x2 .p1 .c3 .f .c2,
    .movF32 .k1 0x3F31F519, .pack64 .c1 .k1 .k1, .fmaRnF32x2 .p2 .p1 .f .c1,
    .movF32 .k0 0x3F800000, .pack64 .c0 .k0 .k0, .fmaRnF32x2 .p3 .p2 .f .c0,
    .unpack64 .q0 .q1 .p3] ++ cuteTail
  io := [(.x0, .y0), (.x1, .y1)]
  consts := [(.kM, cuteBits 0x4B400000), (.cM, cutePair 0x4B400000),
    (.k2, cuteBits 0x3E6906A4), (.c2, cutePair 0x3E6906A4),
    (.k3, cuteBits 0x3D9DF09D), (.c3, cutePair 0x3D9DF09D),
    (.k1, cuteBits 0x3F31F519), (.c1, cutePair 0x3F31F519),
    (.k0, cuteBits 0x3F800000), (.c0, cutePair 0x3F800000)]
  defines := true

/-- The 21-instruction shape, which reuses the packed constants. -/
def cuteExp2Reuse : SegShape CuteSlot where
  body := [.maxF32 .m0 .x0 0xC2FE0000, .maxF32 .m1 .x1 0xC2FE0000, .pack64 .a .m0 .m1,
    .addRmF32x2 .r .a .cM, .unpack64 .ri0 .ri1 .r, .subRnF32x2 .s .r .cM, .subRnF32x2 .f .a .s,
    .fmaRnF32x2 .p1 .c3 .f .c2, .fmaRnF32x2 .p2 .p1 .f .c1, .fmaRnF32x2 .p3 .p2 .f .c0,
    .unpack64 .q0 .q1 .p3] ++ cuteTail
  io := [(.x0, .y0), (.x1, .y1)]
  consts := [(.cM, cutePair 0x4B400000), (.c2, cutePair 0x3E6906A4),
    (.c3, cutePair 0x3D9DF09D), (.c1, cutePair 0x3F31F519), (.c0, cutePair 0x3F800000)]
  defines := false

/-- CuTeDSL's software `exp2` of two `f32` lanes, read as the exact `2 ^ x`. -/
def cuteExp2 : SegTemplate CuteSlot where
  text := "of CuTeDSL's software exp2 of two f32 lanes (max.f32 with 0fC2FE0000, add.rm.f32x2 \
    with 0f4B400000, two sub.rn.f32x2, three fma.rn.f32x2 with 0f3D9DF09D, 0f3E6906A4, \
    0f3F31F519, 0f3F800000, and per lane shl.b32 by 23 and add.s32; 31 instructions defining \
    the constants or 21 reusing them), which computes approximately 2 ^ max(x, -127) with a \
    degree-3 polynomial, read as the exact 2 ^ x for each lane x (the clamp and the polynomial \
    error are approximations)"
  shapes := [cuteExp2Define, cuteExp2Reuse]
  fn := fun x => Real.rpow 2 x

end
end PTX.Assumption
