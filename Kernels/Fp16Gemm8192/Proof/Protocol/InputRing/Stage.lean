-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Objects
public import Kernels.Fp16Gemm8192.Proof.Support.TmaMma

@[expose] public section

/-! # The input ring's stages

Slot `s` of a CTA's input ring holds three 16 KiB tiles (`stageOff s j`): the A tile of MMA warp
`8 + j` (`j < 2`) and the B tile (`j = 2`). A tensor load of the slot writes one tile, element
`(x, y)` byte `byte` at `stageByte` (the 128-byte swizzle of the tile); MMA warp `8 + w % 2` reads
the A tile of its own warp and the B tile, K step `j` under `mmaSpec`, in both CTAs of the pair. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.InputRing
open PTX

/-- The offset from the shared base of tile `j` of slot `s`: the A tile of MMA warp `8 + j`
(`j < 2`) or the B tile (`j = 2`). -/
def stageOff (s j : Nat) : Nat := if j = 2 then 132096 + 16384 * s else 1024 + 16384 * j + 32768 * s

/-- Byte `byte` of element `(x, y)` of a 64 x 128 FP16 tile at shared address `st` of CTA `cta`,
under the 128-byte swizzle. -/
def stageByte (cta st x y byte : Nat) : Loc :=
  ⟨.shared, cta, st + TensorSwizzle.offset .b128 st (128 * y + 2 * x + byte)⟩

/-- The MMAs' instruction descriptor: a CTA pair, FP16 inputs with FP32 accumulation, 256 x 256. -/
def mmaDescriptor : TcMma.Descriptor :=
  ⟨.two, .f16 .f16 .f32, 256, 256, false, false, false, false, false⟩

/-- The operands of K step `j` of slot `s` of MMA warp `8 + w % 2` issued from CTA `cta`: its A
tile and the B tile, in both CTAs of the pair. -/
def mmaSpec (L : Launch) (cta w s j : Nat) : TcMma.OperandSpec :=
  ⟨mmaDescriptor, stepDescriptor (L.sharedBase + stageOff s (w % 2)) 0 j,
    stepDescriptor (L.sharedBase + stageOff s 2) 0 j, cta / 2 * 2, cta / 2 * 2 + 1, none, {}⟩

end PTX.Kernels.Fp16Gemm8192.Proof.InputRing
