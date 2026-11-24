-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaDescriptor

@[expose] public section

/-! # The two MMA instruction descriptors

All 24 `tcgen05.mma.ws.cta_group::1.kind::f16` instructions take their 32-bit instruction
descriptor from one of two registers, each written by one `mov.b32` immediate:
`%r401 = 69207184` for the 16 QK MMAs (PTX 3921 to 4190) and `%r422 = 71369872` for the 8 PV
MMAs. The values come from CuTe's `SM100_MMA_F16BF16_WS_{TS,SS}_NOELECT` atoms
(`config.h:174-181`). This file decodes both with Core's `TcMma.decode`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64

open PTX

/-- The QK descriptor: M 64, N 128 (two top-k blocks of 64), bf16 inputs, f32 accumulator,
A and B K-major. -/
def qkIdesc : Nat := 69207184

/-- The PV descriptor: M 64, N 256, bf16 inputs, f32 accumulator, B MN-major. -/
def pvIdesc : Nat := 71369872

theorem qkIdesc_decode :
    TcMma.decode .one true .f16 qkIdesc = some
      { group := .one, kind := .f16 .bf16 .f32, m := 64, n := 128, negateA := false,
        negateB := false, transposeA := false, transposeB := false, ws := true } := by
  decide

theorem pvIdesc_decode :
    TcMma.decode .one true .f16 pvIdesc = some
      { group := .one, kind := .f16 .bf16 .f32, m := 64, n := 256, negateA := false,
        negateB := false, transposeA := false, transposeB := true, ws := true } := by
  decide

/-- Both descriptors are supported dense MMAs. -/
theorem qkIdesc_valid : TcMma.Valid
    { group := .one, kind := .f16 .bf16 .f32, m := 64, n := 128, negateA := false,
      negateB := false, transposeA := false, transposeB := false, ws := true } := by
  decide

theorem pvIdesc_valid : TcMma.Valid
    { group := .one, kind := .f16 .bf16 .f32, m := 64, n := 256, negateA := false,
      negateB := false, transposeA := false, transposeB := true, ws := true } := by
  decide

end PTX.Kernels.FlashMlaSparseDecodeH64
