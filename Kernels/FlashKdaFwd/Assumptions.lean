-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Assumptions.SharedBits
public import Kernels.FlashKdaFwd.Assumptions.InputReadOnly
public import Assumption.IdealReal
public import Assumption.ApproxExact
public import Core.Sync.Elect

@[expose] public section

/-!
# The assumptions of the FlashKDA packed FP32 recurrence kernel

Each assumption is built from a constructor in `Assumption/` where one fits, and otherwise from
a kernel-local `Assumption` whose hook is narrowed to one instruction form.

The theorem is a statement over the reals: the floating computation is read as exact real
arithmetic (`idealArith`, `approx`, `narrow`). `sharedBits` gives the swizzled address
arithmetic on generic shared pointers its meaning. `electZero` records the choice of leader
that the CUTLASS pipeline's debug check requires (see the README: the frozen build keeps the
`brkpt` of the lane-0 check in the load producer, which CUTLASS compiles unless `NDEBUG` is
defined). `inputReadOnly`
(`Assumptions/InputReadOnly.lean`) says that the loads of the packed-offsets array `cu_seqlens`
return the launch content, and makes any write of that array undefined.
-/

namespace PTX.Kernels.FlashKdaFwd.Assumptions
open PTX PTX.Assumption

noncomputable section

/-- The scalar FP32 arithmetic of the recurrence (the update `(v - k·S) * beta`, the gate
`1 / (1 + 2^(c x))`, the state update `fma (S, g, k_r·u)`) and the warp-level matrix products
over BF16 operands with an FP32 accumulator are exact real operations. -/
def idealArith : Assumption :=
  idealReal "flash-kda-ideal-arith"
    { float := [.add .f32, .mul .f32, .subRn .f32, .fma .f32],
      warpMma := [⟨.float .bf16, .float .bf16, .float .f32, .float .f32, none⟩] }
    "The kernel computes the projections k·S and q·S, the solve INV·u, the output correction \
    Mqk·u and the state update with mma.sync m16n8k16 over bf16 operands and an f32 \
    accumulator, and the element updates with mul/sub/add.ftz.f32 and fma.rn.ftz.f32; PTX rounds \
    these while the theorem states the exact real recurrence."

/-- `ex2.approx.ftz.f32` and `rcp.approx.ftz.f32` of the update gate are the exact `2 ^ x` and
`1 / x`. -/
def approx : Assumption :=
  approxExact "flash-kda-approx-ex2-rcp" [.ex2 .f32, .rcp .f32]
    "The update gate 1 / (1 + 2^(c x)) is computed with ex2.approx.ftz.f32 and \
    rcp.approx.ftz.f32; the theorem states the exact gate, so these are read as the exact 2^x \
    and 1/x, ignoring their ulp error and the flush of subnormal results to zero."

/-- The destination and source of a plain `cvt.rn.bf16.f32 d, a`. -/
def narrowOperands : Op → Option (Nat × Opnd)
  | .cvt c =>
    match c.dst, c.src, c.rnd, c.srcs with
    | .float .bf16, .float .f32, some .rn, [a@(.reg _)] =>
      if c.plain && c.ext == .same then some (c.d, a) else none
    | _, _, _, _ => none
  | _ => none

/-- The FP32 to BF16 conversions (the BF16 state copy, the update vector and the outputs) keep
the real value of a finite operand. -/
def narrow : Assumption where
  name := "flash-kda-bf16-narrow"
  statement := "cvt.rn.bf16.f32 of a finite FP32 value stores its real value without BF16 \
    rounding or overflow. The kernel narrows the FP32 state to the BF16 operand copy of the \
    tensor-core products, the update vector u and the outputs; the theorem states the exact \
    real recurrence. Infinite and NaN operands use Core's conversion rule."
  localRule _ _ t op := do
    let (d, a) ← narrowOperands op
    bindRead (readFinite t .f32 a) fun x => some (pure (next (setReg t d (.float .bf16 x))))

/-- Every election over the full warp returns lane zero. -/
def LeaderZero (X : Execution) : Prop :=
  ∀ e pc inst leader, X.Elect e pc 0xffffffff inst leader → leader = 0

/-- `elect.sync` over the full member mask elects lane zero. -/
def electZero : Assumption where
  name := "flash-kda-elect-lane-zero"
  statement := "An elect.sync whose member mask names all 32 lanes of a warp elects lane 0. \
    PTX ISA 9.7.15.15 fixes one leader per member mask and leaves its identity open. The \
    CUTLASS load pipeline checks that the elected producer is lane 0 \
    (sm90_pipeline.hpp, producer_acquire) and the build keeps the breakpoint behind that check, \
    so with another leader the kernel would stop at it. A standalone election test on two \
    GB300 GPUs elected lane 0 in all 3,072 warps of each device."
  wf _ _ X := LeaderZero X

/-- All assumptions of the kernel's theorems. -/
def all : List Assumption :=
  [idealArith, approx, narrow, sharedBits, electZero, inputReadOnly]

end
end PTX.Kernels.FlashKdaFwd.Assumptions
