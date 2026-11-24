-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmem

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax

/-- The two repeated softmax branches reduce the weights at different sites. -/
inductive Repeated : Type
  | biased
  | unbiased
  deriving DecidableEq

/-- The selected maximum and control registers that remain live beyond the repeated sum. -/
def roundContinuationRegs : List Nat := [7256, 7250, 7253, 7248, 7254, 7249]

namespace Repeated

/-- Each branch carries only the registers read by its continuation. -/
def continuationRegs : Repeated → List Nat
  | .biased => [7256, 7250, 7253, 7248, 7249]
  | .unbiased => [7256, 7253, 7254]

theorem continuationRegs_mem {r : Repeated} {n : Nat} (hn : n ∈ r.continuationRegs) :
    n ∈ roundContinuationRegs := by
  cases r <;>
    simp only [continuationRegs, roundContinuationRegs, List.mem_cons, List.not_mem_nil,
      or_false] at hn ⊢ <;> tauto

def alphaReg : Repeated → Nat
  | .biased => 1362
  | .unbiased => 1492

/-- In the biased branch the first 47 pairs retain their packed FP32 form. -/
def packedInputs : Repeated → List Nat
  | .biased => (List.range 32).map (9573 + ·) ++ (List.range 15).map (9541 + ·)
  | .unbiased => []

/-- The remaining FP32 values are unpacked. The unbiased branch interleaves four groups
of software exponent outputs among the hardware exponent results. -/
def scalarInputs : Repeated → List Nat
  | .biased =>
    [4905, 7252] ++ ((List.range 16).flatMap fun k => [4827 + 4 * k, 4828 + 4 * k])
  | .unbiased =>
    (List.range 44).map (1493 + ·) ++ (List.range 4).map (5128 + 3 * ·) ++
    (List.range 12).map (1537 + ·) ++ (List.range 4).map (5140 + 3 * ·) ++
    (List.range 12).map (1549 + ·) ++ (List.range 4).map (5152 + 3 * ·) ++
    (List.range 12).map (1561 + ·) ++ (List.range 4).map (5164 + 3 * ·) ++
    (List.range 32).map (1573 + ·)

/-- Registers that must reach the repeated denominator unchanged across the P tail and
correction acknowledgement. -/
def sumLive (r : Repeated) : List Nat :=
  r.scalarInputs ++ r.packedInputs ++ [r.alphaReg, 7257, 7258]

end Repeated

end PTX.Kernels.TmlFa4Fwd.Softmax
