-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assembly.Correctness
public import Kernels.RowSum.Ptx
public import Kernels.RowSum.Data.Decoded
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# `row_sum` (row_sum.ptx, nvcc 13.2, sm_100a)

```cuda
unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
if (row >= M) return;
float acc = 0.0f;
#pragma unroll 1
for (unsigned k = 0; k < K; ++k) acc += A[(unsigned long long)row * K + k];
B[row] = acc;
```

A real loop, compiled to a down-counting `%r8` and a moving pointer `%rd9`. Total
correctness for every `M`, `K` and launch, over the reals, under the explicit `idealAdd` numerical
profile.
-/

namespace PTX.Kernels.RowSum
open PTX

/-- The kernel is the decoder's output for the PTX, stored in `Data/Decoded.lean`; `decode_eq`
checks that decoding the source gives exactly this value. -/
def kernel : Kernel := Decoded.kernel

theorem decode_eq : Decode.kernel Generated.RowSum.row_sum = .ok kernel := by rfl

section
variable (L : Launch) (A B M K : Nat) (x : Nat → ℝ) (mem0 : Mem0)

/-- Partial sum of row `g` after `t` iterations. -/
noncomputable def S (g t : Nat) : ℝ := ∑ k ∈ Finset.range t, x (K * g + k)

structure Pre : Prop where
  param0 : L.params "row_sum_param_0" = some (BitVec.ofNat 64 A)
  param1 : L.params "row_sum_param_1" = some (BitVec.ofNat 64 B)
  param2 : L.params "row_sum_param_2" = some (BitVec.ofNat 64 M)
  param3 : L.params "row_sum_param_3" = some (BitVec.ofNat 64 K)
  m32 : M < 2 ^ 32
  k32 : K < 2 ^ 32
  threads32 : L.threads ≤ 2 ^ 32
  block32 : L.block < 2 ^ 32
  alignA : A % 4 = 0
  alignB : B % 4 = 0
  rangeA : A + 4 * (M * K) < 2 ^ 64
  rangeB : B + 4 * M < 2 ^ 64
  disjoint : A + 4 * (M * K) ≤ B ∨ B + 4 * M ≤ A
  /-- Row-major `M × K` input `x`, stored as `f32` at launch. -/
  input : ∀ j < M * K, ∀ k < 4,
    mem0 ⟨.global, 0, A + 4 * j + k⟩ = some (some (.float .f32 (x j), k))
  /-- `B` is allocated. -/
  output : ∀ a < 4 * M, mem0 ⟨.global, 0, B + a⟩ ≠ none
  /-- The grid consists of whole clusters, as required by the launch model. -/
  oneDimLaunch : L.oneDimLaunch

/-- After the kernel, `B[r]`, read as `f32` (`memFloat`: the bytes as `ld` rebuilds them,
read as an `f32` operand), is `Σ_{k<K} A[r][k]` (over the reals) for every row
`r < min M threads`; every other byte holds its launch content. -/
def Post (m : FinalMem) : Prop :=
  (∀ r < min M L.threads, memFloat .f32 m ⟨.global, 0, B + 4 * r⟩ = .ok (S K x r K)) ∧
  ∀ l, ¬ (l.space = .global ∧ l.cta = 0 ∧ B ≤ l.addr ∧ l.addr < B + 4 * min M L.threads) →
    m l = mem0 l

end

end PTX.Kernels.RowSum
