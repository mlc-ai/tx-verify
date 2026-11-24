-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assembly.Correctness
public import Kernels.BlockSum.Ptx
public import Kernels.BlockSum.Data.Decoded
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# `block_sum` (block_sum.ptx, nvcc 13.2, sm_100a)

```cuda
__shared__ float s[256];
unsigned t = threadIdx.x;
s[t] = A[blockIdx.x * 256 + t];
__syncthreads();
if (t == 0) {
  float acc = 0.0f;
#pragma unroll 1
  for (unsigned k = 0; k < 256; ++k) acc += s[k];
  B[blockIdx.x] = acc;
}
```

Shared memory and a CTA barrier. Thread 0 reads values that the other 255 threads
wrote; the barrier establishes the causal order from each shared write to the
reducer's reads. Without the barrier these conflicting accesses would be unordered.
-/

namespace PTX.Kernels.BlockSum
open PTX

/-- The kernel is the decoder's output for the PTX, stored in `Data/Decoded.lean`; `decode_eq`
checks that decoding the source gives exactly this value. -/
def kernel : Kernel := Decoded.kernel

theorem decode_eq : Decode.kernel Generated.BlockSum.block_sum = .ok kernel := by rfl

/-! ### Specification -/

/-- Shared memory location of CTA `c`. -/
def sh (c a : Nat) : Loc := ⟨.shared, c, a⟩
def gl (a : Nat) : Loc := ⟨.global, 0, a⟩

section
variable (L : Launch) (A B : Nat) (x : Nat → ℝ) (mem0 : Mem0)

def fl (v : ℝ) : Value := .float .f32 v
def b64 (n : Nat) : Value := .bits 64 (BitVec.ofNat 64 n)
def b32 (n : Nat) : Value := .bits 32 (BitVec.ofNat 64 n)

/-- Partial sum of CTA `c`'s inputs after `i` loop iterations. -/
noncomputable def S (c i : Nat) : ℝ := ∑ k ∈ Finset.range i, x (256 * c + k)

structure Pre : Prop where
  param0 : L.params "block_sum_param_0" = some (BitVec.ofNat 64 A)
  param1 : L.params "block_sum_param_1" = some (BitVec.ofNat 64 B)
  /-- The kernel hard-codes 256 threads per CTA. -/
  block : L.block = 256
  threads32 : L.threads ≤ 2 ^ 32
  alignA : A % 4 = 0
  alignB : B % 4 = 0
  rangeA : A + 4 * L.threads < 2 ^ 64
  rangeB : B + 4 * L.grid < 2 ^ 64
  disjoint : A + 4 * L.threads ≤ B ∨ B + 4 * L.grid ≤ A
  sharedAlign : L.sharedBase % 4 = 0
  sharedRange : L.sharedBase + 1024 < 2 ^ 32
  input : ∀ j < L.threads, ∀ k < 4, mem0 (gl (A + 4 * j + k)) = some (some (fl (x j), k))
  output : ∀ a < 4 * L.grid, mem0 (gl (B + a)) ≠ none
  /-- Each CTA's static shared memory is allocated, uninitialized, and untouched. -/
  shared : ∀ c < L.grid, ∀ a < 1024, mem0 (sh c (L.sharedBase + a)) = some none
  /-- The grid consists of whole clusters, as required by the launch model. -/
  oneDimLaunch : L.oneDimLaunch

def InA (l : Loc) : Prop := l.space = .global ∧ l.cta = 0 ∧ A ≤ l.addr ∧ l.addr < A + 4 * L.threads
def InB (l : Loc) : Prop := l.space = .global ∧ l.cta = 0 ∧ B ≤ l.addr ∧ l.addr < B + 4 * L.grid
def InS (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta < L.grid ∧ L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 1024

/-- On completion `B[c]`, read as `f32` (`memFloat`: the bytes as `ld` rebuilds them, read
as an `f32` operand), is the sum of CTA `c`'s 256 inputs; global bytes outside `B` hold what
they held at launch. -/
def Post (m : FinalMem) : Prop :=
  (∀ c < L.grid, memFloat .f32 m (gl (B + 4 * c)) = .ok (S x c 256)) ∧
  ∀ l, l.space = .global → ¬ (l.cta = 0 ∧ B ≤ l.addr ∧ l.addr < B + 4 * L.grid) → m l = mem0 l

end

end PTX.Kernels.BlockSum
