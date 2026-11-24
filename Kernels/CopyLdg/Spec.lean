-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assembly.Correctness
public import Kernels.CopyLdg.Ptx
public import Kernels.CopyLdg.Data.Decoded

@[expose] public section

/-!
# `copy_ldg` (copy_ldg.ptx, nvcc 13.2, sm_100a)

```cuda
unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
if (i < N) B[i] = __ldg(&A[i]);
```

Same specification as `copy_dynamic`, but the input is read with `ld.global.nc`, for which
the core has no rule. The theorem therefore holds under exactly one kernel assumption,
`ncInput`, which appears in its statement.
-/

namespace PTX.Kernels.CopyLdg
open PTX

/-- The kernel is the decoder's output for the PTX, stored in `Data/Decoded.lean`; `decode_eq`
checks that decoding the source gives exactly this value. -/
def kernel : Kernel := Decoded.kernel

theorem decode_eq : Decode.kernel Generated.CopyLdg.copy_ldg = .ok kernel := by rfl

section
variable (L : Launch) (A B N : Nat) (x : Nat → Value) (mem0 : Mem0)

/-- Launch and memory preconditions. `x j` is the value stored in `A[j]`. -/
structure Pre : Prop where
  param0 : L.params "copy_ldg_param_0" = some (BitVec.ofNat 64 A)
  param1 : L.params "copy_ldg_param_1" = some (BitVec.ofNat 64 B)
  param2 : L.params "copy_ldg_param_2" = some (BitVec.ofNat 64 N)
  n32 : N < 2 ^ 32
  threads32 : L.threads ≤ 2 ^ 32
  block32 : L.block < 2 ^ 32
  alignA : A % 4 = 0
  alignB : B % 4 = 0
  rangeA : A + 4 * N < 2 ^ 64
  rangeB : B + 4 * N < 2 ^ 64
  disjoint : A + 4 * N ≤ B ∨ B + 4 * N ≤ A
  /-- Each element is one stored 4-byte scalar, not a packed pair. -/
  atom : ∀ j < N, (x j).bytes = 4 ∧ ∀ k < 4, (x j).byteAt k = (x j, k)
  /-- `A` holds `x` at launch. -/
  input : ∀ j < N, ∀ k < 4, mem0 ⟨.global, 0, A + 4 * j + k⟩ = some (some (x j, k))
  /-- `B` is allocated. -/
  output : ∀ a < 4 * N, mem0 ⟨.global, 0, B + a⟩ ≠ none
  /-- The grid consists of whole clusters, as required by the launch model. -/
  oneDimLaunch : L.oneDimLaunch

/-- After the kernel, `B[0 .. min N threads)` holds `A`'s values; every other byte holds its
launch content. -/
def Post (m : FinalMem) : Prop :=
  ∀ l, m l = if l.space = .global ∧ l.cta = 0 ∧ B ≤ l.addr ∧ l.addr < B + 4 * min N L.threads
    then some (some (x ((l.addr - B) / 4), (l.addr - B) % 4)) else mem0 l

end

end PTX.Kernels.CopyLdg
