-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assembly.Correctness
public import Kernels.TcGemm.Ptx
public import Kernels.TcGemm.Data.Decoded

@[expose] public section

/-!
# `tc_gemm` (tc_gemm.ptx, hand-written, checked by ptxas for sm_100a and on a B200)

A naive int8 GEMM on one CTA of 128 threads: `D (128 x 8, s32) = A (128 x 32, s8) *
B (32 x 8, s8)`. Warp 0 allocates 32 Tensor Memory columns and lane 0 stores their address
in shared `tslot`; every thread reads it back after a barrier and keeps its low 16 bits
(the column; the lane field of an allocated address is 0). Thread 0 loads `A` and `B` into shared
memory with two bulk copies
(TMA) completing on `bar0`, waits for them, issues one `tcgen05.mma.kind::i8` and commits
it to `bar1`. Every thread waits on `bar1`, loads its row of `D` from Tensor Memory with
`tcgen05.ld` and stores it to global memory. After a barrier, warp 0 frees the Tensor
Memory.

`A` and `B` are stored in the K-major, unswizzled layout of 16-byte core matrices that the
kernel's descriptors describe (`offA`, `offB`).
-/

namespace PTX.Kernels.TcGemm
open TcMma (byteInt s32)
open PTX

/-- The decoded program of `tc_gemm.ptx`; `decode_eq` checks that the source decodes to it. -/
def kernel : Kernel := Decoded.kernel

theorem decode_eq : Decode.kernel Generated.TcGemm.tc_gemm = .ok kernel := by rfl

/-- Byte offset of `A[i][k]`: K-major, 8-row groups 256 bytes apart (SBO), the two 16-byte
halves of a row 128 bytes apart (LBO). -/
def offA (i k : Nat) : Nat := 16 * (i % 8) + 256 * (i / 8) + k % 16 + 128 * (k / 16)

/-- Byte offset of `B[k][j]`: column `j` of `B` is a K-major row of 32 bytes. -/
def offB (k j : Nat) : Nat := 16 * j + k % 16 + 128 * (k / 16)

/-- `D[i][j] = Σ_k A[i][k] B[k][j]`. -/
def dot (a b : Nat → Nat → Int) (i j : Nat) : Int :=
  ((List.range 32).map fun k => a i k * b k j).sum

section
variable (L : Launch) (A B D : Nat) (a b : Nat → Nat → Int) (mem0 : Mem0)

/-- Launch and memory preconditions. `a i k` and `b k j` are the signed 8-bit entries. -/
structure Pre : Prop where
  param0 : L.params "tc_gemm_param_0" = some (BitVec.ofNat 64 A)
  param1 : L.params "tc_gemm_param_1" = some (BitVec.ofNat 64 B)
  param2 : L.params "tc_gemm_param_2" = some (BitVec.ofNat 64 D)
  /-- One CTA of four warps. -/
  grid : L.grid = 1
  block : L.block = 128
  /-- The shared variables are aligned and lie in the 256 KB shared window (the
  descriptors encode 18-bit shared addresses). -/
  sharedAlign : L.sharedBase % 128 = 0
  sharedRange : L.sharedBase + 4372 ≤ 2 ^ 18
  alignA : A % 16 = 0
  alignB : B % 16 = 0
  alignD : D % 16 = 0
  rangeA : A + 4096 < 2 ^ 64
  rangeB : B + 256 < 2 ^ 64
  rangeD : D + 4096 < 2 ^ 64
  /-- `D` is disjoint from the copies' sources. -/
  disjointA : A + 4096 ≤ D ∨ D + 4096 ≤ A
  disjointB : B + 256 ≤ D ∨ D + 4096 ≤ B
  inputA : ∀ i < 128, ∀ k < 32, ∃ byte, mem0 ⟨.global, 0, A + offA i k⟩ = some (some byte) ∧
    byteInt true (some byte) = some (a i k)
  inputB : ∀ k < 32, ∀ j < 8, ∃ byte, mem0 ⟨.global, 0, B + offB k j⟩ = some (some byte) ∧
    byteInt true (some byte) = some (b k j)
  /-- `D` and the shared variables are allocated. -/
  output : ∀ k < 4096, mem0 ⟨.global, 0, D + k⟩ ≠ none
  shared : ∀ k < 4372, mem0 ⟨.shared, 0, L.sharedBase + k⟩ ≠ none
  /-- The grid consists of whole clusters, as required by the launch model. -/
  oneDimLaunch : L.oneDimLaunch

/-- After the kernel, row `i` of `D` (32 bytes from `D + 32 i`) holds the 32-bit integers
`dot a b i j`; every other global byte holds its launch content. -/
def Post (m : FinalMem) : Prop :=
  ∀ l, l.space = .global →
    m l = if l.cta = 0 ∧ D ≤ l.addr ∧ l.addr < D + 4096 then
      some (some (s32 (dot a b ((l.addr - D) / 32) ((l.addr - D) % 32 / 4)), (l.addr - D) % 4))
    else mem0 l

end

end PTX.Kernels.TcGemm
