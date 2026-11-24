-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assembly.Correctness
public import Kernels.TmaCopy.Ptx
public import Kernels.TmaCopy.Data.Decoded

@[expose] public section

/-!
# `tma_copy` (tma_copy.ptx, hand-written, checked by ptxas for sm_100a)

The minimal use of the bulk-copy engine. Thread 0 initializes an mbarrier, issues a
16-byte `cp.async.bulk` from global `A` to shared `buf` that completes on it, polls
`mbarrier.try_wait` until the copy is visible, then copies the first word of `buf` to
global `B`. Every other thread exits.

Total correctness for every launch of one CTA, with no kernel assumptions: the copy's
write and the read of `buf` are ordered only through the mbarrier.
-/

namespace PTX.Kernels.TmaCopy
open PTX

/-- The kernel is the decoder's output for the PTX, stored in `Data/Decoded.lean`; `decode_eq`
checks that decoding the source gives exactly this value. -/
def kernel : Kernel := Decoded.kernel

theorem decode_eq : Decode.kernel Generated.TmaCopy.tma_copy = .ok kernel := by rfl

section
variable (L : Launch) (A B : Nat) (x : Value) (mem0 : Mem0)

/-- Launch and memory preconditions. `x` is the first word of `A`. -/
structure Pre : Prop where
  param0 : L.params "tma_copy_param_0" = some (BitVec.ofNat 64 A)
  param1 : L.params "tma_copy_param_1" = some (BitVec.ofNat 64 B)
  /-- One CTA, with thread 0. -/
  grid : L.grid = 1
  block : 0 < L.block ∧ L.block < 2 ^ 31
  /-- `buf` (16 bytes) and the mbarrier (8 bytes) are aligned and in the shared window. -/
  sharedAlign : L.sharedBase % 16 = 0
  sharedRange : L.sharedBase + 24 < 2 ^ 32
  alignA : A % 16 = 0
  rangeA : A + 16 < 2 ^ 64
  alignB : B % 4 = 0
  rangeB : B + 4 < 2 ^ 64
  /-- Nothing writes the copy's source. -/
  disjoint : A + 16 ≤ B ∨ B + 4 ≤ A
  /-- The first word of `A` is one stored 4-byte scalar. -/
  atom : x.bytes = 4 ∧ ∀ k < 4, x.byteAt k = (x, k)
  input : ∀ k < 4, mem0 ⟨.global, 0, A + k⟩ = some (some (x, k))
  /-- The rest of the copied range is allocated. -/
  inputAlloc : ∀ k < 16, mem0 ⟨.global, 0, A + k⟩ ≠ none
  /-- `B` and the shared variables are allocated. -/
  output : ∀ k < 4, mem0 ⟨.global, 0, B + k⟩ ≠ none
  shared : ∀ k < 24, mem0 ⟨.shared, 0, L.sharedBase + k⟩ ≠ none
  /-- The grid consists of whole clusters, as required by the launch model. -/
  oneDimLaunch : L.oneDimLaunch

/-- After the kernel, `B[0 .. 4)` holds the first word of `A`; every other global byte holds
its launch content. -/
def Post (m : FinalMem) : Prop :=
  ∀ l, l.space = .global →
    m l = if l.cta = 0 ∧ B ≤ l.addr ∧ l.addr < B + 4 then some (some (x, l.addr - B)) else mem0 l

end

end PTX.Kernels.TmaCopy
