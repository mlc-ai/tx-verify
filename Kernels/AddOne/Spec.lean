-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assembly.Correctness
public import Kernels.AddOne.Ptx
public import Kernels.AddOne.Data.Decoded

@[expose] public section

/-!
# `add_one` (add_one.ptx, hand-written, checked by ptxas for sm_100a)

The smallest kernel with an in-place update. One CTA; thread `i` loads the 32-bit word
`A[i]`, adds 1 and stores the sum back to `A[i]`.

Total correctness for every launch of one CTA, with **no** kernel assumptions. Thread `i`
reads `A[i]` and later writes the same four bytes; no other thread touches them, so there is
nothing to synchronize.
-/

namespace PTX.Kernels.AddOne
open PTX

/-- The kernel is the decoder's output for the PTX, stored in `Data/Decoded.lean`; `decode_eq`
checks that decoding the source gives exactly this value. -/
def kernel : Kernel := Decoded.kernel

theorem decode_eq : Decode.kernel Generated.AddOne.add_one = .ok kernel := by rfl

/-- The 32-bit word `w` as a stored value. -/
def word (w : BitVec 32) : Value := .bits 32 (BitVec.ofNat 64 w.toNat)

section
variable (L : Launch) (A : Nat) (x : Nat → BitVec 32) (mem0 : Mem0)

/-- Launch and memory preconditions. `x i` is the word stored in `A[i]`. -/
structure Pre : Prop where
  param0 : L.params "add_one_param_0" = some (BitVec.ofNat 64 A)
  /-- One CTA. -/
  grid : L.grid = 1
  block32 : L.block ≤ 2 ^ 32
  alignA : A % 4 = 0
  rangeA : A + 4 * L.block < 2 ^ 64
  /-- `A` holds `x` at launch. -/
  input : ∀ i < L.block, ∀ k < 4, mem0 ⟨.global, 0, A + 4 * i + k⟩ = some (some (word (x i), k))
  /-- The grid consists of whole clusters, as required by the launch model. -/
  oneDimLaunch : L.oneDimLaunch

/-- After the kernel, `A[i]` holds `x i + 1` (modulo `2 ^ 32`) for every thread `i`; every
other byte holds its launch content. -/
def Post (m : FinalMem) : Prop :=
  ∀ l, m l = if l.space = .global ∧ l.cta = 0 ∧ A ≤ l.addr ∧ l.addr < A + 4 * L.block
    then some (some (word (x ((l.addr - A) / 4) + 1), (l.addr - A) % 4)) else mem0 l

end

end PTX.Kernels.AddOne
