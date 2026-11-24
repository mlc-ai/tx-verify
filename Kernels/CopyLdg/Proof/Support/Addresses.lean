-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Spec

@[expose] public section

/-! # `copy_ldg`: the global addresses of the kernel

Thread `g` reads `A[g]` and writes `B[g]`, four bytes each. These are address facts only:
which accesses cover which byte, and the bytes of one element of `x`. -/

namespace PTX.Kernels.CopyLdg.Proof
open PTX

/-- Thread `g`'s element of `A` and of `B`. -/
def gA (A g : Nat) : Loc := ⟨.global, 0, A + 4 * g⟩
def gB (B g : Nat) : Loc := ⟨.global, 0, B + 4 * g⟩

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0}

/-- An element of `A` and an element of `B` share no byte. -/
theorem covers_gA_gB (hpre : Pre L A B N x mem0) {g h : Nat} (hg : g < N) (hh : h < N) {l : Loc}
    (h1 : Acc.Covers { loc := gA A g, size := 4 } l)
    (h2 : Acc.Covers { loc := gB B h, size := 4 } l) : False := by
  have := hpre.disjoint
  simp only [Acc.Covers, Loc.InRange, gA, gB] at h1 h2
  omega

/-- Two elements of `B` that share a byte are the same element. -/
theorem covers_gB_gB {B g h : Nat} {l : Loc} (h1 : Acc.Covers { loc := gB B g, size := 4 } l)
    (h2 : Acc.Covers { loc := gB B h, size := 4 } l) : g = h := by
  simp only [Acc.Covers, Loc.InRange, gB] at h1 h2
  omega

end PTX.Kernels.CopyLdg.Proof
