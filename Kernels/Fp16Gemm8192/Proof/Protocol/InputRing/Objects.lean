-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Rings

@[expose] public section

/-! # The input ring's objects

Four input slots. Slot `s` has one full barrier, in the cluster's leader CTA, on which the
leader's loader arrives (expecting the tile bytes) and both CTAs' tensor loads complete; and
one empty barrier in each CTA, on which the two MMA warps' commits arrive and that CTA's
loader polls. Block `b` of a loader trip uses slot `b % 4`; the first four blocks of a trip
poll with parity 1, the last four with parity 0. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.InputRing
open PTX

/-- Slot `s`'s full barrier, in the leader CTA `2 * cluster`. -/
def fullLoc (L : Launch) (cluster : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, 2 * cluster, L.sharedBase + 8 + 8 * s.val⟩

/-- Slot `s`'s empty barrier in CTA `cta`. -/
def emptyLoc (L : Launch) (cta : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, cta, L.sharedBase + 40 + 8 * s.val⟩

/-- The slot of block `b` of a trip. -/
def slotOf (b : Fin 8) : Fin 4 := ⟨b.val % 4, Nat.mod_lt _ (by decide)⟩

/-- The parity the loader polls block `b`'s empty barrier with. -/
def producerParity (b : Fin 8) : Nat := if b.val < 4 then 1 else 0


theorem fullLoc_bar (L : Launch) (c : Nat) (s : Fin 4) :
    fullLoc L c s = Bar.loc L (2 * c) ⟨.input, s.val, true⟩ := by
  simp only [fullLoc, Bar.loc, Bar.off, Nat.add_assoc]

theorem emptyLoc_bar (L : Launch) (cta : Nat) (s : Fin 4) :
    emptyLoc L cta s = Bar.loc L cta ⟨.input, s.val, false⟩ := by
  simp only [emptyLoc, Bar.loc, Bar.off, Nat.add_assoc]

end PTX.Kernels.Fp16Gemm8192.Proof.InputRing
