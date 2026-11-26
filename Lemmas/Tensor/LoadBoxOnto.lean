-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.LoadBox
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # A 64-row 128-byte-swizzled box writes every byte of its `8192` bytes

A proof tool beside `writeLoc_b128_64` (the bytes written lie in the box's `128 R` bytes): for the
64-column, two-byte, 128-byte-swizzled box of 64 rows, every byte after the shared base is the
location of a slot (`writeLoc_b128_64_onto`). The swizzle keeps a 128-byte row in its row and is
an involution (`TensorSwizzle.offset_involutive`), so the slot of the byte at `u` is the one of
the unswizzled offset `offset u`. -/

namespace PTX.TensorCopy
open TensorDescriptor

/-- **Every byte of a 64-column, two-byte, 128-byte-swizzled box of 64 rows is written.** -/
theorem writeLoc_b128_64_onto {s : Spec}
    (h0 : TensorTile.count s.descriptor.box 0 = 64) (hR : TensorTile.rows s.descriptor.box = 64)
    (hf : s.descriptor.format.bytes = 2) (hsw : s.descriptor.swizzle = .b128) {l : Loc}
    (hsp : l.space = s.sharedBase.space) (hc : l.cta = s.sharedBase.cta)
    (hlo : s.sharedBase.addr ≤ l.addr) (hhi : l.addr < s.sharedBase.addr + 8192) :
    ∃ x y k, writeLoc s x y k = some l := by
  obtain ⟨u, hu⟩ : ∃ u, u = TensorSwizzle.offset .b128 s.sharedBase.addr
      (l.addr - s.sharedBase.addr) := ⟨_, rfl⟩
  have hrow := TensorSwizzle.offset_row .b128 s.sharedBase.addr (l.addr - s.sharedBase.addr)
  rw [← hu] at hrow
  have hinv : TensorSwizzle.offset .b128 s.sharedBase.addr u = l.addr - s.sharedBase.addr := by
    rw [hu, TensorSwizzle.offset_involutive]
  have hu8 : u < 8192 := by omega
  refine ⟨u % 128 / 2, u / 128, u % 2, ?_⟩
  unfold writeLoc TensorTransfer.slotAt
  rw [dite_eq_left (by omega), dite_eq_left (by omega), dite_eq_left (by omega),
    Option.map_some]
  congr 1
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, h0, hf, hsw, TensorTile.swizzleWidth]
  have hlin : u / 128 * max (64 * 2) 128 + u % 128 / 2 * 2 + u % 2 = u := by
    simp only [Nat.reduceMul, max_self]
    omega
  rw [hlin, hinv]
  cases l
  simp only [Loc.mk.injEq] at hinv hu hrow hsp hc hlo hhi ⊢
  refine ⟨hsp.symm, hc.symm, ?_⟩
  omega

end PTX.TensorCopy
