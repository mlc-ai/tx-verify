-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorMulticast
public import Lemmas.Tensor.BoxWrite

@[expose] public section

/-! # The shared destination of a tensor load

A proof tool. A tensor load's shared base is the effective address of its destination operand
(`tensorLoadCopy_dst`), and a box of 64 two-byte columns with 128-byte swizzle writes its `R`
rows into the `128 R` bytes after its shared base, in the base's CTA (`writeLoc_b128_64`). -/

namespace PTX.TensorCopy
open TensorDescriptor

/-- **The shared base of a tensor load** is its destination operand's effective address. -/
theorem tensorLoadCopy_dst {L : Launch} {g : Nat} {t : TState} {ca grp : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} {a : Nat}
    {s : TensorCopy.Spec} (h : tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s)) :
    sharedEffAddr L g t ca dst off = .ok s.sharedBase := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  rcases hm : tensorMap L g t map cs lm with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  cases hd : sharedEffAddr L g t ca dst off with
  | error f => rw [hd] at h; cases h
  | ok l =>
    rw [hd] at h
    simp only at h
    repeat' (split at h <;> (try (cases h; done)))
    all_goals (cases h; rfl)

/-- **A 64-column, two-byte, 128-byte-swizzled box of `R` rows writes into the `128 R` bytes
after its shared base.** -/
theorem writeLoc_b128_64 {s : Spec} {R x y k : Nat} {l : Loc}
    (h0 : TensorTile.count s.descriptor.box 0 = 64) (hR : TensorTile.rows s.descriptor.box = R)
    (hf : s.descriptor.format.bytes = 2) (hsw : s.descriptor.swizzle = .b128)
    (h : writeLoc s x y k = some l) :
    l.space = s.sharedBase.space ∧ l.cta = s.sharedBase.cta ∧ s.sharedBase.addr ≤ l.addr ∧
      l.addr < s.sharedBase.addr + 128 * R := by
  obtain ⟨hx, hy, hb⟩ := writeLoc_bounds h
  rw [h0] at hx
  rw [hR] at hy
  rw [hf] at hb
  unfold writeLoc TensorTransfer.slotAt at h
  rw [dite_eq_left (show x < TensorTile.count s.descriptor.box 0 by omega),
    dite_eq_left (show y < TensorTile.rows s.descriptor.box by omega),
    dite_eq_left (show k < s.descriptor.format.bytes by omega), Option.map_some] at h
  obtain rfl := (Option.some.inj h).symm
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, h0, hf, hsw, TensorTile.swizzleWidth]
  have hlt := box_offset_lt (base := s.sharedBase.addr) hx hy hb
  rw [show y * max (64 * 2) 128 + x * 2 + k = 128 * y + 2 * x + k by
    simp only [Nat.reduceMul, max_self]; ring]
  exact ⟨trivial, trivial, by omega, by omega⟩

end PTX.TensorCopy
