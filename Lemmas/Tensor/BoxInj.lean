-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorMemory
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # A load writes each byte once, in every swizzle mode

A proof tool. A tensor box places slot `(x, y, byte)` at the swizzled offset of
`y * rowBytes + x * n + byte` (`n` the element bytes) and the swizzle is a bijection, so two slots
of a load at one location are one slot (`writeLoc_inj`), for every swizzle mode. -/

namespace PTX.TensorCopy
open TensorDescriptor

/-- The mixed-radix offset `y * R + x * n + k` names its digits when `x * n + k < R`. -/
private theorem digits_inj {R n x y k x' y' k' : Nat} (hxk : x * n + k < R) (hk : k < n)
    (hxk' : x' * n + k' < R) (hk' : k' < n) (h : y * R + x * n + k = y' * R + x' * n + k') :
    x = x' ∧ y = y' ∧ k = k' := by
  have hR : 0 < R := by omega
  have hn : 0 < n := by omega
  have e1 : (y * R + (x * n + k)) / R = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hxk]; simp
  have e2 : (y' * R + (x' * n + k')) / R = y' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hxk']; simp
  have m1 : (y * R + (x * n + k)) % R = x * n + k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hxk]
  have m2 : (y' * R + (x' * n + k')) % R = x' * n + k' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hxk']
  have h' : y * R + (x * n + k) = y' * R + (x' * n + k') := by omega
  have hy : y = y' := by rw [← e1, ← e2, h']
  have hr : x * n + k = x' * n + k' := by rw [← m1, ← m2, h']
  have d1 : (x * n + k) / n = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk]; simp
  have d2 : (x' * n + k') / n = x' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk']; simp
  have r1 : (x * n + k) % n = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have r2 : (x' * n + k') % n = k' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk']
  exact ⟨by rw [← d1, ← d2, hr], hy, by rw [← r1, ← r2, hr]⟩

/-- **A load writes a location from one slot**, whatever the swizzle mode. -/
theorem writeLoc_inj {s : Spec} {x y k x' y' k' : Nat} {l : Loc}
    (h : writeLoc s x y k = some l) (h' : writeLoc s x' y' k' = some l) :
    x = x' ∧ y = y' ∧ k = k' := by
  unfold writeLoc TensorTransfer.slotAt at h h'
  split_ifs at h h' with hx hy hb hx' hy' hb'
  · simp only [Option.map_some, Option.some.injEq] at h h'
    rw [← h'] at h
    simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte, Loc.mk.injEq,
      Nat.add_left_cancel_iff] at h
    have h2 := TensorSwizzle.offset_injective _ _ h.2.2
    have hR : ∀ {x k : Nat}, x < TensorTile.count s.descriptor.box 0 →
        k < s.descriptor.format.bytes →
        x * s.descriptor.format.bytes + k < TensorTile.rowBytes s.descriptor.box
          s.descriptor.format.bytes s.descriptor.swizzle := fun {x k} hx hk => by
      have := Nat.mul_le_mul_right s.descriptor.format.bytes (Nat.succ_le_of_lt hx)
      rw [Nat.succ_mul] at this
      have := Nat.le_max_left (TensorTile.count s.descriptor.box 0 * s.descriptor.format.bytes)
        (TensorTile.swizzleWidth s.descriptor.swizzle)
      unfold TensorTile.rowBytes
      omega
    exact digits_inj (hR hx hb) hb (hR hx' hb') hb' (by simpa [Nat.add_assoc] using h2)
  all_goals simp at h h'

end PTX.TensorCopy
