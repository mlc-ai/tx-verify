-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorMemory
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # An unswizzled load writes each byte once

A proof tool. A tensor box without swizzle places slot `(x, y, byte)` at
`base + y * (c * n) + x * n + byte` (`c` the columns, `n` the element bytes), so two slots of a
load at one location are one slot (`writeLoc_none_inj`). -/

namespace PTX.TensorCopy
open TensorDescriptor

/-- The mixed-radix offset `y * (c * n) + x * n + k` names its digits. -/
private theorem digits_inj {c n x y k x' y' k' : Nat} (hx : x < c) (hk : k < n) (hx' : x' < c)
    (hk' : k' < n) (h : y * (c * n) + x * n + k = y' * (c * n) + x' * n + k') :
    x = x' ∧ y = y' ∧ k = k' := by
  have hn : 0 < n := by omega
  have hA : ∀ {x k}, x < c → k < n → x * n + k < c * n := fun {x k} hx hk => by
    have := Nat.mul_le_mul_right n (show x + 1 ≤ c by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hcn : 0 < c * n := Nat.mul_pos (by omega) hn
  have hy : ∀ {x y k}, x < c → k < n → (y * (c * n) + x * n + k) / (c * n) = y ∧
      (y * (c * n) + x * n + k) % (c * n) = x * n + k := fun {x y k} hx hk => by
    rw [show y * (c * n) + x * n + k = x * n + k + c * n * y by rw [Nat.mul_comm]; omega,
      Nat.add_mul_div_left _ _ hcn, Nat.add_mul_mod_self_left, Nat.div_eq_of_lt (hA hx hk),
      Nat.mod_eq_of_lt (hA hx hk)]
    simp
  have hx2 : ∀ {x k}, k < n → (x * n + k) / n = x ∧ (x * n + k) % n = k := fun {x k} hk => by
    rw [show x * n + k = k + n * x by rw [Nat.mul_comm]; omega, Nat.add_mul_div_left _ _ hn,
      Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
    simp
  obtain ⟨h1, h2⟩ := hy (y := y) hx hk
  obtain ⟨h1', h2'⟩ := hy (y := y') hx' hk'
  rw [h] at h1 h2
  rw [h1'] at h1
  rw [h2'] at h2
  obtain ⟨h3, h4⟩ := hx2 (x := x) hk
  obtain ⟨h3', h4'⟩ := hx2 (x := x') hk'
  rw [← h2] at h3 h4
  exact ⟨h3.symm.trans h3', h1.symm, h4.symm.trans h4'⟩

/-- **An unswizzled load writes a location from one slot.** -/
theorem writeLoc_none_inj {s : Spec} {x y k x' y' k' : Nat} {l : Loc}
    (hsw : s.descriptor.swizzle = .none) (h : writeLoc s x y k = some l)
    (h' : writeLoc s x' y' k' = some l) : x = x' ∧ y = y' ∧ k = k' := by
  unfold writeLoc TensorTransfer.slotAt at h h'
  split_ifs at h h' with hx hy hb hx' hy' hb'
  · simp only [Option.map_some, Option.some.injEq] at h h'
    rw [← h'] at h
    simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
      TensorTile.rowBytes, hsw, TensorTile.swizzleWidth, TensorSwizzle.offset_none, Nat.max_zero,
      Loc.mk.injEq, Nat.add_left_cancel_iff] at h
    exact digits_inj hx hb hx' hb' (by simpa using h.symm)
  all_goals simp at h h'

end PTX.TensorCopy
