-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32Interval
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Where the loader warps' row copies write

A row copy (`cp`, `cp.async.cg.shared.global`) writes 16 bytes at its destination register plus
an offset of at most 63488. The destination register is a row base (the shared base plus at most
1008) plus 68608 or 69632, swizzled (at most 112 down), plus in a warm or steady round the ring
slot times 32768 (the slot is below 3 by `RefRing`, the next slot at most 3). So every row copy
writes at `sb + 68496` or above (`cp_lo`), by the interval closure with literal bounds. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat}

theorem iv_sb (hp : Pre p L m) : Iv L.sharedBase L.sharedBase (Mma.sbW L) := by
  have := hp.shared.2.1
  exact iv_lit _ (by omega)

/-- A row base: the shared base plus the lane's 16-byte column block. -/
theorem iv_rowBase (hp : Pre p L m) : Iv L.sharedBase (L.sharedBase + 1008) (rowBase L g) := by
  have hs := hp.shared.2.1
  have h := iv_add32 (iv_sb hp)
    (iv_andi (x := shl (BitVec.ofNat 64 (g % L.block)) 4) 1008 (by decide)) (by omega)
  exact iv_mono (by omega) (by omega) h

/-- The rows of a warm or steady round at column `c` (at most 56). -/
theorem iv_rowsAt (hp : Pre p L m) {c : BitVec 64} (hc : Iv 0 56 c) :
    Iv L.sharedBase (L.sharedBase + 1008) (rowsAt L g c) := by
  have hs := hp.shared.2.1
  have h1 := iv_r32 (iv_andi (x := shl (tidW L g) 4) 896 (by decide)) (by decide)
  have h2 := iv_r32 (iv_shl hc 1 (by decide) (by decide)) (by decide)
  have h := iv_add32 (iv_sb hp) (iv_or h1 h2) (by omega)
  exact iv_mono (by omega) (by omega) h

theorem iv_r87 : Iv 0 56 (andi (shl (tidW L g) 3) 56) := iv_andi 56 (by decide)

/-- A V packet's rows (`%r1008`). -/
theorem iv_r1008 (hp : Pre p L m) :
    Iv L.sharedBase (L.sharedBase + 1008) (add32 (Mma.sbW L) (andi (shl (tidW L g) 4) 1008)) := by
  have hs := hp.shared.2.1
  have h := iv_add32 (iv_sb hp) (iv_andi (x := shl (tidW L g) 4) 1008 (by decide)) (by omega)
  exact iv_mono (by omega) (by omega) h

/-- A ring slot below 3, and the next slot. -/
theorem iv_slot {v : V} {k : Nat} (h : SlotIs v k) : Iv 0 2 v.slot := by
  rw [h.1]; unfold Iv; simp only [BitVec.toNat_ofNat]; omega

theorem iv_nslot {s : BitVec 64} (h : Iv 0 2 s) : Iv 0 3 (nslot s) :=
  iv_sel (iv_mono le_rfl (by decide) (iv_i32 0 (by decide)))
    (iv_mono (by omega) le_rfl (iv_addi h 1 (by decide)))

/-- A swizzled row base plus `n`. -/
theorem iv_sw {b : BitVec 64} (hp : Pre p L m) (hb : Iv L.sharedBase (L.sharedBase + 1008) b)
    (n : Nat) (hn : 68608 ≤ n) (hn' : n ≤ 69632) :
    Iv (L.sharedBase + 68496) (L.sharedBase + 70752) (swz (addi b n)) := by
  have hs := hp.shared.2.1
  have h := iv_swz (iv_addi hb n (by omega)) (by omega)
  exact iv_mono (by omega) (by omega) h

/-- A swizzled row base plus a slot's 32768 bytes. -/
theorem iv_swsl {b s : BitVec 64} (hp : Pre p L m)
    (hb : Iv (L.sharedBase + 68496) (L.sharedBase + 70752) b) (hs : Iv 0 3 s) :
    Iv (L.sharedBase + 68496) (L.sharedBase + 169056) (add32 b (shl s 15)) := by
  have hsb := hp.shared.2.1
  have h := iv_add32 hb (iv_shl hs 15 (by decide) (by decide)) (by omega)
  exact iv_mono (by omega) (by omega) h

/-- The offset of a row copy. -/
theorem cpDst_off (k : Nat) (i : Fin 16) (c : Fin 2) :
    0 ≤ (cpDst k i c).2 ∧ (cpDst k i c).2.toNat ≤ 63488 := by
  simp only [cpDst]
  have hi := i.isLt
  have hc := c.isLt
  constructor
  · omega
  · split <;> omega

/-- The destination register of a row copy. -/
theorem cpDst_reg (k : Nat) (i : Fin 16) (c : Fin 2) :
    (cpDst k i c).1 = ([[1083, 1084], [1083, 1084], [2003, 2006], [2082, 2085], [2161, 2164],
      [2203, 2206]].getD k []).getD 0 0 ∨
    (cpDst k i c).1 = ([[1083, 1084], [1083, 1084], [2003, 2006], [2082, 2085], [2161, 2164],
      [2203, 2206]].getD k []).getD 1 0 := by
  simp only [cpDst]
  rcases Nat.mod_two_eq_zero_or_one i.val with h | h <;> rw [h] <;> simp

set_option maxHeartbeats 8000000 in
/-- **A row copy of the loader warps writes at `sb + 68496` or above.** -/
theorem cp_lo (hp : Pre p L m) {per : Per} {b : Bool} {i : Fin 16} {c : Fin 2} {v : V}
    {kk : Fin 2} {k A : Nat} (hR : RefRing p L g w ⟨.cp per b i c, v, kk⟩ k A) :
    L.sharedBase + 68496 ≤ (smLoc L g (rv p L g w ⟨.cp per b i c, v, kk⟩ (cpDst (pk per b) i c).1)
      (cpDst (pk per b) i c).2).addr ∧
    (smLoc L g (rv p L g w ⟨.cp per b i c, v, kk⟩ (cpDst (pk per b) i c).1)
      (cpDst (pk per b) i c).2).addr ≤ L.sharedBase + 232544 := by
  have hs := hp.shared.2.1
  obtain ⟨h0, h1⟩ := cpDst_off (pk per b) i c
  have key : ∀ x : BitVec 64, Iv (L.sharedBase + 68496) (L.sharedBase + 169056) x →
      L.sharedBase + 68496 ≤ (smLoc L g x (cpDst (pk per b) i c).2).addr ∧
      (smLoc L g x (cpDst (pk per b) i c).2).addr ≤ L.sharedBase + 232544 := fun x hx =>
    eff_le (s := 0) hx h0 (by omega) le_rfl (by omega)
  apply key
  have hR2 := hR.2
  cases per <;> cases b <;> simp only [ringCls] at hR2 <;>
    rcases cpDst_reg (pk _ _) i c with hr | hr <;> rw [hr] <;> simp only [pk, List.getD_cons_succ,
      List.getD_cons_zero]
  · exact iv_mono le_rfl (by omega) (iv_sw hp (iv_rowBase hp) 68608 le_rfl (by decide))
  · exact iv_mono le_rfl (by omega) (iv_sw hp (iv_rowBase hp) 69632 (by decide) le_rfl)
  · exact iv_mono le_rfl (by omega) (iv_sw hp (iv_rowBase hp) 68608 le_rfl (by decide))
  · exact iv_mono le_rfl (by omega) (iv_sw hp (iv_rowBase hp) 69632 (by decide) le_rfl)
  · exact iv_swsl hp (iv_sw hp (iv_rowsAt hp iv_r87) 68608 le_rfl (by decide))
      (iv_mono le_rfl (by decide) (iv_slot hR2.1.1))
  · exact iv_swsl hp (iv_sw hp (iv_rowsAt hp iv_r87) 69632 (by decide) le_rfl)
      (iv_mono le_rfl (by decide) (iv_slot hR2.1.1))
  · exact iv_swsl hp (iv_sw hp (iv_r1008 hp) 68608 le_rfl (by decide))
      (iv_nslot (iv_slot hR2.1.1))
  · exact iv_swsl hp (iv_sw hp (iv_r1008 hp) 69632 (by decide) le_rfl)
      (iv_nslot (iv_slot hR2.1.1))
  · exact iv_swsl hp (iv_sw hp (iv_rowsAt hp iv_r87) 68608 le_rfl (by decide))
      (iv_mono le_rfl (by decide) (iv_slot hR2.1))
  · exact iv_swsl hp (iv_sw hp (iv_rowsAt hp iv_r87) 69632 (by decide) le_rfl)
      (iv_mono le_rfl (by decide) (iv_slot hR2.1))
  · exact iv_swsl hp (iv_sw hp (iv_rowsAt hp iv_r87) 68608 le_rfl (by decide))
      (iv_nslot (iv_slot hR2.1))
  · exact iv_swsl hp (iv_sw hp (iv_rowsAt hp iv_r87) 69632 (by decide) le_rfl)
      (iv_nslot (iv_slot hR2.1))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
