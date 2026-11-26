-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Lemmas.Flow.Arith32LineWord
import Kernels.TmlFa4Fwd.Proof.Loader.Export.Parity

@[expose] public section

/-! # The K/V slots' exact byte ranges

Row copy `c` of row `i` of packet `k` writes the 16 bytes of the lane's column (`rowCol`) of block
`(c, i)` of ring slot `k mod 3` (`cp_slot`): the blocks have 1024 bytes, the rows of the two copies
are 16384 bytes apart, and the swizzle permutes the columns of a 128-byte line. The Q stages end at
`sb + 68608` and the Bias stages begin at `sb + 166912`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat}

theorem tr32 (z : BitVec 64) : (truncBits 32 z).toNat = z.toNat % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))

/-- The column of 16 bytes lane index `t` writes in a block of 1024 bytes. -/
def rowCol (t : Nat) : Nat := 8 * (t / 8) + (t % 8 ^^^ t / 8)

theorem rowCol_inj : ∀ t < 64, ∀ t' < 64, rowCol t = rowCol t' → t = t' := by decide +kernel
theorem rowCol_lt : ∀ t < 64, rowCol t < 64 := by decide

/-- The word is the lane's unswizzled column of the block at `lo`. -/
def RowW (L : Launch) (g lo : Nat) (x : BitVec 64) : Prop :=
  x.toNat = lo + 16 * (g % L.block % 64)

/-- The word is the lane's swizzled column of the block at `lo`. -/
def ColW (L : Launch) (g lo : Nat) (x : BitVec 64) : Prop :=
  x.toNat = lo + 16 * rowCol (g % L.block % 64)

set_option maxRecDepth 100000 in
theorem row_words : ∀ i < 512, (andi (shl (BitVec.ofNat 64 i) 4) 1008).toNat = 16 * (i % 64) ∧
    (or32 (andi (shl (BitVec.ofNat 64 i) 4) 896)
      (shl (andi (shl (BitVec.ofNat 64 i) 3) 56) 1)).toNat = 16 * (i % 64) := by
  decide +kernel

theorem i32_toNat_lit (n : Nat) (hn : n < 2 ^ 31) : (i32 (n : Int)).toNat = n := by
  simp only [i32, tr32, BitVec.toNat_ofInt]; omega

/-- The shared base plus the lane's column. -/
theorem row_add (hp : Pre p L m) {y : BitVec 64} (hy : y.toNat = 16 * (g % L.block % 64)) :
    RowW L g L.sharedBase (add32 (Mma.sbW L) y) := by
  have hs := hp.shared
  have hsb : (Mma.sbW L).toNat = L.sharedBase := by
    simp only [Mma.sbW, BitVec.toNat_ofNat]; omega
  unfold RowW
  simp only [add32, r32, tr32, BitVec.toNat_add, hsb]
  have : y.toNat % 2 ^ 32 = y.toNat := by omega
  rw [this]; omega

theorem lane_lt (hp : Pre p L m) : g % L.block < 512 := by
  rw [hp.block]; exact Nat.mod_lt _ (by decide)

/-- **The row bases.** -/
theorem blk_rowBase (hp : Pre p L m) : RowW L g L.sharedBase (rowBase L g) :=
  row_add hp (row_words _ (lane_lt hp)).1

theorem blk_r1008 (hp : Pre p L m) :
    RowW L g L.sharedBase (add32 (Mma.sbW L) (andi (shl (tidW L g) 4) 1008)) :=
  row_add hp (row_words _ (lane_lt hp)).1

theorem blk_rowsAt (hp : Pre p L m) :
    RowW L g L.sharedBase (rowsAt L g (andi (shl (tidW L g) 3) 56)) :=
  row_add hp (row_words _ (lane_lt hp)).2

/-- **The swizzled row base plus `n`.** -/
theorem blk_swz (hp : Pre p L m) {b : BitVec 64} (hb : RowW L g L.sharedBase b) (n : Nat)
    (hn : n % 1024 = 0) (hn' : n ≤ 69632) : ColW L g (L.sharedBase + n) (swz (addi b n)) := by
  have hs := hp.shared
  have ht : g % L.block % 64 < 64 := Nat.mod_lt _ (by decide)
  unfold RowW at hb
  have hv : (addi b n).toNat = b.toNat + n := by
    simp only [addi, r32, tr32, BitVec.toNat_add, i32_toNat_lit n (by omega)]
    have : b.toNat % 2 ^ 32 = b.toNat := by omega
    rw [this]; omega
  have h := swz_val (x := addi b n) (n := (L.sharedBase + n) / 128 + g % L.block % 64 / 8)
    (c := g % L.block % 64 % 8) (by omega) (by omega) (by omega)
  have h8 : ((L.sharedBase + n) / 128 + g % L.block % 64 / 8) % 8 = g % L.block % 64 / 8 := by
    omega
  rw [h8] at h
  unfold ColW rowCol
  change (swz (addi b n)).toNat = _ at h
  omega

/-- A block moved by a slot's 32768 bytes. -/
theorem blk_slot (hp : Pre p L m) {lo : Nat} {y : BitVec 64} (hy : ColW L g lo y)
    (hlo : lo ≤ L.sharedBase + 69632)
    {s : Nat} (hs : s ≤ 2) : ColW L g (lo + 32768 * s) (add32 y (shl (BitVec.ofNat 64 s) 15)) := by
  have hsh := hp.shared
  have hc := rowCol_lt _ (Nat.mod_lt (g % L.block) (show 0 < 64 by decide))
  unfold ColW at hy ⊢
  have h15 : (i32 15).toNat = 15 := by simp only [i32, tr32, BitVec.toNat_ofInt]; norm_num
  have hsl : (shl (BitVec.ofNat 64 s) 15).toNat = 32768 * s := by
    simp only [shl, h15, show ¬ (15 ≥ 32) by norm_num, ite_false, tr32, BitVec.toNat_shiftLeft,
      r32, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have : s % 2 ^ 64 % 2 ^ 32 = s := by omega
    rw [this]; omega
  have hv : (add32 y (shl (BitVec.ofNat 64 s) 15)).toNat = y.toNat + 32768 * s := by
    simp only [add32, r32, tr32, BitVec.toNat_add, hsl]
    have : y.toNat % 2 ^ 32 = y.toNat := by omega
    rw [this]; omega
  omega

/-- The address of the 16 bytes of copy `c` of row `i` of a packet in slot `s`. -/
def cpAddr (L : Launch) (g s : Nat) (i : Fin 16) (c : Fin 2) : Nat :=
  L.sharedBase + 68608 + 32768 * s + 16384 * c.val + 1024 * i.val +
    16 * rowCol (g % L.block % 64)

/-- **A copy's address from a block of its slot.** -/
theorem slot_addr (hp : Pre p L m) {x : BitVec 64} (i : Fin 16) (c : Fin 2) {lo s₀ e s : Nat}
    (hx : ColW L g lo x) (hlo : lo = L.sharedBase + 68608 + 1024 * (i.val % 2) + 32768 * s₀)
    (hs : s₀ + e = s) (hs2 : s ≤ 2) :
    (smLoc L g x ((2048 * (i.val / 2) + 16384 * c.val + 32768 * e : Nat) : Int)).addr =
      cpAddr L g s i c := by
  have hsh := hp.shared
  have hcl := rowCol_lt _ (Nat.mod_lt (g % L.block) (show 0 < 64 by decide))
  subst hlo
  unfold ColW at hx
  have hi := i.isLt
  have hc := c.isLt
  have hv : (smLoc L g x ((2048 * (i.val / 2) + 16384 * c.val + 32768 * e : Nat) : Int)).addr =
      x.toNat + (2048 * (i.val / 2) + 16384 * c.val + 32768 * e) := by
    simp only [smLoc, tr32, BitVec.toNat_add, BitVec.toNat_ofInt]
    have : x.toNat % 2 ^ 32 = x.toNat := by omega
    rw [this]
    push_cast
    omega
  rw [hv, cpAddr]
  omega

set_option maxHeartbeats 8000000 in
/-- **A row copy of packet `k` writes its lane's column in ring slot `k mod 3`.** -/
theorem cp_slot (hp : Pre p L m) {per : Per} {b : Bool} {i : Fin 16} {c : Fin 2} {v : V}
    {kk : Fin 2} {k A : Nat} (hR : RefRing p L g w ⟨.cp per b i c, v, kk⟩ k A) :
    (smLoc L g (rv p L g w ⟨.cp per b i c, v, kk⟩ (cpDst (pk per b) i c).1)
      (cpDst (pk per b) i c).2).addr = cpAddr L g (pkOf per b k % 3) i c := by
  have hR2 := hR.2
  have hi2 : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  cases per <;> cases b <;> simp only [ringCls] at hR2 <;> rcases hi2 with h | h <;>
    simp only [cpDst, pk, h, pkOf, List.getD_cons_succ, List.getD_cons_zero, ite_true,
      ite_false, Nat.reduceEqDiff, Bool.false_eq_true]
  · exact slot_addr hp i c (s₀ := 0) (e := 0) (blk_swz hp (blk_rowBase hp) 68608 (by norm_num)
      (by norm_num)) (by omega) (by omega) (by omega)
  · exact slot_addr hp i c (s₀ := 0) (e := 0) (blk_swz hp (blk_rowBase hp) 69632 (by norm_num)
      (by norm_num)) (by omega) (by omega) (by omega)
  · exact slot_addr hp i c (s₀ := 0) (e := 1) (blk_swz hp (blk_rowBase hp) 68608 (by norm_num)
      (by norm_num)) (by omega) (by omega) (by omega)
  · exact slot_addr hp i c (s₀ := 0) (e := 1) (blk_swz hp (blk_rowBase hp) 69632 (by norm_num)
      (by norm_num)) (by omega) (by omega) (by omega)
  · have hx : ColW L g (L.sharedBase + 68608 + 32768 * (k % 3))
        (add32 (swz (addi (rowsAt L g (andi (shl (tidW L g) 3) 56)) 68608)) (shl v.slot 15)) := by
      rw [hR2.1.1.1]; exact blk_slot hp (blk_swz hp (blk_rowsAt hp) 68608 (by norm_num)
        (by norm_num)) (by omega) (by omega)
    exact slot_addr hp i c (s₀ := k % 3) (e := 0) hx (by omega) (by omega) (by omega)
  · have hx : ColW L g (L.sharedBase + 69632 + 32768 * (k % 3))
        (add32 (swz (addi (rowsAt L g (andi (shl (tidW L g) 3) 56)) 69632)) (shl v.slot 15)) := by
      rw [hR2.1.1.1]; exact blk_slot hp (blk_swz hp (blk_rowsAt hp) 69632 (by norm_num)
        (by norm_num)) (by omega) (by omega)
    exact slot_addr hp i c (s₀ := k % 3) (e := 0) hx (by omega) (by omega) (by omega)
  · have hx : ColW L g (L.sharedBase + 68608 + 32768 * ((k + 1) % 3))
        (add32 (swz (addi (add32 (Mma.sbW L) (andi (shl (tidW L g) 4) 1008)) 68608))
          (shl (nslot v.slot) 15)) := by
      rw [slotIs_nslot hR2.1.1]
      exact blk_slot hp (blk_swz hp (blk_r1008 hp) 68608 (by norm_num) (by norm_num))
        (by omega) (by omega)
    exact slot_addr hp i c (s₀ := (k + 1) % 3) (e := 0) hx (by omega) (by omega) (by omega)
  · have hx : ColW L g (L.sharedBase + 69632 + 32768 * ((k + 1) % 3))
        (add32 (swz (addi (add32 (Mma.sbW L) (andi (shl (tidW L g) 4) 1008)) 69632))
          (shl (nslot v.slot) 15)) := by
      rw [slotIs_nslot hR2.1.1]
      exact blk_slot hp (blk_swz hp (blk_r1008 hp) 69632 (by norm_num) (by norm_num))
        (by omega) (by omega)
    exact slot_addr hp i c (s₀ := (k + 1) % 3) (e := 0) hx (by omega) (by omega) (by omega)
  · have hx : ColW L g (L.sharedBase + 68608 + 32768 * (k % 3))
        (add32 (swz (addi (rowsAt L g (andi (shl (tidW L g) 3) 56)) 68608)) (shl v.slot 15)) := by
      rw [hR2.1.1]; exact blk_slot hp (blk_swz hp (blk_rowsAt hp) 68608 (by norm_num)
        (by norm_num)) (by omega) (by omega)
    exact slot_addr hp i c (s₀ := k % 3) (e := 0) hx (by omega) (by omega) (by omega)
  · have hx : ColW L g (L.sharedBase + 69632 + 32768 * (k % 3))
        (add32 (swz (addi (rowsAt L g (andi (shl (tidW L g) 3) 56)) 69632)) (shl v.slot 15)) := by
      rw [hR2.1.1]; exact blk_slot hp (blk_swz hp (blk_rowsAt hp) 69632 (by norm_num)
        (by norm_num)) (by omega) (by omega)
    exact slot_addr hp i c (s₀ := k % 3) (e := 0) hx (by omega) (by omega) (by omega)
  · have hx : ColW L g (L.sharedBase + 68608 + 32768 * ((k + 1) % 3))
        (add32 (swz (addi (rowsAt L g (andi (shl (tidW L g) 3) 56)) 68608))
          (shl (nslot v.slot) 15)) := by
      rw [slotIs_nslot hR2.1]
      exact blk_slot hp (blk_swz hp (blk_rowsAt hp) 68608 (by norm_num) (by norm_num))
        (by omega) (by omega)
    exact slot_addr hp i c (s₀ := (k + 1) % 3) (e := 0) hx (by omega) (by omega) (by omega)
  · have hx : ColW L g (L.sharedBase + 69632 + 32768 * ((k + 1) % 3))
        (add32 (swz (addi (rowsAt L g (andi (shl (tidW L g) 3) 56)) 69632))
          (shl (nslot v.slot) 15)) := by
      rw [slotIs_nslot hR2.1]
      exact blk_slot hp (blk_swz hp (blk_rowsAt hp) 69632 (by norm_num) (by norm_num))
        (by omega) (by omega)
    exact slot_addr hp i c (s₀ := (k + 1) % 3) (e := 0) hx (by omega) (by omega) (by omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
