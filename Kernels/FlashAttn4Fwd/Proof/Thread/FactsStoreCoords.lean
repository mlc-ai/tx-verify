-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderCoords
public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreBase
public import Kernels.FlashAttn4Fwd.Proof.Interface.Result

@[expose] public section

/-! # The store warp's coordinates

The output row register of item `i` (`Store.orowW`: the query block shifted by 9, `or` the CTA's
128-row half) holds `512 m + 128 r` for the item's query block `m` and the CTA's rank `r`, and its
second stage's (`or 256`) `256` more (`Store.orow_val`, `Store.orow256_val`): the bits are
disjoint. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- `or` with a multiple of `512` and a value below `512` is a sum. -/
theorem lor_512 (m y : Nat) (hy : y < 512) : 512 * m ||| y = 512 * m + y := by
  have := Nat.two_pow_add_eq_or_of_lt (i := 9) (b := y) (by norm_num; omega) m
  norm_num at this
  omega

theorem Store.orow_val (hpre : Pre P L mem0) {i : Nat} (hw : workOf L g i < 2 ^ 32)
    (hm : 512 * (coordsOf L (workOf L g i)).2.2 + 512 < 2 ^ 31) :
    Store.orowW L g i =
      BitVec.ofNat 64 (512 * (coordsOf L (workOf L g i)).2.2 + 128 * Work.rank L g) := by
  have hr : Work.rank L g < 2 := Nat.mod_lt _ (by decide)
  rw [Store.orowW, Work.Dm.mblkW_eq hpre hw]
  generalize (coordsOf L (workOf L g i)).2.2 = m at hm ⊢
  generalize Work.rank L g = r at hr ⊢
  simp only [Work.orW, Work.shlW, Work.rd, nf_trunc, nf_shl, nf_or, nf_toNat, nf_ofInt,
    nf_mod64_32, Nat.reducePow, Nat.reduceMod, Int.reduceMod, Int.reduceToNat, ge_iff_le,
    Nat.reduceLeDiff, ↓reduceIte]
  rw [nf_eq]
  have e1 : m % 4294967296 * 512 % 4294967296 % 4294967296 % 18446744073709551616 = 512 * m := by
    omega
  have e2 : r % 4294967296 * 128 % 4294967296 % 4294967296 % 18446744073709551616 = 128 * r := by
    omega
  rw [e1, e2, lor_512 m (128 * r) (by omega)]

theorem Store.orow256_val (hpre : Pre P L mem0) {i : Nat} (hw : workOf L g i < 2 ^ 32)
    (hm : 512 * (coordsOf L (workOf L g i)).2.2 + 512 < 2 ^ 31) :
    Work.orW (Store.orowW L g i) (BitVec.ofInt 64 256) =
      BitVec.ofNat 64 (512 * (coordsOf L (workOf L g i)).2.2 + 128 * Work.rank L g + 256) := by
  have hr : Work.rank L g < 2 := Nat.mod_lt _ (by decide)
  rw [Store.orow_val hpre hw hm]
  generalize (coordsOf L (workOf L g i)).2.2 = m at hm ⊢
  generalize Work.rank L g = r at hr ⊢
  simp only [Work.orW, Work.rd, nf_trunc, nf_or, nf_ofInt, nf_mod64_32, Nat.reducePow,
    Nat.reduceMod, Int.reduceMod, Int.reduceToNat]
  rw [nf_eq]
  have e1 : (512 * m + 128 * r) % 4294967296 % 18446744073709551616 = 512 * m + 128 * r := by
    omega
  rw [e1]
  have hor : 128 * r ||| 256 = 128 * r + 256 := by
    rw [Nat.or_comm]
    have := Nat.two_pow_add_eq_or_of_lt (i := 8) (b := 128 * r) (by norm_num; omega) 1
    norm_num at this
    omega
  have h2 : 512 * m + 128 * r ||| 256 = 512 * m + (128 * r ||| 256) := by
    rw [← lor_512 m (128 * r) (by omega), Nat.or_assoc, lor_512 m _ (by rw [hor]; omega)]
  rw [h2, hor]
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
