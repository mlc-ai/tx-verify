-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
import Kernels.TmlFa4Fwd.Proof.Lib.SWord
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

/-! # The MMA, softmax and correction warps agree on the tile's rounds

A tile of `B` K/V blocks has `B - 1` MMA loop rounds (`MmaRounds`), as many rescale rounds
(`CorrRounds`) and `B` softmax rounds (`SoftRounds`: the first, the biased ones after it and the
plain ones): the three compute one block word, and the softmax warps split the rounds after the
first at the diagonal (`soft_total`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g h : Nat}

/-! ### The softmax warps' rounds -/

/-- **The softmax rounds are the blocks** (one when there are none). -/
private theorem soft_total (v : Softmax.V) :
    1 + (Softmax.nB p L g v).toNat + (Softmax.nP p L g v).toNat =
      (S (Softmax.r166 p L g v)).toNat - 1 + 1 := by
  have c1 := S_ceil v.ukw
  have c2 := S_ceil (Softmax.r165 p L g v)
  have hB : S (Softmax.r166 p L g v) =
      min (S (Mma.ceil128 v.ukw)) (S (Mma.ceil128 (Softmax.r165 p L g v))) := S_min _ _
  generalize hy : addi (add32 (add32 (Softmax.r1808 p L g v) v.ukw)
    (sub32 v.sc.c0 v.sc.c1)) 128 = y
  have c3 := S_ceil y
  have hM : S (min32 (Mma.ceil128 v.ukw) (Mma.ceil128 y)) =
      min (S (Mma.ceil128 v.ukw)) (S (Mma.ceil128 y)) := S_min _ _
  have h168 : S (Softmax.r168 p L g v) =
      S (Softmax.r166 p L g v) - S (min32 (Mma.ceil128 v.ukw) (Mma.ceil128 y)) + 10 := by
    unfold Softmax.r168
    rw [hy]
    generalize min32 (Mma.ceil128 v.ukw) (Mma.ceil128 y) = M at hM ⊢
    generalize Softmax.r166 p L g v = B at hB ⊢
    have hs := S_sub (x := B) (y := M) (by omega) (by omega)
    rw [S_addi (by decide) (by omega) (by omega), hs]
  have h299 : S (Softmax.r299 p L g v) = max (S (Softmax.r166 p L g v) -
      min (S (Softmax.r168 p L g v)) (S (Softmax.r166 p L g v))) 0 := by
    unfold Softmax.r299
    generalize Softmax.r168 p L g v = D at h168 ⊢
    generalize Softmax.r166 p L g v = B at hB h168 ⊢
    have h0 : S (i32 0) = 0 := by decide
    show S (Softmax.max32 (sub32 B (min32 D B)) (i32 0)) = _
    have hm := S_min D B
    rw [S_max, h0, S_sub (by rw [hm]; omega) (by rw [hm]; omega), hm]
  have h169 : S (Softmax.r169 p L g v) = S (Softmax.r166 p L g v) - 1 := by
    unfold Softmax.r169
    generalize Softmax.r166 p L g v = B at hB ⊢
    rw [S_addi (by decide) (by omega) (by omega)]
    omega
  have hnB : Softmax.nB p L g v = S (Softmax.r166 p L g v) - 1 - S (Softmax.r299 p L g v) := by
    show S (sub32 (Softmax.r169 p L g v) (Softmax.r299 p L g v)) = _
    generalize Softmax.r169 p L g v = E at h169 ⊢
    generalize Softmax.r299 p L g v = F at h299 ⊢
    rw [S_sub (by omega) (by omega), h169]
  have hnP : Softmax.nP p L g v =
      min (S (Softmax.r166 p L g v) - 1) (S (Softmax.r299 p L g v)) := by
    show S (min32 (Softmax.r169 p L g v) (Softmax.r299 p L g v)) = _
    rw [S_min, h169]
  rw [hnB, hnP]
  generalize S (Softmax.r166 p L g v) = B at *
  generalize S (Softmax.r299 p L g v) = F at *
  clear hnB hnP
  omega

/-! ### The agreement -/

private theorem soft_blocks (R : Nat) (bal : BitVec 64) :
    Softmax.r166 p L g (softRef p L g R bal) = Mma.blocks p L g (mmaRef p L g R bal) := by
  simp only [Softmax.r166, Softmax.r165, Mma.blocks, sum_agree, Softmax.rowOff, Mma.coords,
    softRef, mmaRef, Mma.ukv]

private theorem sub_sub_agree (x a b : BitVec 64) :
    sub32 x (sub32 b a) = add32 x (sub32 a b) := by
  apply BitVec.eq_of_toNat_eq
  rw [sub32_toNat', add32_toNat', sub32_toNat', sub32_toNat']
  have h3 := Nat.mod_lt a.toNat (show 0 < 2 ^ 32 by norm_num)
  have h4 := Nat.mod_lt b.toNat (show 0 < 2 ^ 32 by norm_num)
  generalize x.toNat % 2 ^ 32 = x at *
  generalize a.toNat % 2 ^ 32 = a at *
  generalize b.toNat % 2 ^ 32 = b at *
  omega

private theorem corr_blocks (hp : Pre p L m) (hg : g < L.threads) (R : Nat) (bal : BitVec 64) :
    Correction.blocks p L g (corrRef p L g R bal) = Mma.blocks p L g (mmaRef p L g R bal) := by
  unfold Correction.blocks Mma.blocks Correction.rowOff
  rw [sub_sub_agree, sum_agree, row_agree]
  simp only [Correction.coords, Mma.coords, Correction.ctaR_eq hp hg, corrRef, mmaRef, Mma.ukv]

/-- **The softmax rounds are one more than the MMA loop rounds.** -/
theorem SoftRounds.mma {T R : Nat} (hc : h / L.block = g / L.block) (h1 : SoftRounds p L h T)
    (h2 : MmaRounds p L g R) : T = R + 1 := by
  have h2' : MmaRounds p L h R := h2.cta hc.symm
  obtain ⟨r, bal, hP, rfl⟩ := h1
  obtain ⟨r', bal', hP', rfl⟩ := h2'
  obtain ⟨rfl, rfl⟩ := hP.unique hP'
  rw [soft_total, soft_blocks]
  simp only [Mma.Bs, S]

/-- **The rescale rounds are the MMA loop rounds.** -/
theorem CorrRounds.mma (hp : Pre p L m) (hh : h < L.threads) {R : Nat}
    (h1 : CorrRounds p L h R) : MmaRounds p L h R := by
  obtain ⟨r, bal, hP, rfl⟩ := h1
  refine ⟨r, bal, hP, ?_⟩
  unfold Mma.Bs Correction.Bs
  rw [corr_blocks hp hh]

/-- **The softmax rounds are one more than the rescale rounds.** -/
theorem SoftRounds.corr (hp : Pre p L m) (hg : g < L.threads) {T R : Nat}
    (hc : h / L.block = g / L.block) (h1 : SoftRounds p L h T) (h2 : CorrRounds p L g R) :
    T = R + 1 :=
  h1.mma hc (h2.mma hp hg)

end
end PTX.Kernels.TmlFa4Fwd.Proof
