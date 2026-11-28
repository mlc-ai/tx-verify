-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.NoUbSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ref
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexAddr
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Blocks

@[expose] public section

/-! # The index warp's pair loads are 8-byte aligned

-- domain: consistent

A pair load of the index warp reads at the word the machine's counters name (`ldAddr`): the lane's
first pair (`ixAddr0`, `ixAddr1`), or the next pair, 256 bytes (the main loop) or 4 words (the extra
loop) above. The word is 8-byte aligned: the arrays' bases are, the rows are of whole blocks of 64
words, and the lane's pair is 8 bytes in. The wrap of a sum modulo `2 ^ 64` (or `2 ^ 32`) keeps
the alignment. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The word of a register as the address a global access names. -/
theorem addr_toNat (x : BitVec 64) : (truncBits 64 x + BitVec.ofInt 64 0).toNat = x.toNat := by
  simp [truncBits, x.isLt]

/-- The extra loop is reached only for a positive `extra_topk`. -/
theorem extra_pos (hp : Pre P L m) {c : IxCtl} (h0 : c.l0 = lenWA P L (g / L.block))
    (h1 : c.l1 = lenWB P L (g / L.block)) (hlt : nMain c.l0 < roundsOf c.l0 c.l1) :
    0 < P.extra_topk := by
  obtain ⟨hwa, hwb, hr, hle, hle2⟩ := len_words hp (g / L.block)
  rw [rowOf_cta] at hwa hwb hr hle hle2
  have hM : nMain c.l0 = numOrigBlocks (P.topkLen (ctaidY L g)) := by
    rw [h0, hwa]; exact nMain_val (by have := hp.topkAdd63Lt; omega)
  have hR : roundsOf c.l0 c.l1 = totalBlocks (P.topkLen (ctaidY L g))
      (P.extraTopkLen (ctaidY L g)) := by
    rw [h0, h1, hwa, hwb]; exact rounds_val hr
  simp only [totalBlocks, numOrigBlocks, origPadded, ceilToMultiple, topkBlock] at hR hM
  omega

/-- **A pair load's address is 8-byte aligned.** -/
theorem ldAddr_m8 (hp : Pre P L m) {d : D} {i : Nat} (hct : Ctr P L g d.site d.c i)
    (hl : isLd d.site = true) (h0 : d.c.l0 = lenWA P L (g / L.block))
    (h1 : d.c.l1 = lenWB P L (g / L.block)) :
    (truncBits 64 (ldAddr P L g d) + BitVec.ofInt 64 0).toNat % 8 = 0 := by
  have hl2 := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  have hk := hp.topkDiv64
  have hib := hp.indicesBase
  have h2 : 2 ∣ P.topk := by omega
  have ha : ∀ X Y : Nat, (P.indicesBase + 4 * (X * P.topk + Y * (P.s_q * P.topk)) +
      8 * (tidOf L g % 32)) % 8 = 0 := fun X Y => by
    have e1 : 2 ∣ X * P.topk := h2.mul_left X
    have e2 : 2 ∣ Y * (P.s_q * P.topk) := (h2.mul_left P.s_q).mul_left Y
    omega
  rw [addr_toNat]
  obtain ⟨site, el, ac, c⟩ := d
  dsimp only [ldAddr] at hct hl h0 h1 ⊢
  have key : ∀ s : IxSite, isLd s = true → s = .pre ∨ s = .pf ∨ s = .xpre ∨ s = .xpf := by
    intro s h; cases s <;> simp [isLd] at h ⊢
  rcases key site hl with rfl | rfl | rfl | rfl
  · dsimp only [ldAddr]
    rw [ixAddr0_val hp g]
    simp only [W, BitVec.toNat_ofNat]
    have := ha (ctaidX L g) (ctaidY L g)
    omega
  · obtain ⟨⟨-, -, -, -, hap⟩, -⟩ := hct
    dsimp only [ldAddr]
    rw [hap, ixApB_val hp g, ixAddr0_val hp g]
    simp only [W, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := ha (ctaidX L g) (ctaidY L g)
    omega
  · obtain ⟨hlt, -, -⟩ := hct
    have hx := extra_pos hp h0 h1 hlt
    have hk2 := hp.extraDiv64
    have hib2 : P.extraIndicesBase % 8 = 0 := by
      rcases hp.extraIdxInput with h | ⟨h, -⟩
      · omega
      · exact h
    have h3 : 2 ∣ P.extra_topk := by omega
    dsimp only [ldAddr]
    rw [ixAddr1_val hp g hx]
    simp only [W, BitVec.toNat_ofNat]
    have e1 : 2 ∣ ctaidX L g * P.extra_topk := h3.mul_left _
    have e2 : 2 ∣ ctaidY L g * (P.s_q * P.extra_topk) := (h3.mul_left P.s_q).mul_left _
    omega
  · obtain ⟨⟨hlt, -, -, -, -, hxa⟩, -⟩ := hct
    have hx := extra_pos hp h0 h1 hlt
    have hk2 := hp.extraDiv64
    have hib2 : P.extraIndicesBase % 8 = 0 := by
      rcases hp.extraIdxInput with h | ⟨h, -⟩
      · omega
      · exact h
    have h3 : 2 ∣ P.extra_topk := by omega
    dsimp only [ldAddr]
    rw [hxa, ixXad_val hp g hx (Nat.mod_lt _ (by norm_num))]
    simp only [W, BitVec.toNat_ofNat, ixXa0_val hp g, BitVec.toNat_ofNat]
    have e1 : 2 ∣ ctaidX L g * P.extra_topk := h3.mul_left _
    have e2 : 2 ∣ ctaidY L g * (P.s_q * P.extra_topk) := (h3.mul_left P.s_q).mul_left _
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
