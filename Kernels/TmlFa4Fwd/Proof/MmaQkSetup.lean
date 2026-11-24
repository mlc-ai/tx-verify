-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkIssue
public import Kernels.TmlFa4Fwd.Flow.Code.Part033
public import Lemmas.Flow.Join

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

theorem packedLowHigh (lo : Nat) (hl : lo < 2 ^ 32) :
    let raw := lo + 2 ^ 32 * 0x40004040
    truncBits 32 (BitVec.ofNat 64 raw) = BitVec.ofNat 64 lo ∧
      truncBits 32 (BitVec.ofNat 64 ((BitVec.ofNat 64 raw).toNat / 2 ^ 32)) =
        BitVec.ofNat 64 0x40004040 := by
  let raw := lo + 2 ^ 32 * 0x40004040
  have hRaw : raw < 2 ^ 64 :=
    (Nat.add_lt_add_right hl _).trans_le (by norm_num)
  have hW : 0 < (2 : Nat)^32 := by decide
  have hNat : (BitVec.ofNat 64 raw).toNat = raw := toNat_ofNat_lt hRaw
  have hLow : raw % 2 ^ 32 = lo := by
    change (lo + 2 ^ 32 * 0x40004040) % 2 ^ 32 = lo
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have hHi : raw / 2 ^ 32 = 0x40004040 := by
    change (lo + 2 ^ 32 * 0x40004040) / 2 ^ 32 = 0x40004040
    rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hl, Nat.zero_add]
  change truncBits 32 (BitVec.ofNat 64 raw) = _ ∧
    truncBits 32 (BitVec.ofNat 64 ((BitVec.ofNat 64 raw).toNat / 2 ^ 32)) = _
  refine ⟨?_, ?_⟩
  · change BitVec.ofNat 64 ((BitVec.ofNat 64 raw).toNat % 2 ^ 32) = BitVec.ofNat 64 lo
    rw [hNat, hLow]
  · rw [hNat, hHi]
    rfl

private theorem packedWord {lo : Nat} (hl : lo < 2 ^ 32) :
    joinValue (b32 lo) (b32 0x40004040) = b64 (lo + 2 ^ 32 * 0x40004040) := by
  unfold b32 b64
  rw [Nat.mul_comm (2 ^ 32) 0x40004040]
  exact join_bits32 rfl rfl hl (by decide)

private theorem lowerWord (lo : Nat) (hl : lo < 2 ^ 32) (hBack : 2048 ≤ lo) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 lo) + truncBits 32 (BitVec.ofInt 64 (-2048))) =
      BitVec.ofNat 64 (lo - 2048) := by
  have hm : truncBits 32 (BitVec.ofInt 64 (-2048)) = BitVec.ofNat 64 (2^32 - 2048) := rfl
  rw [truncBits_ofNat hl (by decide), hm, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat]
  have hWide : lo + (2 ^ 32 - 2048) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hWide]
  have h : lo + (2 ^ 32 - 2048) = lo - 2048 + 2 ^ 32 := by omega
  rw [h, Nat.add_mod_right]
  have hLo : lo - 2048 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hLo]

private theorem upperWord {lo off : Nat} {imm : Int} (hImm : imm = (off : Int))
    (hl : lo + off < 2 ^ 32) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 lo) + truncBits 32 (BitVec.ofInt 64 imm)) =
      BitVec.ofNat 64 (lo + off) := by
  rw [hImm, BitVec.ofInt_natCast, truncBits_ofNat (by omega : lo < 2 ^ 32) (by decide),
    truncBits_ofNat (by omega : off < 2 ^ 32) (by decide), ← BitVec.ofNat_add,
    truncBits_ofNat hl (by decide)]

def qkFirstSetupPc (step : Fin 8) : Nat :=
  if step.val = 0 then 2157 else 2156 + 5 * step.val

def qkFirstSetupCount (step : Fin 8) : Nat := if step.val = 0 then 4 else 5

set_option maxRecDepth 100000 in
/-- The initial QK assembly retargets each Q descriptor from stage 1 to stage 0 and builds
the matching K fragment in the first ring slot. -/
theorem qkFirstSetupFragment (l : Launch) (g : Nat) (step : Fin 8) {loQ loK : Nat}
    (hQ : loQ < 2 ^ 32) (hBack : 2048 ≤ loQ) (hK : loK + 1030 < 2 ^ 32) :
    Seg kernel [] l g (qkFirstSetupCount step) (qkFirstSetupPc step)
      [(9624 + step.val, b64 (loQ + 2 ^ 32 * 0x40004040)), (9639, b32 loK),
        (9643, b32 0x40004040)]
      (qkFirstSetupPc step + qkFirstSetupCount step)
      [(9624 + step.val, b64 (loQ - 2048 + 2 ^ 32 * 0x40004040)),
        (9644 + step.val, b64 (loK + qkFragment step / 16 + 2 ^ 32 * 0x40004040))] := by
  obtain ⟨hLow, hHigh⟩ := packedLowHigh loQ hQ
  have hLower := lowerWord loQ hQ hBack
  have hQWord := packedWord (show loQ - 2048 < 2 ^ 32 by omega)
  have hK0 := packedWord (show loK < 2 ^ 32 by omega)
  have hOff2 := upperWord (lo := loK) (off := 2) (imm := 2) rfl (by omega)
  have hOff4 := upperWord (lo := loK) (off := 4) (imm := 4) rfl (by omega)
  have hOff6 := upperWord (lo := loK) (off := 6) (imm := 6) rfl (by omega)
  have hOff1024 := upperWord (lo := loK) (off := 1024) (imm := 1024) rfl (by omega)
  have hOff1026 := upperWord (lo := loK) (off := 1026) (imm := 1026) rfl (by omega)
  have hOff1028 := upperWord (lo := loK) (off := 1028) (imm := 1028) rfl (by omega)
  have hOff1030 := upperWord (lo := loK) (off := 1030) (imm := 1030) rfl (by omega)
  have hK2 := packedWord (show loK + 2 < 2 ^ 32 by omega)
  have hK4 := packedWord (show loK + 4 < 2 ^ 32 by omega)
  have hK6 := packedWord (show loK + 6 < 2 ^ 32 by omega)
  have hK1024 := packedWord (show loK + 1024 < 2 ^ 32 by omega)
  have hK1026 := packedWord (show loK + 1026 < 2 ^ 32 by omega)
  have hK1028 := packedWord (show loK + 1028 < 2 ^ 32 by omega)
  have hK1030 := packedWord (show loK + 1030 < 2 ^ 32 by omega)
  have hRetarget :
      joinValue (.bits 32 (truncBits 32
          (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (loQ + 2 ^ 32 * 0x40004040))) +
           truncBits 32 (BitVec.ofInt 64 (-2048)))))
        (.bits 32 (truncBits 32 (BitVec.ofNat 64
          ((BitVec.ofNat 64 (loQ + 2 ^ 32 * 0x40004040)).toNat / 2 ^ 32)))) =
      b64 (loQ - 2048 + 2 ^ 32 * 0x40004040) := by
    rw [hLow, hLower, hHigh]
    exact hQWord
  fin_cases step <;> intro t ht <;>
    seg_fp ht using
      first
      | (simp only [Nat.reduceDiv]; apply hRetarget)
      | simp only [qkFragment, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
          Nat.add_zero]
        first
        | exact hK0
        | (rw [hOff2]; exact hK2)
        | (rw [hOff4]; exact hK4)
        | (rw [hOff6]; exact hK6)
        | (rw [hOff1024]; exact hK1024)
        | (rw [hOff1026]; exact hK1026)
        | (rw [hOff1028]; exact hK1028)
        | (rw [hOff1030]; exact hK1030)

/-- The first setup instruction of each actual QK fragment. -/
def qkSetupPc (block : Fin 4) (step : Fin 8) : Nat :=
  qkPc block - 40 + if step.val = 0 then 0 else 5 * step.val - 1

def qkRetargetLow (block : Fin 4) (lo : Nat) : Nat :=
  if block.val % 2 = 0 then lo - 2048 else lo + 2048

def qkRetargetOffset (block : Fin 4) : Int :=
  if block.val % 2 = 0 then -2048 else 2048

theorem retargetPacked (block : Fin 4) {lo : Nat} (hQ : lo < 2 ^ 32)
    (hBack : 2048 ≤ lo) (hNext : lo + 2048 < 2 ^ 32) :
    joinValue (.bits 32 (truncBits 32
        (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (lo + 2 ^ 32 * 0x40004040))) +
         truncBits 32 (BitVec.ofInt 64 (qkRetargetOffset block)))))
      (.bits 32 (truncBits 32 (BitVec.ofNat 64
        ((BitVec.ofNat 64 (lo + 2 ^ 32 * 0x40004040)).toNat / 2 ^ 32)))) =
    b64 (qkRetargetLow block lo + 2 ^ 32 * 0x40004040) := by
  obtain ⟨hLow, hHigh⟩ := packedLowHigh lo hQ
  rw [hLow, hHigh]
  by_cases h : block.val % 2 = 0
  · rw [qkRetargetOffset, qkRetargetLow, ite_eq_left h, ite_eq_left h, lowerWord lo hQ hBack]
    exact packedWord (by omega)
  · rw [qkRetargetOffset, qkRetargetLow, ite_eq_right h, ite_eq_right h]
    rw [upperWord (lo := lo) (off := 2048) (imm := 2048) rfl hNext]
    exact packedWord hNext

/-- Operands and results of one fragment's local setup for any of the four QK copies. -/
def qkSetupSpec (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) (loQ loK : Nat) : Prop :=
  Seg kernel [] l g (qkFirstSetupCount step) (qkSetupPc block step)
    [(9624 + step.val, b64 (loQ + 2 ^ 32 * 0x40004040)), (qkBReg block - 5, b32 loK),
      (qkBReg block - 1, b32 0x40004040)]
    (qkSetupPc block step + qkFirstSetupCount step)
    [(9624 + step.val, b64 (qkRetargetLow block loQ + 2 ^ 32 * 0x40004040)),
      (qkBReg block + step.val, b64 (loK + qkFragment step / 16 + 2 ^ 32 * 0x40004040))]

local macro "qk_setup_steps" block:term " using " step:term ", " loQ:ident ", " loK:ident ", "
    hQ:ident ", " hBack:ident ", " hNext:ident ", " hK:ident : tactic =>
  `(tactic| (
    unfold qkSetupSpec
    have hRetarget := retargetPacked $block (lo := $loQ) $hQ $hBack $hNext
    have hK0 := packedWord (Nat.lt_of_le_of_lt (Nat.le_add_right $loK 1030) $hK)
    have hOff2 := upperWord (lo := $loK) (off := 2) (imm := 2) rfl (by omega)
    have hOff4 := upperWord (lo := $loK) (off := 4) (imm := 4) rfl (by omega)
    have hOff6 := upperWord (lo := $loK) (off := 6) (imm := 6) rfl (by omega)
    have hOff1024 := upperWord (lo := $loK) (off := 1024) (imm := 1024) rfl (by omega)
    have hOff1026 := upperWord (lo := $loK) (off := 1026) (imm := 1026) rfl (by omega)
    have hOff1028 := upperWord (lo := $loK) (off := 1028) (imm := 1028) rfl (by omega)
    have hOff1030 := upperWord (lo := $loK) (off := 1030) (imm := 1030) rfl (by omega)
    have hK2 := packedWord (show $loK + 2 < 2 ^ 32 by omega)
    have hK4 := packedWord (show $loK + 4 < 2 ^ 32 by omega)
    have hK6 := packedWord (show $loK + 6 < 2 ^ 32 by omega)
    have hK1024 := packedWord (show $loK + 1024 < 2 ^ 32 by omega)
    have hK1026 := packedWord (show $loK + 1026 < 2 ^ 32 by omega)
    have hK1028 := packedWord (show $loK + 1028 < 2 ^ 32 by omega)
    have hK1030 := packedWord (show $loK + 1030 < 2 ^ 32 by omega)
    fin_cases $step:term <;> intro t ht <;>
      simp only [qkRetargetOffset, qkRetargetLow] at hRetarget ⊢ <;>
      seg_fp ht using
        first
        | (simp only [Nat.reduceDiv]; apply hRetarget)
        | simp only [qkFragment, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
            Nat.add_zero]
          first
          | exact hK0
          | (rw [hOff2]; exact hK2)
          | (rw [hOff4]; exact hK4)
          | (rw [hOff6]; exact hK6)
          | (rw [hOff1024]; exact hK1024)
          | (rw [hOff1026]; exact hK1026)
          | (rw [hOff1028]; exact hK1028)
          | (rw [hOff1030]; exact hK1030)))

set_option maxRecDepth 100000 in
private theorem qkSecondSetupFragment (l : Launch) (g : Nat) (step : Fin 8) {loQ loK : Nat}
    (hQ : loQ < 2 ^ 32) (hBack : 2048 ≤ loQ) (hNext : loQ + 2048 < 2 ^ 32)
    (hK : loK + 1030 < 2 ^ 32) : qkSetupSpec l g 1 step loQ loK := by
  qk_setup_steps (1 : Fin 4) using step, loQ, loK, hQ, hBack, hNext, hK

set_option maxRecDepth 100000 in
private theorem qkThirdSetupFragment (l : Launch) (g : Nat) (step : Fin 8) {loQ loK : Nat}
    (hQ : loQ < 2 ^ 32) (hBack : 2048 ≤ loQ) (hNext : loQ + 2048 < 2 ^ 32)
    (hK : loK + 1030 < 2 ^ 32) : qkSetupSpec l g 2 step loQ loK := by
  qk_setup_steps (2 : Fin 4) using step, loQ, loK, hQ, hBack, hNext, hK

set_option maxRecDepth 100000 in
private theorem qkFourthSetupFragment (l : Launch) (g : Nat) (step : Fin 8) {loQ loK : Nat}
    (hQ : loQ < 2 ^ 32) (hBack : 2048 ≤ loQ) (hNext : loQ + 2048 < 2 ^ 32)
    (hK : loK + 1030 < 2 ^ 32) : qkSetupSpec l g 3 step loQ loK := by
  qk_setup_steps (3 : Fin 4) using step, loQ, loK, hQ, hBack, hNext, hK

/-- The four decoded fragment setups alternate Q banks and build the corresponding K descriptor. -/
theorem qkSetupFragment (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) {loQ loK : Nat}
    (hQ : loQ < 2 ^ 32) (hBack : 2048 ≤ loQ) (hNext : loQ + 2048 < 2 ^ 32)
    (hK : loK + 1030 < 2 ^ 32) : qkSetupSpec l g block step loQ loK := by
  fin_cases block
  · change qkSetupSpec l g 0 step loQ loK
    have hPc : qkSetupPc 0 step = qkFirstSetupPc step := by fin_cases step <;> rfl
    have hQWord : qkRetargetLow 0 loQ = loQ - 2048 := rfl
    simpa only [qkSetupSpec, hPc, qkBReg, hQWord, Nat.reduceSub] using
      qkFirstSetupFragment l g step hQ hBack hK
  · exact qkSecondSetupFragment l g step hQ hBack hNext hK
  · exact qkThirdSetupFragment l g step hQ hBack hNext hK
  · exact qkFourthSetupFragment l g step hQ hBack hNext hK

end PTX.Kernels.TmlFa4Fwd.Mma
