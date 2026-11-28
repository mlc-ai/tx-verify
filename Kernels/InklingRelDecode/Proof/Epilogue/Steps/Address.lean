-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Base
import Kernels.InklingRelDecode.Gen.StepEpilogue03
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Flow.SegPieces
import Lemmas.Flow.SignedBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Value}
local notation "F" => facts e L g v

private theorem token_small (t : Nat) : token t < 11 := by
  unfold token row; omega

private theorem mad_lo (a b c : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) *
      truncBits 32 (BitVec.ofNat 64 b) + truncBits 32 (BitVec.ofNat 64 c))) = u32 (a*b+c) := by
  change _ = Value.bits 32 _
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h64 : ∀ x : Nat, x % 2^64 % 2^32 = x % 2^32 := fun x => Nat.mod_mod_of_dvd _ (by norm_num)
  have hx := Nat.mod_lt a (show 0 < 2^32 by norm_num)
  have hy := Nat.mod_lt b (show 0 < 2^32 by norm_num)
  have hxy : a % 2^32 * (b % 2^32) < 2^64 := by
    calc a % 2^32 * (b % 2^32) < 2^32 * 2^32 := Nat.mul_lt_mul'' hx hy
      _ = 2^64 := by norm_num
  have hc := Nat.mod_lt c (show 0 < 2^32 by norm_num)
  have h32 : ∀ x : Nat, x % 2^32 % 2^64 = x % 2^32 := fun x =>
    Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul, h64, h32,
    Nat.mod_eq_of_lt hxy]
  have h := Nat.mul_mod a b (2^32)
  omega

theorem addr_2674 :
    Seg kernel Assumptions.all L g 1 2674 (F 2674) 2675 (F 2675) := by
  intro t ht
  seg_fp ht using
    rw [mad_lo]
    simp only [valueOf,scalarValue,u32,Nat.reduceEqDiff,↓reduceIte]

theorem addr_2675 :
    SegU kernel Assumptions.all L g 2675 (F 2675) 2676 (F 2676) := by
  have ok : e.firstWord.regBits.isSome ∧ e.tokens * e.split + 11 < 2^31 := e.addr.good
  have small : e.tokens * e.split + token (g % L.block) < 2^31 := by
    have := token_small (g % L.block)
    have := ok.2
    omega
  apply Lib.sum_span (dst := 1897) (r := 610) (δ := e.tokens * e.split + token (g % L.block))
    (op := .reg 1896) true small Flow.code_2675 (by decide) (by decide)
  · change u32 (e.firstToken + _) = Lib.addBase e.firstWord _
    have bits := ok.1
    clear ok
    unfold Entry.firstToken
    cases h : e.firstWord <;> simp_all [Lib.addBase,u32]
    change false = true at bits
    contradiction
  · intro t ht
    have := Lib.delta_reg (L := L) (g := g) ht (by decide : 1896 ∈ ctlLive 2675)
      (δ := e.tokens * e.split + token (g % L.block)) (by
        change b32 _ = _
        rw [Nat.mod_eq_of_lt (by omega)]) (by omega)
    exact this
  · decide +kernel


private theorem tile_word (e : Entry) (t : Nat) :
    u32 (((e.firstToken + (e.tokens * e.split + token t)) % 2^32) * 12 +
      (e.head + headInGroup t) % 2^32) = b32 (e.tile t) := by
  unfold u32 Entry.tile
  congr 1
  omega

theorem addr_2676 :
    Seg kernel Assumptions.all L g 1 2676 (F 2676) 2677 (F 2677) := by
  intro t ht
  seg_fp ht using
    rw [show BitVec.ofInt 64 12 = BitVec.ofNat 64 12 from rfl, mad_lo]
    exact tile_word e _

theorem addr_2677 :
    Seg kernel Assumptions.all L g 1 2677 (F 2677) 2678 (F 2678) := by
  intro t ht
  seg_fp ht using
    change Value.bits 64 (intBits 64 _) = _
    rw [show BitVec.ofInt 64 4 = BitVec.ofNat 64 4 from rfl, Lib.madwide_s32,
      show Lib.sx 4 = 4 by decide]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, ↓reduceIte]
    change Value.bits 64 _ = Value.bits 64 _
    congr 2
    omega

private theorem shl32 (a k : Nat) (hk : k < 32) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) <<< k) = BitVec.ofNat 64 (a * 2^k % 2^32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have h64 : a % 2^64 % 2^32 = a % 2^32 := Nat.mod_mod_of_dvd _ (by norm_num)
  have h32 : a % 2^32 % 2^64 = a % 2^32 := Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num))
    (by norm_num))
  simp only [h64, h32]
  have h1 := Nat.mod_lt a (show 0 < 2^32 by norm_num)
  have h2 : 2^k ≤ 2^31 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : a % 2^32 * 2^k < 2^64 := by
    have h3 : a % 2^32 * 2^k ≤ a % 2^32 * 2^31 := Nat.mul_le_mul_left _ h2
    have h4 : a % 2^32 * 2^31 < 2^32 * 2^31 := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    omega
  rw [Nat.mod_eq_of_lt this, Nat.mul_mod a, Nat.mod_eq_of_lt (show 2^k < 2^32 by omega)]

theorem addr_2683 :
    Seg kernel Assumptions.all L g 1 2683 (F 2683) 2684 (F 2684) := by
  intro t ht
  seg_fp ht using
    have k : (truncBits 32 (BitVec.ofInt 64 7)).toNat = 7 := by decide
    simp only [k, show ¬ (7 ≥ 32) by decide, ↓reduceIte]
    rw [shl32 _ 7 (by decide)]
    simp only [valueOf, scalarValue, u32, Nat.reduceEqDiff, ↓reduceIte]
    rfl

theorem addr_2684 :
    Seg kernel Assumptions.all L g 1 2684 (F 2684) 2685 (F 2685) := by
  intro t ht
  seg_fp ht using
    change Value.bits 64 (intBits 64 _) = _
    rw [show BitVec.ofInt 64 4 = BitVec.ofNat 64 4 from rfl, Lib.madwide_s32,
      show Lib.sx 4 = 4 by decide]
    simp only [valueOf, scalarValue, u64, Entry.rowAddr, Nat.reduceEqDiff, ↓reduceIte]
    change Value.bits 64 _ = Value.bits 64 _
    congr 2
    omega

private theorem shl64 (a : Nat) :
    Value.bits 64 (if (truncBits 32 (BitVec.ofInt 64 2)).toNat ≥ 64 then 0 else
      truncBits 64 (truncBits 64 (BitVec.ofNat 64 a) <<< (truncBits 32 (BitVec.ofInt 64 2)).toNat))
      = u64 (a * 4) := by
  have k : (truncBits 32 (BitVec.ofInt 64 2)).toNat = 2 := by decide
  simp only [k, show ¬ (2 ≥ 64) by decide, ↓reduceIte]
  change _ = Value.bits 64 _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem addr_2685 :
    Seg kernel Assumptions.all L g 1 2685 (F 2685) 2686 (F 2686) := by
  intro t ht
  seg_fp ht using
    rw [shl64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, ↓reduceIte]

private theorem add64 (a b : Nat) :
    Value.bits 64 (truncBits 64 (truncBits 64 (BitVec.ofNat 64 (a % 2^64)) +
      truncBits 64 (BitVec.ofNat 64 b))) = u64 (a + b) := by
  change _ = Value.bits 64 _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.mod_mod]
  omega

theorem addr_2686 :
    Seg kernel Assumptions.all L g 1 2686 (F 2686) 2687 (F 2687) := by
  intro t ht
  seg_fp ht using
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]
    change Value.bits 64 _ = Value.bits 64 _
    congr 2
    omega

theorem addr_chain_0 :
    Seg kernel Assumptions.all L g 8 2687 (F 2687) 2695 (F 2695) := by
  intro t ht
  seg_fp ht using
    simp only [BitVec.ofInt_ofNat]
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]

theorem addr_chain_1 :
    Seg kernel Assumptions.all L g 8 2695 (F 2695) 2703 (F 2703) := by
  intro t ht
  seg_fp ht using
    simp only [BitVec.ofInt_ofNat]
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]

theorem addr_chain_2 :
    Seg kernel Assumptions.all L g 8 2703 (F 2703) 2711 (F 2711) := by
  intro t ht
  seg_fp ht using
    simp only [BitVec.ofInt_ofNat]
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]

theorem addr_chain_3 :
    Seg kernel Assumptions.all L g 8 2711 (F 2711) 2719 (F 2719) := by
  intro t ht
  seg_fp ht using
    simp only [BitVec.ofInt_ofNat]
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]

theorem addr_chain_4 :
    Seg kernel Assumptions.all L g 8 2719 (F 2719) 2727 (F 2727) := by
  intro t ht
  seg_fp ht using
    simp only [BitVec.ofInt_ofNat]
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]

theorem addr_chain_5 :
    Seg kernel Assumptions.all L g 8 2727 (F 2727) 2735 (F 2735) := by
  intro t ht
  seg_fp ht using
    simp only [BitVec.ofInt_ofNat]
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]

theorem addr_chain_6 :
    Seg kernel Assumptions.all L g 8 2735 (F 2735) 2743 (F 2743) := by
  intro t ht
  seg_fp ht using
    simp only [BitVec.ofInt_ofNat]
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]

theorem addr_chain_7 :
    Seg kernel Assumptions.all L g 7 2743 (F 2743) 2750 (F 2750) := by
  intro t ht
  seg_fp ht using
    simp only [BitVec.ofInt_ofNat]
    rw [add64]
    simp only [valueOf, scalarValue, u64, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
      ↓reduceIte]

/-- The output addresses of the 64 word stores, as one exact stretch up to the last unpack. -/
theorem addr_exact : Seg kernel Assumptions.all L g 67 2683 (F 2683) 2750 (F 2750) :=
  addr_2683.comp (addr_2684.comp (addr_2685.comp (addr_2686.comp (addr_chain_0.comp
    (addr_chain_1.comp (addr_chain_2.comp (addr_chain_3.comp (addr_chain_4.comp
      (addr_chain_5.comp (addr_chain_6.comp addr_chain_7))))))))))

/-- The first four address words: the output row index and the LSE address. -/
theorem addr_head :
    SegU kernel Assumptions.all L g 2674 (F 2674) 2678 (F 2678) :=
  (SegU.of_seg addr_2674).comp ((addr_2675).comp ((SegU.of_seg addr_2676).comp
    (SegU.of_seg addr_2677)))

/-- The output addresses of the 64 word stores. -/
theorem addr_tail : SegU kernel Assumptions.all L g 2683 (F 2683) 2751 (F 2751) :=
  (SegU.of_seg addr_exact).comp
    (Lib.control_span (by decide +kernel : Lib.spanCheck ctlLive 2750 2750 2751))

/-- The same, from the facts at the guarded LSE store. -/
theorem addr_from_lse : SegU kernel Assumptions.all L g 2683 (F 2682) 2751 (F 2751) :=
  (Lib.control_span (by decide +kernel : Lib.spanCheck ctlLive 2682 2683 2683)).comp addr_tail

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
