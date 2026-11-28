-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RawArith
public import Lemmas.Flow.Arith32Word

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof Arith32

/-- Softmax and epilogue shift the received warp word by 21 before masking its lane field. -/
theorem shift_lane_word (v : Value) :
    .bits 32 (shl (v.regBits.getD 0) 21) = b32 ((word v).toNat * 2097152 % 2^32) := by
  apply congrArg (Value.bits 32)
  apply BitVec.eq_of_toNat_eq
  change (truncBits 32 (word v <<< 21)).toNat = _
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The mask keeps bits 21 and 22 of the shifted word. -/
theorem and_lane (m : Nat) :
    (m * 2097152 % 4294967296 &&& 6291456) % 4294967296 = m % 4 * 2097152 := by
  have h1 : m * 2097152 % 4294967296 = (m % 2048) <<< 21 := by
    rw [Nat.shiftLeft_eq]
    omega
  have h2 : (6291456 : Nat) = 3 <<< 21 := by rw [Nat.shiftLeft_eq]
  have h3 : (m % 2048) &&& 3 = m % 4 := by
    have := Nat.and_two_pow_sub_one_eq_mod (m % 2048) 2
    norm_num at this
    rw [this]
  rw [h1,h2,← Nat.shiftLeft_and_distrib,h3,Nat.shiftLeft_eq]
  have := Nat.mod_lt m (by decide : 0 < 4)
  norm_num
  omega

/-- The mask instruction shared by the broadcasts at PCs 1261 and 2603.
Only these lane bits of the received value survive into the TMEM operand. -/
theorem lane_mask_step {L : Launch} {g pc dst src : Nat} {rs rs' : List Nat}
    (val : Nat → Value) (m : Nat)
    (hc : kernel.code[pc]? = some ⟨none,.int ⟨.and,.int .b 32,false,[some dst],
      [.reg src,.imm 6291456]⟩⟩) (hs : Assumptions.emuSites.contains pc = false)
    (hr : src ∈ rs) (srcVal : val src = b32 (m * 2097152 % 2^32))
    (dstVal : val dst = b32 (m % 4 * 2097152))
    (live : ∀ r ∈ rs', r = dst ∨ r ∈ rs) :
    SegU kernel Assumptions.all L g pc (factsFrom rs val) (pc+1) (factsFrom rs' val) := by
  apply scalarStepU hc rfl rfl hs (v := val dst) _ (fun _ => writeLive live)
  intro t u regs he
  have h := srcVal ▸ holds_mem regs (mem_factsFrom hr)
  have hb := readBits_regBits (L := L) (g := g) (w := 32) h (show _ = some (W _) from rfl)
  have imm : readBits L g t 32 (.imm 6291456) = .ok (W 6291456) := rfl
  simp only [execInt,DType.width,show ¬ (32 : Nat) = 1 by decide,↓reduceIte,hb,imm,
    pure,Except.pure,bind,Except.bind] at he
  rw [← Except.ok.inj he,dstVal]
  apply congrArg (fun v => PTX.next (setReg t dst v))
  apply congrArg (Value.bits 32)
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits,W,BitVec.toNat_and,BitVec.toNat_ofNat]
  have hm := and_lane m
  have hbound : (m * 2097152 % 4294967296 &&& 6291456) ≤ 6291456 := Nat.and_le_right
  norm_num only [Nat.reducePow, Nat.reduceMod] at *
  have small : m * 2097152 % 4294967296 < 18446744073709551616 := by omega
  simp only [Nat.mod_eq_of_lt small,Nat.mod_mod]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
