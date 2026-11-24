-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasAddr
public import Lemmas.Tensor.TensorSwizzle
import Kernels.TmlFa4Fwd.Proof.Lib.LineWord

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow.Arith32

private theorem offset_atom {B row c j : Nat} (hb : B%1024=0) (hc : c<8) (hj : j<16) :
    TensorSwizzle.offset .b128 B (128*row+16*c+j) =
      128*row+16*(c ^^^ (row%8))+j := by
  simp only [TensorSwizzle.offset,TensorSwizzle.chunk,TensorSwizzle.mask,TensorSwizzle.sectors,
    BitVec.toNat_xor,BitVec.toNat_ofNat]
  rw [show (128*row+16*c+j)/128 = row by omega,
    show (128*row+16*c+j)/16%2^3 = c by omega,
    show ((B/128+row)%8)%2^3 = row%8 by omega,
    show (128*row+16*c+j)%16 = j by omega]

private theorem eff_nat (x : BitVec 64) (a n : Nat) (h : x.toNat = a) (hb : a+n<2^32) :
    (truncBits 32 (truncBits 32 x+BitVec.ofInt 64 (n : Int))).toNat = a+n := by
  simp only [truncBits,BitVec.toNat_ofNat,BitVec.toNat_add,BitVec.toNat_ofInt,h]
  omega

private theorem imm_table : ∀ c : Fin 16, c.val ≠ 0 → c.val ≠ 8 →
    bOffs.getD (if c.val<8 then 14-c.val else 15-c.val) 0 =
      ((166912+16384*(c.val/8)+16*(c.val%8) : Nat) : Int) := by decide

/-- Undo the hardware swizzle at any byte of a vector bias load. The two regions
contain eight chunks each, with eight consecutive BF16 elements per chunk. -/
theorem bias_address {p L m g} (hp : Pre p L m) (hw : g%L.block/32<8) (c : Fin 16) :
    let B := L.sharedBase+166912+32768*(g%L.block/32/4)+16384*(c.val/8)
    let a := (truncBits 32 (truncBits 32 (bldX L g c) + BitVec.ofInt 64 (bldOff c))).toNat
    a = B + 128*(g%L.block%128) + 16*((c.val%8) ^^^ (g%L.block%128%8)) := by
  let row := g%L.block%128
  let st := g%L.block/32/4
  let B := L.sharedBase+166912+32768*st+16384*(c.val/8)
  let N := B/128+row
  let J := c.val%8
  have ha := hp.shared.1
  have hb := hp.shared.2.1
  have hc := c.isLt
  have hB : B%1024=0 := by dsimp [B]; omega
  have hrow : row<128 := Nat.mod_lt _ (by decide)
  have hst : st<2 := by dsimp [st]; omega
  have hphase : N%8=row%8 := by dsimp [N]; omega
  have bound : B+128*row+128 < 2^32 := by dsimp [B]; omega
  have base : 128*N=B+128*row := by dsimp [N]; omega
  have small : J<8 := Nat.mod_lt _ (by decide)
  have addr : (truncBits 32 (truncBits 32 (bldX L g c)+BitVec.ofInt 64 (bldOff c))).toNat =
      B+128*row+16*(J ^^^ (row%8)) := by
    by_cases h : c.val=0 ∨ c.val=8
    · let N0 := (L.sharedBase+166912)/128+row
      have line : 128*N0=L.sharedBase+166912+128*row := by dsimp [N0]; omega
      have phase : N0%8=row%8 := by dsimp [N0]; omega
      have hx := addi_nat (rowSb_nat (g := g) hp) (n := 166912) (by decide) (by omega)
      have sx := swz_val (n := N0) (c := 0) (hx.trans (by dsimp [row] at line; omega))
        (by decide) (by omega)
      rw [Nat.zero_xor,phase,line] at sx
      have sx' := add32_nat sx (bOff_nat hw) (by omega)
      change (bAddr0 L g).toNat = _ at sx'
      rw [bldX,ite_eq_left h]
      rcases h with h | h
      · rw [show bldOff c = (0 : Nat) by simp [bldOff,h],eff_nat _ _ 0 sx' (by omega)]
        simp only [B,J,h,Nat.reduceDiv,Nat.reduceMod,Nat.zero_xor,st]
        omega
      · rw [show bldOff c = (16384 : Nat) by simp [bldOff,h],eff_nat _ _ 16384 sx' (by omega)]
        simp only [B,J,h,Nat.reduceDiv,Nat.reduceMod,Nat.zero_xor,st]
        omega
    · have h0 : c.val ≠ 0 := fun eq => h (.inl eq)
      have h8 : c.val ≠ 8 := fun eq => h (.inr eq)
      rw [bldX,ite_eq_right h,imm_table c h0 h8]
      have hx := add32_nat (rowSb_nat (g := g) hp) (bOff_nat hw) (by omega)
      have ax := addi_nat hx (n := 166912+16384*(c.val/8)+16*J) (by omega) (by omega)
      have sx := swz_val (n := N) (c := J) (ax.trans (by dsimp [B,row,st] at base; omega))
        small (by omega)
      change (bAddr L g _).toNat = _ at sx
      rw [base,hphase] at sx
      have hxor := col_xor_lt J small (row%8) (by omega)
      rw [show bldOff c = (0 : Nat) by simp [bldOff,h8],eff_nat _ _ 0 sx (by omega),Nat.add_zero]
  exact addr

theorem bias_offset {p L m g} (hp : Pre p L m) (hw : g%L.block/32<8) (c : Fin 16) (j : Fin 16) :
    let B := L.sharedBase+166912+32768*(g%L.block/32/4)+16384*(c.val/8)
    let a := (truncBits 32 (truncBits 32 (bldX L g c) + BitVec.ofInt 64 (bldOff c))).toNat
    TensorSwizzle.offset .b128 B (a+j.val-B) = 128*(g%L.block%128)+16*(c.val%8)+j.val := by
  let row := g%L.block%128
  let J := c.val%8
  let B := L.sharedBase+166912+32768*(g%L.block/32/4)+16384*(c.val/8)
  have hB : B%1024=0 := by dsimp [B]; have := hp.shared.1; omega
  have small : J<8 := Nat.mod_lt _ (by decide)
  dsimp only
  rw [bias_address hp hw c]
  change TensorSwizzle.offset .b128 B (_+j.val-B) = _
  rw [show B+128*row+16*(J ^^^ (row%8))+j.val-B = 128*row+16*(J ^^^ (row%8))+j.val by omega,
    ← offset_atom hB small j.isLt, TensorSwizzle.offset_involutive]

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
