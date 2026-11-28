-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
import Lemmas.Flow.Bits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow Arith32

private def third (s : Int) := if s<0 then -((-s)/3) else s/3

private theorem corrected (h : Int) (lo : -2^31 ≤ h) (hi : h < 2^31) :
    (((h%2^64).toNat%2^32 + (h%2^64).toNat%2^32/2^31%2^32)%2^32 : Nat) =
      ((if h<0 then h+1 else h)%2^32).toNat := by
  have pos : 0 ≤ h % 2^64 := Int.emod_nonneg _ (by norm_num)
  have cast := Int.toNat_of_nonneg pos
  generalize (h%2^64).toNat = n at cast ⊢
  split <;> omega

private theorem quotient_signed (i : BitVec 64) :
    ((quotient i).toNat : Int) = third (toSigned 32 (r32 i)) % 2^32 := by
  let s := toSigned 32 (r32 i)
  have small : -2^31 ≤ s ∧ s<2^31 := by
    dsimp [s,toSigned,r32,truncBits]
    split <;> omega
  let h := s*1431655766/2^32
  have range : -2^31 ≤ h ∧ h<2^31 := by dsimp [h]; omega
  have eq : (if h<0 then h+1 else h)=third s := by
    dsimp [h,third]; split <;> split <;> omega
  change ((add32 (r32 (BitVec.ofInt 64 h)) (shru (r32 (BitVec.ofInt 64 h)) 31)).toNat : Int) = _
  nf_simp [add32,r32,shru,i32]
  have fix := corrected h range.1 range.2
  rw [eq] at fix
  simp only [Nat.reducePow,Int.reducePow] at fix
  rw [fix,Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  rfl

/-- The tile displacement for an arbitrary returned counter. Signed division
allows a negative remainder before the launch count has been identified. -/
theorem tile_remainder (i : BitVec 64) :
    ∃ r : Int, -2 ≤ r ∧ r ≤ 2 ∧ (i.toNat<2^31 → r = ((i.toNat%3 : Nat) : Int)) ∧
      ((mad32 (quotient i) (i32 (-98304)) (shl i 15)).toNat : Int) = 32768*r%2^32 := by
  let s := toSigned 32 (r32 i)
  let r := s-3*third s
  have bounds : -2 ≤ r ∧ r ≤ 2 := by dsimp [r,third]; split <;> omega
  have small : i.toNat<2^31 → r = ((i.toNat%3 : Nat) : Int) := by
    intro h
    have hs : s = (i.toNat : Int) := by
      dsimp [s,toSigned,r32,truncBits]
      simp only [BitVec.toNat_ofNat]
      split <;> omega
    dsimp only [r]
    rw [hs]
    dsimp [third]
    split <;> omega
  refine ⟨r,bounds.1,bounds.2,small,?_⟩
  have hq := quotient_signed i
  have natWord (w : BitVec 64) : w=BitVec.ofNat 64 w.toNat := by simp
  dsimp only [r,s]
  rw [natWord (quotient i)]
  generalize (quotient i).toNat = q at hq ⊢
  rw [natWord i] at hq ⊢
  generalize i.toNat = n at hq ⊢
  nf_simp [mad32,r32,shl,i32,toSigned] at hq ⊢
  push_cast at hq ⊢
  split at hq <;> split <;> omega

/-- An 8192-byte transfer at any of the loader offsets ends below the query
tile or begins past the publication area after unsigned address wraparound. -/
theorem tile_separate (L : Launch) (i : BitVec 64) (off : Nat) (hoff : off≤122880)
    (room : L.sharedBase+213340 ≤ 2^18) :
    let tile := add32 (r32 (BitVec.ofNat 64 L.sharedBase))
      (mad32 (quotient i) (i32 (-98304)) (shl i 15))
    let dst := (addi tile (off : Int)).toNat
    dst+8192 ≤ L.sharedBase+196608 ∨ L.sharedBase+213340 ≤ dst := by
  dsimp only
  obtain ⟨r,lo,hi,_,disp⟩ := tile_remainder i
  generalize mad32 (quotient i) (i32 (-98304)) (shl i 15) = delta at disp ⊢
  have word : delta=BitVec.ofNat 64 delta.toNat := by simp
  rw [word]
  nf_simp [addi,add32,i32,r32]
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ (off : Int))
    (by omega : (off : Int) < 18446744073709551616)]
  simp only [Int.toNat_natCast]
  omega

/-- For a counter below `2^31` the tile is slot `i % 3` of the ring, at any loader offset. -/
theorem tile_slot (L : Launch) (i : BitVec 64) (off : Nat) (hoff : off≤122880)
    (room : L.sharedBase+213340 ≤ 2^18) (small : i.toNat<2^31) :
    let tile := add32 (r32 (BitVec.ofNat 64 L.sharedBase))
      (mad32 (quotient i) (i32 (-98304)) (shl i 15))
    (addi tile (off : Int)).toNat = L.sharedBase+32768*(i.toNat%3)+off := by
  dsimp only
  obtain ⟨r,lo,hi,eq,disp⟩ := tile_remainder i
  have hr := eq small
  generalize mad32 (quotient i) (i32 (-98304)) (shl i 15) = delta at disp ⊢
  have word : delta=BitVec.ofNat 64 delta.toNat := by simp
  rw [word]
  nf_simp [addi,add32,i32,r32]
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ (off : Int))
    (by omega : (off : Int) < 18446744073709551616)]
  simp only [Int.toNat_natCast]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Loader
