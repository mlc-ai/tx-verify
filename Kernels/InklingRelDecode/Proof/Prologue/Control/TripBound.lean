-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Values
import Lemmas.Flow.Counter32

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

private theorem shift_range (x : BitVec 64) :
    ∃ y : Int, -(2^24) ≤ y ∧ y < 2^24 ∧ div128 x = i32 y := by
  let v := add32 x (shru (shrs x 31) 25)
  let z := toSigned 32 (r32 v)
  obtain ⟨lo,hi⟩ := toSigned_r32 v
  refine ⟨z/128,?_,?_,rfl⟩ <;> dsimp only [z] <;> omega

private theorem signed_add (s : Nat) (z : Int) (lo : -(2^31) ≤ s+z) (hi : s+z < 2^31) :
    intOf .s 32 (r32 (add32 (W s) (i32 z))) = s+z := by
  simp only [intOf,ite_true,toSigned,r32,add32,i32,W,truncBits,BitVec.toNat_ofNat,
    BitVec.toNat_add,BitVec.toNat_ofInt]
  split <;> omega

private theorem signed_i32 (z : Int) (lo : -(2^31) ≤ z) (hi : z < 2^31) :
    toSigned 32 (r32 (i32 z)) = z := by
  simp only [toSigned,r32,i32,truncBits,BitVec.toNat_ofNat,BitVec.toNat_ofInt]
  split <;> omega

private theorem nat_i32 (z : Int) (lo : 0 ≤ z) (hi : z < 2^31) :
    (r32 (i32 z)).toNat = z.toNat := by
  simp only [r32,i32,truncBits,BitVec.toNat_ofNat,BitVec.toNat_ofInt]
  omega

/-- Even an unconstrained sequence word supplies at most 2^24 blocks to the
signed division. Pre bounds the split count, hence the next softmax key. -/
theorem key_range {Q L m} (hp : Pre Q L m) (s : Nat) (hs : s<Q.splits) (x : BitVec 64) :
    let v := iters Q.splits s (div128 x)
    s + ((positive v).toNat+1)*Q.splits < 2^31 := by
  obtain ⟨y,lo,hi,hy⟩ := shift_range x
  let p := Q.splits-1-s
  let z : Int := p+y
  let q := z.tdiv (Q.splits : Int)
  have hp₁ := hp.splitsRange
  have pos := hp.splitsPos
  have small : Q.splits < 2^29 := by
    have le : Q.splits ≤ Q.splits*Q.nTok := Nat.le_mul_of_pos_right _ hp.nTokPos
    have slack := hp.outRangeSlack
    unfold heads headDim at slack
    omega
  have hz₁ : -(2^31) ≤ z := by dsimp [z,p]; omega
  have hz₂ : z < 2^31 := by dsimp [z,p]; omega
  have denom : intOf .s 32 (r32 (W Q.splits)) = Q.splits := by
    change toSigned 32 (r32 (W Q.splits)) = _
    rw [r32_W (by omega),toSigned_W (by omega)]
  have eq : iters Q.splits s (div128 x) = i32 q := by
    change intBits 32 ((intOf .s 32 (r32 (add32 (add32 (W Q.splits) (not32 (W s)))
      (div128 x)))).tdiv (intOf .s 32 (r32 (W Q.splits)))) = i32 q
    rw [hy,not32_add_W hs (by omega),signed_add _ _ hz₁ hz₂,denom]
    rfl
  intro v
  dsimp only [v]
  rw [eq]
  have divBounds (a : Int) (b : Nat) : min a 0 ≤ a.tdiv b ∧ a.tdiv b ≤ max a 0 ∧
      (a.tdiv b).toNat*b ≤ a.toNat := by
    cases a with
    | ofNat n =>
      have h := Nat.div_le_self n b
      have h' := Nat.div_mul_le_self n b
      change min (n:Int) 0 ≤ (↑(n/b):Int) ∧ (↑(n/b):Int) ≤ max (n:Int) 0 ∧ (n/b)*b≤n
      generalize n/b = k at *
      omega
    | negSucc n =>
      have h := Nat.div_le_self (n+1) b
      change min (Int.negSucc n) 0 ≤ -(↑((n+1)/b):Int) ∧
        -(↑((n+1)/b):Int) ≤ max (Int.negSucc n) 0 ∧ (-(↑((n+1)/b):Int)).toNat*b≤0
      rw [Int.toNat_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg _))]
      simp only [Int.negSucc_eq,zero_mul]
      generalize (n+1)/b = k at *
      omega
  obtain ⟨lb,ub,quot⟩ := divBounds z Q.splits
  change min z 0 ≤ q at lb
  change q ≤ max z 0 at ub
  change q.toNat*Q.splits ≤ z.toNat at quot
  have hq₁ : -(2^31) ≤ q := by omega
  have hq₂ : q < 2^31 := by omega
  have test : scmpi .gt .s (i32 q) 0 = decide (0<q) := by
    change decide (toSigned 32 (r32 (i32 q)) > toSigned 32 (i32 0)) = _
    rw [signed_i32 q hq₁ hq₂]
    rfl
  simp only [positive,test,decide_eq_true_eq]
  split
  · rename_i h
    rw [nat_i32 q (by omega) hq₂]
    rw [Nat.add_mul,Nat.one_mul]
    dsimp only [z,p] at quot
    omega
  · simp; omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
