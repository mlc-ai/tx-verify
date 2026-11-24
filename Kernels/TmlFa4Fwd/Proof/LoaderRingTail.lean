-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEntry
public import Kernels.TmlFa4Fwd.Flow.Code.Part020
public import Kernels.TmlFa4Fwd.Flow.Code.Part021
public import Kernels.TmlFa4Fwd.Flow.Code.Part027

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The three-stage K/V ring flips parity when the next slot wraps to stage zero. -/
def loaderNextPhase (stage : Fin 3) (phase : Bool) : Bool := xor phase (stage.val == 2)

def loaderPhaseWord (phase : Bool) : Value := b32 (if phase then 1 else 0)

def loaderNextRingFacts (stage : Fin 3) (phase : Bool) : List (Nat × Value) :=
  [(7179, b32 ((stage.val + 1) % 3)), (7180, loaderPhaseWord (loaderNextPhase stage phase))]

private theorem warmRingStage (l : Launch) (g : Nat) (stage : Fin 3) (phase : Bool) :
    Seg kernel [] l g 5 1343 [(1139, b32 stage.val), (2064, loaderPhaseWord phase)] 1348
      (loaderNextRingFacts stage phase) := by
  fin_cases stage <;> cases phase <;> intro t ht <;>
    simp only [loaderNextRingFacts, loaderPhaseWord, loaderNextPhase] at ht ⊢ <;>
    seg_fp ht using decide

private theorem steadyRingStage (l : Launch) (g : Nat) (stage : Fin 3) (phase : Bool) :
    Seg kernel [] l g 5 1736 [(1170, b32 stage.val), (2141, loaderPhaseWord phase)] 1741
      (loaderNextRingFacts stage phase) := by
  fin_cases stage <;> cases phase <;> intro t ht <;>
    simp only [loaderNextRingFacts, loaderPhaseWord, loaderNextPhase] at ht ⊢ <;>
    seg_fp ht using decide

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

theorem warmRingCondition (l : Launch) (g : Nat) {i trips : Nat}
    (hTrip : trips < 2 ^ 31) (hi : i < min trips 9) :
    Seg kernel [] l g 4 1348 [(7174, b32 i), (1091, b32 trips)] 1352
      [(199, .pred (decide (i + 1 < min trips 9))), (7174, b32 (i + 1))] := by
  have h1 : i < 2 ^ 32 := by omega
  have h2 : i + 1 < 2 ^ 32 := by omega
  have h3 : trips < 2 ^ 32 := by omega
  have h4 : min trips 9 < 2 ^ 32 := by omega
  have h5 : i + 1 < 2 ^ 64 := by omega
  have h6 : min trips 9 < 2 ^ 64 := by omega
  have hNe : (↑(i + 1 : Nat) : Int) ≠ ↑(min trips 9) ↔ i + 1 < min trips 9 := by
    exact_mod_cast (show (i + 1 ≠ min trips 9) ↔ i + 1 < min trips 9 by omega)
  have hPos : (0 : Int) < trips := by exact_mod_cast (show 0 < trips by omega)
  have hZero : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hNine : toSigned 32 9#64 = 9 := rfl
  have hOne : truncBits 32 (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 := rfl
  have hNineWord : truncBits 32 (BitVec.ofInt 64 9) = BitVec.ofNat 64 9 := rfl
  have hMin :
      (if (trips : Int) < 9 then BitVec.ofNat 64 trips else BitVec.ofNat 64 9) =
        BitVec.ofNat 64 (min trips 9) := by
    by_cases h : trips < 9
    · have h' : (trips : Int) < 9 := by exact_mod_cast h
      simp [h', Nat.min_eq_left h.le]
    · have h' : ¬(trips : Int) < 9 := by exact_mod_cast h
      simp [h', Nat.min_eq_right (Nat.le_of_not_gt h)]
  have hMaxOp : (IntOp.max false == IntOp.max false) = true := rfl
  have hMinOp : (IntOp.min false == IntOp.max false) = false := rfl
  intro t ht
  seg_fp ht using
    simp only [b32, hOne, hNineWord, hMaxOp, hMinOp,
      kind_s_beq_s, Bool.false_eq_true, ↓reduceIte, truncBits_ofNat h1 (by decide),
      truncBits_ofNat h2 (by decide), truncBits_ofNat h3 (by decide),
      truncBits_ofNat h4 (by decide), ← BitVec.ofNat_add, compare,
      signedWord hTrip, hZero, hNine, gt_iff_lt, hPos, decide_true, hMin,
      Option.getD_some, decide_eq_true_eq, toNat_ofNat_lt h5, toNat_ofNat_lt h6,
      hNe]

theorem steadyRingCondition (l : Launch) (g : Nat) {i trips : Nat}
    (hTrip : trips < 2 ^ 31) (hi : i < trips) :
    Seg kernel [] l g 2 1741 [(7181, b32 i), (1091, b32 trips)] 1743
      [(230, .pred (decide (i + 1 < trips))), (7181, b32 (i + 1))] := by
  have hI : i + 1 < 2 ^ 31 := by omega
  have h32 : i < 2 ^ 32 := by omega
  have h32' : i + 1 < 2 ^ 32 := by omega
  have hTrip32 : trips < 2 ^ 32 := by omega
  have hAdd : truncBits 32 (BitVec.ofNat 64 i + BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add, truncBits_ofNat h32' (by decide)]
  have hOne : truncBits 32 (BitVec.ofInt 64 1) = 1#64 := rfl
  intro t ht
  seg_fp ht using first
    | norm_bits
    | simp only [hOne, truncBits_ofNat h32 (by decide),
        truncBits_ofNat h32' (by decide), truncBits_ofNat hTrip32 (by decide), hAdd,
        compare, Option.getD_some, signedWord hI, signedWord hTrip, Int.ofNat_lt]

end
end PTX.Kernels.TmlFa4Fwd.Loader
