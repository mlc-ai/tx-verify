-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.SeededSum
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Rescale
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.PlainWeights
import Kernels.TmlFa4Fwd.Proof.Softmax.BiasStats
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Assumption
noncomputable section
set_option maxRecDepth 100000

private def biasWord (V : Nat → Value) (j : Nat) :=
  if j < 47 then V (if j < 32 then 9573+j else 9541+(j-32))
  else joinValue (biasLanes V j).1 (biasLanes V j).2

private theorem bias_tree (V : Nat → Value) :
    Gen.rsumBb_v6646 (lookupD ((5123, .bits 32 0) :: Gen.rsumBa_facts1 V)) =
      seeded (joinValue (offset (V 7257) (V 1362)) (.bits 32 0)) (biasWord V) := by kernel_rfl

private theorem bias_pass (W : Nat → Value) (xs : List (Nat × Value)) {j : Nat} (hj : j < 64) :
    let E := Gen.expoBTA1_facts4 W
    biasLanes (lookupD (E ++ xs)) j = biasLanes (lookupD E) j :=
  atColumn hj (f := biasLanes (lookupD (Gen.expoBTA1_facts4 W ++ xs)))
    (g := biasLanes (lookupD (Gen.expoBTA1_facts4 W))) (by kernel_rfl)

private theorem bias_read {V : Nat → Value} {j : Nat} {x y : ℝ}
    (h : biasLanes V j = (.float .f32 x, .float .f32 y)) : PairReads (biasWord V j) (x,y) := by
  unfold biasWord
  split
  · rename_i hj
    simp only [biasLanes, hj, ite_true] at h
    apply pairRead_of_reads
    · rw [congrArg Prod.fst h]; exact readEReal_float _
    · rw [congrArg Prod.snd h]; exact readEReal_float _
  · rw [h]
    exact reads_join (reads_float x) (reads_float y)

theorem bias_sum {p L m} (hp : Pre p L m) (g v) :
    rsB p L g v = rowSumT (v.rs * factor p v .bias) (P p L g v .bias) := by
  let V := lookupD (pBData p L g v)
  have hs : Reads (V 7257) v.rs := by
    dsimp only [V]; rw [pB_sum_lookup]; exact reads_float _
  have hf : Reads (V 1362) (factor p v .bias) := by
    dsimp only [V]; rw [pB_factor_lookup]; exact bias_factor p v
  have h (j : Nat) (hj : j < 64) :
      biasLanes V j = (.float .f32 (P p L g v .bias (2*j)),
        .float .f32 (P p L g v .bias (2*j+1))) := by
    dsimp only [V, pBData]
    simp only [List.append_assoc]
    exact (bias_pass (vTailB p L g v) _ hj).trans (bias_weights hp g v hj)
  unfold rsB rsumBbStart
  rw [bias_tree, seeded_value _ _ _ _ (seed_mul hs hf) (fun j hj => bias_read (h j hj))]
  rfl

private def plainWord (V : Nat → Value) (j : Nat) :=
  joinValue (V (plainReg (2*j))) (V (plainReg (2*j+1)))

private theorem plain_tree (V : Nat → Value) :
    Gen.rsumPb_v7598 (lookupD ((5806, .bits 32 (BitVec.ofNat 64 0)) :: Gen.rsumPa_facts1 V)) =
      seeded (joinValue (offset (V 7257) (V 1492)) (.bits 32 0)) (plainWord V) := by kernel_rfl

private theorem plain_pass (W : Nat → Value) (xs : List (Nat × Value)) {i : Nat} (hi : i < 128) :
    let E := Gen.expoP4_facts3 W
    lookupD (E ++ xs) (plainReg i) = lookupD E (plainReg i) :=
  atColumn hi (f := fun i => lookupD (Gen.expoP4_facts3 W ++ xs) (plainReg i))
    (g := fun i => lookupD (Gen.expoP4_facts3 W) (plainReg i)) (by kernel_rfl)

theorem plain_sum {p L m} (hp : Pre p L m) (g v) :
    rsPG p v = rowSumT (v.rs * factor p v .plain) (P p L g v .plain) := by
  let V := lookupD (pPData p v)
  have hs : Reads (V 7257) v.rs := by
    dsimp only [V]; rw [pP_7257]; exact reads_float _
  have hf : Reads (V 1492) (factor p v .plain) := by
    dsimp only [V]; rw [pP_1492]; exact plain_factor p v
  have h (i : Nat) (hi : i < 128) : V (plainReg i) = .float .f32 (P p L g v .plain i) :=
    (plain_pass (lookupD (expoPS7 p v)) _ hi).trans (plain_weight hp g v hi)
  have hpair (j : Nat) (hj : j < 64) :
      PairReads (plainWord V j) (P p L g v .plain (2*j), P p L g v .plain (2*j+1)) := by
    rw [plainWord, h _ (by omega), h _ (by omega)]
    exact reads_join (reads_float _) (reads_float _)
  unfold rsPG
  rw [plain_tree, seeded_value _ _ _ _ (seed_mul hs hf) hpair]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
