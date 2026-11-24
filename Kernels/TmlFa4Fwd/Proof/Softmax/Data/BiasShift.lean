-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.FirstWeights
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoB0
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarrBChain
import Kernels.TmlFa4Fwd.Proof.Softmax.BiasMaxValue
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Assumption
noncomputable section
set_option maxRecDepth 100000

def shifted (p : Params) (M x : EReal) :=
  erealValue .f32 (shift x (scl p) (M.toReal * -(scl p : ℝ)))

private def chunk (W : Nat → Value) (j : Nat) :=
  let z := offset (W 4565) (W 1230)
  splitValue 64 (okVal (.bits 64 0) (fma2E (W (8317 + 2*j))
    (joinValue (W 7132) (W 7132)) (joinValue z z)))

private theorem generated (W : Nat → Value) {j : Nat} (hj : j < 64) :
    let V := lookupD (Gen.expoB0_facts5 W)
    (V (1363+2*j), V (1363+2*j+1)) = chunk W j :=
  atColumn hj (f := fun j => (lookupD (Gen.expoB0_facts5 W) (1363+2*j),
    lookupD (Gen.expoB0_facts5 W) (1363+2*j+1))) (g := chunk W) (by kernel_rfl)

private theorem submax (p L g v) : Reads (valueOfD p L g (statB v) 4565) (maxB p v).toReal := by
  rw [statB_4565]
  cases h : v.mf
  · simpa only [maxB, h, Bool.false_and, Bool.false_eq_true, ite_false, Bool.cond_false, selMax]
      using reads_sel (foldBE_lt_top p v)
  · simp only [maxB, h, Bool.true_and, Bool.cond_true]
    split
    · exact reads_float _
    · exact reads_float _

private theorem prod_read (p v i) : Reads (bv32 (bpf v) (bps p v) i) (bpeB p v i) := by
  unfold bpeB bpe bv32
  split <;> first | exact reads_float _ | exact reads_bot

private theorem chunk_eq {p L m} (hp : Pre p L m) (g v) {j : Nat} (hj : j < 64) :
    chunk (valueOfD p L g (statB v)) j = (shifted p (maxB p v) (bpeB p v (2*j)),
      shifted p (maxB p v) (bpeB p v (2*j+1))) := by
  let W := valueOfD p L g (statB v)
  have hs : Reads (W 7132) (scl p : ℝ) := by
    change Reads (valueOfD _ _ _ _ _) _
    rw [valueOfD_ctl _ (by rfl : ctl 7132 = true)]
    exact (reads_scale hp).1
  have hn : Reads (W 1230) (-(scl p : ℝ)) := by
    change Reads (negS p) _
    rw [show negS p = .float .f32 (-(scl p : ℝ)) from
      congrArg (Value.float .f32) (Rat.cast_neg _)]
    exact reads_float _
  have hab : pairRead (W (8317+2*j)) = some (.ok (bpeB p v (2*j), bpeB p v (2*j+1))) := by
    change pairRead (valueOfD _ _ _ _ _) = _
    rw [statB_prod v hj]
    exact pairRead_of_reads (prod_read p v _).read (prod_read p v _).read
  change chunk W j = _
  dsimp only [chunk]
  rw [offset_val (submax p L g v) hn, shifted_pair hab hs
    (reads_float ((maxB p v).toReal * -(scl p : ℝ))) (reads_scale hp).2
    (bpeB_lt_top p v _) (bpeB_lt_top p v _)]
  rfl

theorem bias_shift {p L m} (hp : Pre p L m) (g v) {j : Nat} (hj : j < 64) :
    (vExpoB p L g v (1363+2*j), vExpoB p L g v (1363+2*j+1)) =
      (shifted p (maxB p v) (bpeB p v (2*j)), shifted p (maxB p v) (bpeB p v (2*j+1))) :=
  (generated (valueOfD p L g (statB v)) hj).trans (chunk_eq hp g v hj)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
