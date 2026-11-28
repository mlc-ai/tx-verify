-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlk
public import Lemmas.Flow.ScalarOut

@[expose] public section

/-! # The words a lane exchanges are scalar

A word another lane reads back through memory is read from its bytes. The row maximum stored at
pc 566 is the last result of a `mul.f32` (`scal_mst_word`); the carried row sum is the last
result of an `fma.f32` (`scal_blkOst_l`), and the sum the epilogue stores at pc 1155 is that sum
or the constant zero (`scal_est_word`). Each is a scalar value (`Scal`), so its bytes rebuild to
itself (`rebuild_of_scal`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

/-- The maximum a block stores (pc 566, register 1109) is scalar. -/
theorem scal_mst_word (V : Nat → Value) : Scal (rmax_v565 V) := by
  unfold rmax_v565
  refine scal_okVal (scal_bits _ _) fun v h => ?_
  unfold fF at h
  simp only [List.map_cons, List.map_nil] at h
  exact scal_mulE h

/-- The running sum a block ends with (register 2955) is scalar. -/
theorem scal_blkOst_l (x : BitVec 64) (b : Blk) : Scal (blkOst x b 2955) := by
  unfold blkOst f_ost
  rw [lk_head_mem (by simp only [pw_facts4, List.map_cons, List.map_nil]; decide)]
  change Scal (pw_v703 _)
  unfold pw_v703
  refine scal_okVal (scal_bits _ _) fun v h => ?_
  unfold fF at h
  simp only [List.map_cons, List.map_nil] at h
  exact scal_floatE (f := fmaI .rn true) rfl h

/-- The sum the epilogue stores (pc 1155, register 1727): the carried sum or zero. -/
theorem scal_est_word (x : BitVec 64) (m l mx sk : Value) (hl : Scal l) :
    Scal (lookupD (f_exit (lookupD (f_car x m l mx sk))) 1727) := by
  unfold f_exit
  rw [lk_head_mem (by simp only [e1_facts1, List.map_cons, List.map_nil]; decide)]
  change Scal (e1_v1150 _)
  unfold e1_v1150
  split
  · exact scal_bits _ _
  · simpa [lookupD, f_car, List.lookup] using hl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
