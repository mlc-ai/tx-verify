-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumRow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StrictLib

@[expose] public section

/-! # Conditions of the row-maximum items

The `fn` items of the row maximum (`max.ftz`, the scale) are no fault when their sources read as
extended reals (`Rd`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

theorem c_max {r1 r2 : Nat} (hne : r1 ≠ r2) {va vb : Value} {x y : EReal} (ha : Rd va x)
    (hb : Rd vb y) : ∃ v, fF maxFL [.reg r1, .reg r2] [va, vb] = .ok v := by
  have e : fF maxFL [.reg r1, .reg r2] [va, vb] = maxFE va vb := by
    have h21 : (r2 == r1) = false := beq_false_of_ne (Ne.symm hne)
    simp [fF, fOpnd, lk, regsOf, regOf, maxFL, List.lookup, h21]
  rw [e, maxFE_reads (rd_read ha) (rd_read hb)]
  exact ⟨_, rfl⟩

theorem c_maxI {r : Nat} {va : Value} {x : EReal} (ha : Rd va x) :
    ∃ v, fF maxFL [.reg r, .f32imm 4286578688] [va] = .ok v := by
  have e : fF maxFL [.reg r, .f32imm 4286578688] [va] = maxFE va negInf32 := by
    simp [fF, fOpnd, lk, regsOf, regOf, maxFL]
  rw [e, maxFE_reads (rd_read ha) readEReal_negInf]
  exact ⟨_, rfl⟩

theorem c_scale {a b : Nat} (hne : a ≠ b) {vm vs : Value} {M : EReal} {sc : ℝ} (hsc : 0 < sc)
    (hm : Rd vm M) (hs : readEReal .f32 vs = some (.ok (sc : EReal))) :
    ∃ v, fF (mulL true) [.reg a, .reg b] [vm, vs] = .ok v := by
  have e : fF (mulL true) [.reg a, .reg b] [vm, vs] = mulE true vm vs := by
    have h21 : (b == a) = false := beq_false_of_ne (Ne.symm hne)
    simp [fF, fOpnd, lk, regsOf, regOf, mulL, List.lookup, h21]
  obtain ⟨hz, -⟩ := w0r_mulpos hm.2.2 hsc
  rw [e, mulE_reads (rd_read hm) hs hz]
  exact ⟨_, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
