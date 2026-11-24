-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Select

@[expose] public section

/-! # A CTA with a work item picks it

`no_exit_of_work`: a lane of a CTA that holds a request's work does not return from the first
pass. The scan ends at the group of the work item, as it does not run out of groups before it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0}

/-- **The scan of a CTA with a work item ends at a group of the batch.** -/
theorem end_of_work (hp : Pre p L m) {g R b : Nat} (hg : g < L.threads) (hb : b < p.batch)
    (hhi : g / L.block < tilePrefix p (b + 1) * p.heads) (hE : End p (g / L.block) false R) :
    scmp .ge .s (gxv p (g / L.block) false R) (batchOf p false) = false := by
  obtain ⟨hReach, hcont⟩ := hE
  have hbb := batch_lt hp
  have hc := cta_lt hp hg
  have hwork : g / L.block < tilePrefix p p.batch * p.heads :=
    hhi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  have hfirst : 31 * R < p.batch ∧ reqN p R 0 = 31 * R := by
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · exact ⟨by omega, rfl⟩
    · exact reached_first hp hReach hR
  obtain ⟨hlt, hf⟩ := hfirst
  have hA1 := A_succ_W hp hReach (by omega)
  rw [hf] at hA1
  have hw := work_lt hp (show min p.batch (31 * R + 31) ≤ p.batch by omega)
  have hG1 : addi (G p false (R + 1)) 31 = W (31 * R + 31) := by
    rw [G_W hp false (R + 1) (by omega), addi31_W (by omega)]
    congr 1; simp only [Nat.add_sub_cancel]; omega
  have hle : scmp .le .s (A p false (R + 1)) (kw (g / L.block)) =
      decide (tilePrefix p (min p.batch (31 * R + 31)) * p.heads ≤ g / L.block) := by
    rw [hA1, kw_W, scmp_le_W hw hc]
  have hT : ¬ tilePrefix p (min p.batch (31 * R + 31)) * p.heads ≤ g / L.block := by
    intro hT
    rw [cont_eq, hle, hG1, batchOf_W hp, scmp_ge_W (by omega) (by omega)] at hcont
    simp only [hT, decide_true, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_false,
      decide_eq_true_eq] at hcont
    rw [Nat.min_eq_left hcont] at hT
    omega
  have hat : atTotal p (g / L.block) false R = true := by
    rw [atTotal_eq, hle]; simp [hT]
  have hgx : gxv p (g / L.block) false R = W (31 * R) := by
    cases R with
    | zero => simp only [gxv, hat, ↓reduceIte]; rfl
    | succ R =>
      simp only [gxv, hat, ↓reduceIte]
      rw [G_W hp false (R + 1) (by omega), addi31_W (by omega), batchOf_W hp,
        min32_W (by omega) (by omega)]
      congr 1
      simp only [Nat.add_sub_cancel]
      omega
  rw [hgx, batchOf_W hp, scmp_ge_W (by omega) (by omega)]
  exact decide_eq_false (by omega)

/-- **A lane of a CTA with a work item does not return from the first pass.** -/
theorem no_exit_of_work (hp : Pre p L m) {g ns nv b : Nat} {d : D} (hg : g < L.threads)
    (hb : b < p.batch) (hhi : g / L.block < tilePrefix p (b + 1) * p.heads)
    (hF : Fits p L g d ns nv) (hs : d.site = .exit false) : False := by
  simp only [Fits, hs] at hF
  obtain ⟨n0, v0, -, R, hE, ⟨h, -, -⟩ | ⟨bal, hBal, hgx, -, -, hn⟩⟩ := hF
  · rw [end_of_work hp hg hb hhi hE] at h
    cases h
  · exact hn rfl (picked_of_pre hp hg ⟨hE, hBal, hgx⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
