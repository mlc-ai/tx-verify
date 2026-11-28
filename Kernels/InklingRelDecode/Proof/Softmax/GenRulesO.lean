-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.AlphaAt

@[expose] public section

/-! # The rescale of the accumulator, for generated runs

The lemmas `Tools/out_gen.py` names in `Gen/Out/softmax_rs.json`: at the pcs 2262 to 2325 (the 64
products of the rescale factor and the loaded accumulator words) the assumption list reads the
scalar multiplication as exact (`idealArith`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat}

/-- A pc of the rescale run (pcs 2262 to 2325). -/
def rsPc (pc : Nat) : Bool := decide (2262 ≤ pc ∧ pc < 2326)

private theorem rs_emu {pc : Nat} (hp : rsPc pc = true) :
    Assumptions.emuSites.contains pc = false := by
  simp only [rsPc, decide_eq_true_eq] at hp
  rw [Bool.eq_false_iff]
  intro h
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, he⟩ := h
  omega

theorem rsSegFree {pc : Nat} (hp : rsPc pc = true) : Assumption.SegFreePc Assumptions.all pc :=
  Kernels.InklingRelDecode.Proof.segFree (rs_emu hp)

/-- The multiplication of a pc of the run is read as exact. -/
theorem rule_mulRs {fz : Bool} {d a b : Nat} (pc : Nat) (hp : rsPc pc = true) :
    ∀ t : TState, t.pc = pc → (XItem.base (.mul fz d a b)).Rule Assumptions.all L g t := by
  intro t ht
  subst ht
  have h := rs_emu hp
  simp only [rsPc, decide_eq_true_eq] at hp
  exact ⟨ideal_at (f := .mul .f32) (by simp [idealForms]) h,
    decline_at (f := .mul .f32) (by simp [idealForms]) h (by omega) (by omega) (by omega)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
