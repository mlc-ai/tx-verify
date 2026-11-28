-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Site

@[expose] public section

/-! # The facts of the rescale window

From the load of the accumulator (pc 2260) to the store of the rescaled words (pc 2328) the data
facts of a state are the generated run's (`Gen/SoftmaxRescale.lean`), as functions of the round's
words and the loaded words (`rsV`). The round's facts are among them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control

noncomputable section
variable {L : Launch}

theorem alphaVal_m (c m mx : Value) : Lib.alphaVal c m mx 1914 = m := by
  rw [Lib.alphaVal, Lib.xFinal_other (by decide)]; simp [Lib.alphaIn]

theorem alphaVal_mx (c m mx : Value) : Lib.alphaVal c m mx 1522 = mx := by
  rw [Lib.alphaVal, Lib.xFinal_other (by decide)]; simp [Lib.alphaIn]

theorem alphaVal_c (c m mx : Value) : Lib.alphaVal c m mx 498 = c := by
  rw [Lib.alphaVal, Lib.xFinal_other (by decide)]; simp [Lib.alphaIn]

/-- The destination registers of the accumulator load (pc 2260). -/
def ovRegs : List Nat := (List.range 64).map (1547 + ·)

theorem zip_mem (v : Vals) {vals : List Value} (hl : vals.length = 64) {r : Nat} (h1 : 1547 ≤ r)
    (h2 : r < 1611) : (r, rsV L {v with ov := vals} r) ∈ ovRegs.zip vals := by
  have hr : r - 1547 < 64 := by omega
  rw [List.mem_iff_getElem?]
  refine ⟨r - 1547, ?_⟩
  simp [ovRegs, rsV, h1, h2, hl, hr]

/-- **The facts after the load**: the round's facts and the loaded words. -/
theorem rs0_of_load (v : Vals) {vals : List Value} (hl : vals.length = 64) :
    ∀ x ∈ Gen.rs_facts0 (rsV L {v with ov := vals}),
      x ∈ ([(498, scaleW L), (1914, v.m)] ++ alphaFacts L v) ++ ovRegs.zip vals := by
  simp only [Gen.rs_facts0, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals first
    | exact fun _ h => nomatch h
    | exact List.mem_append_right _ (zip_mem v hl (by omega) (by omega))
    | (apply List.mem_append_left
       simp [rsV, alphaFacts, alphaVal_c, alphaVal_m, alphaVal_mx])

/-- The round's facts are among those of the start of the rescale run. -/
theorem round_sub_rs0 (v : Vals) :
    ∀ x ∈ [(498, scaleW L), (1914, v.m)] ++ alphaFacts L v, x ∈ Gen.rs_facts0 (rsV L v) := by
  rintro ⟨r, w⟩ hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, alphaFacts,
    Prod.mk.injEq] at hx
  rcases hx with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [Gen.rs_facts0, rsV, alphaVal_c, alphaVal_m, alphaVal_mx]

/-- The round's facts are among those of the end of the rescale run. -/
theorem round_sub_rs2 (v : Vals) :
    ∀ x ∈ [(498, scaleW L), (1914, v.m)] ++ alphaFacts L v, x ∈ Gen.rs_facts2 (rsV L v) := by
  rintro ⟨r, w⟩ hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, alphaFacts,
    Prod.mk.injEq] at hx
  rcases hx with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [Gen.rs_facts2, rsV, alphaVal_c, alphaVal_m, alphaVal_mx]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
