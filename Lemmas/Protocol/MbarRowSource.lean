-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarRow
public import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.MbarRow
open PTX PTX.Flow

/-- A classified event fired from one of the checked instructions in its region. -/
theorem region_source {K : Kernel} {A : List Assumption} {L : Launch} {m : Mem0}
    {X : Execution} {g k lo hi : Nat} {sites : List Site} {e : Event} {l : Loc}
    (check : regionOk K.code lo hi sites = true) (hX : Consistent L K A m X)
    (he : X.get (g,k) = some e) (hm : Frame.MbarOf e l) (hlo : lo ≤ e.pc) (hhi : e.pc < hi) :
    ∃ s ∈ sites, s.pc = e.pc ∧ ∃ t ins u, t.pc = e.pc ∧ K.code[e.pc]? = some ins ∧
      s.shape.ok ins.op = true ∧ Fires e.pc (eventTmpl A L g t ins.op) e (some u) := by
  have hk := objectKind hm
  obtain ⟨f,hf⟩ | ⟨t,ins,o,ht,hc,hf⟩ := get_source hX he
  · rw [hf] at hk
    exact hk.elim
  have hop : objectOp ins.op = true := by
    cases h : objectOp ins.op
    · exact False.elim (notObject_of_op h hf hk)
    · rfl
  have hin : (ins,e.pc) ∈ K.code.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (by simpa using hc)
  obtain ⟨hall,_⟩ := Bool.and_eq_true_iff.mp check
  have hs := List.all_eq_true.mp hall (ins,e.pc) hin
  simp only [decide_eq_true hlo, decide_eq_true hhi, hop, Bool.and_self, Bool.not_true,
    Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨s,hs,⟨hpc,_⟩,hsh⟩ := hs
  cases o with
  | none => exact False.elim (fires_none_notObject hf hk)
  | some u => exact ⟨s,hs,hpc,t,ins,u,ht,hc,hsh,hf⟩

end PTX.MbarRow
