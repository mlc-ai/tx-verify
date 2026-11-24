-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocPlainWaiting
public import Lemmas.Snoc.ObjectAppend

@[expose] public section

/-! Checked object-history extensions preserve old dependencies. These are derived
extension lemmas, not extra execution rules. Callers still prove the history transition,
provenance, and coverage when establishing consistency. -/
namespace PTX
open AsyncCopy
noncomputable section

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
    {records : Loc → List (MBarrier.Record Ref)}
    {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- A not-yet-issued instruction cannot already occur in a checked object history. -/
theorem snoc_fresh_object_id (ht : TmaOk X) {m : Loc} {rec : MBarrier.Record Ref}
    (hr : rec ∈ X.objects m) : rec.id ≠ .thread (g, (X.tr g).length) := by
  intro heq
  have hp := object_record_present ht hr
  rw [heq] at hp
  obtain ⟨ev, he⟩ := hp
  have hl := len_of_get he
  simp at hl

end
end
end PTX
