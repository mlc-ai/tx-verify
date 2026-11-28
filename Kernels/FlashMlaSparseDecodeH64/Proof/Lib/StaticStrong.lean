-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Guarded
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
public import Lemmas.Flow.WeakAccess
public import Lemmas.Order.Order

@[expose] public section

/-! # No strong operation

Every memory instruction of the decoded program is weak (a static scan, evaluated once), so no
thread access is strong (`noStrongAccess`, `fires_read_weak`, `fires_write_weak`; the program has
no atomic, `noAtomicEvent`); every tensor store is a plain tile write (`tensorStoreForm`) and
there is no bulk copy (`noCopy`). So no operation is strong at any scope (`not_strongScoped`) and
the strong pairs that `Race` exempts are ordered vacuously (`strongOrdered`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

private theorem noStrongCode : kernel.code.all (fun ins => !strongOp ins.op) = true := by
  decide +kernel

/-- No thread access is strong. -/
theorem noStrongAccess (hX : Consistent l kernel A m X) {i : EvId} {a : Acc} {w : Bool}
    (h : X.Access i a w) : ¬ a.Strong := by
  have hop : ∀ ins ∈ kernel.code, strongOp ins.op = false := fun _ hm => by
    simpa using List.all_eq_true.mp noStrongCode _ hm
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, ⟨pc, he⟩⟩
  · rcases get_source hX he with ⟨_, hu⟩ | ⟨_, ins, _, _, hc, hf⟩
    · cases hu
    exact fires_read_weak hf (hop _ (List.mem_of_getElem? hc))
  · rcases get_source hX he with ⟨_, hu⟩ | ⟨_, ins, _, _, hc, hf⟩
    · cases hu
    exact fires_write_weak hf (hop _ (List.mem_of_getElem? hc))
  · exact (noAtomicEvent hX he).elim

/-- No operation is strong at any scope. -/
theorem not_strongScoped (hX : Consistent l kernel A m X) (r : AsyncCopy.Ref) (a : Acc)
    (g : Nat) : ¬ StrongScoped l X r a g := by
  intro h
  unfold StrongScoped at h
  split at h
  · obtain ⟨⟨w, hw⟩, hs, -⟩ := h
    exact noStrongAccess hX hw hs
  all_goals first
    | (obtain ⟨⟨addr, s, op, hi, hr⟩, -⟩ := h
       rw [(tensorStoreForm hX hi).2.2] at hr
       cases hr)
    | (obtain ⟨s, -, -, hc, -⟩ := h; exact noCopy hX hc)
    | (obtain ⟨s, -, hc, -⟩ := h; exact noCopy hX hc)
    | exact h

/-- **The strong pairs are ordered**: there are none. -/
theorem strongOrdered (hX : Consistent l kernel A m X) : StrongOrdered l X :=
  fun e _ a _ _ _ _ _ ⟨h1, _⟩ => (not_strongScoped hX e a _ h1).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
