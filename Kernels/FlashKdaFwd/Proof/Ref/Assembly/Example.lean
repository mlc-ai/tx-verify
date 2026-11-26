-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked

@[expose] public section

/-!
# A worked example of the case principle

How a fact about an event of a thread is proved from the chain. The statement: **a matrix
event is made by a compute thread, at a state of the Compute phase** (with the phase's entry
and invariant, which is what the Compute phase's exports for the matrix fields of the contracts
take). The proof has the three steps of every such proof:

1. `event_stage` (`Tracked.lean`): an event that is not undefined behaviour fires from a
   followed state, and that state is in a stage;
2. `Ref/Kinds.lean`: an event of a kind is fired only at a site of that kind (here
   `not_class_of_kind` with `firedOnly_isMatrix`);
3. `Sites.lean`: the instruction of the site decides the stage and the role (here
   `Stage.of_pc_compute`), which hands over the phase's invariant.

A proof by cases looks the same with `cases hst with | startup hI => … | …` in step 3 and
one export of each phase; `Sites.lean: Stage.bar0` is such a proof (the field `bar0` of the
progress contract, from one `bar0` lemma per phase).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Example
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat}

/-- The sites that fire a matrix event are instructions of the compute loop (2106 to
2944). -/
theorem matrix_site_pc (s : Site) (h : s.kind ∈ matrixKinds) : 2105 < s.pc ∧ s.pc ≤ 2944 := by
  have h1 : ∀ j : Fin 104, 2105 < (Site.warpMma j).pc ∧ (Site.warpMma j).pc ≤ 2944 := by
    decide +kernel
  have h2 : ∀ j : Fin 16, 2105 < (Site.matrixMove j).pc ∧ (Site.matrixMove j).pc ≤ 2944 := by
    decide +kernel
  have h3 : ∀ j : Fin 18, 2105 < (Site.matrixStore j).pc ∧ (Site.matrixStore j).pc ≤ 2944 := by
    decide +kernel
  have h4 : ∀ j : Fin 44, 2105 < (Site.matrixLoad j).pc ∧ (Site.matrixLoad j).pc ≤ 2944 := by
    decide +kernel
  cases s with
  | warpMma j => exact h1 j
  | matrixMove j => exact h2 j
  | matrixStore j => exact h3 j
  | matrixLoadMx j row => exact h4 j
  | _ => simp [Site.kind, matrixKinds] at h

/-- **A matrix event is made by a compute thread at a state of the Compute phase.** -/
theorem matrix_in_compute (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) {e : Event}
    (he : X.get (g, k) = some e) (hm : isMatrix e = true) :
    tid g < 128 ∧ ∃ s j0 s0, At (code L) X g k s ∧ CarryLoadDone P L X g j0 s0 ∧
      Compute.In P L X g j0 s0 ∧ Compute.Inv P L X g j0 k s := by
  -- 1. the event is not undefined behaviour, so it fires from a followed state in a stage
  have hne : ∀ f, e.kind ≠ .ub f := by
    intro f hf
    obtain ⟨pc, kd⟩ := e
    subst hf
    cases hm
  obtain ⟨s, hσ, hst, -⟩ := event_stage hpre hX he hne
  -- 2. `Ref/Kinds`: a matrix event is fired at a matrix site
  have hkind : s.site.kind ∈ matrixKinds := by
    by_contra hκ
    rw [not_class_of_kind (sounds hpre) hX firedOnly_isMatrix he hσ hκ] at hm
    cases hm
  -- 3. `Sites.lean`: the instruction of the site decides the stage and the role
  obtain ⟨h1, h2⟩ := matrix_site_pc s.site hkind
  obtain ⟨hr, j0, s0, past, -, hin, hI⟩ := hst.of_pc_compute h1 h2
  exact ⟨hr, s, j0, s0, hσ, past, hin, hI⟩

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Example
