-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
public import Lemmas.Quiet.StoreDrainAppend

@[expose] public section

/-! # The assumptions' constraints survive a collective's events on several lanes

The library's warp-collective step appends one event to every lane of a warp (`appendLanes`) and
asks the constraints of the result for events that read no memory, an exit included. Every lane of
a maximal execution has drained its selected stores (`Prog.drained`), so an appended exit is
harmless (`wf_appendLanes`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Appending events that read no memory to several lanes keeps the constraints** when every
lane has drained its selected stores. -/
theorem wf_appendLanes (hX : Consistent L kernel Assumptions.all mem0 X)
    (hd : ∀ g, TensorStore.Drained drainSel X g) (ds : List Nat) (ev : Nat → Event)
    (hev : ∀ x, (ev x).kind.readsMem = false) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.appendLanes ds ev) := by
  intro a ha
  have hold := hX.asm a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hold
    | exact hold.appendLanes fun g _ _ => hd g
    | exact Assumption.commitPerformedAt_extend (fun _ _ => rfl) hold hX.tcCommit
        le_appendLanes (Execution.notifiedInOrder_of_eq (sel := fun _ => true) rfl)
    | (intro f pc' acc bs he hs
       rcases appendLanes_get_cases he with ⟨-, he'⟩ | ⟨-, -, hq⟩
       · exact hold f pc' acc bs he' hs
       · exfalso
         have := hev f.1
         rw [← hq] at this
         simp [Kind.readsMem] at this)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
