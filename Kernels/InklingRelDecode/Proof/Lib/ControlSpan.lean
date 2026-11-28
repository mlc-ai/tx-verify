-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.Havoc
public import Lemmas.Flow.CtlStepsU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

/-- Only the control facts live at the destination need to survive a silent instruction run. -/
noncomputable def spanCheck (live : Nat → List Nat) (p start stop : Nat) : Bool :=
  (start≤stop && stop≤2856) && (live stop).isSublist (live p) &&
    Havoc.check hooks (live stop) start stop ((kernel.code.drop start).take (stop-start))

theorem control_span {L g live p start stop V} (h : spanCheck live p start stop = true) :
    SegU kernel Assumptions.all L g start (factsFrom (live p) V)
      stop (factsFrom (live stop) V) := by
  obtain ⟨⟨⟨ord,bound⟩,sub⟩,ok⟩ := (by
    simpa only [spanCheck,Bool.and_eq_true,decide_eq_true_eq] using h :
    ((start≤stop ∧ stop≤2856) ∧ (live stop).isSublist (live p) = true) ∧ _)
  apply SegU.of_havoc rulesFrame hooks_ok ord (le_trans bound (by decide +kernel))
  · rwa [factsFrom_keys]
  · intro x hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    exact mem_factsFrom ((List.isSublist_iff_sublist.mp sub).subset hr)

end PTX.Kernels.InklingRelDecode.Proof.Lib
