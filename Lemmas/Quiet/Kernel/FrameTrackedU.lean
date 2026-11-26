-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.FrameTrackedU
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Kernel.NextInOrder

@[expose] public section

/-! # A stopped machine steps under quiet extensions

`Descent.dead_steps_inOrderU` under `Assumption.WfQuiet`. -/

namespace PTX.Frame
open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {m : Mem0} {X : Execution}
  {C : (g : Nat) → Code K A L g} {g k : Nat}

end PTX.Frame

namespace PTX
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

namespace Descent
open PTX.Flow MBarrier AsyncCopy

variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

/-- **A released pending thread whose machine stopped steps** (as `dead_steps`). -/
theorem dead_steps_inOrderUQ {C : (g : Nat) → Flow.Code K A L g}
    (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) {h : Nat}
    (hC : ∀ g < L.threads, (C g).SoundU) (hp : Frame.Pending L X h)
    (hσ : Frame.stateAt C X h (X.tr h).length = none) (hrel : Step.Released L X h) :
    Steps L K A mem0 Obl rank X o := by
  have hX := hmax.1
  obtain ⟨u, hrun⟩ := Frame.run_some hX hub hp
  have hne : X.tr h ≠ [] := by
    rintro hnil
    rw [hnil, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  exact .inl (Step.dead_counted_extension hX hp.1 hne hrel
    (fun _ _ => hA.quiet hX le_snoc rfl (Execution.quietExt_snoc rfl)) hrun
    (Frame.end_deadU hC hp.1 hrun hσ))

end Descent

end

end PTX
