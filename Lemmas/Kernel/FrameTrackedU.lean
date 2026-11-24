-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.FrameU
public import Lemmas.Kernel.NextInOrder

@[expose] public section
namespace PTX.Frame
open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {m : Mem0} {X : Execution}
  {C : (g : Nat) → Code K A L g} {g k : Nat}

theorem state_of_noUbU (hC : ∀ g < L.threads, (C g).SoundU)
    (hX : Consistent L K A m X) (ht : Tracked C X) (hub : ¬ HasUb X) {e : Event}
    (he : X.get (g,k) = some e) : ∃ d, stateAt C X g k = some (some d) := by
  rcases firedU hC hX he with ⟨σ,_,hs,_⟩ | ⟨_,pc,f,rfl⟩
  · cases σ with
    | none => exact (ht g k (lt_of_get hX he) hs).elim
    | some d => exact ⟨d,hs⟩
  · exact (hub ⟨_,pc,f,he⟩).elim

theorem end_deadU (hC : ∀ g < L.threads, (C g).SoundU) (hg : g < L.threads) {t : TState}
    (hr : Run K A L g {} (X.tr g) (some t)) (hσ : stateAt C X g (X.tr g).length = none) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  rw [stateAt_end] at hσ
  exact (hC g hg).machine.final_dead hr ((Code.after_eqU (C := C g) (some (C g).init) (X.tr
      g)).trans hσ)

end PTX.Frame

namespace PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

namespace Descent

open PTX.Flow MBarrier AsyncCopy

variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

/-- **A released pending thread whose machine stopped steps** (as `dead_steps`). -/
theorem dead_steps_inOrderU {C : (g : Nat) → Flow.Code K A L g}
    (hA : Assumption.WfStep sel L K mem0 A)
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
    (fun _ _ => hA.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl)) hrun
    (Frame.end_deadU hC hp.1 hrun hσ))

end Descent
end
end PTX
