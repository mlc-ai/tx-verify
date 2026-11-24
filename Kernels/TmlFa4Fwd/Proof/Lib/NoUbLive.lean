-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed
import Lemmas.Kernel.FrameStop

@[expose] public section

/-! # No undefined behaviour from a followed thread, death clause on defined events (library
candidate)

`Lemmas/Kernel/Safety/NoUb.lean`'s `noUb_of_followed` asks its `live` obligation at every event,
undefined behaviour included, where a machine always dies; this variant asks it only at events that
are no undefined behaviour (which `safe` gives first), so it is the form a role can meet. Lane L:
replace the library statement by this one (it assumes less).

`RoleTable.noUb` (`Lemmas/Kernel/Safety/Table.lean`) asks its `safe` and `death` obligations at
every state that satisfies the invariant, with no execution in context. A role whose invariant
holds only while no event so far was undefined behaviour (tml-fa4's `Ref`s are guarded by
`n .ub = 0`), or whose machine dies at a read whose bytes do not rebuild (the bytes' source is an
execution fact), cannot state them that way. `noUb_of_followed_live` takes the two obligations
at the followed states of one thread's events instead, in the execution: the event is no undefined
behaviour (`safe`), and the machine dies at it only if it is an exit (`live`). Then no event of
the thread is undefined behaviour: an event fired from a followed state is not, by `safe`, and a
dead machine (whose events are undefined behaviour, `Frame.fired`) died at an earlier event,
which by `live` was an exit, the thread's last event. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
variable {C : (g : Nat) → Code K A L g} {J : ∀ g, (C g).D → Prop} {X : Execution}

/-- **No event of a followed thread is undefined behaviour**, given that no event fired from a
followed state is, and that the machine dies at such an event only if it is an exit. -/
theorem noUb_of_followed_live (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X)
    {g : Nat} (hF : ∀ k, FollowedAt C J X g k)
    (safe : ∀ k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      ∀ f, e.kind ≠ .ub f)
    (live : ∀ k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      (∀ f, e.kind ≠ .ub f) → (C g).next d e = none → e.kind = .exit)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f := by
  rcases fired (C := C) hC hX he with ⟨σ, o, hσ, -⟩ | ⟨hσ, -⟩
  · cases σ with
    | none => exact absurd hσ (hF k).1
    | some d => exact safe k d e he hσ ((hF k).2 d hσ) f
  · obtain ⟨i, d, hik, hi, hi'⟩ := first_stop_any (C := C) (X := X) (g := g) (.inl hσ)
    have hlen : i < (X.tr g).length := by
      by_contra hn
      rw [stateAt_of_le (by omega)] at hi
      rw [stateAt_of_le (by omega), hi] at hi'
      simp at hi'
    obtain ⟨ei, hei⟩ : ∃ ei, X.get (g, i) = some ei := ⟨_, List.getElem?_eq_getElem hlen⟩
    rcases hi' with hn | hn
    · rw [stateAt_succ hei, hi] at hn
      obtain ⟨pc, kd⟩ := ei
      have hx := live i d _ hei hi ((hF i).2 d hi) (safe i d _ hei hi ((hF i).2 d hi)) hn
      simp only at hx
      subst hx
      obtain ⟨r, hr⟩ := hX.thr g (lt_of_get hX he)
      have h1 := Flow.Run.end_last hr hei (.inr rfl)
      have h2 : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
      omega
    · exact absurd hn (hF (i + 1)).1

end

end PTX.Frame
