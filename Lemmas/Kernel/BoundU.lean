-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Bound
public import Lemmas.Kernel.FrameU
import Lemmas.Flow.UbStop

@[expose] public section
namespace PTX.Frame
open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : ∀ g, Code K A L g}

/-- Bound counted events on a relaxed thread. A continuing concrete event excludes UB,
so the rank condition only needs the invariant at defined events. -/
theorem count_leU {X : Execution} {g : Nat} (hC : ∀ g < L.threads, (C g).SoundU)
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) (ht : Tracked C X)
    (rank : (C g).D → Nat) (reset : Event → Bool) (budget : Nat)
    (hdec : ∀ k d d' e, (X.tr g)[k]? = some e → stateAt C X g k = some (some d) → (C g).inv d →
      (∀ f, e.kind ≠ .ub f) →
      (C g).next d e = some (some d') →
      rank d' + (if e.counts then 1 else 0) ≤ rank d + (if reset e then budget else 0)) :
    (X.tr g).countP Event.counts ≤ rank (C g).init + 2 + budget * (X.tr g).countP reset := by
  let r : (C g).toMachineU.St → Nat := fun σ => match σ with
    | some d => rank d
    | none => 0
  exact Machine.Trace.count_le_resets_at r reset budget (traceU hC hX hg)
    fun k e σ1 σ2 u he h1 h2 hf => by
      have hu : ∀ f, e.kind ≠ .ub f := by
        obtain ⟨t, _, fire⟩ := hf
        intro f hk
        have ht := fires_ub fire hk
        rw [ht] at fire
        exact absurd fire.2 (by simp)
      rw [Code.after_eqU] at h1 h2
      have h1' : stateAt C X g k = some σ1 := h1
      have h2' : stateAt C X g (k + 1) = some σ2 := h2
      rw [stateAt_succ he, h1'] at h2'
      cases σ1 with
      | none => exact absurd h1' (ht g k hg)
      | some d =>
        cases σ2 with
        | none =>
          refine absurd ?_ (ht g (k + 1) hg)
          rw [stateAt_succ he, h1']
          exact h2'
        | some d' =>
          obtain ⟨-, -, -, hinv, -⟩ := fired_site_ofU hC hg hf hu
          exact hdec k d d' e he h1' hinv hu h2'

end PTX.Frame
