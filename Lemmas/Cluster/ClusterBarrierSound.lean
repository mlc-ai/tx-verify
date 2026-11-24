-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Cluster.ClusterRecordSnoc
public import Core.Sync.ClusterBarrierHistory

@[expose] public section

/-! Soundness of the cluster barrier object's bookkeeping: arrivals of the current phase
carry the current phase, and recorded generations never exceed the phase. -/

namespace PTX.ClusterBarrier

/-- Bookkeeping invariants of the cluster barrier object, preserved by every action. -/
def Sound (s : State) : Prop :=
  (∀ g ∈ s.arrived, s.lastArrival g = some s.phase) ∧
  (∀ g phase, s.lastArrival g = some phase → phase ≤ s.phase)

theorem sound_empty : Sound {} := by
  simp [Sound]

theorem sound_finish {threads : Nat} {s : State} (hs : Sound s) :
    Sound (finish threads s) := by
  unfold finish
  split
  · refine ⟨by simp,?_⟩
    intro g phase h
    exact (hs.2 g phase h).trans (show s.phase ≤ s.phase+1 by omega)
  · exact hs

theorem sound_perform {threads : Nat} {s t : State} {a : Action}
    (hs : Sound s) (hp : perform threads s a = .done t) : Sound t := by
  cases a with
  | arrive g release =>
    simp only [perform] at hp
    split at hp
    · cases hp
    · split at hp
      · cases hp
      · have hu : Sound { s with
          arrived := insert g s.arrived
          lastArrival := fun h => if h = g then some s.phase else s.lastArrival h } := by
          refine ⟨?_,?_⟩
          · intro h hh
            rcases Finset.mem_insert.mp hh with rfl | hh
            · simp
            · by_cases heq : h = g
              · subst h; simp
              · simpa [heq] using hs.1 h hh
          · intro h phase hla
            by_cases heq : h = g
            · subst h
              change (if g = g then some s.phase else s.lastArrival g) = some phase at hla
              have heq : s.phase = phase := by simpa using hla
              change phase ≤ s.phase
              omega
            · exact hs.2 h phase (by simpa [heq] using hla)
        have hEq := Outcome.done.inj hp
        rw [← hEq]
        exact sound_finish hu
  | wait g =>
    simp only [perform] at hp
    split at hp
    · cases hp
    · split at hp
      · cases hp
      · rename_i phase _
        by_cases hlt : phase < s.phase
        · rw [ite_eq_left hlt] at hp
          rw [← Outcome.done.inj hp]
          exact hs
        · rw [ite_eq_right hlt] at hp; cases hp
  | exit g =>
    simp only [perform] at hp
    split at hp
    · cases hp
    · rw [← Outcome.done.inj hp]
      exact sound_finish hs

/-! ## Lifting a per-action relation to records and runs -/

/-- The object actions a record performs. -/
def Record.actions {α : Type} : Record α → List Action
  | .exit g _ => [.exit g]
  | .arrival _ _ release lanes => lanes.map fun p => .arrive p.1 release
  | .wait _ _ lanes => lanes.map fun p => .wait p.1

section Lift
variable {R : State → State → Prop} (hrefl : ∀ s, R s s)
  (htrans : ∀ {s t u}, R s t → R t u → R s u)
include hrefl htrans

/-- A reflexive, transitive relation between object states that each performed action of a list
establishes holds across the list. -/
theorem performAll_lift {threads : Nat} {as : List Action}
    (hstep : ∀ a ∈ as, ∀ s t, perform threads s a = .done t → R s t) {s t : State}
    (hp : performAll threads s as = .done t) : R s t := by
  induction as generalizing s with
  | nil => cases hp; exact hrefl _
  | cons a as ih =>
    simp only [performAll] at hp
    cases hstep' : perform threads s a with
    | blocked => rw [hstep'] at hp; cases hp
    | fault e => rw [hstep'] at hp; cases hp
    | done u =>
      rw [hstep'] at hp
      exact htrans (hstep a (by simp) _ _ hstep') (ih (fun b hb => hstep b (by simp [hb])) hp)

/-- The relation holds across a record when each of its actions establishes it. -/
theorem record_lift {α : Type} {block ctas : Nat} {r : Record α}
    (hstep : ∀ a ∈ r.actions, ∀ s t, perform (block * ctas) s a = .done t → R s t)
    {s t : State} (hp : r.perform block ctas s = .done t) : R s t := by
  cases r with
  | exit g _ =>
    change perform (block * ctas) s (.exit g) = .done t at hp
    exact hstep _ (by simp [Record.actions]) _ _ hp
  | arrival cta warp release lanes =>
    simp only [Record.perform] at hp
    split at hp
    · split at hp
      · cases hp
      exact performAll_lift hrefl htrans hstep hp
    · cases hp
  | wait cta warp lanes =>
    simp only [Record.perform] at hp
    split at hp
    · exact performAll_lift hrefl htrans hstep hp
    · cases hp

/-- The relation holds across a run when each action of each record establishes it. -/
theorem run_lift {α : Type} {block ctas : Nat} {h : List (Record α)}
    (hstep : ∀ r ∈ h, ∀ a ∈ r.actions, ∀ s t, perform (block * ctas) s a = .done t → R s t)
    {s t : State} (hp : run block ctas s h = .done t) : R s t := by
  induction h generalizing s with
  | nil => cases hp; exact hrefl _
  | cons r rs ih =>
    simp only [run] at hp
    cases hstep' : r.perform block ctas s with
    | blocked => rw [hstep'] at hp; cases hp
    | fault e => rw [hstep'] at hp; cases hp
    | done u =>
      rw [hstep'] at hp
      exact htrans (record_lift hrefl htrans (hstep r (by simp)) hstep')
        (ih (fun q hq => hstep q (by simp [hq])) hp)

end Lift

theorem sound_record {α : Type} {block ctas : Nat} {s t : State} {r : Record α}
    (hs : Sound s) (hp : r.perform block ctas s = .done t) : Sound t :=
  record_lift (R := fun s t => Sound s → Sound t) (fun _ h => h) (fun h1 h2 h => h2 (h1 h))
    (fun _ _ _ _ hp hs => sound_perform hs hp) hp hs

theorem sound_run {α : Type} {block ctas : Nat} {s t : State} {h : List (Record α)}
    (hs : Sound s) (hp : run block ctas s h = .done t) : Sound t :=
  run_lift (R := fun s t => Sound s → Sound t) (fun _ h => h) (fun h1 h2 h => h2 (h1 h))
    (fun _ _ _ _ _ _ hp hs => sound_perform hs hp) hp hs

/-- The thread arrived in the open phase: another arrival before completion is a fault. -/
def Locked (g : Nat) (s : State) : Prop := g ∈ s.arrived

theorem finish_exited (threads : Nat) (s : State) :
    (finish threads s).exited = s.exited := by
  unfold finish
  split <;> rfl

theorem perform_arrive_eq {threads g : Nat} {release : Bool} {s t : State}
    (hp : perform threads s (.arrive g release) = .done t) :
    t = finish threads { s with
      arrived := insert g s.arrived
      lastArrival := fun h => if h = g then some s.phase else s.lastArrival h } := by
  simp only [perform] at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · exact (Outcome.done.inj hp).symm

theorem perform_arrive_not_locked {threads g : Nat} {release : Bool} {s t : State}
    (hp : perform threads s (.arrive g release) = .done t) : ¬ Locked g s := by
  simp only [perform] at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · assumption

theorem perform_arrive_other_last {threads g j : Nat} {release : Bool} {s t : State}
    (hne : g ≠ j) (hp : perform threads s (.arrive j release) = .done t) :
    t.lastArrival g = s.lastArrival g := by
  rw [perform_arrive_eq hp,finish_lastArrival]
  simp [hne]

theorem perform_arrive_own_last {threads g : Nat} {release : Bool} {s t : State}
    (hp : perform threads s (.arrive g release) = .done t) :
    t.lastArrival g = some s.phase := by
  rw [perform_arrive_eq hp,finish_lastArrival]
  simp

/-- A performed collective arrival has no lane that already arrived in the open phase. -/
theorem record_arrive_not_locked {α : Type} {block ctas cta warp : Nat} {release : Bool}
    {lanes : List (Nat × α)} {s t : State}
    (hp : Record.perform block ctas s (.arrival cta warp release lanes) = .done t) :
    ∀ g ∈ lanes.map Prod.fst, ¬ Locked g s := by
  intro g hg hl
  simp only [Record.perform] at hp
  split at hp
  · split at hp
    · cases hp
    · rename_i hany
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hg
      exact hany (List.any_eq_true.mpr ⟨p, hp', decide_eq_true hl⟩)
  · cases hp

end PTX.ClusterBarrier

/-! ## Replies of waits and exits, and phase monotonicity -/

namespace PTX.ClusterPhase
open PTX ClusterBarrier

theorem perform_wait_eq {threads j : Nat} {s t : State}
    (hp : perform threads s (.wait j) = .done t) :
    t = s := by
  simp only [perform] at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · split at hp
      · exact (Outcome.done.inj hp).symm
      · cases hp

theorem perform_exit_eq {threads j : Nat} {s t : State}
    (hp : perform threads s (.exit j) = .done t) :
    t = finish threads { s with exited := insert j s.exited } := by
  simp only [perform] at hp
  split at hp
  · cases hp
  · exact (Outcome.done.inj hp).symm

theorem perform_wait_info {threads g : Nat} {s t : State}
    (hp : perform threads s (.wait g) = .done t) :
    ∃ phase, s.lastArrival g = some phase ∧ phase < s.phase := by
  simp only [perform] at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · rename_i phase hl
      split at hp
      · rename_i hlt
        exact ⟨phase, hl, hlt⟩
      · cases hp

theorem performAll_wait_info {threads : Nat} {gs : List Nat} {s t : State}
    (hp : performAll threads s (gs.map Action.wait) = .done t) :
    ∀ g ∈ gs, ∃ phase, s.lastArrival g = some phase ∧ phase < s.phase := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, performAll] at hp
    cases hstep : perform threads s (.wait g) with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      have hu := perform_wait_eq hstep
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact perform_wait_info hstep
      · obtain ⟨phase, hphase, hlt⟩ := ih hp j hj
        subst hu
        exact ⟨phase, hphase, hlt⟩

theorem finish_phase_ge (threads : Nat) (s : State) {p : Nat} (hp : s.phase = p) :
    p ≤ (finish threads s).phase := by
  subst hp
  unfold finish
  split <;> simp

theorem perform_phase_le {threads : Nat} {s t : State} {a : Action}
    (hp : perform threads s a = .done t) : s.phase ≤ t.phase := by
  cases a with
  | arrive g rel => rw [perform_arrive_eq hp]; exact finish_phase_ge _ _ rfl
  | wait g => rw [perform_wait_eq hp]
  | exit g => rw [perform_exit_eq hp]; exact finish_phase_ge _ _ rfl

theorem run_phase_le {α : Type} {block ctas : Nat} {s t : State} {h : List (Record α)}
    (hp : run block ctas s h = .done t) : s.phase ≤ t.phase :=
  run_lift (R := fun s t => s.phase ≤ t.phase) (fun _ => le_rfl) le_trans
    (fun _ _ _ _ _ _ hp => perform_phase_le hp) hp

end PTX.ClusterPhase
