-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Table
public import Lemmas.Kernel.Counted
public import Lemmas.Flow.Glue
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # Facts kept along a followed thread, and the thread's last followed state

A proof tool (it replaces `Lemmas/Kernel/SmallInv.lean` and tml-fa4's `Proof2/Lib/StateInv.lean`
and `Proof2/Lib/EndState.lean`). A fact that following does not need is proved after following,
as a theorem of its own, rather than as a field of a role's reference invariant. One induction
over the run (`small_inv`) carries all of them:

* `small_inv`: a fact that depends only on a view of the state (`Respects`) is kept by every
  transition that leaves the view unchanged (`frame`), so it needs proofs only at the transitions
  marked as writing, given a table that says the other transitions leave the view unchanged
  (`Table`);
* `RoleTable.stateInv`: a predicate of a thread's machine states that holds at the first state
  and is kept by every step from a followed state of the table (with its invariant, its sub-step
  invariant, the event's shape and the successor's invariant) holds at every state of the thread;
* `RoleTable.roleInv`: its form for one role of a glued, counted machine (`Code.glue` with
  `Code.counted`): a predicate of the role's state and the ledger that holds when the role is
  entered and is kept by the role's steps holds at every state of the role;
* `Ledger.rel_step`: a linear relation between ledger counts is kept by an event whose class
  indicators satisfy it (the form-A fact of a role's ledger).

The end of a thread's trace: a thread whose machine stops only at an exit has a followed state at
the end of its trace, or just before its final exit (`end_state`); a count of a class the exit is
not in is the count at that state (`end_countP`). For a role table this state satisfies the
table's invariant (`RoleTable.end_ref`), and with a ghost ledger the count is the ledger's
(`RoleTable.end_ledger`). The thread's liveness premise (`hlive`: the machine stops only at an
exit) follows from the table's death obligation (`RoleTable.live_of_ok`) or from a role's own
liveness theorem. -/

namespace PTX.Frame

open PTX PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-! ### One induction over the run -/

section small
variable {C : (g : Nat) → Flow.Code K A L g} {X : Execution} {g : Nat}

/-- `P` depends only on the view `view`. -/
def Respects {D V : Type} (P : D → Prop) (view : D → V) : Prop :=
  ∀ d d', view d = view d' → P d → P d'

/-- **The frame lemma**: a transition that leaves the view unchanged keeps a fact that depends only
on the view. -/
theorem frame {D V : Type} {P : D → Prop} {view : D → V} (hP : Respects P view) {d d' : D}
    (hv : view d' = view d) (h : P d) : P d' :=
  hP d d' hv.symm h

/-- **The table**: every transition of the run that is not marked as writing leaves the view
unchanged. -/
def Table (C : (g : Nat) → Flow.Code K A L g) (X : Execution) (g : Nat) {V : Type}
    (view : (C g).D → V) (writes : (C g).D → Event → Prop) : Prop :=
  ∀ k d e d', stateAt C X g k = some (some d) → (X.tr g)[k]? = some e →
    (C g).next d e = some (some d') → ¬ writes d e → view d' = view d

/-- **A small invariant**: a fact that holds at the start, depends only on a view, is kept by the
transitions marked as writing, and whose view the other transitions leave unchanged, holds at
every state of a followed run. -/
theorem small_inv (J : ∀ g, (C g).D → Prop) {V : Type} (P : (C g).D → Prop)
    (view : (C g).D → V) (writes : (C g).D → Event → Prop)
    (hfol : ∀ k, FollowedAt C J X g k) (hP : Respects P view) (h0 : P (C g).init)
    (htab : Table C X g view writes)
    (hstep : ∀ k d e d', stateAt C X g k = some (some d) → (X.tr g)[k]? = some e → J g d →
      (C g).next d e = some (some d') → writes d e → P d → P d') :
    ∀ k d, stateAt C X g k = some (some d) → P d := by
  intro k
  induction k with
  | zero => intro d hd; rw [stateAt_zero] at hd; cases hd; exact h0
  | succ k ih =>
    intro d hd
    by_cases hk : k < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      rw [stateAt_succ he] at hd
      cases hs : stateAt C X g k with
      | none => rw [hs] at hd; cases hd
      | some σ =>
        cases σ with
        | none => exact absurd hs (hfol k).1
        | some d0 =>
          rw [hs] at hd
          change (C g).next d0 e = some (some d) at hd
          have hP0 := ih d0 hs
          by_cases hw : writes d0 e
          · exact hstep k d0 e d hs he ((hfol k).2 d0 hs) hd hw hP0
          · exact frame hP (htab k d0 e d hs he hd hw) hP0
    · rw [stateAt_of_le (by omega)] at hd
      exact ih d (by rw [stateAt_of_le (by omega)]; exact hd)

end small

variable {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

/-- **A state predicate kept by every step of a followed thread holds at all its states.** -/
theorem RoleTable.stateInv (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
    (hT : T.ShapeOk S) (hF : T.Followed X S) {P : ∀ g, (C g).D → Prop} {g : Nat} (hg : S g)
    (h0 : P g (C g).init)
    (hstep : ∀ d e d', T.J g d → (C g).inv d → T.Ev g d e → P g d →
      (C g).next d e = some (some d') → T.J g d' → P g d') :
    ∀ k d, stateAt C X g k = some (some d) → P g d :=
  small_inv T.J (P g) id (fun _ _ => True) (hF g hg) (fun _ _ h hp => by subst h; exact hp) h0
    (fun _ _ _ _ _ _ _ hw => absurd trivial hw) fun k d e d' hσ he _ hn _ hP => by
      obtain ⟨hJ, hi, hev⟩ := RoleTable.ev_at hC hX hT hF hg (show X.get (g, k) = some e
        from he) hσ
      have h1 : stateAt C X g (k + 1) = some (some d') := by
        rw [stateAt_succ he, hσ]; exact hn
      exact hstep d e d' hJ hi hev hP hn ((hF g hg (k + 1)).2 d' h1)

/-! ### One role of a glued, counted machine -/

section role

variable {P : (g : Nat) → Code K A L g} {ι : Type} {R : (g : Nat) → ι → Code K A L g}
  {ex : ∀ g, (P g).D → Option ι} {κ : Type} {cls : Nat → κ → Event → Bool}
  {T' : RoleTable (fun g => (Code.glue (P g) (R g) (ex g)).counted (cls g))}

/-- **A role fact**: a predicate of role `i`'s state and the ledger that holds when the role is
entered (at the thread's first state, or by a step of the first fragment) and is kept by the role's
steps holds at every state of the role along a followed thread. -/
theorem RoleTable.roleInv
    (hC : ∀ g < L.threads, ((Code.glue (P g) (R g) (ex g)).counted (cls g)).Sound)
    (hX : Consistent L K A mem0 X) (hT : T'.ShapeOk S) (hF : T'.Followed X S) {g : Nat}
    (hg : S g) (i : ι) {I : (R g i).D → (κ → Nat) → Prop}
    (hinit : ex g (P g).init = some i → I (R g i).init (fun _ => 0))
    (hentry : ∀ s n e s', T'.J g (.inl s, n) → T'.Ev g (.inl s, n) e →
      (P g).next s e = some (some s') → ex g s' = some i →
      I (R g i).init (Code.bump (cls g) n e))
    (hstep : ∀ d n e d', T'.J g (.inr ⟨i, d⟩, n) → T'.Ev g (.inr ⟨i, d⟩, n) e → I d n →
      (R g i).next d e = some (some d') → T'.J g (.inr ⟨i, d'⟩, Code.bump (cls g) n e) →
      I d' (Code.bump (cls g) n e)) :
    ∀ k d n, stateAt (fun g => (Code.glue (P g) (R g) (ex g)).counted (cls g)) X g k =
      some (some (.inr ⟨i, d⟩, n)) → I d n := by
  have key := RoleTable.stateInv (T := T') hC hX hT hF
    (P := fun g' σ => ∀ (h : g' = g) d, h ▸ σ = ((Sum.inr ⟨i, d⟩, σ.2) :
      ((Code.glue (P g) (R g) (ex g)).counted (cls g)).D) → I d (h ▸ σ).2) hg ?_ ?_
  · intro k d n hk
    exact key k _ hk rfl d rfl
  · rintro (h : g = g) d hd
    simp only at hd
    change (Code.enter (P g) (R g) (ex g) (P g).init, fun _ => 0) = (Sum.inr ⟨i, d⟩, _) at hd
    simp only [Prod.mk.injEq] at hd
    obtain ⟨he, -⟩ := hd
    unfold Code.enter at he
    split at he
    · rename_i j hj
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at he
      obtain ⟨rfl, hd⟩ := he
      cases eq_of_heq hd
      exact hinit hj
    · cases he
  · rintro ⟨σ1, n⟩ e ⟨σ1', n'⟩ hJ hi hev hI hn hJ' (h : g = g) d hd
    simp only at hd ⊢
    obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := Code.glue (P g) (R g) (ex g)) hn
    simp only [Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    rcases σ1 with s | ⟨j, d0⟩
    · simp only [Code.glue] at h1
      cases hs : (P g).next s e with
      | none => rw [hs] at h1; cases h1
      | some o =>
        cases o with
        | none => rw [hs] at h1; cases h1
        | some s' =>
          rw [hs] at h1
          simp only [Option.map_some, Option.some.injEq] at h1
          unfold Code.enter at h1
          split at h1
          · rename_i j hj
            simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h1
            obtain ⟨rfl, hd⟩ := h1
            cases eq_of_heq hd
            exact hentry s n e s' hJ hev hs hj
          · cases h1
    · simp only [Code.glue] at h1
      cases hr : (R g j).next d0 e with
      | none => rw [hr] at h1; cases h1
      | some o =>
        cases o with
        | none => rw [hr] at h1; cases h1
        | some d1 =>
          rw [hr] at h1
          simp only [Option.map_some, Option.some.injEq, Sum.inr.injEq, Sigma.mk.inj_iff] at h1
          obtain ⟨rfl, hd⟩ := h1
          cases eq_of_heq hd
          exact hstep d0 n e d1 hJ hev (hI rfl d0 rfl) hr hJ'

end role

/-! ### The last followed state of a thread -/

section endstate
variable {C : (g : Nat) → Flow.Code K A L g} {g : Nat}

/-- **The last followed state**: at the end of the trace, or before the trace's final exit. -/
theorem end_state (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (ht : ∀ k, stateAt C X g k ≠ some none)
    (hlive : ∀ k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) →
      (C g).next d e = none → e.kind = .exit) :
    ∃ k d, stateAt C X g k = some (some d) ∧ (k = (X.tr g).length ∨
      (k + 1 = (X.tr g).length ∧ ∃ pc, X.get (g, k) = some ⟨pc, .exit⟩)) := by
  cases hs : stateAt C X g (X.tr g).length with
  | some σ =>
    cases σ with
    | none => exact absurd hs (ht _)
    | some d => exact ⟨_, d, hs, .inl rfl⟩
  | none =>
    -- the first stop: a followed state whose successor along its event is `none`
    have hstop : ∀ n, stateAt C X g n = none →
        ∃ i d, i < n ∧ stateAt C X g i = some (some d) ∧ stateAt C X g (i + 1) = none := by
      intro n
      induction n with
      | zero => intro h; rw [stateAt_zero] at h; cases h
      | succ n ih =>
        intro h
        cases hn : stateAt C X g n with
        | none =>
          obtain ⟨i, d, hi, h1, h2⟩ := ih hn
          exact ⟨i, d, by omega, h1, h2⟩
        | some σ =>
          cases σ with
          | none => exact absurd hn (ht n)
          | some d => exact ⟨n, d, by omega, hn, h⟩
    obtain ⟨i, d, hi, h1, h2⟩ := hstop _ hs
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i]? = some e := ⟨_, List.getElem?_eq_getElem hi⟩
    rw [stateAt_succ he, h1] at h2
    have hk := hlive i d e he h1 h2
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    exact ⟨i, d, h1, .inr ⟨Execution.exit_last hX hg he, pc, he⟩⟩

/-- **A count at the end of a trace is the count at its last followed state**, for a class
without the exit. -/
theorem end_countP (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (ht : ∀ k, stateAt C X g k ≠ some none)
    (hlive : ∀ k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) →
      (C g).next d e = none → e.kind = .exit) :
    ∃ k d, stateAt C X g k = some (some d) ∧ k ≤ (X.tr g).length ∧
      ∀ P : Event → Bool, (∀ pc, P ⟨pc, .exit⟩ = false) →
        (X.tr g).countP P = ((X.tr g).take k).countP P := by
  obtain ⟨k, d, hd, hk⟩ := end_state hX hg ht hlive
  refine ⟨k, d, hd, by omega, fun P hP => ?_⟩
  rcases hk with rfl | ⟨hk, pc, he⟩
  · rw [List.take_length]
  · conv_lhs => rw [← List.take_length (l := X.tr g), ← hk, List.take_add_one]
    have he' : (X.tr g)[k]? = some ⟨pc, .exit⟩ := he
    rw [he']
    simp [List.countP_append, hP]

end endstate

/-- **The table's death obligation gives a thread's liveness**: a followed thread of `S` stops
only at an exit. -/
theorem RoleTable.live_of_ok (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
    (hO : T.Ok S) (hF : T.Followed X S) {g : Nat} (hg : S g) :
    ∀ k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) →
      (C g).next d e = none → e.kind = .exit := fun _ d e he hσ hn => by
  obtain ⟨hJ, hi, hev⟩ := RoleTable.ev_at hC hX hO.toShapeOk hF hg he hσ
  exact hO.death g hg d e hi hJ hev hn

/-- **The last followed state of a followed thread satisfies the table's invariant**, and every
count of a class without the exit is the count at that state. -/
theorem RoleTable.end_ref (hX : Consistent L K A mem0 X) (hF : T.Followed X S) {g : Nat}
    (hg : S g) (hgt : g < L.threads)
    (hlive : ∀ k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) →
      (C g).next d e = none → e.kind = .exit) :
    ∃ k d, stateAt C X g k = some (some d) ∧ T.J g d ∧ k ≤ (X.tr g).length ∧
      ∀ P : Event → Bool, (∀ pc, P ⟨pc, .exit⟩ = false) →
        (X.tr g).countP P = ((X.tr g).take k).countP P := by
  obtain ⟨k, d, hd, hk, hc⟩ := end_countP hX hgt (fun k => (hF g hg k).1) hlive
  exact ⟨k, d, hd, (hF g hg k).2 d hd, hk, hc⟩

/-- **The ledger at the last followed state is the whole trace's count**, for a counted machine
and a class that does not count the exit. -/
theorem RoleTable.end_ledger {D : (g : Nat) → Code K A L g} {κ : Type}
    {cls : Nat → κ → Event → Bool} {T : RoleTable fun g => (D g).counted (cls g)}
    (hX : Consistent L K A mem0 X) (hF : T.Followed X S) {g : Nat} (hg : S g)
    (hgt : g < L.threads)
    (hlive : ∀ k d e, X.get (g, k) = some e →
      stateAt (fun g => (D g).counted (cls g)) X g k = some (some d) →
      ((D g).counted (cls g)).next d e = none → e.kind = .exit) :
    ∃ k d, stateAt (fun g => (D g).counted (cls g)) X g k = some (some d) ∧ T.J g d ∧
      k ≤ (X.tr g).length ∧
      ∀ c, (∀ pc, cls g c ⟨pc, .exit⟩ = false) → (X.tr g).countP (cls g c) = d.2 c := by
  obtain ⟨k, d, hd, hJ, hk, hc⟩ := RoleTable.end_ref hX hF hg hgt hlive
  exact ⟨k, d, hd, hJ, hk, fun c hx => (hc _ hx).trans (count_eq hd c).symm⟩

/-! ### Ledger relations -/

/-- One for an event of a class. -/
abbrev ind (b : Bool) : Nat := if b then 1 else 0

/-- **A linear relation between ledger counts is kept** by an event whose class indicators
satisfy it: `n a = Σ n b + k` before, and `ind a = Σ ind b` for the event, give the relation
after the event. -/
theorem Ledger.rel_step {κ : Type} (cls : κ → Event → Bool) (n : κ → Nat) (e : Event) (a : κ)
    (bs : List κ) (k : Nat) (h : n a = (bs.map n).sum + k)
    (hi : ind (cls a e) = (bs.map fun b => ind (cls b e)).sum) :
    Code.bump cls n e a = (bs.map (Code.bump cls n e)).sum + k := by
  have hb : bs.map (Code.bump cls n e) = bs.map (fun b => n b + ind (cls b e)) := rfl
  rw [hb, List.sum_map_add, ← hi]
  show n a + ind (cls a e) = _
  omega

end PTX.Frame
