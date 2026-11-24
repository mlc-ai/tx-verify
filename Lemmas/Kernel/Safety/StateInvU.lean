-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.TableU
public import Lemmas.Kernel.Safety.StateInv

@[expose] public section

namespace PTX.Frame

open PTX PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

/-- **A predicate of the state and of a count of earlier events, kept by every step of a followed
thread, holds at all its states.** -/
theorem RoleTable.countInvU (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X)
    (hT : T.ShapeOkU S) (hF : T.Followed X S) {g : Nat} (hg : S g) (c : Event → Bool)
    {P : (C g).D → Nat → Prop} (h0 : P (C g).init 0)
    (hstep : ∀ d e d' n, T.J g d → (C g).inv d → T.Ev g d e → P d n →
      (C g).next d e = some (some d') → T.J g d' → P d' (n + if c e then 1 else 0)) :
    ∀ k d, NoUbBefore X g k → stateAt C X g k = some (some d) →
      P d (((X.tr g).take k).countP c) := by
  intro k
  induction k with
  | zero =>
    intro d hu hd
    rw [stateAt_zero] at hd
    cases hd
    simpa using h0
  | succ k ih =>
    intro d hu hd
    by_cases hk : k < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      have hd' := hd
      rw [stateAt_succ he] at hd
      cases hs : stateAt C X g k with
      | none => rw [hs] at hd; cases hd
      | some σ =>
        cases σ with
        | none => exact absurd hs (hF g hg k).1
        | some d0 =>
          rw [hs] at hd
          obtain ⟨hJ, hi, hev⟩ := RoleTable.ev_atU hC hX hT hF hg (show X.get (g, k) = some e
            from he) hs (hu k (Nat.lt_succ_self k) e he)
          have hp := ih d0 (fun j hj => hu j (Nat.lt_succ_of_lt hj)) hs
          have h := hstep d0 e d _ hJ hi hev hp hd ((hF g hg (k + 1)).2 d hd')
          rw [List.take_add_one, he, List.countP_append]
          simpa [List.countP_cons] using h
    · rw [stateAt_of_le (by omega)] at hd
      have h := ih d (fun j hj => hu j (Nat.lt_succ_of_lt hj))
        (by rw [stateAt_of_le (by omega)]; exact hd)
      rw [List.take_of_length_le (by omega)] at h ⊢
      exact h

/-- **A state predicate kept by every step of a followed thread holds at all its states.** -/
theorem RoleTable.stateInvU (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X)
    (hT : T.ShapeOkU S) (hF : T.Followed X S) {P : ∀ g, (C g).D → Prop} {g : Nat} (hg : S g)
    (h0 : P g (C g).init)
    (hstep : ∀ d e d', T.J g d → (C g).inv d → T.Ev g d e → P g d →
      (C g).next d e = some (some d') → T.J g d' → P g d') :
    ∀ k d, NoUbBefore X g k → stateAt C X g k = some (some d) → P g d :=
  RoleTable.countInvU hC hX hT hF hg (fun _ => false) (P := fun d _ => P g d) h0
    (fun d e d' _ => hstep d e d')

/-! ### One role of a glued, counted machine -/

section role

variable {P : (g : Nat) → Code K A L g} {ι : Type} {R : (g : Nat) → ι → Code K A L g}
  {ex : ∀ g, (P g).D → Option ι} {κ : Type} {cls : Nat → κ → Event → Bool}
  {T' : RoleTable (fun g => (Code.glue (P g) (R g) (ex g)).counted (cls g))}

/-- **A role fact**: a predicate of role `i`'s state and the ledger that holds when the role is
entered (at the thread's first state, or by a step of the first fragment) and is kept by the role's
steps holds at every state of the role along a followed thread. -/
theorem RoleTable.roleInvU
    (hC : ∀ g < L.threads, ((Code.glue (P g) (R g) (ex g)).counted (cls g)).SoundU)
    (hX : Consistent L K A mem0 X) (hT : T'.ShapeOkU S) (hF : T'.Followed X S) {g : Nat}
    (hg : S g) (i : ι) {I : (R g i).D → (κ → Nat) → Prop}
    (hinit : ex g (P g).init = some i → I (R g i).init (fun _ => 0))
    (hentry : ∀ s n e s', T'.J g (.inl s, n) → T'.Ev g (.inl s, n) e →
      (P g).next s e = some (some s') → ex g s' = some i →
      I (R g i).init (Code.bump (cls g) n e))
    (hstep : ∀ d n e d', T'.J g (.inr ⟨i, d⟩, n) → T'.Ev g (.inr ⟨i, d⟩, n) e → I d n →
      (R g i).next d e = some (some d') → T'.J g (.inr ⟨i, d'⟩, Code.bump (cls g) n e) →
      I d' (Code.bump (cls g) n e)) :
    ∀ k d n, NoUbBefore X g k →
      stateAt (fun g => (Code.glue (P g) (R g) (ex g)).counted (cls g)) X g k =
      some (some (.inr ⟨i, d⟩, n)) → I d n := by
  have key := RoleTable.stateInvU (T := T') hC hX hT hF
    (P := fun g' σ => ∀ (h : g' = g) d, h ▸ σ = ((Sum.inr ⟨i, d⟩, σ.2) :
      ((Code.glue (P g) (R g) (ex g)).counted (cls g)).D) → I d (h ▸ σ).2) hg ?_ ?_
  · intro k d n hu hk
    exact key k _ hu hk rfl d rfl
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
end PTX.Frame
