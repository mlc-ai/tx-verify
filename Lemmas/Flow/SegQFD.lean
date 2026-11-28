-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFCode

@[expose] public section

/-! # Typed runs whose end table is the start table with a delta

The table at the end of a piece is `Δ ++ qt a`: the entries of the registers the piece wrote,
in front of the table at its start. `checkD` tests only the entries of `Δ` against the abstract
run and that every written register has an entry of `Δ` or none in `qt a`, so its cost follows the
delta, not the table. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
  {abs : EnvF → Op → Option (List (Nat × TagF))}

/-- The check of a piece whose end table is `Δ ++ qt a`. -/
def checkD (abs : EnvF → Op → Option (List (Nat × TagF))) (env : EnvF) (Δ : EnvF)
    (ops : List Instr) (W : List Nat) : Bool :=
  match runF abs env ops with
  | none => false
  | some (e, w) => Δ.all (fun p => TagF.sat (e.lookup p.1) p.2) && decide (w = W) &&
      W.all (fun r => Δ.any (fun p => p.1 == r) || env.lookup r == none)

theorem checkD_ops {env Δ : EnvF} {ops ops' : List Instr} {W : List Nat} (hops : ops' = ops)
    (h : checkD abs env Δ ops W = true) : checkD abs env Δ ops' W = true := hops ▸ h

theorem lookup_some_of_any {Δ : EnvF} {r : Nat} (h : Δ.any (fun p => p.1 == r) = true) :
    ∃ x, Δ.lookup r = some x := by
  induction Δ with
  | nil => simp at h
  | cons p ps ih =>
    by_cases hp : (r == p.1) = true
    · exact ⟨p.2, by simp [List.lookup, hp]⟩
    · have hp' : (p.1 == r) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at hp ⊢
        exact fun e => hp e.symm
      simp only [List.any_cons, hp', Bool.false_or] at h
      obtain ⟨x, hx⟩ := ih h
      exact ⟨x, by simpa [List.lookup, hp] using hx⟩

/-- **A piece with a delta table runs**: the registers the abstract run does not write keep their
values, the written ones satisfy the entries of `Δ`. -/
theorem typedD_run {env Δ : EnvF} {W : List Nat} {a b : Nat} {F : List (Nat × Value)}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hA : AbsSound A L g a b abs)
    (hc : checkD abs env Δ ((K.code.drop a).take (b - a)) W = true)
    {t : TState} (ht : At t a F) (hq : TypedF env t) :
    ∃ u, run K A L g (b - a) t = some u ∧ At u b [] ∧ TypedF (Δ ++ env) u ∧
      ∀ r, r ∉ W → u.regs r = t.regs r := by
  obtain ⟨hpc, hsub, hacc, hf, -⟩ := ht
  unfold checkD at hc
  split at hc
  · cases hc
  rename_i e w hrun
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, rfl⟩, hw⟩ := hc
  obtain ⟨u, hu, hpcu, hsu, hau, hfu, htu, hfr⟩ :=
    crossF_aux hlen hA (b - a) a env e w t le_rfl (by omega) hpc hsub hacc hf hq hrun
  refine ⟨u, hu, ⟨hpcu, hsu, hau, hfu, trivial⟩, ?_, fun r hr => hfr r hr⟩
  intro r tg hl
  rcases lookup_append_some hl with h1 | ⟨h1, h2⟩
  · exact TagF.sat_ok (v := u.regs r) (need := tg) (h := e.lookup r)
      (by simpa using hs (r, tg) (lookup_mem' h1)) (fun tg' h' => htu r tg' h')
  · have hrw : r ∉ w := fun hm => by
      have := hw r hm
      simp only [Bool.or_eq_true] at this
      rcases this with h | h
      · obtain ⟨x, hx⟩ := lookup_some_of_any h
        rw [hx] at h1
        cases h1
      · simp [h2] at h
    rw [hfr r hrw]
    exact hq r tg h2

/-- **A typed piece whose end table is `Δ ++ qt a` is a strict segment.** -/
theorem segQFD_run (qt : Nat → EnvF) {Δ : EnvF} {W : List Nat} {a b : Nat}
    {F G : List (Nat × Value)} (hab : a ≤ b) (hlen : b ≤ K.code.length)
    (hA : AbsSound A L g a b abs) (hq : qt b = Δ ++ qt a)
    (hc : checkD abs (qt a) Δ ((K.code.drop a).take (b - a)) W = true)
    (hw : ∀ p ∈ G, p.1 ∉ W) (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QTF qt) a F b G := by
  intro t ht hq0
  have hq' : TypedF (qt a) t := by simpa [QTF, ht.1] using hq0
  obtain ⟨u, hu, hAt, hQ, hk⟩ := typedD_run hab hlen hA hc ht hq'
  refine ⟨u, run_rtg hu,
    ⟨hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, Havoc.holds_of_forall fun p hp => ?_⟩, ?_⟩
  · rw [hk p.1 (hw p hp)]
    exact holds_mem ht.2.2.2.2 (hG p hp)
  · unfold QTF
    rw [hAt.1, hq]
    exact hQ

end PTX.Flow.TyG
