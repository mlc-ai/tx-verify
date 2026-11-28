-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataFacts
public import Lemmas.Flow.OutKinds

@[expose] public section

/-! # Lookups in the chain of data facts

The facts of a site are a run's end facts followed by the registers still live (`factsFrom`). A
register in `K` that is live and is no key of the run's facts keeps its value (`lk_frame`); a key
of the run's facts has its value (`lk_head`); a register that is no key of the two appended
pair of new words has the value of the facts before them (`lk_snoc2`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof

noncomputable section

theorem lookup_append_none {A B : List (Nat × Value)} {r : Nat} (h : A.lookup r = none) :
    (A ++ B).lookup r = B.lookup r := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    obtain ⟨q, v⟩ := p
    by_cases e : r = q
    · subst e; simp [List.lookup] at h
    · have hb : (r == q) = false := by simpa using e
      simp only [List.cons_append, List.lookup, hb] at h ⊢
      exact ih h

theorem lookup_none_of_notin {A : List (Nat × Value)} {r : Nat} (h : r ∉ A.map Prod.fst) :
    A.lookup r = none := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    obtain ⟨q, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hb : (r == q) = false := by simpa using h.1
    simp only [List.lookup, hb]
    exact ih h.2

theorem lookup_factsFrom_mem {live : List Nat} {V : Nat → Value} {r : Nat} (h : r ∈ live) :
    (factsFrom live V).lookup r = some (V r) := by
  induction live with
  | nil => cases h
  | cons q live ih =>
    by_cases e : r = q
    · subst e; simp [factsFrom]
    · have hm : r ∈ live := (List.mem_cons.mp h).resolve_left e
      have hb : (r == q) = false := by simpa using e
      simp only [factsFrom, List.map_cons, List.lookup, hb] at ih ⊢
      exact ih hm

/-- A live register that is no key of the run's facts keeps its value. -/
theorem lk_frame {A : List (Nat × Value)} {L : List Nat} {V : Nat → Value} {K : List Nat}
    (hsub : ∀ r ∈ K, r ∈ L) (hk : ∀ r ∈ K, r ∉ A.map Prod.fst) {r : Nat} (hr : r ∈ K) :
    lookupD (A ++ factsFrom L V) r = V r := by
  unfold lookupD
  rw [lookup_append_none (lookup_none_of_notin (hk r hr)), lookup_factsFrom_mem (hsub r hr)]
  rfl

/-- A key of the run's facts has its value. -/
theorem lk_head {A B : List (Nat × Value)} {r : Nat} {v : Value} (h : A.lookup r = some v) :
    lookupD (A ++ B) r = v := by
  unfold lookupD
  have : (A ++ B).lookup r = some v := by
    induction A with
    | nil => cases h
    | cons p A ih =>
      obtain ⟨q, w⟩ := p
      by_cases e : r = q
      · subst e; simpa [List.lookup] using h
      · have hb : (r == q) = false := by simpa using e
        simp only [List.cons_append, List.lookup, hb] at h ⊢
        exact ih h
  rw [this]; rfl

/-- Appended words change no other register. -/
theorem lk_snoc {F T : List (Nat × Value)} {r : Nat} (h : r ∉ T.map Prod.fst) :
    lookupD (F ++ T) r = lookupD F r := by
  have hT := lookup_none_of_notin h
  unfold lookupD
  have key : ∀ G : List (Nat × Value), (G ++ T).lookup r = G.lookup r := by
    intro G
    induction G with
    | nil => simpa using hT
    | cons p G ih =>
      obtain ⟨q, w⟩ := p
      by_cases e : r = q
      · subst e; simp [List.lookup]
      · have hb' : (r == q) = false := by simpa using e
        simp only [List.cons_append, List.lookup, hb'] at ih ⊢
        exact ih
  rw [key]

/-- A key of the appended words, not a key of the facts before them, has its value. -/
theorem lk_snoc_head {F T : List (Nat × Value)} {r : Nat} {v : Value} (hF : r ∉ F.map Prod.fst)
    (hT : T.lookup r = some v) : lookupD (F ++ T) r = v := by
  unfold lookupD
  rw [lookup_append_none (lookup_none_of_notin hF), hT]
  rfl

/-- A key of the run's facts has the value the run's facts give. -/
theorem lk_head' {A B : List (Nat × Value)} {r : Nat} (h : (A.lookup r).isSome = true) :
    lookupD (A ++ B) r = lookupD A r := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  rw [lk_head hv]
  unfold lookupD; rw [hv]; rfl

/-- The register `s + c` of a zipped list holds the `c`th word. -/
theorem lookup_range_zip (s : Nat) : ∀ (hs : List Value) (c : Nat) (h : c < hs.length),
    ((List.range' s hs.length).zip hs).lookup (s + c) = some (hs[c]) := by
  intro hs
  induction hs generalizing s with
  | nil => intro c h; simp at h
  | cons a hs ih =>
    intro c h
    cases c with
    | zero => simp [List.range'_succ]
    | succ c =>
      have hne : (s + (c + 1) == s) = false := by simp
      rw [List.length_cons, List.range'_succ]
      simp only [List.zip_cons_cons, List.lookup, hne]
      have := ih (s + 1) c (by simpa using h)
      rw [show s + 1 + c = s + (c + 1) by omega] at this
      simpa using this

theorem lookup_isSome_of_mem {A : List (Nat × Value)} {r : Nat} (h : r ∈ A.map Prod.fst) :
    (A.lookup r).isSome = true := by
  induction A with
  | nil => simp at h
  | cons p A ih =>
    obtain ⟨q, w⟩ := p
    by_cases e : r = q
    · subst e; simp [List.lookup]
    · have hb : (r == q) = false := by simpa using e
      have hm : r ∈ A.map Prod.fst := by simpa [e] using h
      simp only [List.lookup, hb]
      exact ih hm

/-- A register that is a key of the run's facts has the run's value. -/
theorem lk_head_mem {A B : List (Nat × Value)} {r : Nat} (h : r ∈ A.map Prod.fst) :
    lookupD (A ++ B) r = lookupD A r :=
  lk_head' (lookup_isSome_of_mem h)

/-- A register that is no key of the first part has the second's value. -/
theorem lk_skip {A B : List (Nat × Value)} {r : Nat} (h : r ∉ A.map Prod.fst) :
    lookupD (A ++ B) r = lookupD B r := by
  unfold lookupD
  rw [lookup_append_none (lookup_none_of_notin h)]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
