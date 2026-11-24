-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.Order

@[expose] public section

namespace PTX
open AsyncCopy
variable {L : Launch} {X Y : Execution} {l : Loc}

/-- Transport direct edges after fixing their byte footprints. Target-dependent
thread-order reflection is sufficient; an unrelated newly appended event is irrelevant. -/
theorem AsyncBefore.congr
    (hc : ∀ i p, AsyncCovers X i p l ↔ AsyncCovers Y i p l)
    (hf : ∀ i p w, AsyncFinished L X i p w ↔ AsyncFinished L Y i p w)
    (ho : ∀ i p w, AsyncOnlyFinished X i p w ↔ AsyncOnlyFinished Y i p w)
    (hb : ∀ j q w, AsyncCovers Y j q l → (baseCausality L X w j ↔ baseCausality L Y w j))
    (hp : ∀ j q w, AsyncCovers Y j q l → (po X w j ↔ po Y w j))
    {a b : EvId × Part} : AsyncBefore L X l a b ↔ AsyncBefore L Y l a b := by
  simp only [AsyncBefore,hc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hcover
  have hh := fun w => hb b.1 b.2 w hcover
  have hpo := fun w => hp b.1 b.2 w hcover
  simp only [hf,ho,hh,hpo]

theorem AsyncChain.left_cover {a b : EvId × Part} (h : AsyncChain L X l a b) :
    AsyncCovers X a.1 a.2 l := by
  induction h with
  | direct h => exact h.1
  | tail _ _ _ ih => exact ih

/-- A composed path still needs a real first completion-observation edge. -/
theorem AsyncChain.first {a b : EvId × Part} (h : AsyncChain L X l a b) :
    ∃ c, AsyncBefore L X l a c := by
  induction h with
  | direct h => exact ⟨_,h⟩
  | tail _ _ _ ih => exact ih

/-- Composition at an actual effect, keeping its identity and the same byte. -/
theorem AsyncChain.trans {a b c : EvId × Part} (hab : AsyncChain L X l a b)
    (hp : X.AsyncPresent b.1 b.2) (hbc : AsyncChain L X l b c) :
    AsyncChain L X l a c := by
  induction hbc with
  | direct h => exact .tail hab hp h
  | tail _ hp' h ih => exact .tail ih hp' h

/-- Transport actual interior effects only where an outgoing edge exists.
This matters when an extension records a new, still-unobserved effect. -/
theorem AsyncChain.map {a b : EvId × Part} (h : AsyncChain L X l a b)
    (hd : ∀ {a b}, AsyncBefore L X l a b → AsyncBefore L Y l a b)
    (hp : ∀ {a b}, X.AsyncPresent a.1 a.2 → AsyncBefore L X l a b →
      Y.AsyncPresent a.1 a.2) : AsyncChain L Y l a b := by
  induction h with
  | direct h => exact .direct (hd h)
  | tail _ hx h ih => exact .tail ih (hp hx h) (hd h)

theorem AsyncChain.congr_on_edges
    (hd : ∀ a b, AsyncBefore L X l a b ↔ AsyncBefore L Y l a b)
    (hp : ∀ a b, AsyncBefore L X l a b →
      (X.AsyncPresent a.1 a.2 ↔ Y.AsyncPresent a.1 a.2)) {a b : EvId × Part} :
    AsyncChain L X l a b ↔ AsyncChain L Y l a b :=
  ⟨fun h => h.map (fun {a b} => (hd a b).mp) (fun hx edge => (hp _ _ edge).mp hx),
   fun h => h.map (fun {a b} => (hd a b).mpr)
     (fun hx edge => (hp _ _ ((hd _ _).mpr edge)).mpr hx)⟩

theorem AsyncChain.congr
    (hd : ∀ a b, AsyncBefore L X l a b ↔ AsyncBefore L Y l a b)
    (hp : ∀ i p, X.AsyncPresent i p ↔ Y.AsyncPresent i p) {a b : EvId × Part} :
    AsyncChain L X l a b ↔ AsyncChain L Y l a b :=
  AsyncChain.congr_on_edges hd (fun a _ _ => hp a.1 a.2)

theorem sameCtaGroup_trans {g : CtaGroup} {a b c : Nat} (h : SameCtaGroup L g a b)
    (h' : SameCtaGroup L g b c) : SameCtaGroup L g a c := by
  rw [sameCtaGroup_iff] at h h' ⊢
  refine ⟨⟨h.1.1, h'.1.2.1, h.1.2.2.trans h'.1.2.2⟩, ?_⟩
  omega

/-- The endpoint condition of `modelCausality` between asynchronous accesses composes. -/
theorem pairOrSame_trans {i j k : Nat}
    (h : SameCta L i j ∨ PairAsync L l i j) (h' : SameCta L j k ∨ PairAsync L l j k) :
    SameCta L i k ∨ PairAsync L l i k := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact .inl ⟨h.1, h'.2.1, h.2.2.trans h'.2.2⟩
  · refine .inr ⟨h'.1, ?_, ?_⟩ <;> rw [h.2.2]
    · exact h'.2.1
    · exact h'.2.2
  · refine .inr ⟨h.1, ?_, h.2.2⟩
    rw [← h'.2.2]
    exact h.2.1
  · exact .inr ⟨h.1, sameCtaGroup_trans h.2.1 h'.2.1, h.2.2⟩

/-- A direct asynchronous edge between two CTAs of a `cta_group::2` pair, one of which issues a
`cta_group::2` `tcgen05` operation, is `modelCausality` (EXT-PAIR-ASYNC). -/
theorem modelCausality_pair_direct {i j : EvId} {p q : Part} (hpa : PairAsync L l i.1 j.1)
    (ht : PairTc X i ∨ PairTc X j) (h : AsyncBefore L X l (i, p) (j, q)) :
    modelCausality L X l (.async i p) (.async j q) :=
  ⟨.inr ⟨hpa, ht⟩, .direct h⟩

/-- The asynchronous case of `modelCausality` is preserved by a change of execution that keeps the
`cta_group::2` `tcgen05` operations and the chain between the two operations. -/
theorem modelCausality_async_congr {i j : EvId} {p q : Part}
    (hp : ∀ e, PairTc Y e ↔ PairTc X e)
    (hc : AsyncChain L Y l (i, p) (j, q) ↔ AsyncChain L X l (i, p) (j, q)) :
    modelCausality L Y l (.async i p) (.async j q) ↔
      modelCausality L X l (.async i p) (.async j q) := by
  simp only [modelCausality, hp, hc]

/-- An execution with the same events has the same `cta_group::2` `tcgen05` operations. -/
theorem pairTc_congr (h : ∀ e, Y.get e = X.get e) (e : EvId) : PairTc Y e ↔ PairTc X e := by
  simp only [PairTc, Execution.MmaIssue, Execution.CpIssue, h]

/-- The public byte-specific bridge never treats an issuer as a release. Between two CTAs of a
pair, the composed order needs one of its endpoints to be a `cta_group::2` `tcgen05` operation
(EXT-PAIR-ASYNC). -/
theorem modelCausality_async_trans {i j k : EvId} {p q r : Part}
    (hij : modelCausality L X l (.async i p) (.async j q)) (hj : X.AsyncPresent j q)
    (hjk : modelCausality L X l (.async j q) (.async k r))
    (hend : SameCta L i.1 k.1 ∨ PairTc X i ∨ PairTc X k) :
    modelCausality L X l (.async i p) (.async k r) := by
  refine ⟨?_, AsyncChain.trans hij.2 hj hjk.2⟩
  rcases pairOrSame_trans (hij.1.imp_right And.left) (hjk.1.imp_right And.left) with hs | hpa
  · exact .inl hs
  · rcases hend with hs | ht
    · exact .inl hs
    · exact .inr ⟨hpa, ht⟩

end PTX
