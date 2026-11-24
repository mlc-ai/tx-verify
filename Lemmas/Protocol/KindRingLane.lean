-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.KindRingBlock

@[expose] public section

/-! # Phases of a ring of kinds, for any bound on its items

`KindRingBlock.lean` bounds the final phases by the polls of a producer or consumer. Here by any
number above the uses of the items (`E_phase_of`, `F_phase_of`), so that another lane which is in
step with a producer or consumer can stand for it. -/

namespace PTX.MbarRing
open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

namespace KRing

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {np nc nk : Nat}

/-- **A notification's use has an item of every kind on the full object.** -/
theorem E_items (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {y : Fin nc × Nat}
    (hy : y ∈ R.SE) (k : Fin nk) : (k, y.2) ∈ R.SF := by
  obtain ⟨i, -, hi, hp⟩ := R.polE y hy
  have hlt : y.2 < okPolls R.F (X.tr (R.cons y.1)) := by
    have := Poll.okPolls_mono R.F (X.tr (R.cons y.1)) hi.le
    rw [List.take_of_length_le le_rfl] at this
    omega
  exact (R.full_observes hX hlt k).1

/-- **The final phase of the empty object** is at most any number above its notifications' uses. -/
theorem E_phase_of (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) (hnc : 0 < nc)
    (hinit : PairTmaRing.InitFirst X R.E nc)
    (hinc : ∀ r ∈ X.objects R.E, r.action ≠ .increment)
    (hone : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects R.E)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → c = 1)
    (hrec : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects R.E)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → ∃ y ∈ R.SE, r.id = R.note y.1 y.2)
    {N : Nat} (hN : ∀ y ∈ R.SE, y.2 + 1 ≤ N) {st : State}
    (hst : stateBefore (X.objects R.E) (X.objects R.E).length = some st) : st.phase ≤ N := by
  obtain ⟨h1, h2⟩ := units_bounds hX hinit R.cE.noInval hinc hone hrec hst
  have h3 : R.SE.card ≤ nc * N := by
    calc R.SE.card ≤ (Finset.univ ×ˢ Finset.range N : Finset (Fin nc × Nat)).card :=
          Finset.card_le_card fun y hy =>
            Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (hN y hy)⟩
      _ = _ := by simp
  exact Nat.le_of_mul_le_mul_left (h2.trans (h1.trans h3)) hnc

/-- **The final phase of the full object** is at most one more than any number above its items'
uses, when the arrivals are those of the items of `N` kinds. -/
theorem F_phase_of (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk)
    {κ : Finset (Fin nk)} (hκ : 0 < κ.card) (hinit : PairTmaRing.InitFirst X R.F κ.card)
    (hinc : ∀ r ∈ X.objects R.F, r.action ≠ .increment)
    (hone : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects R.F)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → c = 1)
    (hrec : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects R.F)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → ∃ x ∈ R.SF, x.1 ∈ κ ∧ r.id = R.itF x.1 x.2)
    {N : Nat} (hN : ∀ x ∈ R.SF, x.2 ≤ N) {st : State}
    (hst : stateBefore (X.objects R.F) (X.objects R.F).length = some st) : st.phase ≤ N + 1 := by
  classical
  obtain ⟨h1, h2⟩ := units_bounds hX hinit R.cF.noInval hinc hone
    (S := R.SF.filter fun x => x.1 ∈ κ) (it := R.itF) (fun hr hf ha => by
      obtain ⟨x, hx, hk, hid⟩ := hrec hr hf ha
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, hk⟩, hid⟩) hst
  have h3 : (R.SF.filter fun x => x.1 ∈ κ).card ≤ κ.card * (N + 1) := by
    calc _ ≤ (κ ×ˢ Finset.range (N + 1) : Finset (Fin nk × Nat)).card :=
          Finset.card_le_card fun y hy => by
            obtain ⟨hy, hk⟩ := Finset.mem_filter.mp hy
            exact Finset.mem_product.mpr ⟨hk, Finset.mem_range.mpr (Nat.lt_succ_of_le (hN y hy))⟩
      _ = _ := by simp
  exact Nat.le_of_mul_le_mul_left (h2.trans (h1.trans h3)) hκ

end KRing
end
end PTX.MbarRing
