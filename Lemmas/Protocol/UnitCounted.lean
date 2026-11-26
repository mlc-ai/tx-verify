-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitItems
public import Lemmas.Protocol.KindRing
public import Lemmas.Order.WaitOrderEnables

@[expose] public section

/-! # The counted items of a unit object, as counted units

A proof tool. The counted items of a unit object (`Unit.S`, `UnitItems.lean`) are counted units of
the object (`MbarRing.Counted`, `KindRing.lean`) read through the arrival events (`Unit.itRef`),
so a unit object can be either barrier of a ring of kinds (`KRing.cF`, `KRing.cE`), its phases
those of `Unit.ph` (`ph_eq`). A producer's arrival of use `t` that follows more successful polls of
another barrier `m'` than its earlier arrivals is placed as `KRing.polF` and `KRing.polE` ask
(`Obj.pol`), and an update a poll observes is a producer's arrival of its use (`Obj.wait_obs`). -/

namespace PTX.MbarRing.Unit

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {X : Execution} {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- Producer `a`'s arrival of use `u`, as a reference. -/
def itRef (X : Execution) (m : Loc) (prod : Fin N → Nat) (a : Fin N) (u : Nat) : Ref :=
  .thread (it X m prod a u)

/-- The phase of a counted unit is the item's phase. -/
theorem ph_eq (x : Fin N × Nat) : Counted.ph X m (itRef X m prod) x = ph X m prod x := rfl

/-- **The counted items of a unit object are counted units.** -/
theorem Obj.counted (O : Obj X m N prod δ) : Counted X m (S X m prod) (itRef X m prod) where
  record x hx := by
    obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := O.S_rec hx
    exact ⟨k, r, hk, hid, hf, by rw [ha]; trivial⟩
  init := ⟨N, O.init⟩
  noInval := O.noInval

/-- **A counted item's arrival follows more successful polls of `m'` than its use**, when every
producer arrival does. -/
theorem Obj.pol (O : Obj X m N prod δ) {m' : Loc}
    (hin : ∀ {a : Fin N} {i pc : Nat} {sc : MbarScope},
      X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ →
      arrivals m ((X.tr (prod a)).take i) < okPolls m' ((X.tr (prod a)).take i))
    {y : Fin N × Nat} (hy : y ∈ S X m prod) :
    ∃ i, it X m prod y.1 y.2 = (prod y.1, i) ∧ i < (X.tr (prod y.1)).length ∧
      y.2 + 1 ≤ okPolls m' ((X.tr (prod y.1)).take i) := by
  obtain ⟨-, ⟨pc, sc, hget⟩, hcnt⟩ := O.S_rec hy
  have hget' : X.get (prod y.1, (it X m prod y.1 y.2).2) =
      some ⟨pc, .arrive m 0 1 true sc⟩ := hget
  refine ⟨_, rfl, len_of_get hget', ?_⟩
  have := hin hget'
  simp only [it] at hcnt this ⊢
  omega

/-- **An observed counted item is a producer's arrival of its use.** -/
theorem Obj.wait_obs (O : Obj X m N prod δ) {y : Fin N × Nat} (hy : y ∈ S X m prod)
    {h j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩)
    (hub : UpdateBeforeWait (X.objects m) (.thread (it X m prod y.1 y.2)) (.thread (h, j))) :
    ∃ i pc' sc', X.get (prod y.1, i) = some ⟨pc', .arrive m 0 1 true sc'⟩ ∧
      arrivals m ((X.tr (prod y.1)).take i) = y.2 ∧
      WaitObserves X (.thread (prod y.1, i)) (h, j) m acq sc := by
  obtain ⟨-, ⟨pc', sc', hget⟩, hcnt⟩ := O.S_rec hy
  exact ⟨_, pc', sc', hget, hcnt, ⟨pc, p, he⟩, hub⟩

end
end PTX.MbarRing.Unit
