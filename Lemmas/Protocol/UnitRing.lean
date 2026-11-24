-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitItems
public import Lemmas.Protocol.UnitGate
public import Lemmas.Protocol.MbarRingItems

@[expose] public section

/-! # A ring of two unit objects

A proof tool. A ring slot handed back and forth through two unit objects (`Unit.Obj`): the `np`
producers `prod a` arrive on `full` (polled with offset 0) and the `nc` consumers `cons b` arrive
on `empty` (polled with offset 1); a producer's arrival of use `s` follows more successful polls
of `empty` than `s`, a consumer's arrival of use `t` more successful polls of `full` than `t`
(`Ring.gateP`, `Ring.gateC`; FA4's output staging: the correction threads produce, the store
lanes consume). It is an `MbarRing.Items.Ring` (`items`) with one full object of `np` kinds, one
per producer, read through the unit items of each object (`UnitItems`). Its attribution gives the
unit handoffs of both objects (`full_handoff`, offset 0; `empty_handoff`, offset 1). -/

namespace PTX.MbarRing.Unit

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

/-- **A ring of two unit objects.** -/
structure Ring (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (full empty : Loc) (np nc : Nat) (prod : Fin np → Nat) (cons : Fin nc → Nat) : Prop where
  F : Obj X full np prod 0
  E : Obj X empty nc cons 1
  /-- A producer's arrival of use `s` follows more than `s` successful polls of `empty`. -/
  gateP : ∀ {a : Fin np} {i pc : Nat} {sc : MbarScope},
    X.get (prod a, i) = some ⟨pc, .arrive full 0 1 true sc⟩ →
      arrivals full ((X.tr (prod a)).take i) + 1 ≤ okPolls empty ((X.tr (prod a)).take i)
  /-- A consumer's arrival of use `t` follows more than `t` successful polls of `full`. -/
  gateC : ∀ {b : Fin nc} {i pc : Nat} {sc : MbarScope},
    X.get (cons b, i) = some ⟨pc, .arrive empty 0 1 true sc⟩ →
      arrivals empty ((X.tr (cons b)).take i) + 1 ≤ okPolls full ((X.tr (cons b)).take i)
  /-- Every successful poll is the poll of a canonical spin (DEP-CANONICAL-SPIN). -/
  spins : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  /-- A consumer's successful poll of `full` acquires. -/
  acqF : ∀ {b : Fin nc} {j pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (cons b, j) = some ⟨pc, .wait full p true acq sc⟩ → acq = true
  /-- A producer's successful poll of `empty` acquires. -/
  acqE : ∀ {a : Fin np} {j pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (prod a, j) = some ⟨pc, .wait empty p true acq sc⟩ → acq = true
  /-- Producers and consumers are threads of one CTA. -/
  cta : ∀ a b, SameCta L (prod a) (cons b)

namespace Ring

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {full empty : Loc} {np nc : Nat} {prod : Fin np → Nat} {cons : Fin nc → Nat}

/-- Thread `g`'s poll of `m` with `n` earlier successful ones is present exactly when it made
more. -/
theorem present {m : Loc} {g n : Nat} :
    X.RefPresent (.thread (g, MbarRing.Poll.nth X m g n)) ↔ n < okPolls m (X.tr g) :=
  MbarRing.Poll.nth_present

/-- An item's event is guarded by its thread's polls of the other object. -/
theorem guard_item (H : Ring L K A X full empty np nc prod cons) {m m' : Loc} {N : Nat}
    {pr : Fin N → Nat} {δ : Nat} (O : Obj X m N pr δ) {x : Fin N × Nat} (hx : x ∈ S X m pr)
    (hgate : ∀ {i pc : Nat} {sc : MbarScope},
      X.get (pr x.1, i) = some ⟨pc, .arrive m 0 1 true sc⟩ →
        arrivals m ((X.tr (pr x.1)).take i) + 1 ≤ okPolls m' ((X.tr (pr x.1)).take i))
    {n : Nat} (hn : n ≤ x.2) :
    Resumes K X (pr x.1, MbarRing.Poll.nth X m' (pr x.1) n) (it X m pr x.1 x.2) := by
  obtain ⟨-, ⟨pc, sc, he⟩, hu⟩ := O.S_rec hx
  have hb := hgate he
  have hu' : arrivals m ((X.tr (pr x.1)).take (nthEv X (arrivesOn m) (pr x.1) x.2)) = x.2 := hu
  rw [hu'] at hb
  exact MbarRing.Poll.guard H.spins (len_of_get he) (by omega)

/-- **The ring as a ring of items.** -/
def items (hX : Consistent L K A mem0 X) (H : Ring L K A X full empty np nc prod cons) :
    MbarRing.Items.Ring L K A X np nc 1 (fun _ => np) where
  owner _ := 0
  ownF _ k := k
  wE a n := (prod a, MbarRing.Poll.nth X empty (prod a) n)
  opF _ k u := it X full prod k u
  itF _ k u := .thread (it X full prod k u)
  wF b j := (cons b, MbarRing.Poll.nth X full (cons b) j)
  cm b t := it X empty cons b t
  note b _ t := .thread (it X empty cons b t)
  SF _ := S X full prod
  phF _ := ph X full prod
  SE _ := S X empty cons
  phE _ := ph X empty cons
  oF b j := obsOf X full (cons b) j
  oE a n := obsOf X empty (prod a) n
  cover _ a := ⟨a, rfl⟩
  guardP _ _ hx _ _ hn := H.guard_item H.F hx H.gateP hn
  issueF _ _ _ := .refl
  guardM _ _ hy _ hj := H.guard_item H.E hy H.gateC hj
  issue _ _ _ := .refl
  obsF _ _ hw _ hx hph := H.F.observed hX (Nat.zero_le _) (present.mp hw) hx hph
  obsE _ _ hn hw _ hy hph := H.E.observed hX hn (present.mp hw) hy hph
  fullF _ _ hw := H.F.card_phase hX (Nat.zero_le _) (present.mp hw)
  fullE _ _ hn hw := H.E.card_phase hX hn (present.mp hw)
  ltF _ _ _ hjj hw := ⟨present.mpr (by have := present.mp hw; omega),
    MbarRing.Poll.observed_lt hX (by decide) (H.F.pclean hX) H.F.noInval (H.F.alt hX _)
      (Nat.zero_le _) hjj (present.mp hw)⟩
  ltE _ _ _ hn hnn hw := ⟨present.mpr (by have := present.mp hw; omega),
    MbarRing.Poll.observed_lt hX (le_refl 1) (H.E.pclean hX) H.E.noInval (H.E.alt hX _) hn hnn
      (present.mp hw)⟩

/-- The synchronization of an observed unit arrival. -/
theorem syncs {m : Loc} {N δ : Nat} {pr : Fin N → Nat} (O : Obj X m N pr δ) {x : Fin N × Nat}
    (hx : x ∈ S X m pr) {h j pc p : Nat} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait m p true true sc⟩)
    (hu : UpdateBeforeWait (X.objects m) (.thread (it X m pr x.1 x.2)) (.thread (h, j)))
    (hcta : SameCta L (pr x.1) h) :
    arrivals m ((X.tr (pr x.1)).take (it X m pr x.1 x.2).2) = x.2 ∧
      Syncs L X (it X m pr x.1 x.2) (h, j) m := by
  obtain ⟨-, ⟨pca, sca, hea⟩, huse⟩ := O.S_rec hx
  exact ⟨huse, sca, ⟨0, 1, pca, hea⟩, sc, ⟨⟨pc, p, he⟩, hu⟩, Gate.scopesMeet hcta _ _⟩

/-- **The full handoff**: a consumer's successful poll of `full` with `q` earlier ones
synchronizes with every producer's arrival of use `q`. -/
theorem full_handoff (hX : Consistent L K A mem0 X) (H : Ring L K A X full empty np nc prod cons) :
    MbarRing.UnitHandoff L X full (fun g => ∃ a, g = prod a) (fun h => ∃ b, h = cons b) 0 := by
  intro h j pc p acq sc q ⟨b, hb⟩ he hq g ⟨a, hga⟩
  subst hb hga
  have hacq := H.acqF he
  subst hacq
  have hjn : MbarRing.Poll.nth X full (cons b) q = j := by
    rw [← MbarRing.Poll.nth_eq he, hq, Nat.add_zero]
  have hn : q < okPolls full (X.tr (cons b)) := by
    rw [← present, hjn]
    exact ⟨_, he⟩
  obtain ⟨hS, hp⟩ := ((items hX H).content_full hX.depAcyclic (b := b) (j := q)
    (present.mpr hn)).2 a
  have hu := H.F.ubw hX (Nat.zero_le q) hn hS hp
  rw [hjn] at hu
  exact ⟨_, syncs H.F hS he hu (H.cta a b)⟩

/-- **The empty handoff**: a producer's successful poll of `empty` with `q + 1` earlier ones
synchronizes with every consumer's arrival of use `q`. -/
theorem empty_handoff (hX : Consistent L K A mem0 X)
    (H : Ring L K A X full empty np nc prod cons) :
    MbarRing.UnitHandoff L X empty (fun g => ∃ b, g = cons b) (fun h => ∃ a, h = prod a) 1 := by
  intro h j pc p acq sc q ⟨a, ha⟩ he hq g ⟨b, hgb⟩
  subst ha hgb
  have hacq := H.acqE he
  subst hacq
  have hjn : MbarRing.Poll.nth X empty (prod a) (q + 1) = j := by
    rw [← MbarRing.Poll.nth_eq he, hq]
  have hn : q + 1 < okPolls empty (X.tr (prod a)) := by
    rw [← present, hjn]
    exact ⟨_, he⟩
  obtain ⟨hS, hp⟩ := ((items hX H).content_empty hX.depAcyclic (a := a) (n := q)
    (present.mpr hn)).2 b
  have hu := H.E.ubw hX (by omega) hn hS hp
  rw [hjn] at hu
  have hc := H.cta a b
  exact ⟨_, syncs H.E hS he hu ⟨hc.2.1, hc.1, hc.2.2.symm⟩⟩

end Ring
end
end PTX.MbarRing.Unit
