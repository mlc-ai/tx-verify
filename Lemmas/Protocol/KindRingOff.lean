-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.KindRing

@[expose] public section

/-! # A slot of a one-CTA ring of kinds, with the empty side's poll offset a parameter

Generalizes `MbarRing.KRing` (`Lemmas/Protocol/KindRing.lean`): there the producers poll the
empty barrier `E` with the parity of their successful polls plus one, the first poll passing on
the fresh barrier, and a producer's item of use `s` follows `s + 1` successful polls of `E`. In
`KRingOff … dE` the offset is `dE ≤ 1`: the parity of the polls plus `dE` (`parE`), the item of
use `s` after `s + dE` successful polls of `E` (`polF`), and a producer's poll with `n ≥ dE`
earlier ones observes a phase holding every consumer's notification (`fullE`). With `dE = 0` the
producer's first poll waits for the consumers' notifications of use 0 (a ring whose producer
waits for the consumers before reusing the slot even the first time, e.g. an MMA lane that waits
for a softmax warpgroup's release of a score buffer after each block).

The slot is the same `MbarRing.Items.Ring`, with the producer's poll for use `n ≥ 1` its
successful poll with `n - 1 + dE` earlier ones. The lemmas are those of `KRing` with the offset:

* `full_observes`: consumer `b`'s poll of `F` with `u` earlier ones observes every item of use `u`;
* `empty_observes`: a producer's poll of `E` with `u + dE` earlier ones observes every
  notification of use `u`;
* `reachF`: an item of use `s` follows every consumer's polls of `F` for the uses before `s`;
* `reachE`: a notification of use `t` follows every producer's polls of `E` with `n` earlier ones,
  `dE ≤ n < t + dE`. -/

namespace PTX.MbarRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A slot of a one-CTA ring by the kinds of items, empty-side offset `dE`** (module
docstring). -/
structure KRingOff (L : Launch) (K : Kernel) (X : Execution) (np nc nk dE : Nat) where
  F : Loc
  E : Loc
  prod : Fin np → Nat
  cons : Fin nc → Nat
  ownF : Fin nk → Fin np
  opF : Fin nk → Nat → EvId
  itF : Fin nk → Nat → Ref
  cm : Fin nc → Nat → EvId
  note : Fin nc → Nat → Ref
  SF : Finset (Fin nk × Nat)
  SE : Finset (Fin nc × Nat)
  dE_le : dE ≤ 1
  cover : ∀ a, ∃ k, ownF k = a
  cF : Counted X F SF itF
  cE : Counted X E SE note
  spins : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  parF : ∀ b {k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (cons b, k) = some ⟨pc, .wait F p true acq sc⟩ →
      p % 2 = (okPolls F ((X.tr (cons b)).take k) + 0) % 2
  parE : ∀ a {k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (prod a, k) = some ⟨pc, .wait E p true acq sc⟩ →
      p % 2 = (okPolls E ((X.tr (prod a)).take k) + dE) % 2
  fullF : ∀ b j, j < okPolls F (X.tr (cons b)) →
    nk ≤ (SF.filter (fun x => Counted.ph X F itF x = Unit.obsOf X F (cons b) j)).card
  fullE : ∀ a n, dE ≤ n → n < okPolls E (X.tr (prod a)) →
    nc ≤ (SE.filter (fun y => Counted.ph X E note y = Unit.obsOf X E (prod a) n)).card
  polF : ∀ x ∈ SF, ∃ i, opF x.1 x.2 = (prod (ownF x.1), i) ∧ i < (X.tr (prod (ownF x.1))).length ∧
    x.2 + dE ≤ okPolls E ((X.tr (prod (ownF x.1))).take i)
  polE : ∀ y ∈ SE, ∃ i, cm y.1 y.2 = (cons y.1, i) ∧ i < (X.tr (cons y.1)).length ∧
    y.2 + 1 ≤ okPolls F ((X.tr (cons y.1)).take i)
  issueF : ∀ x ∈ SF, Relation.ReflTransGen (DepStep L K X)
    (.thread (opF x.1 x.2), false) (itF x.1 x.2, false)
  issueE : ∀ y ∈ SE, Relation.ReflTransGen (DepStep L K X)
    (.thread (cm y.1 y.2), false) (note y.1 y.2, false)

namespace KRingOff

variable {np nc nk dE : Nat}

theorem altF (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE) (b : Fin nc) :
    SelectedAlternates (objectThreadSelected (R.cons b)) (X.objects R.F) 0 :=
  R.cF.alt hX (R.parF b)

theorem altE (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE) (a : Fin np) :
    SelectedAlternates (objectThreadSelected (R.prod a)) (X.objects R.E) dE :=
  R.cE.alt hX (R.parE a)

/-- The slot as an items ring: the producer's poll for use `n ≥ 1` is its successful poll with
`n - 1 + dE` earlier ones. -/
def ring (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE) :
    Items.Ring L K A X np nc 1 (fun _ => nk) where
  owner _ := 0
  ownF _ := R.ownF
  wE a n := (R.prod a, Poll.nth X R.E (R.prod a) (n - 1 + dE))
  opF _ := R.opF
  itF _ := R.itF
  wF b j := (R.cons b, Poll.nth X R.F (R.cons b) j)
  cm := R.cm
  note b _ := R.note b
  SF _ := R.SF
  phF _ := Counted.ph X R.F R.itF
  SE _ := R.SE
  phE _ := Counted.ph X R.E R.note
  oF b j := Unit.obsOf X R.F (R.cons b) j
  oE a n := Unit.obsOf X R.E (R.prod a) (n - 1 + dE)
  cover _ := R.cover
  guardP _ x hx n _ hn := by
    obtain ⟨i, hop, hi, hp⟩ := R.polF x hx
    rw [hop]
    exact Poll.guard R.spins hi (by omega)
  issueF _ := R.issueF
  guardM _ y hy j hj := by
    obtain ⟨i, hop, hi, hp⟩ := R.polE y hy
    rw [hop]
    exact Poll.guard R.spins hi (by omega)
  issue _ := R.issueE
  obsF b _ hw _ hx hph := R.cF.observed hX (Nat.zero_le _) (R.altF hX b) (Nat.zero_le _)
    (Poll.nth_present.mp hw) hx hph
  obsE a _ hn hw _ hy hph := R.cE.observed hX R.dE_le (R.altE hX a) (by omega)
    (Poll.nth_present.mp hw) hy hph
  fullF b _ hw := R.fullF b _ (Poll.nth_present.mp hw)
  fullE a _ hn hw := R.fullE a _ (by omega) (Poll.nth_present.mp hw)
  ltF b _ _ hjj hw := ⟨Poll.nth_present.mpr (by have := Poll.nth_present.mp hw; omega),
    R.cF.lt hX (Nat.zero_le _) (R.altF hX b) (Nat.zero_le _) hjj (Poll.nth_present.mp hw)⟩
  ltE a _ _ hn hnn hw := ⟨Poll.nth_present.mpr (by have := Poll.nth_present.mp hw; omega),
    R.cE.lt hX R.dE_le (R.altE hX a) (by omega) (by omega) (Poll.nth_present.mp hw)⟩

/-- **The consumer's poll of `F` with `u` earlier ones observes every item of use `u`.** -/
theorem full_observes (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE)
    {b : Fin nc} {u : Nat} (hu : u < okPolls R.F (X.tr (R.cons b))) (k : Fin nk) :
    (k, u) ∈ R.SF ∧ UpdateBeforeWait (X.objects R.F) (R.itF k u)
      (.thread (R.cons b, Poll.nth X R.F (R.cons b) u)) := by
  obtain ⟨hS, hph⟩ := ((R.ring hX).content_full hX.depAcyclic (b := b) (j := u)
    (Poll.nth_present.mpr hu)).2 k
  exact ⟨hS, R.cF.ubw hX (Nat.zero_le _) (R.altF hX b) (Nat.zero_le _) hu hS hph⟩

/-- **The producer's poll of `E` with `u + dE` earlier ones observes every notification of use
`u`.** -/
theorem empty_observes (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE)
    {a : Fin np} {u : Nat} (hu : u + dE < okPolls R.E (X.tr (R.prod a))) (b : Fin nc) :
    (b, u) ∈ R.SE ∧ UpdateBeforeWait (X.objects R.E) (R.note b u)
      (.thread (R.prod a, Poll.nth X R.E (R.prod a) (u + dE))) := by
  have he : u + 1 - 1 + dE = u + dE := by omega
  have hw : X.RefPresent (.thread ((R.ring hX).wE a (u + 1))) := by
    show X.RefPresent (.thread (R.prod a, Poll.nth X R.E (R.prod a) (u + 1 - 1 + dE)))
    rw [he]
    exact Poll.nth_present.mpr hu
  obtain ⟨hS, hph⟩ := ((R.ring hX).content_empty hX.depAcyclic hw).2 b
  have hph' : Counted.ph X R.E R.note (b, u) = Unit.obsOf X R.E (R.prod a) (u + dE) := by
    rw [← he]
    exact hph
  exact ⟨hS, R.cE.ubw hX R.dE_le (R.altE hX a) (by omega) hu hS hph'⟩

/-- **The reuse**: an item of use `s` follows every consumer's polls of `F` for the uses before
`s`. -/
theorem reachF (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE)
    {x : Fin nk × Nat} (hx : x ∈ R.SF) (b : Fin nc) {j : Nat} (hj : j < x.2) :
    Relation.TransGen (DepStep L K X) (.thread (R.cons b, Poll.nth X R.F (R.cons b) j), true)
      (R.itF x.1 x.2, false) :=
  ((R.ring hX).reach hX.depAcyclic).1 0 x hx b j hj

/-- **The release**: a notification of use `t` follows every producer's polls of `E` with `n`
earlier ones, `dE ≤ n < t + dE`. -/
theorem reachE (hX : Consistent L K A mem0 X) (R : KRingOff L K X np nc nk dE)
    {y : Fin nc × Nat} (hy : y ∈ R.SE) (a : Fin np) {n : Nat} (h1 : dE ≤ n)
    (hn : n < y.2 + dE) :
    Relation.TransGen (DepStep L K X) (.thread (R.prod a, Poll.nth X R.E (R.prod a) n), true)
      (R.note y.1 y.2, false) := by
  have h := ((R.ring hX).reach hX.depAcyclic).2 a y hy (n + 1 - dE) (by omega) (by omega)
  have he : n + 1 - dE - 1 + dE = n := by omega
  simp only [ring, he] at h
  exact h

end KRingOff
end
end PTX.MbarRing
