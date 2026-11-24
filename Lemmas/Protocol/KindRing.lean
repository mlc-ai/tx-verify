-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarRingItems
public import Lemmas.Protocol.UnitItems
public import Lemmas.Protocol.PollIndex

@[expose] public section

/-! # A slot of a one-CTA ring, by the kinds of items that complete its barriers

A proof tool: `MbarRing.Items.Ring` for one full barrier `F` and one empty barrier `E`, with the
history facts stated once. `Counted` is a set of counted units of an object (each with a fault-free
counter-update record); its polls observe the units of the phase they find (`Counted.ubw`). `KRing`
is a slot:

* every phase of `F` holds an item of each of `nk` kinds; kind `k` is made by producer `ownF k`,
  its item of use `s` after `s + 1` successful polls of `E` (`polF`; the first poll passes on the
  fresh barrier);
* every phase of `E` holds a notification of each of `nc` consumers, consumer `b`'s of use `t`
  after `t + 1` successful polls of `F` (`polE`).

Then consumer `b`'s poll of `F` with `u` earlier ones observes every item of use `u`
(`full_observes`), and a producer's poll of `E` with `u + 1` earlier ones every notification of use
`u` (`empty_observes`). The kinds are a kernel's: thread arrivals, `cp.async` arrive-ons, a TMA
arrival with its copies, commits. -/

namespace PTX.MbarRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-! ### Counted units of one object -/

/-- **Counted units of an object**: each has a fault-free counter-update record. -/
structure Counted (X : Execution) (m : Loc) {κ : Type} (S : Finset (κ × Nat))
    (it : κ → Nat → Ref) : Prop where
  record : ∀ x ∈ S, ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
    r.id = it x.1 x.2 ∧ r.fault = none ∧ CounterUpdate r.action
  init : ∃ c, PairTmaRing.InitFirst X m c
  noInval : NoInval (X.objects m)

namespace Counted

variable {m : Loc} {κ : Type} {S : Finset (κ × Nat)} {it : κ → Nat → Ref} {δ : Nat}

theorem pclean (hX : Consistent L K A mem0 X) (C : Counted X m S it) :
    ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none := by
  obtain ⟨c, hc⟩ := C.init
  exact PairTmaRing.poll_clean hX hc C.noInval

/-- A thread whose successful polls have the parity of its earlier ones plus `δ` alternates. -/
theorem alt (hX : Consistent L K A mem0 X) (C : Counted X m S it) {g : Nat}
    (hpar : ∀ {k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
        p % 2 = (okPolls m ((X.tr g).take k) + δ) % 2) :
    SelectedAlternates (objectThreadSelected g) (X.objects m) δ :=
  MbarRing.Poll.alternates hX (C.pclean hX) fun _ _ _ _ _ he => hpar he

/-- A thread's successful poll with `n ≥ δ` earlier ones: its record, which observed the phase
before the one it found. -/
theorem poll_obs (hX : Consistent L K A mem0 X) (C : Counted X m S it) {g n : Nat} (hδ' : δ ≤ 1)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ) (hδ : δ ≤ n)
    (hn : n < okPolls m (X.tr g)) :
    ∃ (k : Nat) (w : Record Ref) (st : State), (X.objects m)[k]? = some w ∧
      w.id = .thread (g, MbarRing.Poll.nth X m g n) ∧ w.reply.waited = some true ∧
      w.fault = none ∧ stateBefore (X.objects m) k = some st ∧ 0 < st.phase ∧
      observedAt (X.objects m) k = some (st.phase - 1) ∧
      Unit.obsOf X m g n = st.phase - 1 := by
  obtain ⟨k, w, -, hk, hwid, -, hww, hwf, hsel⟩ := MbarRing.Poll.record hX (C.pclean hX) hn
  have hs : objectThreadSelected g w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX m)
    C.noInval hδ' hAlt hk hs hww (by omega)
  refine ⟨k, w, st, hk, hwid, hww, hwf, hst, hpos, ho, ?_⟩
  unfold Unit.obsOf
  rw [← hwid]
  exact MbarRing.Poll.observedOf_eq hX hk ho

/-- The phase of a counted unit. -/
def ph (X : Execution) (m : Loc) (it : κ → Nat → Ref) (x : κ × Nat) : Nat :=
  MbarRing.Poll.phaseOf X m (it x.1 x.2)

theorem phase (hX : Consistent L K A mem0 X) (C : Counted X m S it) {x : κ × Nat} (hx : x ∈ S) :
    ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = it x.1 x.2 ∧
      r.fault = none ∧ CounterUpdate r.action ∧
      phaseAt (X.objects m) k = some (ph X m it x) := by
  obtain ⟨k, r, hk, hid, hf, ha⟩ := C.record x hx
  obtain ⟨c, hc⟩ := C.init
  obtain ⟨-, sd, hsd, -⟩ := PairTmaRing.state_of_init hX hc C.noInval hk
    (by intro n h; rw [h] at ha; exact ha)
  have hp : phaseAt (X.objects m) k = some sd.phase := by simp [phaseAt, hsd]
  refine ⟨k, r, hk, hid, hf, ha, ?_⟩
  unfold ph
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hk hp]
  exact hp

/-- **A poll observes the counted units of the phase it found last**, in the object's order. -/
theorem ubw (hX : Consistent L K A mem0 X) (C : Counted X m S it) {g n : Nat} (hδ' : δ ≤ 1)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ) (hδ : δ ≤ n)
    (hn : n < okPolls m (X.tr g)) {x : κ × Nat} (hx : x ∈ S)
    (hph : ph X m it x = Unit.obsOf X m g n) :
    UpdateBeforeWait (X.objects m) (it x.1 x.2) (.thread (g, MbarRing.Poll.nth X m g n)) := by
  obtain ⟨kw, w, st, hkw, hwid, hww, hwf, -, -, ho, hoo⟩ := C.poll_obs hX hδ' hAlt hδ hn
  obtain ⟨k, r, hk, hid, hf, -, hp⟩ := C.phase hX hx
  rw [hph, hoo] at hp
  have h := MbarRing.Slot.updateBeforeWait_of_phase (X.objects_checked hX m) C.noInval hk hf
    hkw hwf hww hp ho
  rwa [hid, hwid] at h

theorem observed (hX : Consistent L K A mem0 X) (C : Counted X m S it) {g n : Nat} (hδ' : δ ≤ 1)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ) (hδ : δ ≤ n)
    (hn : n < okPolls m (X.tr g)) {x : κ × Nat} (hx : x ∈ S)
    (hph : ph X m it x = Unit.obsOf X m g n) :
    Witness L X (it x.1 x.2) (g, MbarRing.Poll.nth X m g n) := by
  obtain ⟨kw, w, st, hkw, hwid, hww, hwf, -, -, ho, hoo⟩ := C.poll_obs hX hδ' hAlt hδ hn
  obtain ⟨k, r, hk, hid, hf, ha, hp⟩ := C.phase hX hx
  rw [hph, hoo] at hp
  have h := Consistent.observed_of_phase hX C.noInval hk hf ha hkw hww hp ho
  rw [hid, hwid] at h
  exact Witness.of_mbarObserved h

theorem lt (hX : Consistent L K A mem0 X) (C : Counted X m S it) {g n n' : Nat} (hδ' : δ ≤ 1)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ) (hδ : δ ≤ n)
    (hnn : n < n') (hn : n' < okPolls m (X.tr g)) :
    Unit.obsOf X m g n < Unit.obsOf X m g n' :=
  Poll.observed_lt hX hδ' (C.pclean hX) C.noInval hAlt hδ hnn hn

end Counted

/-! ### The slot -/

/-- **A slot of a one-CTA ring by the kinds of items** (module docstring). -/
structure KRing (L : Launch) (K : Kernel) (X : Execution) (np nc nk : Nat) where
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
      p % 2 = (okPolls E ((X.tr (prod a)).take k) + 1) % 2
  fullF : ∀ b j, j < okPolls F (X.tr (cons b)) →
    nk ≤ (SF.filter (fun x => Counted.ph X F itF x = Unit.obsOf X F (cons b) j)).card
  fullE : ∀ a n, 1 ≤ n → n < okPolls E (X.tr (prod a)) →
    nc ≤ (SE.filter (fun y => Counted.ph X E note y = Unit.obsOf X E (prod a) n)).card
  polF : ∀ x ∈ SF, ∃ i, opF x.1 x.2 = (prod (ownF x.1), i) ∧ i < (X.tr (prod (ownF x.1))).length ∧
    x.2 + 1 ≤ okPolls E ((X.tr (prod (ownF x.1))).take i)
  polE : ∀ y ∈ SE, ∃ i, cm y.1 y.2 = (cons y.1, i) ∧ i < (X.tr (cons y.1)).length ∧
    y.2 + 1 ≤ okPolls F ((X.tr (cons y.1)).take i)
  issueF : ∀ x ∈ SF, Relation.ReflTransGen (DepStep L K X)
    (.thread (opF x.1 x.2), false) (itF x.1 x.2, false)
  issueE : ∀ y ∈ SE, Relation.ReflTransGen (DepStep L K X)
    (.thread (cm y.1 y.2), false) (note y.1 y.2, false)

namespace KRing

variable {np nc nk : Nat}

theorem altF (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) (b : Fin nc) :
    SelectedAlternates (objectThreadSelected (R.cons b)) (X.objects R.F) 0 :=
  R.cF.alt hX (R.parF b)

theorem altE (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) (a : Fin np) :
    SelectedAlternates (objectThreadSelected (R.prod a)) (X.objects R.E) 1 :=
  R.cE.alt hX (R.parE a)

/-- The slot as an items ring. -/
def ring (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) :
    Items.Ring L K A X np nc 1 (fun _ => nk) where
  owner _ := 0
  ownF _ := R.ownF
  wE a n := (R.prod a, Poll.nth X R.E (R.prod a) n)
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
  oE a n := Unit.obsOf X R.E (R.prod a) n
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
  obsE a _ hn hw _ hy hph := R.cE.observed hX le_rfl (R.altE hX a) hn
    (Poll.nth_present.mp hw) hy hph
  fullF b _ hw := R.fullF b _ (Poll.nth_present.mp hw)
  fullE a _ hn hw := R.fullE a _ hn (Poll.nth_present.mp hw)
  ltF b _ _ hjj hw := ⟨Poll.nth_present.mpr (by have := Poll.nth_present.mp hw; omega),
    R.cF.lt hX (Nat.zero_le _) (R.altF hX b) (Nat.zero_le _) hjj (Poll.nth_present.mp hw)⟩
  ltE a _ _ hn hnn hw := ⟨Poll.nth_present.mpr (by have := Poll.nth_present.mp hw; omega),
    R.cE.lt hX le_rfl (R.altE hX a) hn hnn (Poll.nth_present.mp hw)⟩

/-- **The consumer's poll of `F` with `u` earlier ones observes every item of use `u`.** -/
theorem full_observes (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {b : Fin nc}
    {u : Nat} (hu : u < okPolls R.F (X.tr (R.cons b))) (k : Fin nk) :
    (k, u) ∈ R.SF ∧ UpdateBeforeWait (X.objects R.F) (R.itF k u)
      (.thread (R.cons b, Poll.nth X R.F (R.cons b) u)) := by
  obtain ⟨hS, hph⟩ := ((R.ring hX).content_full hX.depAcyclic (b := b) (j := u)
    (Poll.nth_present.mpr hu)).2 k
  exact ⟨hS, R.cF.ubw hX (Nat.zero_le _) (R.altF hX b) (Nat.zero_le _) hu hS hph⟩

/-- **The producer's poll of `E` with `u + 1` earlier ones observes every notification of use
`u`.** -/
theorem empty_observes (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {a : Fin np}
    {u : Nat} (hu : u + 1 < okPolls R.E (X.tr (R.prod a))) (b : Fin nc) :
    (b, u) ∈ R.SE ∧ UpdateBeforeWait (X.objects R.E) (R.note b u)
      (.thread (R.prod a, Poll.nth X R.E (R.prod a) (u + 1))) := by
  obtain ⟨hS, hph⟩ := ((R.ring hX).content_empty hX.depAcyclic (a := a) (n := u)
    (Poll.nth_present.mpr hu)).2 b
  exact ⟨hS, R.cE.ubw hX le_rfl (R.altE hX a) (by omega) hu hS hph⟩

/-- **The reuse**: an item of use `s` follows every consumer's polls of `F` for the uses before
`s`. -/
theorem reachF (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {x : Fin nk × Nat}
    (hx : x ∈ R.SF) (b : Fin nc) {j : Nat} (hj : j < x.2) :
    Relation.TransGen (DepStep L K X) (.thread (R.cons b, Poll.nth X R.F (R.cons b) j), true)
      (R.itF x.1 x.2, false) :=
  ((R.ring hX).reach hX.depAcyclic).1 0 x hx b j hj

/-- **The release**: a notification of use `t` follows every producer's polls of `E` for the uses
`1, …, t`. -/
theorem reachE (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {y : Fin nc × Nat}
    (hy : y ∈ R.SE) (a : Fin np) {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ y.2) :
    Relation.TransGen (DepStep L K X) (.thread (R.prod a, Poll.nth X R.E (R.prod a) n), true)
      (R.note y.1 y.2, false) :=
  ((R.ring hX).reach hX.depAcyclic).2 a y hy n h1 hn

end KRing
end
end PTX.MbarRing
