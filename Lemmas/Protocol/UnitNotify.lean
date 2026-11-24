-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ObservedSync
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Flow.NotCommit

@[expose] public section

/-! # The notifications of a commit object

A proof tool, the analog of `MbarRing.Unit.Obj` and its items (`UnitItems`) for an object of
count 1 completed by Tensor Core commit notifications (FA4's S-full and O-full objects). An object
`m` whose every record is its initialization, a poll, or the notification of a commit of one
thread `g` naming barrier `m0` (`Source`), initialized first with count 1, never invalidated,
whose successful polls have the parity of their thread's earlier successful polls plus `δ`
(`Obj`; built from the record sources by `Obj.of_commits`). A notification is numbered by its
commit's *use*: `g`'s commits to `m0` before it.

* Unit `t` is the notification on `m` of `g`'s commit with `t` earlier ones (`it`, the rank the
  commit's target selection gives `m`, unique by `rank_eq`). The counted units are those with a
  fault-free record (`S`), each in the phase of its record (`ph`); every fault-free arrival record
  is a counted unit's (`rec_S`), and a counted unit's commit names `m0` and targets `m`
  (`S_rec`).
* A selected poller's success with at least `δ` earlier polls observes a completed phase and
  every counted unit of it (`observed`); that phase holds a counted unit (`card_phase`).
* With the dependency paths of the object's reuse as thread `h` polls it (`Reach`), the units are
  `MbarRing.Multi.Units` of one kind (`Obj.units`), and `h`'s poll with `u + δ` earlier
  successful polls observes the notification of the commit with `u` earlier commits
  (`Obj.observes`). -/

namespace PTX.MbarRing.Notify

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- How a record of a commit object arises. -/
inductive Source (X : Execution) (m : Loc) (g : Nat) (m0 : Loc) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {h j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (h, j))
      (he : X.get (h, j) = some ⟨pc, .wait m p ok acq sc⟩) (ha : r.action = .pollParity p ok)
  | commit {i pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
      (hid : r.id = .async (g, i) (.tcNotify rank))
      (he : X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = m0)
      (ht : TcCommit.target sp rank = some m) (ha : r.action = .arrive 1 0)

/-- **A commit object**: completed by the notifications of thread `g`'s commits naming `m0`,
polled with offset `δ`. -/
structure Obj (X : Execution) (m : Loc) (g : Nat) (m0 : Loc) (δ : Nat)
    (selected : Nat → Prop := fun _ => True) : Prop where
  src : ∀ r ∈ X.objects m, Source X m g m0 r
  init : PairTmaRing.InitFirst X m 1
  noInval : NoInval (X.objects m)
  /-- A selected thread's successful polls use the same alternating offset `δ`. -/
  parityOf : ∀ {h k pc p : Nat} {acq : Bool} {sc : MbarScope},
    selected h → X.get (h, k) = some ⟨pc, .wait m p true acq sc⟩ →
      p % 2 = (okPolls m ((X.tr h).take k) + δ) % 2
  δ_le : δ ≤ 1

/-- The selection of a commit's targets is injective in the rank. -/
theorem rank_eq {sp : TcCommit.Spec} {r r' : Fin 16} {m : Loc}
    (h : TcCommit.target sp r = some m) (h' : TcCommit.target sp r' = some m) : r = r' := by
  unfold TcCommit.target at h h'
  split_ifs at h h'
  simp only [Option.some.injEq] at h h'
  rw [← h'] at h
  simp only [Loc.mk.injEq] at h
  exact Fin.ext (by omega)

/-- Thread `g`'s commit to `m0` with `t` earlier ones. -/
def cm (X : Execution) (g : Nat) (m0 : Loc) (t : Nat) : Nat := nthEv X (commitsTo m0) g t

open Classical in
/-- The rank by which that commit notifies `m`. -/
def rank (X : Execution) (m : Loc) (g : Nat) (m0 : Loc) (t : Nat) : Fin 16 :=
  if h : ∃ r : Fin 16, ∃ pc sp, X.get (g, cm X g m0 t) = some ⟨pc, .tc (.commit sp)⟩ ∧
    TcCommit.target sp r = some m then Classical.choose h else 0

/-- Unit `t`: the notification on `m` of `g`'s commit to `m0` with `t` earlier ones. -/
def it (X : Execution) (m : Loc) (g : Nat) (m0 : Loc) (t : Nat) : Ref :=
  .async (g, cm X g m0 t) (.tcNotify (rank X m g m0 t))

open Classical in
/-- The counted units of `m`: those with a fault-free record. -/
def S (X : Execution) (m : Loc) (g : Nat) (m0 : Loc) : Finset (Fin 1 × Nat) :=
  (Finset.univ ×ˢ Finset.range ((X.tr g).length + 1)).filter fun x =>
    ∃ r ∈ X.objects m, r.id = it X m g m0 x.2 ∧ r.fault = none ∧ r.action = .arrive 1 0

/-- The phase of a counted unit's record. -/
def ph (X : Execution) (m : Loc) (g : Nat) (m0 : Loc) (x : Fin 1 × Nat) : Nat :=
  Poll.phaseOf X m (it X m g m0 x.2)

/-- The rank of a commit notifying `m` is its unit's. -/
theorem rank_of {m m0 : Loc} {g t pc : Nat} {sp : TcCommit.Spec} {r : Fin 16}
    (he : X.get (g, cm X g m0 t) = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp r = some m) : rank X m g m0 t = r := by
  have hex : ∃ r : Fin 16, ∃ pc sp, X.get (g, cm X g m0 t) = some ⟨pc, .tc (.commit sp)⟩ ∧
      TcCommit.target sp r = some m := ⟨r, pc, sp, he, ht⟩
  unfold rank
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨pc', sp', he', ht'⟩ := Classical.choose_spec hex
  rw [he] at he'
  cases he'
  exact rank_eq ht' ht

/-- **The commit object from its record sources**: no thread arrives on `m`, no tensor copy,
linear copy, `cp.async.mbarrier.arrive` or cancellation request completes on it, nothing
invalidates it, and every commit targeting it is `g`'s, naming `m0`. -/
theorem Obj.of_commits (hX : Consistent L K A mem0 X) {m m0 : Loc} {g δ : Nat}
    (hinit : PairTmaRing.InitFirst X m 1)
    (harr : ∀ {h i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
      X.get (h, i) ≠ some ⟨pc, .arrive m tx cnt rel sc⟩)
    (hten : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
      X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ m)
    (hcopy : ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec},
      X.get i = some ⟨pc, .copy s⟩ → s.completion ≠ .mbarrier m)
    (hcpa : ∀ {i : EvId} {pc : Nat} {m' : Loc} {noinc : Bool},
      X.get i = some ⟨pc, .asyncArrive m' noinc⟩ → m' ≠ m)
    (hclc : ∀ {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat},
      X.get i ≠ some ⟨pc, .clcIssue sp tg⟩)
    (hinv : ∀ {i : EvId} {pc : Nat} {m' : Loc}, X.get i ≠ some ⟨pc, .mbInval m'⟩)
    (hcom : ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
      X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some m →
        i.1 = g ∧ sp.mbar = m0)
    (hpar : ∀ {h k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait m p true acq sc⟩ →
        p % 2 = (okPolls m ((X.tr h).take k) + δ) % 2)
    (hδ : δ ≤ 1) : Obj X m g m0 δ where
  src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact (hinv he).elim
    | arrive _ he _ => exact (harr he).elim
    | wait hid he ha => exact .poll hid he ha
    | tensor _ he hm _ => exact (hten he hm).elim
    | bulk _ he hc _ _ => exact (hcopy he hc).elim
    | increment _ he _ => exact (hcpa he rfl).elim
    | arriveOn _ he hm _ _ => exact (hcpa he hm).elim
    | @commit i pc sp rank hid he ht ha =>
      obtain ⟨g', i'⟩ := i
      obtain ⟨hg, hm⟩ := hcom he ht
      subst hg
      exact .commit hid he hm ht ha
    | clc _ he _ _ _ => exact (hclc he).elim
  init := hinit
  noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => hinv he) _
  parityOf _ := hpar
  δ_le := hδ

variable {selected : Nat → Prop}

namespace Obj

variable {m m0 : Loc} {g δ : Nat}

/-- In the default view, every thread is selected. -/
theorem parity (O : Obj X m g m0 δ) {h k pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .wait m p true acq sc⟩) :
    p % 2 = (okPolls m ((X.tr h).take k) + δ) % 2 :=
  O.parityOf trivial he

/-- The object's poll records do not fault. -/
theorem pclean (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) :
    ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none :=
  PairTmaRing.poll_clean hX O.init O.noInval

/-- Each thread's successful polls alternate parity with offset `δ`. -/
theorem alt (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) (h : Nat)
    (hh : selected h := by trivial) :
    SelectedAlternates (objectThreadSelected h) (X.objects m) δ :=
  MbarRing.Poll.alternates hX (O.pclean hX) fun _ _ _ _ _ he => O.parityOf hh he

/-- An arrival record is the notification of a commit of `g` naming `m0`, of count 1. -/
theorem arrive_rec (O : Obj X m g m0 δ selected) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (ha : r.action = .arrive c tx) :
    c = 1 ∧ tx = 0 ∧ ∃ i pc sp rank, r.id = .async (g, i) (.tcNotify rank) ∧
      X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = m0 ∧
      TcCommit.target sp rank = some m := by
  cases O.src r (List.mem_of_getElem? hr) with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | commit hid he hm ht ha' =>
    rw [ha] at ha'
    cases ha'
    exact ⟨rfl, rfl, _, _, _, _, hid, he, hm, ht⟩

/-- A counted unit's record and commit: a commit of `g` naming `m0`, with `t` earlier ones,
targeting `m` at the unit's rank. -/
theorem S_rec (O : Obj X m g m0 δ selected) {x : Fin 1 × Nat} (hx : x ∈ S X m g m0) :
    (∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = it X m g m0 x.2 ∧
      r.fault = none ∧ r.action = .arrive 1 0) ∧
    ∃ pc sp, X.get (g, cm X g m0 x.2) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = m0 ∧
      TcCommit.target sp (rank X m g m0 x.2) = some m ∧
      ((X.tr g).take (cm X g m0 x.2)).countP (commitsTo m0) = x.2 := by
  obtain ⟨-, r, hr, hid, hf, ha⟩ := Finset.mem_filter.mp hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨-, -, i, pc, sp, rk, hid', he, hm, ht⟩ := O.arrive_rec hk ha
  rw [hid] at hid'
  simp only [it, Ref.async.injEq, Prod.mk.injEq, Part.tcNotify.injEq, true_and] at hid'
  obtain ⟨hi, hrk⟩ := hid'
  rw [← hi] at he
  refine ⟨⟨k, r, hk, hid, hf, ha⟩, pc, sp, he, hm, by rw [hrk]; exact ht, ?_⟩
  exact (nthEv_spec_of_get he).2

/-- A fault-free arrival record is a counted unit's. -/
theorem rec_S (O : Obj X m g m0 δ selected) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (hf : r.fault = none) (ha : r.action = .arrive c tx) :
    ∃ x ∈ S X m g m0, r.id = it X m g m0 x.2 := by
  classical
  obtain ⟨rfl, rfl, i, pc, sp, rk, hid, he, hm, ht⟩ := O.arrive_rec hr ha
  have hp : commitsTo m0 ⟨pc, .tc (.commit sp)⟩ = true := by simp [commitsTo, hm]
  set t := ((X.tr g).take i).countP (commitsTo m0)
  have hcm : cm X g m0 t = i := nthEv_eq he hp
  have hit : it X m g m0 t = .async (g, i) (.tcNotify rk) := by
    unfold it
    rw [rank_of (by rw [hcm]; exact he) ht, hcm]
  have hlt : t < (X.tr g).length + 1 := by
    have h1 := len_of_get he
    have h2 : t ≤ i := (List.countP_le_length).trans (List.length_take_le _ _)
    simp only at h1
    omega
  refine ⟨(0, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_range.mpr hlt⟩, r, List.mem_of_getElem? hr, by rw [hid, hit], hf, ha⟩, ?_⟩
  rw [hid, hit]

/-- The record of thread `h`'s successful poll with `n ≥ δ` earlier ones, and the completed phase
it observes. -/
theorem poll_obs (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) {h n : Nat}
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr h)) (hh : selected h := by trivial) :
    ∃ (k : Nat) (w : Record Ref) (st : State), (X.objects m)[k]? = some w ∧
      w.id = .thread (h, MbarRing.Poll.nth X m h n) ∧
      w.reply.waited = some true ∧ w.fault = none ∧ stateBefore (X.objects m) k = some st ∧
      0 < st.phase ∧ observedAt (X.objects m) k = some (st.phase - 1) ∧
      Unit.obsOf X m h n = st.phase - 1 := by
  obtain ⟨k, w, -, hk, hwid, -, hww, hwf, hsel⟩ := MbarRing.Poll.record hX (O.pclean hX) hn
  have hs : objectThreadSelected h w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX m)
    O.noInval O.δ_le (O.alt hX h hh) hk hs hww (by omega)
  refine ⟨k, w, st, hk, hwid, hww, hwf, hst, hpos, ho, ?_⟩
  unfold Unit.obsOf
  rw [← hwid]
  exact MbarRing.Poll.observedOf_eq hX hk ho

/-- A counted unit's record in its phase. -/
theorem S_phase (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) {x : Fin 1 × Nat}
    (hx : x ∈ S X m g m0) :
    ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = it X m g m0 x.2 ∧
      r.fault = none ∧ r.action = .arrive 1 0 ∧
      phaseAt (X.objects m) k = some (ph X m g m0 x) := by
  obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := O.S_rec hx
  obtain ⟨-, sd, hsd, -⟩ := PairTmaRing.state_of_init hX O.init O.noInval hk
    (by intro n; rw [ha]; simp)
  have hp : phaseAt (X.objects m) k = some sd.phase := by simp [phaseAt, hsd]
  refine ⟨k, r, hk, hid, hf, ha, ?_⟩
  unfold ph
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hk hp]
  exact hp

/-- **A poll observes the counted units of its phase.** -/
theorem observed (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) {h n : Nat}
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr h)) {x : Fin 1 × Nat} (hx : x ∈ S X m g m0)
    (hph : ph X m g m0 x = Unit.obsOf X m h n) (hh : selected h := by trivial) :
    Witness L X (it X m g m0 x.2) (h, MbarRing.Poll.nth X m h n) := by
  obtain ⟨kw, w, st, hkw, hwid, hww, hwf, -, -, ho, hoo⟩ := O.poll_obs hX hδ hn hh
  obtain ⟨k, r, hk, hid, hf, ha, hp⟩ := O.S_phase hX hx
  rw [hph, hoo] at hp
  have hcu : CounterUpdate r.action := by rw [ha]; trivial
  have hob := Consistent.observed_of_phase hX O.noInval hk hf hcu hkw hww hp ho
  rw [hid, hwid] at hob
  exact Witness.of_mbarObserved hob

/-- The object has no pending-count increment. -/
theorem noIncrement (O : Obj X m g m0 δ selected) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases O.src r hr with
    | init ha | poll _ _ ha | commit _ _ _ _ ha => rw [hi] at ha; cases ha

open Classical in
/-- **The phase a poll observes holds a counted unit.** -/
theorem card_phase (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) {h n : Nat}
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr h)) (hh : selected h := by trivial) :
    1 ≤ ((S X m g m0).filter (fun x => ph X m g m0 x = Unit.obsOf X m h n)).card := by
  obtain ⟨kw, w, st, hkw, -, -, -, hst, hpos, -, hoo⟩ := O.poll_obs hX hδ hn hh
  have hch := X.objects_checked hX m
  have hcard := hch.card_unit_arrivals_phase O.noInval (n := 1) (q := st.phase - 1)
    (fun _ r c tx hr _ ha => (O.arrive_rec hr ha).1)
    (fun _ st' _ hs => PairTmaRing.expected_of_init hX O.init O.noInval hs) O.noIncrement
    (List.getElem?_eq_some_iff.mp hkw).1.le hst (by omega)
  refine le_trans (le_of_eq hcard.symm) ?_
  refine PairTmaRing.card_le_of_rel _ _
    (fun k x => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m g m0 x.2)
    (fun k hk => ?_) (fun k _ k' _ x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨-, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hk
  obtain ⟨x, hx, hid⟩ := O.rec_S hr hf ha
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, r, hr, hid⟩
  unfold ph
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hr hph, hoo]

end Obj

/-- **The reuse of a commit object as thread `h` polls it**: the notification of the commit with
`t` earlier commits follows, in the dependency order, `h`'s polls for the uses before `t` (its
successful polls with `j + δ` earlier ones, `j < t`). -/
def Reach (L : Launch) (K : Kernel) (_A : List Assumption) (X : Execution) (m : Loc) (g : Nat)
    (m0 : Loc) (δ h : Nat) : Prop :=
  ∀ x ∈ S X m g m0, ∀ j < x.2,
    Relation.TransGen (DepStep L K X) (.thread (h, Poll.nth X m h (j + δ)), true)
      (it X m g m0 x.2, false)

/-- The reuse from the dependency paths of the recorded notifications, numbered by their commits'
earlier commits to `m0`. -/
theorem Reach.of_records (O : Obj X m g m0 δ selected) {h : Nat}
    (hR : ∀ i rank, (∃ r ∈ X.objects m, r.id = .async (g, i) (.tcNotify rank) ∧
        r.fault = none) → ∀ j < ((X.tr g).take i).countP (commitsTo m0),
      Relation.TransGen (DepStep L K X) (.thread (h, Poll.nth X m h (j + δ)), true)
        (.async (g, i) (.tcNotify rank), false)) :
    Reach L K A X m g m0 δ h := by
  intro x hx j hj
  obtain ⟨⟨k, r, hk, hid, hf, -⟩, -, -, -, -, -, hc⟩ := O.S_rec hx
  exact hR _ _ ⟨r, List.mem_of_getElem? hk, hid, hf⟩ j (by rw [hc]; exact hj)

namespace Obj

variable {m m0 : Loc} {g δ : Nat}

/-- **A commit object read by one consumer thread**: its units, of one kind. -/
def units (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) (h : Nat)
    (hR : Reach L K A X m g m0 δ h) (hh : selected h := by trivial) :
    Multi.Units L K A X (Fin 1) where
  S := S X m g m0
  ph := ph X m g m0
  use _ t := t
  it _ t := it X m g m0 t
  w j := (h, Poll.nth X m h (j + δ))
  o j := Unit.obsOf X m h (j + δ)
  use_inj _ _ _ _ _ he := he
  obs _ hp x hx hph := O.observed hX (Nat.le_add_left _ _) (Poll.nth_present.mp hp) hx hph hh
  full _ hp := by
    classical
    convert O.card_phase hX (Nat.le_add_left _ _) (Poll.nth_present.mp hp) hh using 1
    simp
  lt _ _ hjj hp := ⟨Poll.nth_present.mpr (by have := Poll.nth_present.mp hp; omega),
    Poll.observed_lt hX O.δ_le (O.pclean hX) O.noInval (O.alt hX h hh) (Nat.le_add_left _ _)
      (by omega) (Poll.nth_present.mp hp)⟩
  reach x hx j hj := hR x hx j hj

/-- **The poll with `u + δ` earlier successful polls observes the notification of the commit
with `u` earlier commits.** -/
theorem observes (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) {h j pc p u : Nat}
    {acq : Bool} {sc : MbarScope} (hR : Reach L K A X m g m0 δ h)
    (he : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩)
    (hq : okPolls m ((X.tr h).take j) = u + δ) (hh : selected h := by trivial) :
    ∃ i pc' sp rank, X.get (g, i) = some ⟨pc', .tc (.commit sp)⟩ ∧ sp.mbar = m0 ∧
      TcCommit.target sp rank = some m ∧ ((X.tr g).take i).countP (commitsTo m0) = u ∧
      rank ∈ X.tcNotified (g, i) ∧
      WaitObserves X (.async (g, i) (.tcNotify rank)) (h, j) m acq sc := by
  set U := O.units hX h hR hh
  have hjn : Poll.nth X m h (u + δ) = j := by
    rw [← hq]
    exact Poll.nth_eq he
  have hpw : X.RefPresent (.thread (U.w u)) := by
    show X.RefPresent (.thread (h, Poll.nth X m h (u + δ)))
    rw [hjn]
    exact ⟨_, he⟩
  obtain ⟨t, hS, ht, hobs⟩ := U.observes hX.depAcyclic hpw 0
  change t = u at ht
  subst ht
  change Witness L X (it X m g m0 t) (h, Poll.nth X m h (t + δ)) at hobs
  rw [hjn] at hobs
  obtain ⟨-, pc', sp, hget, hm, ht, hc⟩ := O.S_rec hS
  obtain ⟨hrank, hwo⟩ := hobs.waitObserves_tcNotify he
  exact ⟨_, pc', sp, _, hget, hm, ht, hc, hrank, hwo⟩

end Obj
end
end PTX.MbarRing.Notify
