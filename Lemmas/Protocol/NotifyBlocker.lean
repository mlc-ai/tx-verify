-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitNotify
public import Lemmas.Protocol.MbarCommitObj

@[expose] public section

/-! # Who blocks a commit object

A proof tool for the progress of a commit object (`MbarRing.Notify.Obj`: count 1, completed by
the notifications of one thread `g`'s commits naming `m0`, polled with offset `δ`; FA4's S-full
and O-full objects). Its history is a unit-transaction history without bytes (`unitTx`), so its
arrival units are its phase number when it ends in a state (`units_eq_phase`), and they are its
fault-free arrival records (`units_eq_card`).

* **The phase is bounded by the poller's polls.** With the dependency paths of the object's reuse
  as thread `h` polls it (`Reach`), a counted unit's use is at most `h`'s successful polls minus
  `δ` (`S_le`): the notification of a later use would follow a successful poll `h` has not made,
  and the source of a dependency step from a successful poll is a present event
  (`DepStep.present_of_return`). So the phase is at most `h`'s successful polls minus `δ`, plus one
  (`phase_le`), and when it has the parity of those polls plus `δ`, at most the polls minus `δ`.
* **The producer is short, or a commit is undelivered** (`blocker`). When every commit's
  notification of every target is delivered and its records do not fault, each of `g`'s commits
  naming `m0` that targets `m` is a counted unit (`notified_rec`), so `g` made no more such commits
  than the phase number. -/

namespace PTX.MbarRing.Notify

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A commit to `m0` is a commit event naming `m0`. -/
theorem commit_of_commitsTo {m0 : Loc} {e : Event} (h : commitsTo m0 e = true) :
    ∃ sp, e.kind = .tc (.commit sp) ∧ sp.mbar = m0 := by
  unfold commitsTo at h
  split at h
  · next sp heq => exact ⟨sp, heq, of_decide_eq_true h⟩
  · cases h

namespace Obj

variable {m m0 : Loc} {g δ : Nat} {selected : Nat → Prop}

/-- **A commit object's history is a unit-transaction history without bytes.** -/
theorem unitTx (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) :
    UnitTx (X.objects m) 0 where
  arrive r hr _ c tx ha := by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨h1, h2, -⟩ := O.arrive_rec hk ha
    exact ⟨h1, h2⟩
  complete r hr _ n ha := by
    cases O.src r hr with
    | init ha' | poll _ _ ha' | commit _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  expected _ _ hs := PairTmaRing.expected_of_init hX O.init O.noInval hs

/-- **The arrival units of a commit object ending in a state are its phase number.** -/
theorem units_eq_phase (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) {st : State}
    (hs : stateBefore (X.objects m) (X.objects m).length = some st) :
    arrivalUnits (X.objects m) = st.phase := by
  have hch := X.objects_checked hX m
  have hu := O.unitTx hX
  have htx := hu.tx hch O.noInval le_rfl hs
  simp only [Nat.zero_mul] at htx
  exact Blocker.units_eq_phase hch O.noInval hs htx (hu.expected _ _ hs) O.noIncrement

/-- **The arrival units of a commit object are its fault-free arrival records.** -/
theorem units_eq_card (O : Obj X m g m0 δ selected) :
    arrivalUnits (X.objects m) = ((Finset.range (X.objects m).length).filter
      fun k => ((X.objects m)[k]?).any countedArrive = true).card := by
  rw [arrivalUnits_eq_length (fun r hr c tx _ ha => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      exact (O.arrive_rec hk ha).1), ← List.countP_eq_length_filter,
    ← MbarRing.Slot.countP_take_card, List.take_length]

/-- **A counted unit's use is at most the poller's successful polls minus `δ`.** -/
theorem S_le {h : Nat} (hR : Reach L K A X m g m0 δ h)
    {x : Fin 1 × Nat} (hx : x ∈ S X m g m0) : x.2 ≤ okPolls m (X.tr h) - δ := by
  by_contra hlt
  have hp := hR x hx (okPolls m (X.tr h) - δ) (by omega)
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.mp hp
  have := Poll.nth_present.mp (hc.present_of_return)
  omega

/-- **The phase of a commit object is at most the poller's successful polls minus `δ`, plus
one.** -/
theorem phase_le (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ) {h : Nat}
    (hR : Reach L K A X m g m0 δ h) {st : State}
    (hs : stateBefore (X.objects m) (X.objects m).length = some st) :
    st.phase ≤ okPolls m (X.tr h) - δ + 1 := by
  classical
  rw [← O.units_eq_phase hX hs, O.units_eq_card]
  refine le_trans (PairTmaRing.card_le_of_rel _ (Finset.range (okPolls m (X.tr h) - δ + 1))
    (fun k t => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m g m0 t)
    (fun k hk => ?_) (fun k _ k' _ t _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq (X.objects_checked hX m) hr hr'
        (hrid.trans hrid'.symm))) (by simp)
  obtain ⟨-, hka⟩ := Finset.mem_filter.mp hk
  cases hr : (X.objects m)[k]? with
  | none => rw [hr] at hka; cases hka
  | some r =>
    rw [hr, Option.any_some] at hka
    obtain ⟨hf, c, tx, ha⟩ := countedArrive_iff.mp hka
    obtain ⟨x, hx, hid⟩ := O.rec_S hr hf ha
    exact ⟨x.2, Finset.mem_range.mpr (by have := S_le hR hx; omega), r, rfl, hid⟩

/-- Every completed phase was caused by a distinct commit of the given issuer. This bound
also applies to waiters that skip generations instead of polling every phase. -/
theorem phase_le_commit_count (hX : Consistent L K A mem0 X)
    (O : Obj X m g m0 δ selected) {st : State}
    (hs : stateBefore (X.objects m) (X.objects m).length = some st) :
    st.phase ≤ (X.tr g).countP (commitsTo m0) := by
  classical
  rw [← O.units_eq_phase hX hs, O.units_eq_card]
  refine le_trans (PairTmaRing.card_le_of_rel _ (Finset.range ((X.tr g).countP (commitsTo m0)))
    (fun k t => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m g m0 t)
    (fun k hk => ?_) (fun k _ k' _ t _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq (X.objects_checked hX m) hr hr'
        (hrid.trans hrid'.symm))) (by simp)
  obtain ⟨-, hka⟩ := Finset.mem_filter.mp hk
  cases hr : (X.objects m)[k]? with
  | none => rw [hr] at hka; cases hka
  | some r =>
    rw [hr, Option.any_some] at hka
    obtain ⟨hf, c, tx, ha⟩ := countedArrive_iff.mp hka
    obtain ⟨x, hx, hid⟩ := O.rec_S hr hf ha
    obtain ⟨_, _, sp, he, hm, _, hc⟩ := O.S_rec hx
    refine ⟨x.2, Finset.mem_range.mpr ?_, r, rfl, hid⟩
    have hi : cm X g m0 x.2 < (X.tr g).length := PTX.len_of_get he
    have hEvent : (X.tr g)[cm X g m0 x.2]? = _ := he
    have hTaken := countP_take_mono (commitsTo m0) (X.tr g) hi
    rw [List.take_length, List.take_add_one, List.countP_append, hc, hEvent] at hTaken
    simpa [commitsTo, hm] using hTaken

/-- A delivered notification of the chosen commit is a counted arrival record. -/
theorem notified_rec_of_rank (hX : Consistent L K A mem0 X)
    (hff : ∀ r ∈ X.objects m, r.fault = none)
    {t pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (he : X.get (g, cm X g m0 t) = some ⟨pc, .tc (.commit sp)⟩)
    (htr : TcCommit.target sp rank = some m)
    (hn : rank ∈ X.tcNotified (g, cm X g m0 t)) :
    ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = it X m g m0 t ∧
      countedArrive r = true := by
  have hact : objectAction X X.async m (.async (g, cm X g m0 t) (.tcNotify rank)) =
      some (.arrive 1 0) := by
    simp [objectAction, he, htr, hn]
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 m).2.2 _ _ hact
  have hact' := ((hX.tma.2.2.1 m).2.1 r hr).1
  rw [hid, hact] at hact'
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  refine ⟨k, r, hk, ?_, countedArrive_iff.mpr ⟨hff r hr, 1, 0, (Option.some.inj hact').symm⟩⟩
  rw [hid]
  unfold it
  rw [rank_of he htr]

/-- **A delivered commit notification is a counted unit's record**: when every commit's
notification of every target is delivered and the object's records do not fault, `g`'s commit to
`m0` with `t` earlier ones, targeting `m`, has its record on `m`. -/
theorem notified_rec (hX : Consistent L K A mem0 X)
    (hff : ∀ r ∈ X.objects m, r.fault = none)
    (htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec}, X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = m0 → ∃ rank, TcCommit.target sp rank = some m)
    (hall : ∀ i s rank m', X.Commit i s → TcCommit.target s rank = some m' →
      rank ∈ X.tcNotified i)
    {t : Nat} (ht : t < (X.tr g).countP (commitsTo m0)) :
    ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = it X m g m0 t ∧
      countedArrive r = true := by
  obtain ⟨⟨pc, kind⟩, he, hp, -⟩ := nthEv_spec ht
  obtain ⟨sp, hk, hm⟩ := commit_of_commitsTo hp
  simp only at hk
  subst hk
  change X.get (g, cm X g m0 t) = some ⟨pc, .tc (.commit sp)⟩ at he
  obtain ⟨rank, htr⟩ := htgt he hm
  have hn := hall _ _ rank m ⟨pc, he⟩ htr
  exact notified_rec_of_rank hX hff he htr hn

/-- If the first `n` notifications have counted records, the object completed `n` phases. -/
theorem phase_ge_of_records (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected)
    {st : State} {n : Nat} (hs : stateBefore (X.objects m) (X.objects m).length = some st)
    (hCount : n ≤ (X.tr g).countP (commitsTo m0))
    (hRecords : ∀ t < n, ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
      r.id = it X m g m0 t ∧ countedArrive r = true) :
    n ≤ st.phase := by
  rw [← O.units_eq_phase hX hs, O.units_eq_card]
  refine le_trans (le_of_eq (Finset.card_range _).symm)
    (PairTmaRing.card_le_of_rel (Finset.range n) _
      (fun t k => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m g m0 t)
      (fun t ht => ?_) (fun t ht t' ht' k _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ => ?_))
  · obtain ⟨k, r, hk, hid, hca⟩ := hRecords t (Finset.mem_range.mp ht)
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (List.getElem?_eq_some_iff.mp hk).1, ?_⟩, r, hk, hid⟩
    rw [hk]
    exact hca
  · rw [hr] at hr'
    cases hr'
    have heq := hrid.symm.trans hrid'
    simp only [it, Ref.async.injEq, Prod.mk.injEq, true_and] at heq
    obtain ⟨-, -, -, hc⟩ := nthEv_spec ((Finset.mem_range.mp ht).trans_le hCount)
    obtain ⟨-, -, -, hc'⟩ := nthEv_spec ((Finset.mem_range.mp ht').trans_le hCount)
    unfold cm at heq
    rw [heq.1] at hc
    exact hc.symm.trans hc'

/-- **Who blocks a commit object.** When its final state has the parity of thread `h`'s
successful polls plus `δ` (at least `δ` of them), its phase is at most those polls minus `δ`,
and either `g` made no more commits to `m0` than the phase number, or some commit's notification
of a target is undelivered. -/
theorem blocker (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ) {h : Nat}
    (hR : Reach L K A X m g m0 δ h) (hff : ∀ r ∈ X.objects m, r.fault = none)
    (htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec}, X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = m0 → ∃ rank, TcCommit.target sp rank = some m)
    {st : State} (hs : stateBefore (X.objects m) (X.objects m).length = some st)
    (hpar : st.phase % 2 = (okPolls m (X.tr h) + δ) % 2) (hδ : δ ≤ okPolls m (X.tr h)) :
    st.phase ≤ okPolls m (X.tr h) - δ ∧
      ((X.tr g).countP (commitsTo m0) ≤ st.phase ∨
        ¬ ∀ i s rank m', X.Commit i s → TcCommit.target s rank = some m' →
          rank ∈ X.tcNotified i) := by
  classical
  have hle := O.phase_le hX hR hs
  refine ⟨by omega, ?_⟩
  by_cases hall : ∀ i s rank m', X.Commit i s → TcCommit.target s rank = some m' →
      rank ∈ X.tcNotified i
  · exact .inl (phase_ge_of_records hX O hs le_rfl fun _ ht =>
      notified_rec hX hff htgt hall ht)
  · exact .inr hall

end Obj
end
end PTX.MbarRing.Notify
