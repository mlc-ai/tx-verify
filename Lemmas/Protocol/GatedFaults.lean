-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitGate
public import Lemmas.Protocol.UnitNotify
public import Lemmas.Protocol.MbarPending

@[expose] public section

/-! # The arrivals of a gated object are fault-free

A proof tool. An object whose every arrival is one unit without transaction bytes, labeled by a
kind of a set of `N` kinds (`N` the expected count) and a use, two arrivals with one label being
one record, and whose every arrival of use `s ≥ 1` follows, in the object's history, a successful
poll that found a phase of at least `s`:

* **every arrival lies in the phase of its use and does not fault** (`CheckedLog.gated_arrive`),
  by induction on the history position: the gating poll bounds the phase from below
  (`phase_mono`); a later phase would hold `N` fault-free arrivals of the use, of `N` distinct
  kinds by the induction, the arriving one's too, before it. In the phase of its use the arrival
  finds the phase observed (by the gating poll, or the initial phase) and a pending arrival (no
  transaction bytes, `stateBefore_pending_pos`), so it neither arrives in an unobserved phase nor
  underflows.

For an object with an initialization first (`PairTmaRing.InitFirst`) and that discipline every
record is fault-free (`fault_free_of_gated`), in particular:

* a unit object (`Unit.Obj`) whose every producer arrival of use `s ≥ 1` follows, in the
  dependency order, a successful poll with `s + δ - 1` earlier ones (`Unit.Gated`,
  `Unit.Obj.fault_free`); a gated unit object (`Unit.Gate`) is one (`Unit.Gate.gated`);
* a commit object (`Notify.Obj`) whose every notification of a commit with `t ≥ 1` earlier
  commits follows, in the dependency order, a successful poll with `t + δ - 1` earlier ones
  (`Notify.Gated`, `Notify.Obj.fault_free`).

The dependency path places the poll before the arrival in the object's history
(DEP-ORDER, `Unit.Gate.poll_before`), and the poll with `s + δ - 1` earlier successful
ones of its thread found a phase of at least `s` (`MbarRing.poll_phase_ge`). A path from a
thread's poll with `s + δ - 1` earlier ones gives the gate (`Unit.gated_of_paths`,
`Notify.gated_of_paths`): the path's start is present (`present_of_path`). The gate is stated
for every arrival event, not only the counted ones: an arrival that would fault is not counted,
so a premise on counted arrivals says nothing about it. An object whose records other than its
initialization are polls is fault-free (`fault_free_of_polls`). -/

namespace PTX

namespace MBarrier

variable {ι : Type}

/-- **The arrivals of a gated log lie in the phase of their use and do not fault.** -/
theorem CheckedLog.gated_arrive {κ : Type} [DecidableEq κ] {log : List (Record ι)}
    (h : CheckedLog log) (hni : NoInval log) (U : Finset κ) (lab : ι → κ × Nat)
    (hexp : ∀ i s, i ≤ log.length → stateBefore log i = some s → s.expected = U.card ∧ s.tx = 0)
    (hdef : ∀ (k : Nat) (r : Record ι) (c tx : Nat), log[k]? = some r → r.action = .arrive c tx →
      ∃ s, stateBefore log k = some s)
    (hunit : ∀ (k : Nat) (r : Record ι) (c tx : Nat), log[k]? = some r → r.action = .arrive c tx →
      c = 1 ∧ tx = 0 ∧ (lab r.id).1 ∈ U)
    (hinj : ∀ (k k' : Nat) (r r' : Record ι) (c tx c' tx' : Nat), log[k]? = some r →
      log[k']? = some r' → r.action = .arrive c tx → r'.action = .arrive c' tx' →
        lab r.id = lab r'.id → k = k')
    (hgate : ∀ (k : Nat) (r : Record ι) (c tx : Nat), log[k]? = some r → r.action = .arrive c tx →
      1 ≤ (lab r.id).2 → ∃ kw w sw, kw < k ∧ log[kw]? = some w ∧ w.reply.waited = some true ∧
        stateBefore log kw = some sw ∧ (lab r.id).2 ≤ sw.phase)
    (hinc : incrementsBefore log log.length = 0) :
    ∀ (k : Nat) (r : Record ι) (c tx : Nat), log[k]? = some r → r.action = .arrive c tx →
      r.fault = none ∧ phaseAt log k = some (lab r.id).2 := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro r c tx hk ha
  obtain ⟨rfl, rfl, hU⟩ := hunit k r c tx hk ha
  have hkl : k < log.length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨s, hs⟩ := hdef k r 1 0 hk ha
  obtain ⟨hse, hstx⟩ := hexp k s hkl.le hs
  -- the gating poll found a phase of at least the use, and the phase only grows
  have hpoll : 1 ≤ (lab r.id).2 → ∃ kw w sw, kw < k ∧ log[kw]? = some w ∧
      w.reply.waited = some true ∧ stateBefore log kw = some sw ∧ (lab r.id).2 ≤ sw.phase ∧
      sw.phase ≤ s.phase := by
    intro hpos
    obtain ⟨kw, w, sw, hkw, hw, hww, hsw, hle⟩ := hgate k r 1 0 hk ha hpos
    obtain ⟨s2, hs2, hmono⟩ := h.phase_mono hni hkw.le hkl.le hsw
    rw [hs] at hs2
    cases hs2
    exact ⟨kw, w, sw, hkw, hw, hww, hsw, hle, hmono⟩
  have hlo : (lab r.id).2 ≤ s.phase := by
    rcases Nat.eq_zero_or_pos (lab r.id).2 with h0 | hpos
    · omega
    · obtain ⟨-, -, -, -, -, -, -, h1, h2⟩ := hpoll hpos
      omega
  -- a later phase would hold an arrival of every kind with this use before it
  have hup : s.phase ≤ (lab r.id).2 := by
    by_contra hgt
    replace hgt := Nat.lt_of_not_le hgt
    have hcard := h.card_unit_arrivals_phase hni (n := U.card) (q := (lab r.id).2)
      (fun i r c tx hr _ ha => (hunit i r c tx hr ha).1)
      (fun i s' hi hs' => (hexp i s' hi hs').1) hinc hkl.le hs hgt
    have hle : ((Finset.range log.length).filter
        (fun i => UnitArrivalIn log (lab r.id).2 i)).card ≤ (U.erase (lab r.id).1).card := by
      apply Finset.card_le_card_of_injOn (fun i => (lab ((log[i]?).getD r).id).1)
      · intro i hi
        obtain ⟨-, q, tq, hq, haq, hfq, hpq⟩ := Finset.mem_filter.mp hi
        have hik : i < k := by
          by_contra hge
          replace hge := Nat.le_of_not_lt hge
          obtain ⟨t, ht, hst⟩ := h.phase_mono hni hge
            (List.getElem?_eq_some_iff.mp hq).1.le hs
          rw [phaseAt, ht] at hpq
          simp only [Option.map_some, Option.some.injEq] at hpq
          omega
        obtain ⟨-, hpi⟩ := ih i hik q 1 tq hq haq
        rw [hpq, Option.some.injEq] at hpi
        simp only [hq, Option.getD_some]
        refine Finset.mem_erase.mpr ⟨fun he => ?_, (hunit i q 1 tq hq haq).2.2⟩
        have hlab : lab q.id = lab r.id := Prod.ext he hpi.symm
        have := hinj i k q r 1 tq 1 0 hq hk haq ha hlab
        omega
      · intro i hi i' hi' he
        obtain ⟨-, q, tq, hq, haq, hfq, hpq⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
        obtain ⟨-, q', tq', hq', haq', hfq', hpq'⟩ :=
          Finset.mem_filter.mp (Finset.mem_coe.mp hi')
        have hik : ∀ {i : Nat} {q : Record ι}, log[i]? = some q →
            phaseAt log i = some (lab r.id).2 → i < k := by
          intro i q hq hpq
          by_contra hge
          replace hge := Nat.le_of_not_lt hge
          obtain ⟨t, ht, hst⟩ := h.phase_mono hni hge
            (List.getElem?_eq_some_iff.mp hq).1.le hs
          rw [phaseAt, ht] at hpq
          simp only [Option.map_some, Option.some.injEq] at hpq
          omega
        obtain ⟨-, hpi⟩ := ih i (hik hq hpq) q 1 tq hq haq
        obtain ⟨-, hpi'⟩ := ih i' (hik hq' hpq') q' 1 tq' hq' haq'
        rw [hpq, Option.some.injEq] at hpi
        rw [hpq', Option.some.injEq] at hpi'
        simp only [hq, hq', Option.getD_some] at he
        exact hinj i i' q q' 1 tq 1 tq' hq hq' haq haq' (Prod.ext he (hpi.symm.trans hpi'))
    rw [Finset.card_erase_of_mem hU, hcard] at hle
    have := Finset.card_pos.mpr ⟨_, hU⟩
    omega
  have hph : s.phase = (lab r.id).2 := le_antisymm hup hlo
  have hobs : s.observed = true := by
    refine h.observed_of_poll hni hs ?_
    rcases Nat.eq_zero_or_pos (lab r.id).2 with h0 | hpos
    · exact .inl (by omega)
    · obtain ⟨kw, w, sw, hkw, hw, hww, hsw, h1, h2⟩ := hpoll hpos
      exact .inr ⟨kw, w, sw, hkw, hw, hww, hsw, by omega⟩
  have hpend := stateBefore_pending_pos h hs hstx
  have hok := h.at hk
  rw [hs] at hok
  refine ⟨?_, by simp [phaseAt, hs, hph]⟩
  unfold RecordOk at hok
  rw [ha] at hok
  simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, hobs] at hok
  split_ifs at hok with h1 h2 h3
  · exact hok.2
  · exact absurd (by rw [hstx]; norm_num [validTx, limit]) h3
  · omega
  · exact absurd (by norm_num [validCount, validTxOperand, limit]) h1

end MBarrier

namespace MbarRing

open AsyncCopy Flow
open MBarrier hiding okPolls

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The transaction counter of an object stays zero when no arrival carries transaction bytes
and nothing completes transactions on it. -/
theorem tx_zero_of (hX : Consistent L K A mem0 X) {m : Loc} (hni : NoInval (X.objects m))
    (harr : ∀ r ∈ X.objects m, ∀ c tx, r.action = .arrive c tx → tx = 0)
    (hcomp : ∀ r ∈ X.objects m, ∀ n, r.action ≠ .completeTx n) {j : Nat}
    (hj : j ≤ (X.objects m).length) {st : State}
    (hst : stateBefore (X.objects m) j = some st) : st.tx = 0 := by
  have hbal := (X.objects_checked hX m).tx_balance hni hj hst
  have hz : ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects m) →
      expectedTxBytes xs = 0 ∧ completedTxBytes xs = 0 := by
    intro xs hxs
    induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons r rest ih =>
      have hr := hxs r List.mem_cons_self
      obtain ⟨h1, h2⟩ := ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))
      rw [expectedTxBytes, completedTxBytes, h1, h2]
      unfold Record.expectedTxBytes Record.completedTxBytes
      cases ha : r.action with
      | arrive n tx =>
        rw [harr r hr n tx ha]
        cases r.fault <;> simp
      | completeTx n => exact absurd ha (hcomp r hr n)
      | _ => cases r.fault <;> simp
  obtain ⟨h1, h2⟩ := hz _ (fun q hq => List.mem_of_mem_take hq)
  rw [hbal, h1, h2]
  rfl

/-- **A successful poll found a phase of at least its use**: the record of thread `h`'s
successful poll with `n` earlier ones, polled with offset `δ`, has a state whose phase plus `δ`
exceeds `n`. -/
theorem poll_phase_ge_for_thread (hX : Consistent L K A mem0 X) {m : Loc} {δ : Nat} (hδ : δ ≤ 1)
    (hni : NoInval (X.objects m))
    (hclean : ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none)
    {h : Nat}
    (hpar : ∀ {k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait m p true acq sc⟩ →
        p % 2 = (okPolls m ((X.tr h).take k) + δ) % 2)
    {j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩) :
    ∃ kw w sw, (X.objects m)[kw]? = some w ∧ w.id = .thread (h, j) ∧
      (∃ p', w.action = .pollParity p' true) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects m) kw = some sw ∧ okPolls m ((X.tr h).take j) + 1 ≤ sw.phase + δ := by
  have hlt : okPolls m ((X.tr h).take j) < okPolls m (X.tr h) := by
    have h1 := MbarRing.Poll.okPoll_get he
    have h2 := MbarRing.Poll.okPolls_mono m (X.tr h) (show j + 1 ≤ (X.tr h).length from
      (List.getElem?_eq_some_iff.mp he).1)
    rw [List.take_length] at h2
    omega
  obtain ⟨kw, w, p', hkw, hwid, hwa, hww, -, hsel⟩ := MbarRing.Poll.record hX hclean hlt
  rw [MbarRing.Poll.nth_eq he] at hwid
  have halt : SelectedAlternates (objectThreadSelected h) (X.objects m) δ :=
    MbarRing.Poll.alternates hX hclean fun _ _ _ _ _ he => hpar he
  obtain ⟨sw, hsw, hge, -⟩ := (X.objects_checked hX m).selected_poll_phase_ge hni _ hδ halt hkw
    (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww
  rw [hsel] at hge
  exact ⟨kw, w, sw, hkw, hwid, ⟨p', hwa⟩, hww, hsw, hge⟩

/-- Specialization when all threads poll with offset `δ`. -/
theorem poll_phase_ge (hX : Consistent L K A mem0 X) {m : Loc} {δ : Nat} (hδ : δ ≤ 1)
    (hni : NoInval (X.objects m))
    (hclean : ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none)
    (hpar : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
        p % 2 = (okPolls m ((X.tr g).take k) + δ) % 2)
    {h j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩) :
    ∃ kw w sw, (X.objects m)[kw]? = some w ∧ w.id = .thread (h, j) ∧
      (∃ p', w.action = .pollParity p' true) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects m) kw = some sw ∧ okPolls m ((X.tr h).take j) + 1 ≤ sw.phase + δ := by
  exact poll_phase_ge_for_thread hX hδ hni hclean hpar he

/-- **Every record of a gated object is fault-free.** An object initialized first with count
`|U|`, never invalidated, polled with offset `δ`, nothing completing transactions on it and no
pending-count increment, whose arrivals are units without transaction bytes labeled by a kind of
`U` and a use, two arrivals with one label being one, and whose every arrival of use `s ≥ 1`
follows, in the dependency order, a successful poll with `s + δ - 1` earlier ones of its
thread. -/
theorem fault_free_of_selected_gate (hX : Consistent L K A mem0 X) {m : Loc} {δ : Nat} (hδ : δ ≤ 1)
    {κ : Type} [DecidableEq κ] (U : Finset κ) (lab : Ref → κ × Nat)
    (hinit : PairTmaRing.InitFirst X m U.card) (hni : NoInval (X.objects m))
    {selected : Nat → Prop}
    (hpar : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
      selected g → X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
        p % 2 = (okPolls m ((X.tr g).take k) + δ) % 2)
    (hcomp : ∀ r ∈ X.objects m, ∀ n, r.action ≠ .completeTx n)
    (hincr : ∀ r ∈ X.objects m, r.action ≠ .increment)
    (harr : ∀ r ∈ X.objects m, ∀ c tx, r.action = .arrive c tx →
      c = 1 ∧ tx = 0 ∧ (lab r.id).1 ∈ U)
    (hlab : ∀ r ∈ X.objects m, ∀ r' ∈ X.objects m, ∀ c tx c' tx', r.action = .arrive c tx →
      r'.action = .arrive c' tx' → lab r.id = lab r'.id → r.id = r'.id)
    (hgate : ∀ r ∈ X.objects m, ∀ c tx, r.action = .arrive c tx → 1 ≤ (lab r.id).2 →
      ∃ h j pc p acq sc, selected h ∧ X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
        okPolls m ((X.tr h).take j) + 1 = (lab r.id).2 + δ ∧
        Relation.TransGen (DepStep L K X) (.thread (h, j), true) (r.id, false)) :
    ∀ r ∈ X.objects m, r.fault = none := by
  have hch := X.objects_checked hX m
  have hclean := PairTmaRing.poll_clean hX hinit hni
  have key := hch.gated_arrive hni U lab
    (fun i s hi hs => ⟨PairTmaRing.expected_of_init hX hinit hni hs,
      tx_zero_of hX hni (fun r hr c tx ha => (harr r hr c tx ha).2.1) hcomp hi hs⟩)
    (fun k r c tx hk ha => by
      obtain ⟨-, s, hs, -⟩ := PairTmaRing.state_of_init hX hinit hni hk
        (by intro n; rw [ha]; simp)
      exact ⟨s, hs⟩)
    (fun k r c tx hk ha => harr r (List.mem_of_getElem? hk) c tx ha)
    (fun k k' r r' c tx c' tx' hk hk' ha ha' hl => ObjectInit.checked_record_index_eq hch hk hk'
      (hlab r (List.mem_of_getElem? hk) r' (List.mem_of_getElem? hk') c tx c' tx' ha ha' hl))
    (fun k r c tx hk ha hpos => by
      obtain ⟨h, j, pc, p, acq, sc, hsel, he, hcnt, hpath⟩ :=
        hgate r (List.mem_of_getElem? hk) c tx ha hpos
      obtain ⟨kw, w, sw, hkw, hwid, ⟨p', hwa⟩, hww, hsw, hge⟩ :=
        poll_phase_ge_for_thread hX hδ hni hclean (hpar hsel) he
      refine ⟨kw, w, sw, ?_, hkw, hww, hsw, by omega⟩
      exact Unit.Gate.poll_before hX hpath hk rfl hkw hwid (by rw [ha, hwa]; simp))
    (incrementsBefore_length_of _ hincr)
  intro r hr
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  cases ha : r.action with
  | init n => exact PairTmaRing.init_clean hinit hr ha
  | pollParity p ok => exact hclean r hr ⟨p, ok, ha⟩
  | inval => exact (hni r hr ha).elim
  | completeTx n => exact (hcomp r hr n ha).elim
  | increment => exact (hincr r hr ha).elim
  | arrive c tx => exact (key k r c tx hk ha).1

/-- Specialization of the gated check when every poller has the same offset. -/
theorem fault_free_of_gated (hX : Consistent L K A mem0 X) {m : Loc} {δ : Nat} (hδ : δ ≤ 1)
    {κ : Type} [DecidableEq κ] (U : Finset κ) (lab : Ref → κ × Nat)
    (hinit : PairTmaRing.InitFirst X m U.card) (hni : NoInval (X.objects m))
    (hpar : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
        p % 2 = (okPolls m ((X.tr g).take k) + δ) % 2)
    (hcomp : ∀ r ∈ X.objects m, ∀ n, r.action ≠ .completeTx n)
    (hincr : ∀ r ∈ X.objects m, r.action ≠ .increment)
    (harr : ∀ r ∈ X.objects m, ∀ c tx, r.action = .arrive c tx →
      c = 1 ∧ tx = 0 ∧ (lab r.id).1 ∈ U)
    (hlab : ∀ r ∈ X.objects m, ∀ r' ∈ X.objects m, ∀ c tx c' tx', r.action = .arrive c tx →
      r'.action = .arrive c' tx' → lab r.id = lab r'.id → r.id = r'.id)
    (hgate : ∀ r ∈ X.objects m, ∀ c tx, r.action = .arrive c tx → 1 ≤ (lab r.id).2 →
      ∃ h j pc p acq sc, X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
        okPolls m ((X.tr h).take j) + 1 = (lab r.id).2 + δ ∧
        Relation.TransGen (DepStep L K X) (.thread (h, j), true) (r.id, false)) :
    ∀ r ∈ X.objects m, r.fault = none := by
  apply fault_free_of_selected_gate hX hδ U lab hinit hni (selected := fun _ => True)
    (fun _ he => hpar he) hcomp hincr harr hlab
  intro r hr c tx ha ht
  obtain ⟨h, j, pc, p, acq, sc, he, hcount, hpath⟩ := hgate r hr c tx ha ht
  exact ⟨h, j, pc, p, acq, sc, trivial, he, hcount, hpath⟩

/-- **An object initialized first whose other records are polls has no faulting record.** -/
theorem fault_free_of_polls (hX : Consistent L K A mem0 X) {m : Loc} {n : Nat}
    (hinit : PairTmaRing.InitFirst X m n) (hni : NoInval (X.objects m))
    (hpoll : ∀ r ∈ X.objects m, (∀ n, r.action ≠ .init n) → ∃ p ok, r.action = .pollParity p ok) :
    ∀ r ∈ X.objects m, r.fault = none := by
  intro r hr
  by_cases hn : ∃ n, r.action = .init n
  · obtain ⟨n', ha⟩ := hn
    exact PairTmaRing.init_clean hinit hr ha
  · exact PairTmaRing.poll_clean hX hinit hni r hr (hpoll r hr fun n h => hn ⟨n, h⟩)

/-- The start of a dependency path from a thread event's return is present: its first step is
to an event that resumes from it. -/
theorem present_of_path {w : EvId} {n : Ref × Bool}
    (hp : Relation.TransGen (DepStep L K X) (.thread w, true) n) : X.RefPresent (.thread w) := by
  obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp hp
  exact hb.present_of_return

/-- A path from thread `h`'s poll of `m` with `n` earlier successful ones names that poll: it is a
successful poll with `n` earlier ones. -/
theorem poll_of_path {m : Loc} {h n : Nat} {u : Ref × Bool}
    (hp : Relation.TransGen (DepStep L K X) (.thread (h, Poll.nth X m h n), true) u) :
    ∃ pc p acq sc, X.get (h, Poll.nth X m h n) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr h).take (Poll.nth X m h n)) = n :=
  Poll.nth_spec (Poll.nth_present.mp (present_of_path hp))

namespace Unit

variable {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- **The gate of a unit object**: each producer arrival of use `s ≥ 1` follows, in the
dependency order, a successful poll of the object with `s + δ - 1` earlier successful ones of its
thread. -/
def Gated (L : Launch) (K : Kernel) (_A : List Assumption) (X : Execution) (m : Loc) (N : Nat)
    (prod : Fin N → Nat) (δ : Nat) : Prop :=
  ∀ {a : Fin N} {i pc : Nat} {sc : MbarScope},
    X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ →
    1 ≤ arrivals m ((X.tr (prod a)).take i) →
      ∃ h j pc' p acq sc', X.get (h, j) = some ⟨pc', .wait m p true acq sc'⟩ ∧
        okPolls m ((X.tr h).take j) + 1 = arrivals m ((X.tr (prod a)).take i) + δ ∧
        Relation.TransGen (DepStep L K X) (.thread (h, j), true) (.thread (prod a, i), false)

/-- The label of a thread arrival on `m`: its thread and its use. -/
def lab (X : Execution) (m : Loc) : Ref → Nat × Nat
  | .thread (g, i) => (g, arrivals m ((X.tr g).take i))
  | _ => (0, 0)

/-- **Every record of a gated unit object is fault-free.** -/
theorem Obj.fault_free (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ)
    (hg : Gated L K A X m N prod δ) : ∀ r ∈ X.objects m, r.fault = none := by
  classical
  have hcard : (Finset.univ.image prod).card = N := by
    rw [Finset.card_image_of_injective _ O.inj, Finset.card_univ, Fintype.card_fin]
  refine fault_free_of_gated hX O.δ_le (Finset.univ.image prod) (lab X m)
    (by rw [hcard]; exact O.init) O.noInval O.parity ?_ ?_ ?_ ?_ ?_
  · intro r hr n ha
    cases O.src r hr with
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | arrive _ _ _ ha' => rw [ha] at ha'; cases ha'
  · intro r hr ha
    cases O.src r hr with
    | init ha' | poll _ _ ha' | arrive _ _ _ ha' => rw [ha] at ha'; cases ha'
  · intro r hr c tx ha
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨rfl, rfl, a, i, pc, sc, hid, -⟩ := O.arrive_rec hk ha
    exact ⟨rfl, rfl, by rw [hid]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
  · intro r hr r' hr' c tx c' tx' ha ha' hl
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.mp hr'
    obtain ⟨-, -, a, i, pc, sc, hid, he⟩ := O.arrive_rec hk ha
    obtain ⟨-, -, a', i', pc', sc', hid', he'⟩ := O.arrive_rec hk' ha'
    rw [hid, hid'] at hl ⊢
    simp only [lab, Prod.mk.injEq] at hl
    obtain ⟨hp, hu⟩ := hl
    rw [O.inj hp] at he hu ⊢
    rw [arr_index_eq he he' hu]
  · intro r hr c tx ha hpos
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨-, -, a, i, pc, sc, hid, he⟩ := O.arrive_rec hk ha
    rw [hid] at hpos ⊢
    exact hg he hpos

/-- **The gate from dependency paths**: each producer arrival of use `s ≥ 1` follows some
thread's poll of `m` with `s + δ - 1` earlier successful ones. -/
theorem gated_of_paths
    (hp : ∀ {a : Fin N} {i pc : Nat} {sc : MbarScope},
      X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ →
      1 ≤ arrivals m ((X.tr (prod a)).take i) → ∃ h,
        Relation.TransGen (DepStep L K X)
          (.thread (h, Poll.nth X m h (arrivals m ((X.tr (prod a)).take i) - 1 + δ)), true)
          (.thread (prod a, i), false)) :
    Gated L K A X m N prod δ := by
  intro a i pc sc he hpos
  obtain ⟨h, hpath⟩ := hp he hpos
  obtain ⟨pc', p, acq, sc', hw, hcnt⟩ := poll_of_path hpath
  exact ⟨h, _, pc', p, acq, sc', hw, by omega, hpath⟩

/-- A gated unit object (`Gate`) is gated. -/
theorem Gate.gated {cons : Nat → Prop} {pair : Fin N → Nat → Prop}
    (G : Gate L K A X m N prod δ cons pair) : Gated L K A X m N prod δ := by
  intro a i pc sc he hpos
  obtain ⟨h, hpair⟩ := G.partner a
  obtain ⟨j, pc', p, acq, sc', hw, hcnt, hpath⟩ := G.gate hpair he (by omega)
  exact ⟨h, j, pc', p, acq, sc', hw, hcnt, hpath⟩

end Unit

namespace Notify

variable {m m0 : Loc} {g δ : Nat}

/-- **The gate of a commit object**: the recorded notification of each commit of `g` naming
`m0` with `t ≥ 1` earlier ones follows, in the dependency order, a successful poll of the object
with `t + δ - 1` earlier successful ones of a selected thread. -/
def SelectedGated (L : Launch) (K : Kernel) (_A : List Assumption) (X : Execution) (m : Loc)
    (g : Nat) (m0 : Loc) (δ : Nat) (selected : Nat → Prop) : Prop :=
  ∀ {i pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
    X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = m0 →
    TcCommit.target sp rank = some m →
    (∃ r ∈ X.objects m, r.id = .async (g, i) (.tcNotify rank)) →
    1 ≤ ((X.tr g).take i).countP (commitsTo m0) →
      ∃ h j pc' p acq sc, selected h ∧ X.get (h, j) = some ⟨pc', .wait m p true acq sc⟩ ∧
        okPolls m ((X.tr h).take j) + 1 = ((X.tr g).take i).countP (commitsTo m0) + δ ∧
        Relation.TransGen (DepStep L K X) (.thread (h, j), true)
          (.async (g, i) (.tcNotify rank), false)

/-- A commit gate with any poller allowed. -/
def Gated (L : Launch) (K : Kernel) (_A : List Assumption) (X : Execution) (m : Loc) (g : Nat)
    (m0 : Loc) (δ : Nat) : Prop :=
  ∀ {i pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
    X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = m0 →
    TcCommit.target sp rank = some m →
    (∃ r ∈ X.objects m, r.id = .async (g, i) (.tcNotify rank)) →
    1 ≤ ((X.tr g).take i).countP (commitsTo m0) →
      ∃ h j pc' p acq sc, X.get (h, j) = some ⟨pc', .wait m p true acq sc⟩ ∧
        okPolls m ((X.tr h).take j) + 1 = ((X.tr g).take i).countP (commitsTo m0) + δ ∧
        Relation.TransGen (DepStep L K X) (.thread (h, j), true)
          (.async (g, i) (.tcNotify rank), false)

/-- Recover the successful poll of a selected thread from the dependency path. -/
theorem selected_gated_of_paths
    {selected : Nat → Prop}
    (hp : ∀ {i pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
      X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = m0 →
      TcCommit.target sp rank = some m →
      (∃ r ∈ X.objects m, r.id = .async (g, i) (.tcNotify rank)) →
      1 ≤ ((X.tr g).take i).countP (commitsTo m0) → ∃ h, selected h ∧
        Relation.TransGen (DepStep L K X)
          (.thread (h, Poll.nth X m h (((X.tr g).take i).countP (commitsTo m0) - 1 + δ)), true)
          (.async (g, i) (.tcNotify rank), false)) :
    SelectedGated L K A X m g m0 δ selected := by
  intro i pc sp rank he hm ht hrec hpos
  obtain ⟨h, hsel, hpath⟩ := hp he hm ht hrec hpos
  obtain ⟨pc', p, acq, sc', hw, hcnt⟩ := poll_of_path hpath
  exact ⟨h, _, pc', p, acq, sc', hsel, hw, by omega, hpath⟩

/-- **The gate from dependency paths**: the recorded notification of each commit with `t ≥ 1`
earlier ones follows some thread's poll of `m` with `t + δ - 1` earlier successful ones. -/
theorem gated_of_paths
    (hp : ∀ {i pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
      X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = m0 →
      TcCommit.target sp rank = some m →
      (∃ r ∈ X.objects m, r.id = .async (g, i) (.tcNotify rank)) →
      1 ≤ ((X.tr g).take i).countP (commitsTo m0) → ∃ h,
        Relation.TransGen (DepStep L K X)
          (.thread (h, Poll.nth X m h (((X.tr g).take i).countP (commitsTo m0) - 1 + δ)), true)
          (.async (g, i) (.tcNotify rank), false)) :
    Gated L K A X m g m0 δ := by
  intro i pc sp rank he hm ht hrec hpos
  obtain ⟨h, hpath⟩ := hp he hm ht hrec hpos
  obtain ⟨pc', p, acq, sc', hw, hcnt⟩ := poll_of_path hpath
  exact ⟨h, _, pc', p, acq, sc', hw, by omega, hpath⟩

/-- The label of a commit's notification: its use, the commits to `m0` before it. -/
def lab (X : Execution) (m0 : Loc) : Ref → Unit × Nat
  | .async (g, i) _ => ((), ((X.tr g).take i).countP (commitsTo m0))
  | _ => ((), 0)

/-- **Every record of a gated commit object is fault-free.** -/
theorem Obj.fault_free_selected (hX : Consistent L K A mem0 X)
    {selected : Nat → Prop} (O : Obj X m g m0 δ selected)
    (hg : SelectedGated L K A X m g m0 δ selected) : ∀ r ∈ X.objects m, r.fault = none := by
  refine fault_free_of_selected_gate hX O.δ_le {()} (lab X m0) O.init O.noInval O.parityOf
    ?_ ?_ ?_ ?_ ?_
  · intro r hr n ha
    cases O.src r hr with
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | commit _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  · intro r hr ha
    cases O.src r hr with
    | init ha' | poll _ _ ha' | commit _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  · intro r hr c tx ha
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨rfl, rfl, -⟩ := O.arrive_rec hk ha
    exact ⟨rfl, rfl, Finset.mem_singleton_self _⟩
  · intro r hr r' hr' c tx c' tx' ha ha' hl
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.mp hr'
    obtain ⟨-, -, i, pc, sp, rk, hid, he, hm, ht⟩ := O.arrive_rec hk ha
    obtain ⟨-, -, i', pc', sp', rk', hid', he', hm', ht'⟩ := O.arrive_rec hk' ha'
    rw [hid, hid'] at hl ⊢
    simp only [lab, Prod.mk.injEq, true_and] at hl
    have hp : ∀ {pc : Nat} {sp : TcCommit.Spec}, sp.mbar = m0 →
        commitsTo m0 ⟨pc, .tc (.commit sp)⟩ = true := by
      intro pc sp hm
      simp [commitsTo, hm]
    have hii : i = i' := by
      rw [← nthEv_eq he (hp hm), ← nthEv_eq he' (hp hm'), hl]
    subst hii
    rw [he] at he'
    cases he'
    rw [rank_eq ht ht']
  · intro r hr c tx ha hpos
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨-, -, i, pc, sp, rk, hid, he, hm, ht⟩ := O.arrive_rec hk ha
    rw [hid] at hpos ⊢
    exact hg he hm ht ⟨r, hr, hid⟩ hpos

/-- The commit fault check when every poller uses the common offset. -/
theorem Obj.fault_free (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ)
    (hg : Gated L K A X m g m0 δ) : ∀ r ∈ X.objects m, r.fault = none := by
  apply O.fault_free_selected hX
  intro i pc sp rank he hm ht hr hn
  obtain ⟨h, j, pc', p, acq, sc, hp, hcnt, hpath⟩ := hg he hm ht hr hn
  exact ⟨h, j, pc', p, acq, sc, trivial, hp, hcnt, hpath⟩

end Notify

end MbarRing

end PTX
