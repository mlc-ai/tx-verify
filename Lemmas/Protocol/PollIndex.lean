-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Polls
public import Lemmas.Protocol.PollPhase
public import Lemmas.Order.ObjectThreadWaitWindowCount
public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Protocol.CountNth
public import Lemmas.Order.CausalThreadCount
public import Lemmas.Protocol.MbarInit

@[expose] public section

/-! # A thread's successful polls of one object, by index

A proof tool for instantiating `MbarRing.Items.Ring` (or `MbarRing.Round.Slot`). The successful
poll of object `m` by thread `g` with `n` earlier successful polls of `m` is at position
`nth X m g n` of `g`'s trace (`nth_spec`), past the trace when there is none (`nth_present`).
A later event of `g` with more successful polls before it resumes from that poll when the
poll is that of a canonical spin (`guard`). On `m`'s history, when `g`'s polls of `m` alternate
parity with offset `δ` and poll records do not fault, the poll's record is `g`'s selected
success with `n` earlier ones (`record`), the records of `g`'s polls are in the order of `g`'s
trace, and the completed phases they observe increase (`observed_lt`). -/

namespace PTX.MbarRing.Poll

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

open Classical in
/-- The position of thread `g`'s successful poll of `m` with `n` earlier successful polls of
`m`; the end of `g`'s trace when there is none. -/
def nth (X : Execution) (m : Loc) (g n : Nat) : Nat :=
  if h : ∃ j pc p acq sc, X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr g).take j) = n then Classical.choose h
  else (X.tr g).length

theorem okPoll_get {g j pc p : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩) :
    okPolls m ((X.tr g).take (j + 1)) = okPolls m ((X.tr g).take j) + 1 := by
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have he' : (X.tr g)[j] = ⟨pc, .wait m p true acq sc⟩ :=
    (List.getElem?_eq_some_iff.mp he).2
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, okPolls_snoc, he']
  simp [okPoll, sourceWaitSuccess]

theorem okPolls_mono (m : Loc) (es : List Event) {i j : Nat} (hij : i ≤ j) :
    okPolls m (es.take i) ≤ okPolls m (es.take j) := by
  unfold okPolls
  exact (List.take_sublist_take_left hij).countP_le

/-- Two successful polls of `m` with the same count are one. -/
theorem okPoll_index_unique {g j j' pc pc' p p' : Nat} {m : Loc} {acq acq' : Bool}
    {sc sc' : MbarScope} (he : X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩)
    (he' : X.get (g, j') = some ⟨pc', .wait m p' true acq' sc'⟩)
    (hc : okPolls m ((X.tr g).take j) = okPolls m ((X.tr g).take j')) : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h1 := okPoll_get he
    have h2 := okPolls_mono m (X.tr g) (show j + 1 ≤ j' by omega)
    omega
  · have h1 := okPoll_get he'
    have h2 := okPolls_mono m (X.tr g) (show j' + 1 ≤ j by omega)
    omega

/-- A thread with more than `n` successful polls of `m` among its first `k` events made the one
with `n` earlier ones before position `k`. -/
theorem exists_nth {g k n : Nat} {m : Loc} (h : n + 1 ≤ okPolls m ((X.tr g).take k)) :
    ∃ j pc p acq sc, j < k ∧ X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr g).take j) = n := by
  obtain ⟨j, e, he, ho, hc⟩ := MbarRing.Slot.exists_nth_countP (okPoll m)
    (xs := (X.tr g).take k) (c := n) h
  have hj : j < k := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hj] at he
  rw [List.take_take, Nat.min_eq_left hj.le] at hc
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | wait mw p okw acq sc =>
    simp only [okPoll, sourceWaitSuccess] at ho
    cases okw <;> simp at ho
    subst ho
    exact ⟨j, pc, p, acq, sc, hj, he, hc⟩
  | _ => simp [okPoll, sourceWaitSuccess] at ho

/-- The poll with `n` earlier successful polls, when the thread made more than `n`. -/
theorem nth_spec {g n : Nat} {m : Loc} (h : n < okPolls m (X.tr g)) :
    ∃ pc p acq sc, X.get (g, nth X m g n) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr g).take (nth X m g n)) = n := by
  have h' : n + 1 ≤ okPolls m ((X.tr g).take (X.tr g).length) := by
    rw [List.take_length]; omega
  obtain ⟨j, pc, p, acq, sc, -, he, hc⟩ := exists_nth h'
  have hex : ∃ j pc p acq sc, X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr g).take j) = n := ⟨j, pc, p, acq, sc, he, hc⟩
  unfold nth
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨pc', p', acq', sc', he', hc'⟩ := Classical.choose_spec hex
  exact ⟨pc', p', acq', sc', he', hc'⟩

/-- A successful poll of `m` is the one its count names. -/
theorem nth_eq {g j pc p : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩) :
    nth X m g (okPolls m ((X.tr g).take j)) = j := by
  have hlt : okPolls m ((X.tr g).take j) < okPolls m (X.tr g) := by
    have h1 := okPoll_get he
    have h2 := okPolls_mono m (X.tr g) (show j + 1 ≤ (X.tr g).length from
      (List.getElem?_eq_some_iff.mp he).1)
    rw [List.take_length] at h2
    omega
  obtain ⟨pc', p', acq', sc', he', hc'⟩ := nth_spec hlt
  exact okPoll_index_unique he' he hc'

/-- The poll's position is in the trace exactly when the thread made more than `n` successful
polls of `m`. -/
theorem nth_present {g n : Nat} {m : Loc} :
    X.RefPresent (.thread (g, nth X m g n)) ↔ n < okPolls m (X.tr g) := by
  constructor
  · intro hp
    by_contra hn
    have hex : ¬ ∃ j pc p acq sc, X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
        okPolls m ((X.tr g).take j) = n := by
      rintro ⟨j, pc, p, acq, sc, he, hc⟩
      have := nth_eq he
      have h1 := okPoll_get he
      have h2 := okPolls_mono m (X.tr g) (show j + 1 ≤ (X.tr g).length from
        (List.getElem?_eq_some_iff.mp he).1)
      rw [List.take_length] at h2
      omega
    obtain ⟨ev, hev⟩ := hp
    unfold nth at hev
    rw [dite_eq_right_of_eq_false (eq_false hex)] at hev
    have := len_of_get hev
    simp at this
  · intro h
    obtain ⟨pc, p, acq, sc, he, -⟩ := nth_spec h
    exact ⟨_, he⟩

/-- A later event of the thread, with more than `n` successful polls of `m` before it, follows
the poll with `n` earlier ones. -/
theorem nth_lt {g k n : Nat} {m : Loc} (h : n + 1 ≤ okPolls m ((X.tr g).take k)) :
    nth X m g n < k := by
  obtain ⟨j, pc, p, acq, sc, hj, he, hc⟩ := exists_nth h
  rw [← hc, nth_eq he]
  exact hj

/-- Polls with fewer earlier ones come first. -/
theorem nth_lt_nth {g n n' : Nat} {m : Loc} (hn : n < n') (h : n' < okPolls m (X.tr g)) :
    nth X m g n < nth X m g n' := by
  obtain ⟨pc, p, acq, sc, he, hc⟩ := nth_spec h
  apply nth_lt
  rw [← hc] at hn
  have := okPoll_get he
  omega

/-- **The guard.** A successful poll of a canonical spin resumes each later event of its
thread (DEP-CANONICAL-SPIN): an event with more than `n` successful polls of `m` before it
resumes from the poll with `n` earlier ones. -/
theorem guard (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {g k n : Nat} {m : Loc} (hk : k < (X.tr g).length)
    (h : n + 1 ≤ okPolls m ((X.tr g).take k)) :
    Resumes K X (g, nth X m g n) (g, k) := by
  obtain ⟨j, pc, p, acq, sc, hj, he, hc⟩ := exists_nth h
  have hjn : nth X m g n = j := by rw [← hc, nth_eq he]
  rw [hjn]
  obtain ⟨ex, hs⟩ := hspin _ _ _ _ _ _ he
  refine ⟨⟨rfl, hj, hk⟩, ?_⟩
  simp only [he, Option.map_some, Kind.resume]
  exact ⟨pc, ex, m, p, acq, sc, he, hs, ⟨rfl, hj, hk⟩⟩

/-! ### The poll records on the object's history -/

private theorem countP_take_eq_range {α : Type} (pred : α → Bool) (xs : List α) (k : Nat) :
    (xs.take k).countP pred = (List.range k).countP (fun j => xs[j]?.any pred) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.take_add_one, List.range_succ, List.countP_append, List.countP_append, ih]
    cases hg : xs[k]? <;> simp [hg]

private theorem sourceWaitSuccess_objectAction {m : Loc} {g j : Nat}
    (hs : (X.get (g, j)).any (sourceWaitSuccess m) = true) :
    ∃ p, objectAction X X.async m (.thread (g, j)) = some (.pollParity p true) := by
  cases he : X.get (g, j) with
  | none => simp only [he, Option.any_none, Bool.false_eq_true] at hs
  | some ev =>
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> try simp only [he, Option.any_some, sourceWaitSuccess, Bool.false_eq_true] at hs
    rename_i target parity ok acquire scope
    cases ok <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at hs
    subst hs
    exact ⟨parity, by simp [objectAction, he]⟩

/-- The selected successes of thread `g` before position `i` of `m`'s history are its successful
polls of `m` before its own record there, when poll records do not fault. -/
theorem count_before (hX : Consistent L K A mem0 X) {m : Loc} {i g k : Nat}
    {r : Record Ref} (hi : (X.objects m)[i]? = some r) (hrid : r.id = .thread (g, k))
    (hpclean : ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none) :
    selectedBefore (objectThreadSelected g) (X.objects m) i = okPolls m ((X.tr g).take k) := by
  let prior := (X.objects m).take i
  have hsub : ∀ q ∈ prior, q ∈ X.objects m := fun _ hq => List.mem_of_mem_take hq
  have hnodup : (prior.map Record.id).Nodup :=
    (hX.tma.2.2.1 m).1.1.sublist ((List.take_sublist _ _).map _)
  have hwin : ∀ q j, q ∈ X.objects m → q.id = .thread (g, j) → (q ∈ prior ↔ j < k) :=
    fun _ _ hq hqid => hX.object_thread_take_mem_iff hi hrid hq hqid
  let good := fun q : Record Ref =>
    decide (objectThreadSelected g q.id = true ∧ q.reply.waited = some true)
  let source := fun j => (X.get (g, j)).any (sourceWaitSuccess m)
  let actualIds := (prior.filter good).map Record.id
  let sourceIds := ((List.range k).filter source).map (fun j => Ref.thread (g, j))
  have haNodup : actualIds.Nodup := hnodup.sublist (List.filter_sublist.map _)
  have hsNodup : sourceIds.Nodup := by
    apply ((List.nodup_range (n := k)).filter source).map
    intro i j he
    exact congrArg (fun id => id.issuer.2) he
  have hmem : ∀ id, id ∈ actualIds ↔ id ∈ sourceIds := by
    intro id
    constructor
    · intro hid
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hid
      obtain ⟨hq, hgood⟩ := List.mem_filter.mp hq
      have hg : objectThreadSelected g q.id = true ∧ q.reply.waited = some true :=
        of_decide_eq_true hgood
      obtain ⟨j, hqid⟩ := objectThreadSelected_iff.mp hg.1
      have hlog := hsub q hq
      have hj : j < k := (hwin q j hlog hqid).mp hq
      obtain ⟨jq, hjq⟩ := List.mem_iff_getElem?.mp hlog
      obtain ⟨-, p, -, hpa, -⟩ := (hX.tma.2.2.1 m).1.okPoll hjq hg.2
      have hsource : source j = true :=
        (hX.object_thread_waited_iff hlog hqid (hpclean q hlog ⟨p, true, hpa⟩)).mp hg.2
      exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, hsource⟩, hqid.symm⟩
    · intro hid
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hid
      obtain ⟨hj, hs⟩ := List.mem_filter.mp hj
      obtain ⟨parity, ha⟩ := sourceWaitSuccess_objectAction hs
      obtain ⟨q, hq, hqid⟩ := (hX.tma.2.2.1 m).2.2 (.thread (g, j)) (.pollParity parity true) ha
      have hp : q ∈ prior := (hwin q j hq hqid).mpr (List.mem_range.mp hj)
      have hqa : q.action = .pollParity parity true := by
        have := ((hX.tma.2.2.1 m).2.1 q hq).1
        rw [hqid, ha] at this
        exact (Option.some.inj this).symm
      have hw : q.reply.waited = some true :=
        (hX.object_thread_waited_iff hq hqid (hpclean q hq ⟨parity, true, hqa⟩)).mpr hs
      apply List.mem_map.mpr
      refine ⟨q, List.mem_filter.mpr ⟨hp, decide_eq_true ?_⟩, hqid⟩
      exact ⟨objectThreadSelected_iff.mpr ⟨j, hqid⟩, hw⟩
  have hperm : actualIds.Perm sourceIds := (List.perm_ext_iff_of_nodup haNodup hsNodup).mpr hmem
  calc
    selectedBefore (objectThreadSelected g) (X.objects m) i = actualIds.length := by
      rw [selectedBefore, MBarrier.selectedCount_eq_countP, List.countP_eq_length_filter]
      exact (List.length_map _).symm
    _ = sourceIds.length := hperm.length_eq
    _ = ((X.tr g).take k).countP (sourceWaitSuccess m) := by
      rw [countP_take_eq_range, List.countP_eq_length_filter]
      exact List.length_map _

/-- Thread `g`'s successful polls of `m` alternate parity with offset `δ` on `m`'s history, when
each poll uses the parity of the thread's earlier successful polls plus `δ`. -/
theorem alternates (hX : Consistent L K A mem0 X) {m : Loc} {g δ : Nat}
    (hpclean : ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none)
    (hpar : ∀ k pc p acq sc, X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
      p % 2 = (okPolls m ((X.tr g).take k) + δ) % 2) :
    SelectedAlternates (objectThreadSelected g) (X.objects m) δ := by
  intro j r p ok hj ha hsel hw
  obtain ⟨k, hrid⟩ := objectThreadSelected_iff.mp hsel
  have hr := List.mem_of_getElem? hj
  have hf := hpclean r hr ⟨p, ok, ha⟩
  have hsrc := (hX.object_thread_waited_iff hr hrid hf).mp hw
  cases he : X.get (g, k) with
  | none => simp [he] at hsrc
  | some ev =>
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> simp only [he, Option.any_some, sourceWaitSuccess, Bool.false_eq_true] at hsrc
    rename_i target parity okw acq sc
    cases okw <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at hsrc
    subst hsrc
    have hact : objectAction X X.async target (.thread (g, k)) =
        some (.pollParity parity true) := by
      simp [objectAction, he]
    have := ((hX.tma.2.2.1 target).2.1 r hr).1
    rw [hrid, hact, ha] at this
    cases this
    rw [count_before hX hj hrid hpclean]
    exact hpar k pc p acq sc he

/-- **The record of the poll with `n` earlier ones.** It is a successful poll record of `m`, at
a position where `g` has `n` earlier selected successes. -/
theorem record (hX : Consistent L K A mem0 X) {m : Loc} {g n : Nat}
    (hpclean : ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none)
    (h : n < okPolls m (X.tr g)) :
    ∃ i w p, (X.objects m)[i]? = some w ∧ w.id = .thread (g, nth X m g n) ∧
      w.action = .pollParity p true ∧ w.reply.waited = some true ∧ w.fault = none ∧
      selectedBefore (objectThreadSelected g) (X.objects m) i = n := by
  obtain ⟨pc, p, acq, sc, he, hc⟩ := nth_spec h
  have hact : objectAction X X.async m (.thread (g, nth X m g n)) = some (.pollParity p true) := by
    simp [objectAction, he]
  obtain ⟨w, hw, hwid⟩ := (hX.tma.2.2.1 m).2.2 _ _ hact
  have hwa : w.action = .pollParity p true := by
    have := ((hX.tma.2.2.1 m).2.1 w hw).1
    rw [hwid, hact] at this
    exact (Option.some.inj this).symm
  have hwf := hpclean w hw ⟨p, true, hwa⟩
  have hww : w.reply.waited = some true :=
    (hX.object_thread_waited_iff hw hwid hwf).mpr (by simp [he, sourceWaitSuccess])
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
  exact ⟨i, w, p, hi, hwid, hwa, hww, hwf, by rw [count_before hX hi hwid hpclean, hc]⟩

/-- The completed phase observed by the record of `id` in `m`'s history (0 when absent). -/
def observedOf (X : Execution) (m : Loc) (id : Ref) : Nat :=
  ((X.objects m).findIdx? (fun r => decide (r.id = id))).bind
    (observedAt (X.objects m)) |>.getD 0

/-- The phase in which the record of `id` in `m`'s history lies (0 when absent). -/
def phaseOf (X : Execution) (m : Loc) (id : Ref) : Nat :=
  ((X.objects m).findIdx? (fun r => decide (r.id = id))).bind
    (phaseAt (X.objects m)) |>.getD 0

/-- The position of a record found by its identity. -/
theorem findIdx_of_get (hX : Consistent L K A mem0 X) {m : Loc} {i : Nat} {r : Record Ref}
    (hi : (X.objects m)[i]? = some r) :
    (X.objects m).findIdx? (fun q => decide (q.id = r.id)) = some i := by
  have hnd := (hX.tma.2.2.1 m).1.1
  rw [List.findIdx?_eq_some_iff_getElem]
  have hlt : i < (X.objects m).length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨hlt, by rw [(List.getElem?_eq_some_iff.mp hi).2]; simp, fun j hj => ?_⟩
  simp only [decide_eq_true_eq]
  intro heq
  have hjj : (X.objects m)[j]? = some (X.objects m)[j] := List.getElem?_eq_getElem (by omega)
  have := ObjectInit.checked_record_index_eq (hX.tma.2.2.1 m).1 hjj hi heq
  omega

theorem observedOf_eq (hX : Consistent L K A mem0 X) {m : Loc} {i : Nat} {r : Record Ref}
    (hi : (X.objects m)[i]? = some r) {q : Nat} (hq : observedAt (X.objects m) i = some q) :
    observedOf X m r.id = q := by
  simp [observedOf, findIdx_of_get hX hi, hq]

theorem phaseOf_eq (hX : Consistent L K A mem0 X) {m : Loc} {i : Nat} {r : Record Ref}
    (hi : (X.objects m)[i]? = some r) {q : Nat} (hq : phaseAt (X.objects m) i = some q) :
    phaseOf X m r.id = q := by
  simp [phaseOf, findIdx_of_get hX hi, hq]

/-- The poll with `n ≥ δ` earlier ones, of an alternating poller with offset `δ`, observed a
completed phase: the one before the phase it found. -/
theorem observed_some {log : List (Record Ref)} (h : CheckedLog log)
    (hni : NoInval log) {sel : Ref → Bool}
    {δ : Nat} (hδ : δ ≤ 1) (halt : SelectedAlternates sel log δ) {i : Nat} {w : Record Ref}
    (hi : log[i]? = some w) (hsel : sel w.id = true) (hw : w.reply.waited = some true)
    (hn : δ ≤ selectedBefore sel log i) :
    ∃ st, stateBefore log i = some st ∧ 0 < st.phase ∧
      observedAt log i = some (st.phase - 1) := by
  obtain ⟨st, hst, hge, -⟩ := h.selected_poll_phase_ge hni sel hδ halt hi hsel hw
  obtain ⟨s, p, hs, -, -, hc⟩ := h.okPoll hi hw
  rw [hst] at hs
  cases hs
  have hpos : 0 < st.phase := by omega
  refine ⟨st, hst, hpos, ?_⟩
  simp [observedAt, hi, hc, hpos]

/-- **Observed phases increase.** Of an alternating poller's polls with at least `δ` earlier
ones, a later poll observed a later completed phase. -/
theorem observed_lt (hX : Consistent L K A mem0 X) {m : Loc} {g δ : Nat} (hδ : δ ≤ 1)
    (hpclean : ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none)
    (hni : NoInval (X.objects m))
    (halt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ)
    {n n' : Nat} (hδn : δ ≤ n) (hnn : n < n') (h : n' < okPolls m (X.tr g)) :
    observedOf X m (.thread (g, nth X m g n)) < observedOf X m (.thread (g, nth X m g n')) := by
  have hch : CheckedLog (X.objects m) := (hX.tma.2.2.1 m).1
  obtain ⟨i, w, -, hi, hwid, -, hww, -, hc⟩ :=
    record hX hpclean (show n < okPolls m (X.tr g) by omega)
  obtain ⟨i', w', -, hi', hwid', -, hww', -, hc'⟩ := record hX hpclean h
  have hsel : objectThreadSelected g w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  have hsel' : objectThreadSelected g w'.id = true := objectThreadSelected_iff.mpr ⟨_, hwid'⟩
  have hii : i < i' := by
    by_contra hge
    have := selectedBefore_mono (objectThreadSelected g) (X.objects m) (Nat.le_of_not_gt hge)
    omega
  obtain ⟨st, -, -, ho⟩ := observed_some hch hni hδ halt hi hsel hww (by omega)
  obtain ⟨st', -, -, ho'⟩ := observed_some hch hni hδ halt hi' hsel' hww' (by omega)
  have hlt := hch.selected_observed_lt hni (objectThreadSelected g) halt hii hi hsel hww hi' hsel'
    hww' ho ho'
  rw [← hwid, ← hwid', observedOf_eq hX hi ho, observedOf_eq hX hi' ho']
  exact hlt

end
end PTX.MbarRing.Poll
