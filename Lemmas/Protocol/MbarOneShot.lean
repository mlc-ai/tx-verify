-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.BulkObserve
public import Lemmas.MBarrier.MBarrierInitOrder
public import Lemmas.Protocol.PairTmaRing.Hyp

@[expose] public section

/-! # A one-phase mbarrier, from its history

A proof tool for an mbarrier used for one phase: an initialization with count `c`, `c` unit
arrivals `ras` (each a thread's arrival or an asynchronous arrive-on, with the transaction bytes it
expects), the complete-tx records of a list `cs` of bulk copies (issue event, bytes) whose sizes
sum to the bytes the arrivals expect, and polls of phase 0's parity, in any order after the
initialization. The object's history (`Hist`) has these records, and the initialization is the
first record, once and without fault (`PairTmaRing.InitFirst`). From the object's own checked
history:

* the initialization is record 0 (`first`); after the first `n` records the object is in phase
  0 with pending arrivals `c - (recorded arrivals)` and transaction count
  `(bytes the recorded arrivals expect) - (bytes of recorded copies)`, or, once every arrival and
  every copy are recorded, in the completed phase 1 (`stateAt`, `invariant`);
* no record faults (`fault_free`);
* a successful poll observes every arrival and every copy in the phase it observes
  (`observes_arrive`), hence each copy's completion (`observes_copy`);
* the final state is phase 1 exactly when every arrival and every copy are recorded
  (`final_state`); a notified copy and an arrival that the object covers are recorded
  (`copy_recorded`, `arrive_recorded`).

A kernel either proves `InitFirst` from the publication of the initialization
(OBJ-MBAR-INIT-PUBLICATION) or supplies an event table (`Table`) whose initialization happens before
the issuer of every other record; the table gives the history (`Table.hist`) and that every record
follows the published initialization (`Table.published`). -/

namespace PTX.MbarOneShot

open AsyncCopy MBarrier

noncomputable section

/-- The ids of the first `n` records of `log`. -/
def ids (log : List (Record Ref)) (n : Nat) : List Ref := (log.take n).map Record.id

/-- The weights `w` of the members of `l` whose key is in `S`. -/
def wsum {α : Type} (l : List α) (key : α → Ref) (w : α → Nat) (S : List Ref) : Nat :=
  (l.map fun a => if key a ∈ S then w a else 0).sum

/-- The number of the arrivals `ras` among the first `n` records. -/
def arrived (log : List (Record Ref)) (ras : List (Ref × Nat)) (n : Nat) : Nat :=
  wsum ras Prod.fst (fun _ => 1) (ids log n)

/-- The bytes that the arrivals among the first `n` records expect. -/
def expected (log : List (Record Ref)) (ras : List (Ref × Nat)) (n : Nat) : Nat :=
  wsum ras Prod.fst Prod.snd (ids log n)

/-- The copy completion of a copy (issue event, bytes). -/
def copyRef (c : EvId × Nat) : Ref := .async c.1 (.notify .copy)

/-- The bytes of the copies of `cs` whose complete-tx is among the first `n` records. -/
def done (log : List (Record Ref)) (cs : List (EvId × Nat)) (n : Nat) : Nat :=
  wsum cs copyRef Prod.snd (ids log n)

/-- The object's state for count `c`, `a` recorded arrivals expecting `x` bytes and `s` completed
bytes: phase 0, or the completed phase 1 once every arrival and all `x` bytes are in. -/
def state (c a x s : Nat) (observed : Bool) : State :=
  if a = c ∧ x = s then ⟨1, c, c, 0, observed⟩
  else ⟨0, c, c - a, (x : Int) - s, true⟩

/-- The object's state after the first `n` records of `log`. -/
def stateAt (log : List (Record Ref)) (ras : List (Ref × Nat)) (cs : List (EvId × Nat))
    (n : Nat) (observed : Bool) : State :=
  state ras.length (arrived log ras n) (expected log ras n) (done log cs n) observed

theorem mem_ids {log : List (Record Ref)} {n : Nat} {x : Ref} :
    x ∈ ids log n ↔ ∃ j < n, ∃ q, log[j]? = some q ∧ q.id = x := by
  simp only [ids, List.mem_map, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨q, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, by omega, _, List.getElem?_eq_getElem (by omega), rfl⟩
  · rintro ⟨j, hj, q, hq, rfl⟩
    obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp hq
    exact ⟨q, ⟨j, by omega, he⟩, rfl⟩

theorem ids_succ {log : List (Record Ref)} {k : Nat} {r : Record Ref} (hr : log[k]? = some r) :
    ids log (k + 1) = ids log k ++ [r.id] := by
  simp [ids, List.take_add_one, hr]

theorem mem_ids_length {log : List (Record Ref)} {x : Ref} :
    x ∈ ids log log.length ↔ ∃ r ∈ log, r.id = x := by
  simp [ids]

section wsum
variable {α : Type} {key : α → Ref} {w : α → Nat}

theorem wsum_le (l : List α) (S : List Ref) : wsum l key w S ≤ (l.map w).sum := by
  induction l with
  | nil => simp [wsum]
  | cons c l ih =>
    simp only [wsum, List.map_cons, List.sum_cons] at ih ⊢
    split_ifs <;> omega

theorem wsum_nil (l : List α) : wsum l key w [] = 0 := by
  induction l with
  | nil => simp [wsum]
  | cons c l ih => simp [wsum]

/-- Once every key is in, the weights are all the weights. -/
theorem wsum_all {l : List α} {S : List Ref} (h : ∀ a ∈ l, key a ∈ S) :
    wsum l key w S = (l.map w).sum := by
  induction l with
  | nil => simp [wsum]
  | cons c l ih =>
    simp only [wsum, List.map_cons, List.sum_cons, h c List.mem_cons_self, ↓reduceIte] at ih ⊢
    rw [ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- With positive weights, the weights of the members with keys in `S` are all the weights only
when every key is in. -/
theorem wsum_eq_iff {l : List α} {S : List Ref} (hpos : ∀ a ∈ l, 0 < w a) :
    wsum l key w S = (l.map w).sum ↔ ∀ a ∈ l, key a ∈ S := by
  induction l with
  | nil => simp [wsum]
  | cons c l ih =>
    have hle := wsum_le (key := key) (w := w) l S
    have h0 := hpos c List.mem_cons_self
    have ih := ih fun d hd => hpos d (List.mem_cons_of_mem _ hd)
    simp only [wsum, List.map_cons, List.sum_cons, List.forall_mem_cons] at ih hle ⊢
    by_cases hc : key c ∈ S
    · simp only [hc, ↓reduceIte, true_and]
      rw [← ih]
      omega
    · simp only [hc, ↓reduceIte, false_and, iff_false]
      omega

/-- A key no member has leaves the weights unchanged. -/
theorem wsum_snoc_other {l : List α} {S : List Ref} {y : Ref} (h : ∀ a ∈ l, key a ≠ y) :
    wsum l key w (S ++ [y]) = wsum l key w S := by
  unfold wsum
  congr 1
  refine List.map_congr_left fun a ha => if_congr ?_ rfl rfl
  simp only [List.mem_append, List.mem_singleton]
  exact or_iff_left (h a ha)

/-- A new key of the member `a` adds its weight. -/
theorem wsum_snoc_new {l : List α} {S : List Ref} {a : α} (hnd : (l.map key).Nodup)
    (ha : a ∈ l) (hn : key a ∉ S) :
    wsum l key w (S ++ [key a]) = wsum l key w S + w a := by
  induction l with
  | nil => simp at ha
  | cons d l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [wsum, List.map_cons, List.sum_cons, List.mem_append, List.mem_singleton] at ih ⊢
    rcases List.mem_cons.mp ha with rfl | ha
    · have hrest : ∀ e ∈ l, key e ∉ S ++ [key a] ↔ key e ∉ S := fun e he => by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact and_iff_left fun h => hnd.1 ⟨e, he, h⟩
      have := wsum_snoc_other (key := key) (w := w) (S := S) (y := key a)
        (fun e he h => hnd.1 ⟨e, he, h⟩)
      simp only [wsum, List.mem_append, List.mem_singleton] at this
      rw [this]
      simp only [hn, or_true, ↓reduceIte]
      omega
    · have hdc : key d ≠ key a := fun h => hnd.1 ⟨a, ha, h.symm⟩
      rw [ih hnd.2 ha]
      simp only [hdc, or_false]
      omega

end wsum

theorem sum_map_one {α : Type} (l : List α) : (l.map fun _ => (1 : Nat)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

/-- The number of arrivals is at most their count. -/
theorem arrived_le (log : List (Record Ref)) (ras : List (Ref × Nat)) (n : Nat) :
    arrived log ras n ≤ ras.length := by
  have := wsum_le (key := Prod.fst) (w := fun _ => (1 : Nat)) ras (ids log n)
  rw [sum_map_one] at this
  exact this

/-- Every arrival is among the first `n` records exactly when their number is the count. -/
theorem arrived_eq_iff {log : List (Record Ref)} {ras : List (Ref × Nat)} {n : Nat} :
    arrived log ras n = ras.length ↔ ∀ a ∈ ras, a.1 ∈ ids log n := by
  unfold arrived
  rw [← sum_map_one ras]
  exact wsum_eq_iff fun _ _ => Nat.one_pos

/-- Once every arrival is recorded, the expected bytes are all the bytes the arrivals expect. -/
theorem expected_of_arrived {log : List (Record Ref)} {ras : List (Ref × Nat)} {n : Nat}
    (h : arrived log ras n = ras.length) : expected log ras n = (ras.map Prod.snd).sum :=
  wsum_all (arrived_eq_iff.mp h)

theorem perform_arrive {c a x s t : Nat} (ha : a < c) (hx : x + t ≤ limit) (hs : s ≤ limit)
    (observed : Bool) :
    perform (some (state c a x s observed)) (.arrive 1 t) =
      .ok ⟨some (state c (a + 1) (x + t) s false), none, none⟩ := by
  have h1 : t < 4294967296 := by unfold limit at hx; omega
  unfold limit at hx hs
  have hac : ¬ (a = c ∧ x = s) := fun h => by omega
  simp only [state, hac, ↓reduceIte]
  simp [perform, validCount, validTxOperand, validTx, advance, limit, h1, pure, Except.pure]
  split_ifs <;> simp_all <;> omega

theorem perform_complete {c a x s n : Nat} (hopen : ¬ (a = c ∧ x = s)) (ha : a ≤ c)
    (hn : 0 < n) (hx : x ≤ limit) (hs : s + n ≤ limit) (observed : Bool) :
    perform (some (state c a x s observed)) (.completeTx n) =
      .ok ⟨some (state c a x (s + n) false), none, none⟩ := by
  have h1 : n < 4294967296 := by unfold limit at hs; omega
  unfold limit at hx hs
  simp only [state, hopen, ↓reduceIte]
  simp [perform, validTxOperand, validTx, advance, limit, h1, pure, Except.pure]
  split_ifs <;> simp_all <;> omega

theorem perform_poll_open {c a x s : Nat} (h : ¬ (a = c ∧ x = s)) (observed ok : Bool) :
    perform (some (state c a x s observed)) (.pollParity 0 ok) =
      .ok ⟨some (state c a x s observed), some false, none⟩ := by
  simp only [state, h, ↓reduceIte]
  cases ok <;> rfl

theorem perform_poll_done {c a x s : Nat} (h : a = c ∧ x = s) (observed ok : Bool) :
    perform (some (state c a x s observed)) (.pollParity 0 ok) =
      .ok ⟨some (state c a x s (observed || ok)), some ok, if ok then some 0 else none⟩ := by
  simp only [state, h, and_self, ↓reduceIte]
  cases observed <;> cases ok <;> rfl

/-- The history of a one-phase mbarrier `m` that is initialized first (`InitFirst`) with the
count of the arrivals `ras`: each arrival (id, expected bytes) a unit arrival, the complete-tx
records of the copies `cs` (issue event, bytes), and polls of phase 0's parity. The
initialization need not happen before the other records' issuers: a kernel can prove that it is
first in the object's history from its publication (OBJ-MBAR-INIT-PUBLICATION). An event table whose
initialization happens before every other record's issuer has such a history (`Table.hist`). -/
structure Hist (X : Execution) (m : Loc) (ras : List (Ref × Nat)) (cs : List (EvId × Nat)) :
    Prop where
  /-- The arrival count is a valid count. -/
  count : validCount ras.length
  bytes : (ras.map Prod.snd).sum ≤ limit
  /-- The copies' sizes are positive and sum to the bytes the arrivals expect. -/
  sizes : (cs.map Prod.snd).sum = (ras.map Prod.snd).sum ∧ ∀ c ∈ cs, 0 < c.2
  /-- The copies are distinct issue events. -/
  nodup : (cs.map Prod.fst).Nodup
  /-- The arrivals have distinct ids. -/
  arrivals_nodup : (ras.map Prod.fst).Nodup
  /-- Every record is an initialization, an arrival, a copy's complete-tx or a poll. -/
  records : ∀ r ∈ X.objects m, r.action = .init ras.length ∨
    (∃ a ∈ ras, r.id = a.1 ∧ r.action = .arrive 1 a.2) ∨
    (∃ c ∈ cs, r.id = .async c.1 (.notify .copy) ∧ r.action = .completeTx c.2) ∨
    ∃ k ok, r.id = .thread k ∧ r.action = .pollParity 0 ok
  /-- A record with an arrival's id is that arrival. -/
  arrive_record : ∀ r ∈ X.objects m, ∀ a ∈ ras, r.id = a.1 → r.action = .arrive 1 a.2
  /-- The object is initialized first, once, with the arrival count, without fault. -/
  init_first : PairTmaRing.InitFirst X m ras.length
  /-- The copies complete on `m`. -/
  copy_mbar : ∀ c ∈ cs, ∀ s, issuedBy X c.1 = some s → s.completion = .mbarrier m
  /-- No event invalidates `m`. -/
  no_inval : ∀ v, ¬ X.MbInval v m

namespace Hist

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {ras : List (Ref × Nat)} {cs : List (EvId × Nat)}
  (ht : Hist X m ras cs) (hX : Consistent L K A mem0 X)
include ht hX

omit hX in
/-- The history of `m` invalidates nothing. -/
theorem noInval : NoInval (X.objects m) := by
  intro r hr ha
  rcases ht.records r hr with h1 | ⟨_, -, -, h1⟩ | ⟨_, -, -, h1⟩ | ⟨_, _, -, h1⟩ <;>
    rw [ha] at h1 <;> cases h1

omit ht hX in
theorem mem_of_get {k : Nat} {r : Record Ref} (hr : (X.objects m)[k]? = some r) :
    r ∈ X.objects m := List.mem_of_getElem? hr

/-- **The initialization is record 0** and succeeds, of every history with a record. -/
theorem first {r : Record Ref} (hr : r ∈ X.objects m) :
    ∃ r0, (X.objects m)[0]? = some r0 ∧ r0.action = .init ras.length ∧ r0.fault = none ∧
      r0.reply = ⟨some ⟨0, ras.length, ras.length, 0, true⟩, none, none⟩ := by
  obtain ⟨r0, h0, ha, hf, -⟩ := ht.init_first r hr
  have hok := (hX.tma.2.2.1 m).1.at h0
  obtain ⟨-, hreply⟩ := init_record_success hok ha (by simp [stateBefore]) ht.count
  exact ⟨r0, h0, ha, hf, hreply⟩

/-- An initialization's record is record 0. -/
theorem index_init {k : Nat} {r : Record Ref} (hr : (X.objects m)[k]? = some r) {n : Nat}
    (ha : r.action = .init n) : k = 0 := by
  obtain ⟨r0, h0, -, -, huniq⟩ := ht.init_first r (mem_of_get hr)
  have := huniq r (mem_of_get hr) ⟨n, ha⟩
  subst this
  exact hX.object_index_eq hr h0 rfl

omit ht in
/-- A record's id is not among the ids of the records before it. -/
theorem not_mem_ids {k : Nat} {r : Record Ref} (hr : (X.objects m)[k]? = some r) :
    r.id ∉ ids (X.objects m) k := by
  intro h
  obtain ⟨j, hj, q, hq, hqid⟩ := mem_ids.mp h
  have := hX.object_index_eq hq hr hqid
  omega

omit ht in
/-- A copy's complete-tx is not an arrival. -/
theorem copy_ne_arrive {r : Record Ref} (hr : r ∈ X.objects m) {n tx : Nat}
    (ha : r.action = .arrive n tx) (i : EvId) : r.id ≠ .async i (.notify .copy) := by
  intro hid
  obtain ⟨s, -, -, -, hs⟩ := hX.copy_record hr hid
  rw [ha] at hs
  cases hs

omit ht in
/-- A copy's complete-tx is not an initialization. -/
theorem copy_ne_init {r : Record Ref} (hr : r ∈ X.objects m) {n : Nat}
    (ha : r.action = .init n) (i : EvId) : r.id ≠ .async i (.notify .copy) := by
  intro hid
  obtain ⟨s, -, -, -, hs⟩ := hX.copy_record hr hid
  rw [ha] at hs
  cases hs

omit hX in
/-- A record whose action is not an arrival has no arrival's id. -/
theorem not_arrival_id {r : Record Ref} (hr : r ∈ X.objects m)
    (hna : ∀ n tx, r.action ≠ .arrive n tx) :
    ∀ a ∈ ras, a.1 ≠ r.id :=
  fun a ha h => hna 1 a.2 (ht.arrive_record r hr a ha h.symm)

omit hX in
/-- The copies' completions are distinct. -/
theorem copy_nodup : (cs.map copyRef).Nodup := by
  have : cs.map copyRef = (cs.map Prod.fst).map (fun i => Ref.async i (.notify .copy)) := by
    simp [copyRef, Function.comp_def]
  rw [this]
  exact ht.nodup.map fun i j h => by cases h; rfl

/-- The state after the first `k + 1` records: `stateAt` of the recorded arrivals and copies. -/
def Inv (log : List (Record Ref)) (ras : List (Ref × Nat)) (cs : List (EvId × Nat)) (k : Nat)
    (r : Record Ref) : Prop :=
  r.fault = none ∧ ∃ observed, r.reply.state = some (stateAt log ras cs (k + 1) observed)

omit hX in
theorem done_le (n : Nat) : done (X.objects m) cs n ≤ (ras.map Prod.snd).sum := by
  have := wsum_le (key := copyRef) (w := Prod.snd) cs (ids (X.objects m) n)
  rw [ht.sizes.1] at this
  exact this

omit ht hX in
theorem expected_le (log : List (Record Ref)) (n : Nat) :
    expected log ras n ≤ (ras.map Prod.snd).sum :=
  wsum_le _ _

omit hX in
/-- The object has completed its phase before record `k` exactly when every arrival and every
copy are among the records before it. -/
theorem completed_iff (k : Nat) :
    (arrived (X.objects m) ras k = ras.length ∧
        expected (X.objects m) ras k = done (X.objects m) cs k) ↔
      (∀ a ∈ ras, a.1 ∈ ids (X.objects m) k) ∧
        ∀ c ∈ cs, Ref.async c.1 (.notify .copy) ∈ ids (X.objects m) k := by
  constructor
  · rintro ⟨ha, hx⟩
    refine ⟨arrived_eq_iff.mp ha, ?_⟩
    rw [expected_of_arrived ha, ← ht.sizes.1] at hx
    exact (wsum_eq_iff ht.sizes.2).mp hx.symm
  · rintro ⟨ha, hc⟩
    have ha' := arrived_eq_iff.mpr ha
    refine ⟨ha', ?_⟩
    rw [expected_of_arrived ha', ← ht.sizes.1]
    exact (wsum_all hc).symm

omit ht hX in
private theorem invariant_step (ht : Hist X m ras cs) (hX : Consistent L K A mem0 X)
    {k : Nat} {r q : Record Ref} (hr : (X.objects m)[k]? = some r)
    (hq : (X.objects m)[k + 1]? = some q) (ih : Inv (X.objects m) ras cs k r) :
    Inv (X.objects m) ras cs (k + 1) q := by
  have hc := (hX.tma.2.2.1 m).1.at hq
  have hs : stateBefore (X.objects m) (k + 1) = r.reply.state := by
    simp [stateBefore, hr]
  obtain ⟨observed, hv⟩ := ih.2
  rw [hs, hv] at hc
  have hids := ids_succ hq
  have hnew := not_mem_ids hX hq
  have hqm := mem_of_get hq
  have hT := ht.bytes
  have hdle := ht.done_le (k + 1 + 1)
  have hxle := expected_le (ras := ras) (X.objects m) (k + 1 + 1)
  have hale := arrived_le (X.objects m) ras (k + 1 + 1)
  -- a record other than an arrival keeps the arrivals
  have hkeep (hna : ∀ n tx, q.action ≠ .arrive n tx) :
      arrived (X.objects m) ras (k + 1 + 1) = arrived (X.objects m) ras (k + 1) ∧
        expected (X.objects m) ras (k + 1 + 1) = expected (X.objects m) ras (k + 1) := by
    unfold arrived expected
    rw [hids, wsum_snoc_other (ht.not_arrival_id hqm hna),
      wsum_snoc_other (ht.not_arrival_id hqm hna)]
    exact ⟨rfl, rfl⟩
  rcases ht.records q hqm with ha | ⟨a, ham, hid, ha⟩ | ⟨c, hcm, hid, ha⟩ |
    ⟨j, ok, hid, ha⟩
  · have := ht.index_init hX hq ha; omega
  · -- an arrival
    have hna : a.1 ∉ ids (X.objects m) (k + 1) := hid ▸ hnew
    have harr : arrived (X.objects m) ras (k + 1 + 1) = arrived (X.objects m) ras (k + 1) + 1 := by
      unfold arrived
      rw [hids, hid]
      exact wsum_snoc_new ht.arrivals_nodup ham hna
    have hexp : expected (X.objects m) ras (k + 1 + 1) =
        expected (X.objects m) ras (k + 1) + a.2 := by
      unfold expected
      rw [hids, hid]
      exact wsum_snoc_new ht.arrivals_nodup ham hna
    have hdone : done (X.objects m) cs (k + 1 + 1) = done (X.objects m) cs (k + 1) := by
      unfold done
      rw [hids]
      exact wsum_snoc_other fun c _ h => copy_ne_arrive hX hqm ha c.1 h.symm
    simp only [stateAt] at hc
    have hdle' := ht.done_le (k + 1)
    have hstep := perform_arrive (c := ras.length) (a := arrived (X.objects m) ras (k + 1))
      (x := expected (X.objects m) ras (k + 1)) (t := a.2) (s := done (X.objects m) cs (k + 1))
      (by omega) (by omega) (by omega) observed
    simp only [RecordOk, ha, hstep] at hc
    refine ⟨hc.2, false, ?_⟩
    rw [hc.1, stateAt, harr, hexp, hdone]
  · -- a copy's complete-tx
    have hnc : copyRef c ∉ ids (X.objects m) (k + 1) := by
      rw [copyRef, ← hid]
      exact hnew
    have hdone : done (X.objects m) cs (k + 1 + 1) = done (X.objects m) cs (k + 1) + c.2 := by
      unfold done
      rw [hids, show q.id = copyRef c from hid]
      exact wsum_snoc_new ht.copy_nodup hcm hnc
    obtain ⟨harr, hexp⟩ := hkeep (by rw [ha]; nofun)
    have hpos := ht.sizes.2 c hcm
    have hopen : ¬ (arrived (X.objects m) ras (k + 1) = ras.length ∧
        expected (X.objects m) ras (k + 1) = done (X.objects m) cs (k + 1)) := by
      rintro ⟨h1, h2⟩
      rw [expected_of_arrived h1] at h2
      omega
    simp only [stateAt] at hc
    simp only [RecordOk, ha, perform_complete hopen (arrived_le _ _ _) hpos
      (by have := expected_le (ras := ras) (X.objects m) (k + 1); omega) (by omega)] at hc
    exact ⟨hc.2, false, by rw [hc.1, stateAt, harr, hexp, hdone]⟩
  · -- a poll
    obtain ⟨harr, hexp⟩ := hkeep (by rw [ha]; nofun)
    have hdone : done (X.objects m) cs (k + 1 + 1) = done (X.objects m) cs (k + 1) := by
      unfold done
      rw [hids]
      exact wsum_snoc_other fun c _ h => by rw [hid] at h; cases h
    simp only [stateAt] at hc
    by_cases hdn : arrived (X.objects m) ras (k + 1) = ras.length ∧
        expected (X.objects m) ras (k + 1) = done (X.objects m) cs (k + 1)
    · simp only [RecordOk, ha, perform_poll_done hdn] at hc
      exact ⟨hc.2, _, by rw [hc.1, stateAt, harr, hexp, hdone]⟩
    · simp only [RecordOk, ha, perform_poll_open hdn] at hc
      exact ⟨hc.2, _, by rw [hc.1, stateAt, harr, hexp, hdone]⟩

/-- **The object's states**: after the first `k + 1` records, `stateAt` of the recorded
arrivals and copies, without faults. -/
theorem invariant {k : Nat} {r : Record Ref} (hr : (X.objects m)[k]? = some r) :
    Inv (X.objects m) ras cs k r := by
  induction k generalizing r with
  | zero =>
    obtain ⟨r0, h0, ha0, hf0, hv0⟩ := ht.first hX (mem_of_get hr)
    rw [hr] at h0
    cases h0
    have hids : ids (X.objects m) 1 = [r.id] := by
      rw [ids_succ hr]
      simp [ids]
    have hna : ∀ n tx, r.action ≠ .arrive n tx := by rw [ha0]; nofun
    have harr : arrived (X.objects m) ras 1 = 0 := by
      unfold arrived
      rw [hids, show [r.id] = [] ++ [r.id] from rfl,
        wsum_snoc_other (ht.not_arrival_id (mem_of_get hr) hna), wsum_nil]
    have hexp : expected (X.objects m) ras 1 = 0 := by
      unfold expected
      rw [hids, show [r.id] = [] ++ [r.id] from rfl,
        wsum_snoc_other (ht.not_arrival_id (mem_of_get hr) hna), wsum_nil]
    have hdone : done (X.objects m) cs 1 = 0 := by
      unfold done
      rw [hids, show [r.id] = [] ++ [r.id] from rfl,
        wsum_snoc_other (fun c _ h => copy_ne_init hX (mem_of_get hr) ha0 c.1 h.symm), wsum_nil]
    have hc0 := ht.count.1
    refine ⟨hf0, true, ?_⟩
    rw [hv0, stateAt, harr, hexp, hdone]
    have hne : ¬ 0 = ras.length := by omega
    simp [state, hne]
  | succ k ih =>
    have hlen := (List.getElem?_eq_some_iff.mp hr).1
    have hp := List.getElem?_eq_getElem (show k < (X.objects m).length by omega)
    exact invariant_step ht hX hp hr (ih hp)

/-- **No record faults.** -/
theorem fault_free {r : Record Ref} (hr : r ∈ X.objects m) : r.fault = none := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hr
  exact (ht.invariant hX (by rw [← hget]; exact List.getElem?_eq_getElem hk)).1

/-- The state before record `k ≥ 1`. -/
theorem stateBefore_eq {k : Nat} (h1 : 1 ≤ k) (hk : k ≤ (X.objects m).length) :
    ∃ observed, stateBefore (X.objects m) k = some (stateAt (X.objects m) ras cs k observed) := by
  have hp := List.getElem?_eq_getElem (show k - 1 < (X.objects m).length by omega)
  obtain ⟨-, obs, hv⟩ := ht.invariant hX hp
  rw [Nat.sub_add_cancel h1] at hv
  exact ⟨obs, by simp only [stateBefore, show k ≠ 0 by omega, ↓reduceIte, hp, Option.bind_some, hv]⟩

/-- An arrival and a copy update phase 0. -/
theorem phase_update {i : Nat} {d : Record Ref} (hd : (X.objects m)[i]? = some d)
    (hid : (∃ a ∈ ras, d.id = a.1) ∨ ∃ c ∈ cs, d.id = .async c.1 (.notify .copy)) :
    phaseAt (X.objects m) i = some 0 := by
  have hi : 1 ≤ i := by
    by_contra h
    obtain rfl : i = 0 := by omega
    obtain ⟨r0, h0, ha0, -⟩ := ht.first hX (mem_of_get hd)
    rw [hd] at h0
    cases h0
    rcases hid with ⟨a, ha, h⟩ | ⟨c, -, h⟩
    · have := ht.arrive_record _ (mem_of_get hd) a ha h
      rw [ha0] at this
      cases this
    · exact copy_ne_init hX (mem_of_get hd) ha0 c.1 h
  have hlen := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨obs, hs⟩ := ht.stateBefore_eq hX hi (by omega)
  have hnew := not_mem_ids hX hd
  have hopen : ¬ (arrived (X.objects m) ras i = ras.length ∧
      expected (X.objects m) ras i = done (X.objects m) cs i) := by
    rw [ht.completed_iff]
    rintro ⟨ha, hc⟩
    rcases hid with ⟨a, ha', h⟩ | ⟨c, hc', h⟩
    · exact hnew (h ▸ ha a ha')
    · exact hnew (h ▸ hc c hc')
  simp only [phaseAt, hs, stateAt, state, hopen, ↓reduceIte, Option.map_some]

/-- A successful poll of phase 0 follows every arrival and every copy, and observes the
completed phase 0. -/
theorem poll_done {j : Nat} {w : Record Ref} (hw : (X.objects m)[j]? = some w)
    (ha : w.action = .pollParity 0 true) :
    w.fault = none ∧ w.reply.waited = some true ∧ (∀ a ∈ ras, a.1 ∈ ids (X.objects m) j) ∧
      (∀ c ∈ cs, Ref.async c.1 (.notify .copy) ∈ ids (X.objects m) j) ∧
      observedAt (X.objects m) j = some 0 := by
  have hf := ht.fault_free hX (mem_of_get hw)
  have hwait := ((hX.tma.2.2.1 m).2.1 w (mem_of_get hw)).2 0 true ha hf
  have hj : 1 ≤ j := by
    by_contra h
    obtain rfl : j = 0 := by omega
    obtain ⟨r0, h0, ha0, -⟩ := ht.first hX (mem_of_get hw)
    rw [hw] at h0
    cases h0
    rw [ha] at ha0
    cases ha0
  have hlen := (List.getElem?_eq_some_iff.mp hw).1
  obtain ⟨obs, hs⟩ := ht.stateBefore_eq hX hj (by omega)
  have hc := (hX.tma.2.2.1 m).1.at hw
  rw [hs] at hc
  simp only [stateAt] at hc
  by_cases hdn : arrived (X.objects m) ras j = ras.length ∧
      expected (X.objects m) ras j = done (X.objects m) cs j
  · simp only [RecordOk, ha, perform_poll_done hdn] at hc
    obtain ⟨hra, hcs⟩ := (ht.completed_iff j).mp hdn
    exact ⟨hf, hwait, hra, hcs, by simp [observedAt, hw, hc.1]⟩
  · simp only [RecordOk, ha, perform_poll_open hdn] at hc
    rw [hc.1] at hwait
    cases hwait

omit ht in
/-- The record of an object action that the object's history covers. -/
theorem record_of_action {id : Ref} {act : Action}
    (ha : objectAction X X.async m id = some act) :
    ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = id ∧ r.action = act := by
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 m).2.2 _ _ ha
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hr
  have hmatch := ((hX.tma.2.2.1 m).2.1 r hr).1
  rw [hid, ha] at hmatch
  exact ⟨k, r, by rw [← hget]; exact List.getElem?_eq_getElem hk, hid,
    (Option.some.inj hmatch).symm⟩

/-- **A successful poll of phase 0 observes every arrival and every copy**: their records
precede the poll's in the phase it observes. -/
theorem poll_observes {k : EvId} {pc : Nat} {acq : Bool} {ws : MbarScope}
    (he : X.get k = some ⟨pc, .wait m 0 true acq ws⟩) {x : Ref}
    (hx : (∃ a ∈ ras, x = a.1) ∨ ∃ c ∈ cs, x = .async c.1 (.notify .copy)) :
    ∃ i j d w, (X.objects m)[i]? = some d ∧ d.id = x ∧ d.fault = none ∧
      (X.objects m)[j]? = some w ∧ w.id = .thread k ∧ w.fault = none ∧
      w.reply.waited = some true ∧ phaseAt (X.objects m) i = some 0 ∧
      observedAt (X.objects m) j = some 0 := by
  have hact : objectAction X X.async m (.thread k) = some (.pollParity 0 true) := by
    simp only [objectAction, he, ↓reduceIte]
  obtain ⟨j, w, hw, hwid, ha⟩ := record_of_action hX hact
  obtain ⟨hwf, hwait, hra, hcs, ho⟩ := ht.poll_done hX hw ha
  have hmem : x ∈ ids (X.objects m) j := by
    rcases hx with ⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩
    · exact hra a ha
    · exact hcs c hc
  obtain ⟨i, -, d, hd, hdid⟩ := mem_ids.mp hmem
  exact ⟨i, j, d, w, hd, hdid, ht.fault_free hX (mem_of_get hd), hw, hwid, hwf, hwait,
    ht.phase_update hX hd (hdid ▸ hx), ho⟩

/-- **A successful poll of phase 0 observes every arrival.** -/
theorem observes_arrive {a : Ref × Nat} (ham : a ∈ ras) {k : EvId} {pc : Nat} {acq : Bool}
    {ws : MbarScope} (he : X.get k = some ⟨pc, .wait m 0 true acq ws⟩) :
    UpdateBeforeWait (X.objects m) a.1 (.thread k) := by
  obtain ⟨i, j, d, w, hd, hdid, hdf, hw, hwid, hwf, hwait, hp, ho⟩ :=
    ht.poll_observes hX he (.inl ⟨a, ham, rfl⟩)
  have hu := MbarRing.Slot.updateBeforeWait_of_phase (hX.tma.2.2.1 m).1 ht.noInval hd hdf hw hwf
    hwait hp ho
  rwa [hdid, hwid] at hu

/-- **A successful poll of phase 0 observes every copy's completion.** -/
theorem observes_copy {c : EvId × Nat} (hc : c ∈ cs) {k : EvId} {pc : Nat} {acq : Bool}
    {ws : MbarScope} (he : X.get k = some ⟨pc, .wait m 0 true acq ws⟩) :
    AsyncObserved X c.1 (.notify .copy) k acq ws := by
  obtain ⟨i, j, d, w, hd, hdid, hdf, hw, hwid, hwf, hwait, hp, ho⟩ :=
    ht.poll_observes hX he (.inr ⟨c, hc, rfl⟩)
  exact hX.copy_observed_of_phase ht.noInval hd hdid hdf hw hwid hwf hwait hp ho he

/-- **The final state**, of a history with a record, is the completed phase 1 exactly when
every arrival and every copy are recorded, and phase 0 otherwise. -/
theorem final_state (hne : X.objects m ≠ []) :
    ∃ s, stateBefore (X.objects m) (X.objects m).length = some s ∧ s.phase ≤ 1 ∧
      (s.phase = 1 ↔ (∀ a ∈ ras, ∃ r ∈ X.objects m, r.id = a.1) ∧
        ∀ c ∈ cs, ∃ r ∈ X.objects m, r.id = .async c.1 (.notify .copy)) := by
  have hl : 1 ≤ (X.objects m).length := List.length_pos_iff.mpr hne
  obtain ⟨obs, hs⟩ := ht.stateBefore_eq hX hl le_rfl
  refine ⟨_, hs, ?_, ?_⟩
  · unfold stateAt state
    split_ifs <;> simp
  · simp only [← mem_ids_length, ← ht.completed_iff]
    unfold stateAt state
    split_ifs with h
    · simp [h]
    · simpa using h

/-- A notified copy of `cs` is recorded. -/
theorem copy_recorded {c : EvId × Nat} (hc : c ∈ cs)
    (hn : (X.async.copies c.1).notified = true) :
    ∃ r ∈ X.objects m, r.id = .async c.1 (.notify .copy) := by
  obtain ⟨spec, hspec, -⟩ := hX.tma.1 c.1 ⟨.notify .copy, by simp [present, hn]⟩
  have hm := ht.copy_mbar c hc spec hspec
  refine (hX.tma.2.2.1 m).2.2 _ (.completeTx spec.dst.size) ?_
  change (do
    let s ← issuedBy X c.1
    if s.completion = AsyncCopy.Completion.mbarrier m ∧ (X.async.copies c.1).notified = true then
      some (MBarrier.Action.completeTx s.dst.size) else none) = _
  simp [hspec, hm, hn]

/-- An arrival that the object covers is recorded, as the arrival. -/
theorem arrive_recorded {a : Ref × Nat} (ham : a ∈ ras) {act : Action}
    (ha : objectAction X X.async m a.1 = some act) :
    ∃ r ∈ X.objects m, r.id = a.1 ∧ r.action = .arrive 1 a.2 := by
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 m).2.2 _ _ ha
  exact ⟨r, hr, hid, ht.arrive_record r hr a ham hid⟩

end Hist

/-- The event table of a one-phase mbarrier `m`: initialization `e0` with the count of the
arrivals `ras`, each arrival (id, expected bytes) a unit arrival, the complete-tx records of the
copies `cs` (issue event, bytes), and polls of phase 0's parity. -/
structure Table (L : Launch) (X : Execution) (m : Loc) (e0 : EvId) (ras : List (Ref × Nat))
    (cs : List (EvId × Nat)) : Prop where
  /-- The arrival count is a valid count. -/
  count : validCount ras.length
  bytes : (ras.map Prod.snd).sum ≤ limit
  /-- The copies' sizes are positive and sum to the bytes the arrivals expect. -/
  sizes : (cs.map Prod.snd).sum = (ras.map Prod.snd).sum ∧ ∀ c ∈ cs, 0 < c.2
  /-- The copies are distinct issue events. -/
  nodup : (cs.map Prod.fst).Nodup
  /-- The arrivals have distinct ids. -/
  arrivals_nodup : (ras.map Prod.fst).Nodup
  /-- Every record is the initialization, an arrival, a copy's complete-tx or a poll. -/
  records : ∀ r ∈ X.objects m, (r.id = .thread e0 ∧ r.action = .init ras.length) ∨
    (∃ a ∈ ras, r.id = a.1 ∧ r.action = .arrive 1 a.2) ∨
    (∃ c ∈ cs, r.id = .async c.1 (.notify .copy) ∧ r.action = .completeTx c.2) ∨
    ∃ k ok, r.id = .thread k ∧ r.action = .pollParity 0 ok
  /-- A record with an arrival's id is that arrival. -/
  arrive_record : ∀ r ∈ X.objects m, ∀ a ∈ ras, r.id = a.1 → r.action = .arrive 1 a.2
  /-- The initialization happens before the issuer of every other record. -/
  init_hb : ∀ r ∈ X.objects m, r.id ≠ .thread e0 → baseCausality L X e0 r.id.issuer
  /-- The initialization event initializes `m` with the arrival count. -/
  init_event : ∀ ev, X.get e0 = some ev → ev.kind = .mbInit m ras.length
  /-- The copies complete on `m`. -/
  copy_mbar : ∀ c ∈ cs, ∀ s, issuedBy X c.1 = some s → s.completion = .mbarrier m
  /-- No event invalidates `m`. -/
  no_inval : ∀ v, ¬ X.MbInval v m

namespace Table

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {e0 : EvId} {ras : List (Ref × Nat)} {cs : List (EvId × Nat)}
  (ht : Table L X m e0 ras cs) (hX : Consistent L K A mem0 X)
include ht hX

/-- The initialization event, when the history has a record. -/
theorem init_mbInit {r : Record Ref} (hr : r ∈ X.objects m) : X.MbInit e0 m ras.length := by
  have hpres : ∃ ev, X.get e0 = some ev := by
    by_cases hid : r.id = .thread e0
    · have hp := object_record_present hX.tma hr
      rw [hid] at hp
      exact hp
    · have hh := baseCausality_events (ht.init_hb r hr hid)
      exact ⟨_, List.getElem?_eq_getElem hh.1⟩
  obtain ⟨⟨pc, k⟩, he⟩ := hpres
  have := ht.init_event _ he
  subst this
  exact ⟨pc, he⟩

/-- The initialization's record initializes. -/
theorem id_init {r : Record Ref} (hr : r ∈ X.objects m) (hid : r.id = .thread e0) :
    r.action = .init ras.length := by
  have hmatch := ((hX.tma.2.2.1 m).2.1 r hr).1
  obtain ⟨pc, he⟩ := ht.init_mbInit hX hr
  rw [hid] at hmatch
  simp only [objectAction, he, ↓reduceIte] at hmatch
  exact (Option.some.inj hmatch).symm

/-- **The initialization is record 0** and succeeds, of every history with a record. -/
theorem first {r : Record Ref} (hr : r ∈ X.objects m) :
    ∃ r0, (X.objects m)[0]? = some r0 ∧ r0.id = .thread e0 ∧ r0.action = .init ras.length ∧
      r0.fault = none ∧
      r0.reply = ⟨some ⟨0, ras.length, ras.length, 0, true⟩, none, none⟩ := by
  have huniq : ∀ (j : Nat) (s : Record Ref) (n : Nat), (X.objects m)[j]? = some s →
      s.action = .init n → s.id = .thread e0 := by
    intro j s n hs ha
    rcases ht.records s (Hist.mem_of_get hs) with ⟨h1, -⟩ | ⟨_, -, -, h1⟩ | ⟨_, -, -, h1⟩ |
      ⟨_, _, -, h1⟩
    · exact h1
    all_goals rw [ha] at h1; cases h1
  have hnot : ∀ (j : Nat) (s : Record Ref), (X.objects m)[j]? = some s →
      (∀ n, s.action ≠ .init n) → s.id ≠ .thread e0 := by
    intro j s hs hnon h0
    exact hnon _ (ht.id_init hX (Hist.mem_of_get hs) h0)
  exact init_record_success_of_unique_init hX (ht.init_mbInit hX hr) ht.count huniq
    fun j s hs hnon => object_not_before_of_baseCausality hX ⟨_, ht.init_mbInit hX hr⟩
      (ht.init_hb s (Hist.mem_of_get hs) (hnot j s hs hnon))

/-- The initialization's record is record 0. -/
theorem index_init {k : Nat} {r : Record Ref} (hr : (X.objects m)[k]? = some r)
    (hid : r.id = .thread e0) : k = 0 := by
  obtain ⟨r0, h0, hid0, -⟩ := ht.first hX (Hist.mem_of_get hr)
  exact hX.object_index_eq hr h0 (hid.trans hid0.symm)

/-- **The table's history is that of a mbarrier initialized first.** -/
theorem hist : Hist X m ras cs := by
  refine ⟨ht.count, ht.bytes, ht.sizes, ht.nodup, ht.arrivals_nodup, fun r hr => ?_,
    ht.arrive_record, fun r hr => ?_, ht.copy_mbar, ht.no_inval⟩
  · rcases ht.records r hr with ⟨-, h⟩ | h | h | h
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl h)), .inr (.inr (.inr h))]
  · obtain ⟨r0, h0, hid0, ha0, hf0, -⟩ := ht.first hX hr
    refine ⟨r0, h0, ha0, hf0, fun q hq ⟨n, hn⟩ => ?_⟩
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hq
    have hg : (X.objects m)[k]? = some q := by rw [← hget]; exact List.getElem?_eq_getElem hk
    have hid : q.id = .thread e0 := by
      rcases ht.records q hq with ⟨h1, -⟩ | ⟨_, -, -, h1⟩ | ⟨_, -, -, h1⟩ | ⟨_, _, -, h1⟩
      · exact h1
      all_goals rw [hn] at h1; cases h1
    have := ht.index_init hX hg hid
    subst this
    rw [hg] at h0
    exact Option.some.inj h0

/-- **Every record follows the published initialization.** -/
theorem published {r : Record Ref} (hr : r ∈ X.objects m) :
    ObjectPublished L X m r := by
  obtain ⟨r0, h0, hid0, ha0, hf0, -⟩ := ht.first hX hr
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hr
  have hg : (X.objects m)[j]? = some r := by rw [← hget]; exact List.getElem?_eq_getElem hj
  by_cases hid : r.id = .thread e0
  · left
    have hz := ht.index_init hX hg hid
    subst j
    rw [hg] at h0
    cases h0
    exact ⟨⟨_, ha0⟩, fun v hv => (ht.no_inval v hv).elim⟩
  right
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · rw [hg] at h0; cases h0; exact (hid hid0).elim
    · exact h
  refine ⟨e0, ras.length, ht.init_mbInit hX hr,
    ⟨0, j, r0, r, ras.length, h0, hid0, ha0, hf0, hg, rfl, hj0,
      ((ht.hist hX).noInval).sameLifetime 0 j⟩,
    .inl (ht.init_hb r hr hid), fun v hv => (ht.no_inval v hv).elim⟩

end Table

end

end PTX.MbarOneShot
