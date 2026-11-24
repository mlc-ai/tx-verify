-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Interface
public import Lemmas.Kernel.MbarBulk

@[expose] public section

/-! # `tma_copy`: the events of a possible execution

From the thread facts: every event of a thread other than 0 is its exit, and thread 0's events
are its four issue events, then polls, then after a successful poll the read of `buf`, the
write of `B` with the read's value, and the exit, or undefined behaviour after a read whose bytes
are not one word (`event_cases`). So every event is of the mbarrier/bulk class (`mbarBulk`), and
each kind of event is at its known place (`reads_cases`, `writes_cases`, `bulk_cases`,
`mbInit_cases`, `arrive_cases`, `wait_cases`, …). -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof

noncomputable section

variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {X : Execution}

theorem get_lt {g k : Nat} {e : Event} (he : X.get (g, k) = some e) : k < (X.tr g).length :=
  (List.getElem?_eq_some_iff.mp he).1

/-- A prefix fixes the position and the events before it. -/
theorem take_eq {g k : Nat} {p : List Event} (hk : k < (X.tr g).length)
    (h : (X.tr g).take k = p) : k = p.length ∧ ∀ i < p.length, X.get (g, i) = p[i]? := by
  have hl := congrArg List.length h
  simp only [List.length_take] at hl
  refine ⟨by omega, fun i hi => ?_⟩
  change (X.tr g)[i]? = _
  rw [← h]
  exact (List.getElem?_take_of_lt (by omega)).symm

theorem issue_get {S : Nat} {l : List Event} {k : Nat} (hk : k < 4) :
    (issue A S ++ l)[k]? = (issue A S)[k]? :=
  List.getElem?_append_left (by simp [issue]; omega)

theorem idx_after {S : Nat} (w : Event) (s : List Event) (n k : Nat) :
    (issue A S ++ List.replicate n w ++ s)[4 + n + k]? = s[k]? := by
  have hl : (issue A S ++ List.replicate n w).length = 4 + n := by simp [issue]; omega
  rw [List.getElem?_append_right (by omega), hl]
  simp

theorem idx_rep {S : Nat} (w : Event) (s : List Event) {n k : Nat} (h4 : 4 ≤ k)
    (hk : k < 4 + n) : (issue A S ++ List.replicate n w ++ s)[k]? = some w := by
  have hl : (issue A S ++ List.replicate n w).length = 4 + n := by simp [issue]; omega
  rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by simp [issue]; omega)]
  simp only [issue, List.length_cons, List.length_nil, List.getElem?_replicate]
  split_ifs with h
  · rfl
  · omega

section
variable (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)
include ht hX

/-- An event fires from a followed state, or is after the machine stopped. -/
theorem state_cases {g k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    (∃ s, stateAt L A B X g k = some (some s)) ∨ stateAt L A B X g k = none := by
  rcases Frame.fired ht.sound hX he with ⟨σ, o, hσ, -⟩ | ⟨hσ, -⟩
  · cases σ with
    | none => exact absurd hσ (ht.tracked g k (Frame.lt_of_get hX he))
    | some s => exact .inl ⟨s, hσ⟩
  · exact .inr hσ

/-- A read is at a followed load of thread 0, after the issue events, failed polls and a
successful poll. -/
theorem read_at {g k : Nat} {bs : List (Option Byte)}
    (he : X.get (g, k) = some (rdE L.sharedBase bs)) :
    g = 0 ∧ ∃ n, k = 4 + n + 1 ∧ (X.tr g).take k = issue A L.sharedBase ++
      List.replicate n (waitE L.sharedBase false) ++ [waitE L.sharedBase true] := by
  have hg := Frame.lt_of_get hX he
  rcases state_cases ht hX he with ⟨s, hσ⟩ | hσ
  · have hev := ht.event hg he hσ
    have hJ := ht.along hg (get_lt he).le hσ
    cases s with
    | load =>
      obtain ⟨h0, n, hp⟩ := hJ
      refine ⟨h0, n, ?_, hp⟩
      rw [(take_eq (get_lt he) hp).1]
      simp [issue]
      omega
    | store v =>
      rcases hev with ⟨-, h⟩ | ⟨-, f, h⟩ <;> simp [rdE, wrE] at h
    | exit => simp [SiteEvent, rdE, exE] at hev
    | wait => obtain ⟨ok, h⟩ := hev; simp [rdE, waitE] at h
    | _ => simp [SiteEvent, rdE, initE, fenceE, arriveE, bulkE] at hev
  · obtain ⟨pc, f, bs', h, -⟩ := ht.dead hg he hσ
    simp [rdE] at h

/-- The events of a possible execution, with the issue phase of thread 0 before every later
event of it. -/
theorem event_cases {e : EvId} {ev : Event} (h : X.get e = some ev) :
    e.1 < L.threads ∧
    ((e.1 ≠ 0 ∧ ev = exE) ∨
     (e.1 = 0 ∧ e.2 = 0 ∧ ev = initE L.sharedBase) ∨
     (e.1 = 0 ∧ e.2 = 1 ∧ ev = fenceE) ∨
     (e.1 = 0 ∧ e.2 = 2 ∧ ev = arriveE L.sharedBase) ∨
     (e.1 = 0 ∧ e.2 = 3 ∧ ev = bulkE A L.sharedBase) ∨
     (e.1 = 0 ∧ 4 ≤ e.2 ∧ (∀ k < 4, X.get (0, k) = (issue A L.sharedBase)[k]?) ∧
       ((∃ ok, ev = waitE L.sharedBase ok) ∨
        ∃ i, 4 ≤ i ∧ i < e.2 ∧ X.get (0, i) = some (waitE L.sharedBase true) ∧
          ((∃ bs, ev = rdE L.sharedBase bs) ∨
           (∃ bs v, X.get (0, e.2 - 1) = some (rdE L.sharedBase bs) ∧ rebuild 3 bs = .ok v ∧
              v.bytes = 4 ∧ ev = wrE B v) ∨
           ev = exE ∨
           (∃ pc f, ev = ⟨pc, .ub f⟩ ∧ ∃ bs, X.get (0, e.2 - 1) = some (rdE L.sharedBase bs) ∧
              ∀ v, rebuild 3 bs = .ok v → v.bytes ≠ 4))))) := by
  obtain ⟨g, k⟩ := e
  have hg := Frame.lt_of_get hX h
  refine ⟨hg, ?_⟩
  simp only
  have hk := get_lt h
  -- the shape after the successful poll at `4 + n`
  have tail : ∀ n (rest : List Event), (X.tr g).take k = issue A L.sharedBase ++
      List.replicate n (waitE L.sharedBase false) ++ waitE L.sharedBase true :: rest →
      g = 0 → k = 4 + n + 1 + rest.length ∧ (∀ j < 4, X.get (0, j) = (issue A L.sharedBase)[j]?) ∧
        X.get (0, 4 + n) = some (waitE L.sharedBase true) ∧
        ∀ j < rest.length, X.get (0, 4 + n + 1 + j) = rest[j]? := by
    intro n rest hp h0
    subst h0
    obtain ⟨hkl, hat⟩ := take_eq hk hp
    have hlen : (issue A L.sharedBase ++ List.replicate n (waitE L.sharedBase false) ++
        waitE L.sharedBase true :: rest).length = 4 + n + 1 + rest.length := by
      simp [issue]; omega
    refine ⟨by rw [hkl, hlen], fun j hj => ?_, ?_, fun j hj => ?_⟩
    · rw [hat j (by rw [hlen]; omega), List.append_assoc, issue_get hj]
    · rw [hat _ (by rw [hlen]; omega)]
      have := idx_after (A := A) (S := L.sharedBase) (waitE L.sharedBase false)
        (waitE L.sharedBase true :: rest) n 0
      simpa using this
    · rw [hat _ (by rw [hlen]; omega)]
      have := idx_after (A := A) (S := L.sharedBase) (waitE L.sharedBase false)
        (waitE L.sharedBase true :: rest) n (j + 1)
      rw [show 4 + n + 1 + j = 4 + n + (j + 1) by omega, this]
      rfl
  rcases state_cases ht hX h with ⟨s, hσ⟩ | hσ
  · have hev := ht.event hg h hσ
    have hJ := ht.along hg hk.le hσ
    cases s with
    | init =>
      obtain ⟨h0, hp⟩ := hJ
      exact .inr (.inl ⟨h0, (take_eq hk hp).1, hev⟩)
    | fence =>
      obtain ⟨h0, hp⟩ := hJ
      exact .inr (.inr (.inl ⟨h0, (take_eq hk hp).1, hev⟩))
    | arrive =>
      obtain ⟨h0, hp⟩ := hJ
      exact .inr (.inr (.inr (.inl ⟨h0, (take_eq hk hp).1, hev⟩)))
    | bulk =>
      obtain ⟨h0, hp⟩ := hJ
      exact .inr (.inr (.inr (.inr (.inl ⟨h0, (take_eq hk hp).1, hev⟩))))
    | wait =>
      obtain ⟨h0, n, hp⟩ := hJ
      subst h0
      obtain ⟨hkl, hat⟩ := take_eq hk hp
      have hlen : (issue A L.sharedBase ++ List.replicate n (waitE L.sharedBase false)).length =
          4 + n := by simp [issue]; omega
      refine .inr (.inr (.inr (.inr (.inr ⟨rfl, by omega, fun j hj => ?_, .inl hev⟩))))
      rw [hat j (by rw [hlen]; omega), issue_get hj]
    | load =>
      obtain ⟨h0, n, hp⟩ := hJ
      have hp' : (X.tr g).take k = issue A L.sharedBase ++
          List.replicate n (waitE L.sharedBase false) ++ waitE L.sharedBase true :: [] := by
        simp [hp]
      obtain ⟨hkl, h4, hw, -⟩ := tail n [] hp' h0
      subst h0
      simp only [List.length_nil] at hkl
      exact .inr (.inr (.inr (.inr (.inr ⟨rfl, by omega, h4,
        .inr ⟨4 + n, by omega, by omega, hw, .inl hev⟩⟩))))
    | store v =>
      obtain ⟨h0, n, bs, hp, hv, -⟩ := hJ
      have hp' : (X.tr g).take k = issue A L.sharedBase ++
          List.replicate n (waitE L.sharedBase false) ++
            waitE L.sharedBase true :: [rdE L.sharedBase bs] := by simp [hp]
      obtain ⟨hkl, h4, hw, hr⟩ := tail n _ hp' h0
      subst h0
      simp only [List.length_singleton] at hkl
      have hrd : X.get (0, k - 1) = some (rdE L.sharedBase bs) := by
        rw [show k - 1 = 4 + n + 1 + 0 by omega, hr 0 (by simp)]
        rfl
      refine .inr (.inr (.inr (.inr (.inr ⟨rfl, by omega, h4,
        .inr ⟨4 + n, by omega, by omega, hw, ?_⟩⟩))))
      rcases hev with ⟨hb, rfl⟩ | ⟨hb, f, rfl⟩
      · exact .inr (.inl ⟨bs, v, hrd, hv, hb, rfl⟩)
      · refine .inr (.inr (.inr ⟨_, f, rfl, bs, hrd, fun v' hv' => ?_⟩))
        rw [hv] at hv'
        cases hv'
        exact hb
    | exit =>
      rcases hJ with ⟨hg0, -⟩ | ⟨h0, n, bs, v, hp, -, -⟩
      · exact .inl ⟨hg0, hev⟩
      · have hp' : (X.tr g).take k = issue A L.sharedBase ++
            List.replicate n (waitE L.sharedBase false) ++
              waitE L.sharedBase true :: [rdE L.sharedBase bs, wrE B v] := by simp [hp]
        obtain ⟨hkl, h4, hw, -⟩ := tail n _ hp' h0
        subst h0
        simp only [List.length_cons, List.length_nil] at hkl
        exact .inr (.inr (.inr (.inr (.inr ⟨rfl, by omega, h4,
          .inr ⟨4 + n, by omega, by omega, hw, .inr (.inr (.inl hev))⟩⟩))))
  · obtain ⟨pc, f, bs, rfl, hk0, hrd, hbad⟩ := ht.dead hg h hσ
    obtain ⟨h0, n, hk1, hp⟩ := read_at ht hX hrd
    have hp' : (X.tr g).take (k - 1) = issue A L.sharedBase ++
        List.replicate n (waitE L.sharedBase false) ++ waitE L.sharedBase true :: [] := by
      simp [hp]
    have hk' : k - 1 < (X.tr g).length := by omega
    subst h0
    obtain ⟨hkl, hat⟩ := take_eq hk' hp'
    have hlen : (issue A L.sharedBase ++ List.replicate n (waitE L.sharedBase false) ++
        [waitE L.sharedBase true]).length = 4 + n + 1 := by simp [issue]; omega
    have h4 : ∀ j < 4, X.get (0, j) = (issue A L.sharedBase)[j]? := fun j hj => by
      rw [hat j (by simp [issue]; omega), List.append_assoc, issue_get hj]
    have hw : X.get (0, 4 + n) = some (waitE L.sharedBase true) := by
      rw [hat _ (by simp [issue]; omega)]
      have := idx_after (A := A) (S := L.sharedBase) (waitE L.sharedBase false)
        [waitE L.sharedBase true] n 0
      simpa using this
    exact .inr (.inr (.inr (.inr (.inr ⟨rfl, by omega, h4,
      .inr ⟨4 + n, by omega, by omega, hw,
        .inr (.inr (.inr ⟨pc, f, rfl, bs, hrd, hbad⟩))⟩⟩))))

/-- Every event is of the mbarrier/bulk class. -/
theorem mbarBulk : X.MbarBulk := by
  intro e pc kind hp
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (cases he; rfl)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩
  all_goals cases he; rfl

/-- No event is of a kind outside the mbarrier/bulk class. -/
theorem not_class {v : EvId} {pc : Nat} {k : Kind} (hp : X.get v = some ⟨pc, k⟩)
    (hk : k.isMbarBulk = false) : False := by
  rw [mbarBulk ht hX v pc k hp] at hk
  cases hk

/-- No cancellation request is issued. -/
theorem no_clc {i : EvId} {s : Clc.Spec} {ts : List Nat} : ¬ X.ClcIssue i s ts :=
  fun ⟨_, hi⟩ => not_class ht hX hi rfl

theorem reads_cases {e : EvId} {a : Acc} {bs : List (Option Byte)} (h : X.Reads e a bs) :
    e.1 = 0 ∧ a = { loc := buf L.sharedBase, size := 4 } ∧
      ∃ i, 4 ≤ i ∧ i < e.2 ∧ X.get (0, i) = some (waitE L.sharedBase true) ∧
        ∀ k < 4, X.get (0, k) = (issue A L.sharedBase)[k]? := by
  obtain ⟨pc, hp⟩ := h
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨h0, -, hp4, ⟨ok, he⟩ | ⟨i, hi, hie, hw, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩
  · simp only [rdE, Event.mk.injEq, Kind.rd.injEq] at he
    exact ⟨h0, he.2.1, i, hi, hie, hw, hp4⟩
  all_goals simp [wrE, exE] at he

theorem writes_cases {w : EvId} {a : Acc} {bs : List Byte} (h : X.Writes w a bs) :
    w.1 = 0 ∧ a = { loc := gB B, size := 4 } ∧
      ∃ bs0 v, X.get (0, w.2 - 1) = some (rdE L.sharedBase bs0) ∧
      rebuild 3 bs0 = .ok v ∧ v.bytes = 4 ∧ bs = v.toBytes := by
  obtain ⟨pc, hp⟩ := h
  rcases (event_cases ht hX hp).2 with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩ |
    ⟨_, _, he⟩ | ⟨h0, _, _, ⟨ok, he⟩ | ⟨i, _, _, _, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨bs0, v, h0', hv, hb, he⟩ | he | ⟨_, _, he, _⟩
  · simp [rdE] at he
  · simp only [wrE, Event.mk.injEq, Kind.wr.injEq] at he
    exact ⟨h0, he.2.1, bs0, v, h0', hv, hb, he.2.2⟩
  all_goals simp [exE] at he

theorem no_nc {e : EvId} {a : Acc} {bs : List (Option Byte)} : ¬ X.NcReads e a bs := by
  rintro ⟨pc, hp⟩
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

theorem no_barrier {e : EvId} {id : Nat} {count : Option Nat} {pc : Nat} :
    ¬ X.IsBarrier e id count pc := by
  intro hp
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

theorem no_bar {e : EvId} {k : Nat} : ¬ X.BarK e k := by
  rintro ⟨⟨id,pc,hp⟩,_⟩
  exact no_barrier ht hX hp

/-- The kernel issues no `cp.async.bulk.prefetch`. -/
theorem no_bulkPrefetch {e : EvId} {a : Acc} : ¬ X.BulkPrefetch e a := by
  rintro ⟨pc, hp⟩
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

/-- No event is an atomic read-modify-write. -/
theorem no_rmw {e : EvId} {pc : Nat} {a : Acc} {o : List (Option Byte)}
    {n : Option (List Byte)} : X.get e ≠ some ⟨pc, .rmw a o n⟩ := by
  intro hp
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

/-- An access is a read or a write: no event is an atomic read-modify-write. -/
theorem access_cases {i : EvId} {a : Acc} {w : Bool} (hi : X.Access i a w) :
    (∃ bs, X.Reads i a bs ∧ w = false) ∨ (∃ bs, X.Writes i a bs ∧ w = true) :=
  (Execution.access_iff_of_not_rmw fun _ _ _ _ => no_rmw ht hX).mp hi

/-- No event is a `tcgen05` instruction. -/
theorem noTc : X.NoTc := (mbarBulk ht hX).noTc

theorem acquireWait_cases {w : EvId} {m : Loc} (h : X.AcquireWait w m) :
    w.1 = 0 ∧ 4 ≤ w.2 ∧ m = mbar L.sharedBase := by
  obtain ⟨pc, parity, scope, hp⟩ := h
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨h0, h4, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE] at he)
  · simp only [waitE, Event.mk.injEq, Kind.wait.injEq] at he
    exact ⟨h0, h4, he.2.1⟩
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

/-- The only linear copy is thread 0's bulk copy, event 3. -/
theorem bulk_cases {b : EvId} {s : AsyncCopy.Spec} (h : X.Copy b s) :
    b = (0, 3) ∧ s = copySpec A L.sharedBase := by
  obtain ⟨pc, hp⟩ := h
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨h0, h3, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, waitE] at he)
  · simp only [bulkE, Event.mk.injEq, Kind.copy.injEq] at he
    exact ⟨Prod.ext h0 h3, he.2⟩
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

omit ht hX in
theorem threads_pos (hpre : Pre L A B x mem0) : 0 < L.threads := by
  have := hpre.block.1; have := hpre.grid; unfold Launch.threads; rw [this]; omega


end

section
variable (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)
include ht hX

theorem mbInit_cases {e : EvId} {m : Loc} {c : Nat} (h : X.MbInit e m c) :
    e = (0, 0) ∧ m = mbar L.sharedBase ∧ c = 1 := by
  obtain ⟨pc, hp⟩ := h
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨h0, h1, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, fenceE, arriveE, bulkE, waitE] at he)
  · simp only [initE, Event.mk.injEq, Kind.mbInit.injEq] at he
    exact ⟨Prod.ext h0 h1, he.2.1, he.2.2⟩
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

/-- The kernel invalidates no mbarrier. -/
theorem no_inval {e : EvId} {m : Loc} : ¬ X.MbInval e m := by
  rintro ⟨pc, hp⟩
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

/-- Every poll is at the kernel's one `mbarrier.try_wait`. -/
theorem wait_pc {e : EvId} {pc : Nat} {m : Loc} {q : Nat} {ok acq : Bool} {sc : MbarScope}
    (hp : X.get e = some ⟨pc, .wait m q ok acq sc⟩) : pc = Flow.mbarWait_0 := by
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok', he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE] at he)
  · exact (Event.mk.inj he).1
  · rcases hc with ⟨_, he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

/-- The kernel has no thread fence (its one fence is a proxy fence). -/
theorem no_threadFence {e : EvId} {sem : FenceSem} {sc : MbarScope} : ¬ X.ThreadFence e sem sc := by
  rintro ⟨pc, hp⟩
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

/-- The kernel issues no `cp.async.mbarrier.arrive`. -/
theorem no_asyncArrive {e : EvId} {m : Loc} {noinc : Bool} : ¬ X.AsyncArrive e m noinc := by
  rintro ⟨pc, hp⟩
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

theorem arrive_cases {e : EvId} {m : Loc} {tx count : Nat} {release : Bool} {scope : MbarScope}
    (h : X.Arrive e m tx count release scope) :
    e = (0, 2) ∧ m = mbar L.sharedBase ∧ tx = 16 ∧ count = 1 := by
  obtain ⟨pc, hp⟩ := h
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨h0, h2, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, bulkE, waitE] at he)
  · simp only [arriveE, Event.mk.injEq, Kind.arrive.injEq] at he
    exact ⟨Prod.ext h0 h2, he.2.1, he.2.2.1, he.2.2.2.1⟩
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

theorem wait_cases {e : EvId} {pc : Nat} {m : Loc} {q : Nat} {ok acquire : Bool}
    {scope : MbarScope} (hp : X.get e = some ⟨pc, .wait m q ok acquire scope⟩) :
    e.1 = 0 ∧ 4 ≤ e.2 ∧ m = mbar L.sharedBase ∧ q = 0 ∧ acquire = true ∧ scope = .cta := by
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨h0, h4, -, ⟨ok', he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE] at he)
  · simp only [waitE, Event.mk.injEq, Kind.wait.injEq] at he
    exact ⟨h0, h4, he.2.1, he.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;> simp [rdE, wrE, exE] at he

/-- Every mbarrier operand is `mbar`. -/
theorem uses_cases {e : EvId} {m : Loc} (hu : X.UsesMbar e m) : m = mbar L.sharedBase := by
  rcases hu with ⟨tx, count, release, scope, ha⟩ | ⟨s, hb, hm⟩ | ⟨noinc, ha⟩ | ⟨_, _, hc, _⟩ |
    ⟨pc, q, ok, acquire, scope, hp⟩ | hv | ⟨_, _, ⟨pc, hi⟩, _⟩ | ⟨_, _, _, ⟨pc, hi⟩, _⟩ | ⟨c, hi⟩
  · exact (arrive_cases ht hX ha).2.1
  · obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
    simpa [copySpec, bulkSpec] using hm.symm
  · exact (no_asyncArrive ht hX ha).elim
  · exact ((noTc ht hX).not_commit hc).elim
  · exact (wait_cases ht hX hp).2.2.1
  · exact (no_inval ht hX hv).elim
  · exact (not_class ht hX hi rfl).elim
  · exact (not_class ht hX hi rfl).elim
  · exact (mbInit_cases ht hX hi).2.1

omit ht hX in
/-- An event of thread 0 has every earlier position of thread 0 filled. -/
theorem pre_of {j k : Nat} {ev : Event} (h : X.get (0, j) = some ev) (hk : k ≤ j) :
    ∃ ev', X.get (0, k) = some ev' := by
  have hj := len_of_get h
  simp only at hj
  exact ⟨(X.tr 0)[k], show (X.tr 0)[k]? = _ from List.getElem?_eq_getElem (by omega)⟩

theorem init_get {j : Nat} {ev : Event} (h : X.get (0, j) = some ev) :
    X.get (0, 0) = some (initE L.sharedBase) := by
  obtain ⟨ev', h0⟩ := pre_of h (Nat.zero_le _)
  rcases (event_cases ht hX h0).2 with ⟨hne, -⟩ | ⟨-, -, he⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ |
    ⟨-, h1, -⟩ | ⟨-, h1, -⟩
  all_goals simp_all


end

end

end PTX.Kernels.TmaCopy.Proof
