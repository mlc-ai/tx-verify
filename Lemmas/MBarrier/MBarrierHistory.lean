-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.MBarrierHistory
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Nodup

@[expose] public section

namespace PTX.MBarrier

/-- Extract the checked transition at any position of an object history. -/
theorem RecordedHistory.at {initial last : Option State} {log : List (Record ι)}
    (h : RecordedHistory initial log last) {i : Nat} {r : Record ι}
    (hi : log[i]? = some r) :
    RecordOk (if i = 0 then initial else log[i - 1]?.bind (fun q => q.reply.state)) r := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons initial q rest last hq ht ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst r; exact hq
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have hh := ih hi
      cases i <;> simpa using hh

/-- `stateBefore` is the actual checked object state, not a guessed phase value. -/
theorem CheckedLog.at {log : List (Record ι)} (h : CheckedLog log) {i : Nat} {r : Record ι}
    (hi : log[i]? = some r) : RecordOk (stateBefore log i) r := by
  obtain ⟨last, hh⟩ := h.2
  exact hh.at hi

/-- The terminal object state is the response of its actual last operation. -/
theorem RecordedHistory.last {initial final : Option State} {log : List (Record ι)}
    (h : RecordedHistory initial log final) {r : Record ι}
    (hr : log.getLast? = some r) : final = r.reply.state := by
  induction h with
  | nil => simp at hr
  | @cons initial q rest final hq ht ih =>
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hr
      subst r
      cases ht
      rfl
    | cons q' rest =>
      exact ih (by simpa only [List.getLast?_cons_cons] using hr)

theorem RecordedHistory.append {initial middle last : Option State}
    {xs ys : List (Record ι)} (hx : RecordedHistory initial xs middle)
    (hy : RecordedHistory middle ys last) : RecordedHistory initial (xs ++ ys) last := by
  induction hx with
  | nil => exact hy
  | cons hstep _ ih => exact .cons hstep (ih hy)

/-- Appending a fresh operation preserves checked history; its response is still
required to be the actual result (or actual fault) of the object transition. -/
theorem CheckedLog.snoc {log : List (Record ι)} {last : Option State} {r : Record ι}
    (hh : RecordedHistory none log last) (hn : (log.map Record.id).Nodup)
    (hfresh : r.id ∉ log.map Record.id) (hr : RecordOk last r) : CheckedLog (log ++ [r]) := by
  refine ⟨?_, r.reply.state, hh.append (.cons hr (.nil _))⟩
  simp only [List.map_append, List.nodup_append, hn, List.map_cons, List.map_nil,
    List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, true_and]
  intro a ha b hb h
  simp only [List.mem_singleton] at hb
  subst hb
  exact hfresh (h ▸ ha)

/-- Build replies from object rules; on failure report the actual operation identity. -/
def replay (initial : Option State) : List (ι × Action) → Except (ι × Error) (List (Record ι))
  | [] => .ok []
  | (id, action) :: rest =>
    match perform initial action with
    | .error e => .error (id, e)
    | .ok r => match replay r.state rest with
      | .error e => .error e
      | .ok tail => .ok (⟨id, action, r, none⟩ :: tail)

/-- A replay preserves operation identities; it does not invent or omit a notification. -/
theorem replay_ids {initial : Option State} {ops : List (ι × Action)}
    {log : List (Record ι)} (h : replay initial ops = .ok log) :
    log.map Record.id = ops.map Prod.fst := by
  induction ops generalizing initial log with
  | nil => cases h; rfl
  | cons op rest ih =>
    obtain ⟨id, action⟩ := op
    cases hp : perform initial action with
    | error e => simp [replay, hp] at h
    | ok r =>
      cases ht : replay r.state rest with
      | error e => simp [replay, hp, ht] at h
      | ok tail =>
        have heq : log = ⟨id, action, r, none⟩ :: tail := by
          simpa [replay, hp, ht, Except.mapError, Except.bind] using h.symm
        subst log
        simp only [List.map_cons, ih ht]

/-- A successful replay also inhabits the fault-aware execution relation. -/
theorem replay_recorded {initial : Option State} {ops : List (ι × Action)}
    {log : List (Record ι)} (h : replay initial ops = .ok log) :
    ∃ last, RecordedHistory initial log last := by
  induction ops generalizing initial log with
  | nil => cases h; exact ⟨initial, .nil initial⟩
  | cons op rest ih =>
    obtain ⟨id, action⟩ := op
    cases hp : perform initial action with
    | error e => simp [replay, hp] at h
    | ok r =>
      cases ht : replay r.state rest with
      | error e => simp [replay, hp, ht] at h
      | ok tail =>
        have heq : log = ⟨id, action, r, none⟩ :: tail := by
          simpa [replay, hp, ht, Except.mapError, Except.bind] using h.symm
        subst log
        obtain ⟨last, htail⟩ := ih ht
        exact ⟨last, .cons (by simp [RecordOk, hp]) htail⟩

theorem checkedLog_of_replay {ops : List (ι × Action)} {log : List (Record ι)}
    (h : replay none ops = .ok log) (hid : (ops.map Prod.fst).Nodup) : CheckedLog log :=
  ⟨by rwa [replay_ids h], replay_recorded h⟩

/-- No record of the history invalidates the object: one lifetime at most. -/
abbrev NoInval (log : List (Record ι)) : Prop := ∀ r ∈ log, r.action ≠ .inval

theorem NoInval.sameLifetime {log : List (Record ι)} (h : NoInval log) (i j : Nat) :
    SameLifetime log i j :=
  fun _ _ _ _ hk => h _ (List.mem_of_getElem? hk)

/-- Adjacent positions are in one lifetime. -/
theorem SameLifetime.succ (log : List (Record ι)) (i : Nat) : SameLifetime log i (i + 1) :=
  fun _ _ _ h2 _ => absurd h2 (by omega)

theorem SameLifetime.append {log extra : List (Record ι)} {i j : Nat} (hj : j ≤ log.length) :
    SameLifetime (log ++ extra) i j ↔ SameLifetime log i j := by
  constructor
  · intro h k s hik hkj hk
    exact h k s hik hkj (by rwa [List.getElem?_append_left (by omega)])
  · intro h k s hik hkj hk
    exact h k s hik hkj (by rwa [List.getElem?_append_left (by omega)] at hk)

theorem stateBefore_append (log extra : List (Record ι)) {i : Nat}
    (hi : i ≤ log.length) : stateBefore (log ++ extra) i = stateBefore log i := by
  unfold stateBefore
  split_ifs with hz
  · rfl
  · rw [List.getElem?_append_left (by omega : i - 1 < log.length)]

theorem phaseAt_append (log extra : List (Record ι)) {i : Nat} (hi : i ≤ log.length) :
    phaseAt (log ++ extra) i = phaseAt log i := by
  simp only [phaseAt, stateBefore_append log extra hi]

theorem observedAt_append (log extra : List (Record ι)) {i : Nat} (hi : i < log.length) :
    observedAt (log ++ extra) i = observedAt log i := by
  simp only [observedAt, List.getElem?_append_left hi]

/-- Appending operations preserves a previously established arrival/wait relation. -/
theorem UpdateBeforeWait.extends {before after : List (Record ι)}
    (hext : List.IsPrefix before after) {u w : ι}
    (h : UpdateBeforeWait before u w) : UpdateBeforeWait after u w := by
  obtain ⟨extra, rfl⟩ := hext
  obtain ⟨i, j, r, s, p, hi, hu, hf, hj, hw, hsf, hs, hij, hp, hq, hl⟩ := h
  have hil := (List.getElem?_eq_some_iff.mp hi).1
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  exact ⟨i, j, r, s, p, by rwa [List.getElem?_append_left hil], hu, hf,
    by rwa [List.getElem?_append_left hjl], hw, hsf, hs, hij,
    by rwa [phaseAt_append before extra
      (Nat.le_of_lt hil)], by rwa [observedAt_append before extra hjl],
    (SameLifetime.append (Nat.le_of_lt hjl)).2 hl⟩

/-- An appended operation cannot become part of an earlier wait's observation. -/
theorem UpdateBeforeWait.snoc_iff {log : List (Record ι)} {r : Record ι}
    {u w : ι} (hnw : r.id ≠ w) :
    UpdateBeforeWait (log ++ [r]) u w ↔ UpdateBeforeWait log u w := by
  constructor
  · rintro ⟨i, j, q, s, p, hi, hu, hf, hj, hw, hsf, hs, hij, hp, hq, hl⟩
    have hjold : j < log.length := by
      by_contra h
      rw [List.getElem?_append_right (by omega)] at hj
      have hidx : j - log.length = 0 := by
        have hh := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_singleton] at hh
        omega
      rw [hidx] at hj
      cases hj
      exact hnw hw
    have hiold : i < log.length := by omega
    exact ⟨i, j, q, s, p, by rwa [List.getElem?_append_left hiold] at hi, hu, hf,
      by rwa [List.getElem?_append_left hjold] at hj, hw, hsf, hs, hij,
      by rwa [phaseAt_append log [r] (Nat.le_of_lt hiold)] at hp,
      by rwa [observedAt_append log [r] hjold] at hq, (SameLifetime.append
        (Nat.le_of_lt hjold)).1 hl⟩
  · exact fun h => h.extends ⟨[r], rfl⟩

/-- Appending a different operation cannot add predecessors to an existing endpoint. -/
theorem Before.snoc_iff {log : List (Record ι)} {r : Record ι} {u w : ι}
    (hnw : r.id ≠ w) : Before (log ++ [r]) u w ↔ Before log u w := by
  constructor
  · rintro ⟨i, j, q, s, hi, hu, hj, hw, hij⟩
    have hjold : j < log.length := by
      by_contra h
      rw [List.getElem?_append_right (by omega)] at hj
      have hidx : j - log.length = 0 := by
        have hh := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_singleton] at hh
        omega
      rw [hidx] at hj
      cases hj
      exact hnw hw
    have hiold : i < log.length := by omega
    exact ⟨i, j, q, s, by rwa [List.getElem?_append_left hiold] at hi, hu,
      by rwa [List.getElem?_append_left hjold] at hj, hw, hij⟩
  · rintro ⟨i, j, q, s, hi, hu, hj, hw, hij⟩
    have hiold := (List.getElem?_eq_some_iff.mp hi).1
    have hjold := (List.getElem?_eq_some_iff.mp hj).1
    exact ⟨i, j, q, s, by rwa [List.getElem?_append_left hiold], hu,
      by rwa [List.getElem?_append_left hjold], hw, hij⟩

end PTX.MBarrier
