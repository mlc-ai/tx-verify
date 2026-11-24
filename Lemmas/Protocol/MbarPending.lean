-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierHistory
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! # An mbarrier without outstanding transactions has a pending arrival

A proof tool. A phase completes in the same step as its last arrival or transaction
completion (`advance`), which reloads the pending arrivals with the expected count. So every
state of a checked history whose transaction count is zero still expects an arrival
(`stateBefore_pending_pos`). -/

namespace PTX.MBarrier

/-- The state expects arrivals, and has a pending one unless transactions are outstanding. -/
def PendingOk (s : State) : Prop := 0 < s.expected ∧ (s.tx = 0 → 0 < s.pending)

theorem advance_pendingOk {s : State} (he : 0 < s.expected) : PendingOk (advance s) := by
  unfold advance
  split_ifs with h
  · exact ⟨he, fun _ => he⟩
  · refine ⟨he, fun ht => ?_⟩
    by_contra hp
    exact h ⟨by omega, ht⟩

theorem perform_pendingOk {before : Option State} {a : Action} {r : Reply}
    (hb : ∀ s, before = some s → PendingOk s) (h : perform before a = .ok r) :
    ∀ s, r.state = some s → PendingOk s := by
  intro s hs
  cases a with
  | init n =>
    unfold perform at h
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h
         simp only [Option.some.injEq] at hs
         subst hs
         simp_all [PendingOk])
  | completeTx n =>
    cases before with
    | none => cases h
    | some s0 =>
      have he := (hb s0 rfl).1
      unfold perform at h
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | (cases h
           simp only [Option.some.injEq] at hs
           subst hs
           exact advance_pendingOk he)
  | arrive n tx =>
    cases before with
    | none => cases h
    | some s0 =>
      have he := (hb s0 rfl).1
      unfold perform at h
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | (cases h
           simp only [Option.some.injEq] at hs
           subst hs
           exact advance_pendingOk he)
  | increment =>
    cases before with
    | none => cases h
    | some s0 =>
      have he := (hb s0 rfl).1
      unfold perform at h
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | (cases h
           simp only [Option.some.injEq] at hs
           subst hs
           exact ⟨he, fun _ => Nat.succ_pos _⟩)
  | inval =>
    cases before with
    | none => cases h
    | some s0 =>
      unfold perform at h
      cases h
      cases hs
  | pollParity p success =>
    cases before with
    | none => cases h
    | some s0 =>
      have h0 := hb s0 rfl
      unfold perform at h
      cases h
      simp only [Option.some.injEq] at hs
      subst hs
      exact h0

theorem recordOk_pendingOk {ι : Type} {before : Option State} {r : Record ι}
    (hb : ∀ s, before = some s → PendingOk s) (h : RecordOk before r) :
    ∀ s, r.reply.state = some s → PendingOk s := by
  unfold RecordOk at h
  split at h
  · rename_i hp
    rw [h.1]
    exact perform_pendingOk hb hp
  · rw [h.1]
    exact hb

theorem recordedHistory_pendingOk {ι : Type} {s : Option State} {log : List (Record ι)}
    {t : Option State} (h : RecordedHistory s log t) (hs : ∀ x, s = some x → PendingOk x) :
    ∀ r ∈ log, ∀ x, r.reply.state = some x → PendingOk x := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hm
    · exact recordOk_pendingOk hs hr
    · exact ih (recordOk_pendingOk hs hr) r' hm

/-- In a checked history, a state with no outstanding transactions has a pending arrival. -/
theorem stateBefore_pending_pos {ι : Type} {log : List (Record ι)} (h : CheckedLog log)
    {i : Nat} {s : State} (hs : stateBefore log i = some s) (ht : s.tx = 0) : 0 < s.pending := by
  obtain ⟨-, last, hrec⟩ := h
  unfold stateBefore at hs
  split_ifs at hs
  obtain ⟨r, hr, hrs⟩ := Option.bind_eq_some_iff.mp hs
  exact (recordedHistory_pendingOk hrec (by simp) r (List.mem_of_getElem? hr) s hrs).2 ht

theorem perform_some {s : State} {a : Action} {r : Reply} (h : perform (some s) a = .ok r)
    (ha : a ≠ .inval) : r.state.isSome := by
  cases a with
  | inval => exact absurd rfl ha
  | init n =>
    unfold perform at h
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first | (cases h; done) | (cases h; rfl)
  | completeTx n =>
    unfold perform at h
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first | (cases h; done) | (cases h; rfl)
  | arrive n tx =>
    unfold perform at h
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first | (cases h; done) | (cases h; rfl)
  | increment =>
    unfold perform at h
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first | (cases h; done) | (cases h; rfl)
  | pollParity p success =>
    unfold perform at h
    cases h
    rfl

theorem recordOk_some {ι : Type} {s : State} {r : Record ι} (h : RecordOk (some s) r)
    (ha : r.action ≠ .inval) : r.reply.state.isSome := by
  unfold RecordOk at h
  split at h
  · rename_i hp
    rw [h.1]
    exact perform_some hp ha
  · rw [h.1]
    rfl

theorem recordedHistory_some {ι : Type} {s : Option State} {log : List (Record ι)}
    {t : Option State} (h : RecordedHistory s log t) (hni : NoInval log) (hs : s.isSome) :
    t.isSome := by
  induction h with
  | nil => exact hs
  | @cons s0 r rest t0 hr _ ih =>
    obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hs
    exact ih (fun q hq => hni q (List.mem_cons_of_mem _ hq))
      (recordOk_some hr (hni r List.mem_cons_self))

theorem recordOk_init {ι : Type} {before : Option State} {r : Record ι} {n : Nat}
    (h : RecordOk before r) (ha : r.action = .init n) (hn : validCount n) :
    r.reply.state.isSome := by
  cases before with
  | some s => exact recordOk_some h (by rw [ha]; exact nofun)
  | none =>
    unfold RecordOk at h
    rw [ha] at h
    unfold perform at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i hp
      repeat' split at hp
      all_goals first
        | (cases hp; done)
        | (cases hp; rw [h.1]; rfl)
    · rename_i hp
      exfalso
      repeat' split at hp
      all_goals first | (cases hp; done) | simp_all

theorem recordedHistory_split {ι : Type} {pre rest : List (Record ι)} :
    ∀ {s0 t : Option State}, RecordedHistory s0 (pre ++ rest) t →
      ∃ u, RecordedHistory u rest t := by
  induction pre with
  | nil => exact fun hh => ⟨_, hh⟩
  | cons x xs ih =>
    intro s0 t hh
    cases hh with
    | cons _ hrest => exact ih hrest

/-- A checked history with a valid initialization ends in a state. -/
theorem stateBefore_length_some {ι : Type} {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    {r : Record ι} (hr : r ∈ log) {n : Nat} (ha : r.action = .init n) (hn : validCount n) :
    ∃ s, stateBefore log log.length = some s := by
  obtain ⟨-, last, hrec⟩ := h
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hr
  clear hr
  -- split the history at the initialization
  have key : ∀ {s0 : Option State} {xs : List (Record ι)} {t : Option State},
      RecordedHistory s0 xs t → xs ≠ [] → (xs.getLast?.bind fun q => q.reply.state) = t := by
    intro s0 xs t hh hne
    induction hh with
    | nil => exact absurd rfl hne
    | cons hr' hrest ih =>
      rename_i s1 q rest t1
      cases rest with
      | nil => cases hrest; simp
      | cons y ys =>
        rw [List.getLast?_cons_cons]
        exact ih (by simp)
  obtain ⟨u, hu⟩ := recordedHistory_split hrec
  have hsome : last.isSome := by
    cases hu with
    | cons hr0 hrest =>
      exact recordedHistory_some hrest (fun q hq => hni q (by simp [hq]))
        (recordOk_init hr0 ha hn)
  have hk := key hrec (by simp)
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨s, ?_⟩
  have hlen : (pre ++ r :: post).length ≠ 0 := by simp
  unfold stateBefore
  rw [List.getLast?_eq_getElem?] at hk
  simp only [hlen, ↓reduceIte, hk, hs]

end PTX.MBarrier
