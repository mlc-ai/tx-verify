-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Rank

@[expose] public section

/-! # Collective schedules

A collective (the events `p` selects: warp collectives, warp-collective `tcgen05` events, the
events on one named barrier, paired Tensor Memory operations, ...) is scheduled for a group of
threads `Grp` by a function `S` of the group's key and the ordinal (`CollSched`): a state whose
event is the thread's `n`-th collective has time `S key n` in the time table `M`, a state whose
event is not a collective is earlier than the thread's next collective, a state at the trace's end
is no later than it, and `S` increases with the ordinal.

* From a schedule, a thread that has made at most `n` collectives is no later than the time of
  the `n`-th (`threadTime_le_sched`), its machine stopped or not; so it is no later than a thread
  of its key at its `n`-th collective (`lag_of_sched`). This is the blocker's time a wait at a
  collective needs: the waiter is at its `n`-th, the blocker has not made it.
* A schedule follows from three facts of the threads' states (`collSched_of`): the collectives
  before a state are a function of the state, the event fired from a state is a collective exactly
  when the state's site is one, and the site times against `S`.
* Schedules of the parts of a group cut by a predicate of the key make one of the group
  (`collSched_union`), and a schedule of a group is one of each smaller group
  (`CollSched.mono_grp`). -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **A collective schedule** of the events `p` selects, for the threads `Grp` with key `key`. -/
structure CollSched (M : Timed K A L) (X : Execution) {κ : Type} (p : Event → Bool) (key : Nat → κ)
    (Grp : Nat → Prop) (S : κ → Nat → Nat) : Prop where
  /-- A state whose event is the thread's `n`-th collective has time `S key n`. -/
  atEv : ∀ {g k : Nat} {d : (M.code g).D} {e : Event}, g < L.threads → Grp g →
    Frame.stateAt M.code X g k = some (some d) → X.get (g, k) = some e → p e = true →
    M.time g d = S (key g) (((X.tr g).take k).countP p)
  /-- A state whose event is not a collective is earlier than the thread's next collective. -/
  nonEv : ∀ {g k : Nat} {d : (M.code g).D} {e : Event}, g < L.threads → Grp g →
    Frame.stateAt M.code X g k = some (some d) → X.get (g, k) = some e → p e = false →
    M.time g d < S (key g) (((X.tr g).take k).countP p)
  /-- A state at the trace's end is no later than the thread's next collective. -/
  endLe : ∀ {g : Nat} {d : (M.code g).D}, g < L.threads → Grp g →
    Frame.stateAt M.code X g (X.tr g).length = some (some d) →
    M.time g d ≤ S (key g) ((X.tr g).countP p)
  /-- The schedule increases with the ordinal. -/
  mono : ∀ c n, S c n < S c (n + 1)

theorem sched_le {κ : Type} {S : κ → Nat → Nat} (hm : ∀ c n, S c n < S c (n + 1)) (c : κ)
    {n m : Nat} (h : n ≤ m) : S c n ≤ S c m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with h' | h'
    · exact (ih (by omega)).trans (hm c m).le
    · rw [show n = m + 1 by omega]

theorem sched_lt {κ : Type} {S : κ → Nat → Nat} (hm : ∀ c n, S c n < S c (n + 1)) (c : κ)
    {n m : Nat} (h : n < m) : S c n < S c m :=
  (hm c n).trans_le (sched_le hm c h)

/-- A thread's trace is nonempty when its machine has stopped at its end. -/
theorem len_pos_of_stop {C : (g : Nat) → Flow.Code K A L g} {g : Nat}
    (hσ : Frame.stateAt C X g (X.tr g).length = none) : 0 < (X.tr g).length := by
  by_contra h0
  have hl : (X.tr g).length = 0 := by omega
  have h1 : Frame.stateAt C X g (X.tr g).length = some (some (C g).init) := by
    rw [hl]; exact Frame.stateAt_zero
  rw [h1] at hσ
  cases hσ

/-- The trace split at its last event. -/
theorem split_last {g : Nat} (hlen : 0 < (X.tr g).length) :
    X.tr g = (X.tr g).take ((X.tr g).length - 1) ++ [(X.tr g)[(X.tr g).length - 1]] := by
  have h := List.take_succ_eq_append_getElem (l := X.tr g) (i := (X.tr g).length - 1)
    (by omega)
  rwa [Nat.sub_add_cancel hlen, List.take_length] at h

/-- **A thread that has made `c` collectives is no later than the `c`-th.** -/
theorem threadTime_le_sched {κ : Type} {p : Event → Bool} {key : Nat → κ} {Grp : Nat → Prop}
    {S : κ → Nat → Nat} (hs : CollSched M X p key Grp S) {h : Nat} (hh : h < L.threads)
    (hg : Grp h) : threadTime M X h ≤ S (key h) ((X.tr h).countP p) := by
  unfold threadTime
  split
  · rename_i d hσ
    exact hs.endLe hh hg hσ
  · exact Nat.zero_le _
  · rename_i hσ
    split
    · rename_i d hσ'
      have hlen := len_pos_of_stop hσ
      have hj : (X.tr h).length - 1 < (X.tr h).length := by omega
      have he : X.get (h, (X.tr h).length - 1) = some (X.tr h)[(X.tr h).length - 1] :=
        List.getElem?_eq_getElem hj
      have hsp := split_last (X := X) (g := h) hlen
      cases hp : p (X.tr h)[(X.tr h).length - 1]
      · have h1 := hs.nonEv hh hg hσ' he hp
        have h2 := congrArg (List.countP p) hsp
        rw [List.countP_append] at h2
        simp only [List.countP_singleton, hp] at h2
        simp at h2
        rw [h2]
        omega
      · have h1 := hs.atEv hh hg hσ' he hp
        have h2 := congrArg (List.countP p) hsp
        rw [List.countP_append] at h2
        simp only [List.countP_singleton, hp] at h2
        simp at h2
        rw [h2, h1]
        exact hs.mono _ _
    · exact Nat.zero_le _

/-- **The lag of a thread at a collective**: a thread of its group with the same key that has
made at most as many collectives is no later. -/
theorem lag_of_sched {κ : Type} {p : Event → Bool} {key : Nat → κ} {Grp : Nat → Prop}
    {S : κ → Nat → Nat} (hs : CollSched M X p key Grp S) {g h j : Nat} {d : (M.code g).D}
    {e : Event}
    (hg : g < L.threads) (hh : h < L.threads) (hG : Grp g) (hH : Grp h) (hk : key h = key g)
    (hσ : Frame.stateAt M.code X g j = some (some d)) (he : X.get (g, j) = some e) (hp : p e = true)
    (hc : (X.tr h).countP p ≤ ((X.tr g).take j).countP p) :
    threadTime M X h ≤ M.time g d := by
  rw [hs.atEv hg hG hσ he hp, ← hk]
  exact (threadTime_le_sched hs hh hH).trans (sched_le hs.mono _ hc)

/-- **A collective schedule from the counts and the site tables.** -/
theorem collSched_of {κ : Type} {p : Event → Bool} {key : Nat → κ} {Grp : Nat → Prop}
    {S : κ → Nat → Nat} (C : ∀ g, (M.code g).D → Nat) (isP : ∀ g, (M.code g).D → Bool)
    (hcnt : ∀ {g k : Nat} {d : (M.code g).D}, g < L.threads → Grp g → k ≤ (X.tr g).length →
      Frame.stateAt M.code X g k = some (some d) → ((X.tr g).take k).countP p = C g d)
    (hev : ∀ {g k : Nat} {d : (M.code g).D} {e : Event}, g < L.threads → Grp g →
      Frame.stateAt M.code X g k = some (some d) → X.get (g, k) = some e → p e = isP g d)
    (htime : ∀ {g k : Nat} {d : (M.code g).D}, g < L.threads → Grp g → k ≤ (X.tr g).length →
      Frame.stateAt M.code X g k = some (some d) →
        (isP g d = true → M.time g d = S (key g) (C g d)) ∧
        (isP g d = false → M.time g d < S (key g) (C g d)))
    (hmono : ∀ c n, S c n < S c (n + 1)) : CollSched M X p key Grp S where
  atEv := by
    intro g k d e hg hG hσ he hp
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    rw [hcnt hg hG hk.le hσ]
    exact (htime hg hG hk.le hσ).1 (by rw [← hev hg hG hσ he]; exact hp)
  nonEv := by
    intro g k d e hg hG hσ he hp
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    rw [hcnt hg hG hk.le hσ]
    exact (htime hg hG hk.le hσ).2 (by rw [← hev hg hG hσ he]; exact hp)
  endLe := by
    intro g d hg hG hσ
    have h := hcnt hg hG le_rfl hσ
    rw [List.take_length] at h
    rw [h]
    cases hP : isP g d
    · exact ((htime hg hG le_rfl hσ).2 hP).le
    · exact ((htime hg hG le_rfl hσ).1 hP).le
  mono := hmono

/-- **Two counts agree on a prefix** when they agree on every event fired from a followed state
before it. -/
theorem countP_take_congr {C : (g : Nat) → Flow.Code K A L g} (ht : Frame.Tracked C X)
    {p q : Event → Bool} {g k : Nat} {d : (C g).D} (hg : g < L.threads) (hσ : Frame.stateAt C X g k
        = some (some d))
    (h : ∀ {j : Nat} {d' : (C g).D} {e : Event}, j < k →
      Frame.stateAt C X g j = some (some d') → X.get (g, j) = some e → p e = q e) :
    ((X.tr g).take k).countP p = ((X.tr g).take k).countP q := by
  refine List.countP_congr fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hjk : j < k := by
    have := List.length_take_le k (X.tr g)
    rw [List.length_take] at hj
    omega
  have hjl : j < (X.tr g).length := by rw [List.length_take] at hj; omega
  obtain ⟨d', hσ'⟩ := Frame.stateAt_live (C := C) ht hg hσ hjk.le
  have he : X.get (g, j) = some ((X.tr g).take k)[j] := by
    rw [List.getElem_take]
    exact List.getElem?_eq_getElem hjl
  rw [h hjk hσ' he]

/-- **Two schedules of the parts of a group** cut by a predicate of the key make one of the
group. -/
theorem collSched_union {κ : Type} {p : Event → Bool} {key : Nat → κ} {G : Nat → Prop}
    {Q : κ → Prop} [DecidablePred Q] {S1 S2 : κ → Nat → Nat}
    (h1 : CollSched M X p key (fun g => G g ∧ Q (key g)) S1)
    (h2 : CollSched M X p key (fun g => G g ∧ ¬ Q (key g)) S2) :
    CollSched M X p key G (fun c n => if Q c then S1 c n else S2 c n) where
  atEv := by
    intro g k d e hg hG hσ he hp
    by_cases hq : Q (key g)
    · simp only [hq, ↓reduceIte]; exact h1.atEv hg ⟨hG, hq⟩ hσ he hp
    · simp only [hq, ↓reduceIte]; exact h2.atEv hg ⟨hG, hq⟩ hσ he hp
  nonEv := by
    intro g k d e hg hG hσ he hp
    by_cases hq : Q (key g)
    · simp only [hq, ↓reduceIte]; exact h1.nonEv hg ⟨hG, hq⟩ hσ he hp
    · simp only [hq, ↓reduceIte]; exact h2.nonEv hg ⟨hG, hq⟩ hσ he hp
  endLe := by
    intro g d hg hG hσ
    by_cases hq : Q (key g)
    · simp only [hq, ↓reduceIte]; exact h1.endLe hg ⟨hG, hq⟩ hσ
    · simp only [hq, ↓reduceIte]; exact h2.endLe hg ⟨hG, hq⟩ hσ
  mono := by
    intro c n
    by_cases hq : Q c
    · simp only [hq, ↓reduceIte]; exact h1.mono c n
    · simp only [hq, ↓reduceIte]; exact h2.mono c n

/-- A schedule of a group is one of each smaller group. -/
theorem CollSched.mono_grp {κ : Type}
    {p : Event → Bool} {key : Nat → κ} {G G' : Nat → Prop}
    {S : κ → Nat → Nat} (h : CollSched M X p key G S) (hG : ∀ g, G' g → G g) :
    CollSched M X p key G' S where
  atEv hg hG' := h.atEv hg (hG _ hG')
  nonEv hg hG' := h.nonEv hg (hG _ hG')
  endLe hg hG' := h.endLe hg (hG _ hG')
  mono := h.mono

end

end PTX.Sched
