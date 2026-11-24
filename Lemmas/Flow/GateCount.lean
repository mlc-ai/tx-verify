-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Polls

@[expose] public section

/-! # Acts counted against successful polls of a gate

A proof tool. A thread acts on an object (arrives, issues a request) only after it has polled a
gate object successfully. Its state says how many successful gate polls it holds unused
(`pend`), how many acts it has done ahead of its polls (`ahead`), the parity its successful
gate polls have (`par`) and whether it still polls the gate (`live`). Along its run the acts
and held polls are then bounded by its successful gate polls (`GateRel`) when every step changes
the view as the step's own act and poll do (`GateStep`); when every step moves it at least that
much, the polls are bounded by the acts and held polls (`LowRel`, `LowStep`). -/

namespace PTX.Flow

/-- A thread state's view of one gate: held polls, acts ahead, poll parity, still polling. -/
structure GateView where
  pend : Nat
  ahead : Nat
  par : Nat
  live : Bool

/-- The acts and held polls of a prefix are at most its successful gate polls plus the acts
ahead, and while the thread polls, those polls have the parity of the view. -/
def GateRel (gate : Loc) (act : Event → Bool) (v : GateView) (es : List Event) : Prop :=
  es.countP act + v.pend ≤ okPolls gate es + v.ahead ∧
    (v.live = true → okPolls gate es % 2 = v.par % 2)

/-- A step's change of the view follows its own act and successful gate poll. -/
def GateStep (gate : Loc) (act : Event → Bool) (v : GateView) (e : Event) (v' : GateView) :
    Prop :=
  v'.pend + (if act e then 1 else 0) + v.ahead ≤
      v.pend + (if okPoll gate e then 1 else 0) + v'.ahead ∧
    (v'.live = true → v.live = true ∧
      v'.par % 2 = (v.par + if okPoll gate e then 1 else 0) % 2)

theorem GateRel.step {gate : Loc} {act : Event → Bool} {v v' : GateView} {es : List Event}
    {e : Event} (h : GateRel gate act v es) (hs : GateStep gate act v e v') :
    GateRel gate act v' (es ++ [e]) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨s1, s2⟩ := hs
  unfold GateRel
  rw [List.countP_append, List.countP_singleton, okPolls_snoc]
  refine ⟨by omega, fun hl => ?_⟩
  obtain ⟨hl', hp⟩ := s2 hl
  have := h2 hl'
  omega

/-- A view with nothing held or ahead, and the parity of no polls, starts a prefix without acts
or successful gate polls. -/
theorem GateRel.start {gate : Loc} {act : Event → Bool} {v : GateView} {es : List Event}
    (ha : es.countP act = 0) (hp : okPolls gate es = 0) (h0 : v.pend = 0)
    (hpar : v.live = true → v.par % 2 = 0) : GateRel gate act v es := by
  refine ⟨by omega, fun hl => ?_⟩
  rw [hp, hpar hl]

/-- A poll in a polling state uses the parity of the earlier successful gate polls. -/
theorem GateRel.parity {gate : Loc} {act : Event → Bool} {v : GateView} {es : List Event}
    (h : GateRel gate act v es) {p : Nat} (hl : v.live = true) (hp : p % 2 = v.par % 2) :
    p % 2 = okPolls gate es % 2 := by
  rw [hp, h.2 hl]

/-- An act from a state holding a poll and with nothing ahead follows more successful gate
polls than earlier acts. -/
theorem GateRel.budget {gate : Loc} {act : Event → Bool} {v : GateView} {es : List Event}
    (h : GateRel gate act v es) (hp : v.pend = 1) (ha : v.ahead = 0) :
    es.countP act + 1 ≤ okPolls gate es := by
  have := h.1
  omega

/-- The converse bound: the successful gate polls are at most the acts plus the held polls. -/
def LowRel (gate : Loc) (act : Event → Bool) (v : GateView) (es : List Event) : Prop :=
  okPolls gate es ≤ es.countP act + v.pend

/-- A step's held polls drop by its act at most, and grow by its successful gate poll at least. -/
def LowStep (gate : Loc) (act : Event → Bool) (v : GateView) (e : Event) (v' : GateView) : Prop :=
  (if okPoll gate e then 1 else 0) + v.pend ≤ v'.pend + (if act e then 1 else 0)

theorem LowRel.step {gate : Loc} {act : Event → Bool} {v v' : GateView} {es : List Event}
    {e : Event} (h : LowRel gate act v es) (hs : LowStep gate act v e v') :
    LowRel gate act v' (es ++ [e]) := by
  unfold LowRel LowStep at *
  rw [List.countP_append, List.countP_singleton, okPolls_snoc]
  omega

theorem LowRel.start {gate : Loc} {act : Event → Bool} {v : GateView} {es : List Event}
    (hp : okPolls gate es = 0) : LowRel gate act v es := by
  unfold LowRel
  omega

/-- While `flag` holds, a marked event follows the last successful gate poll of the prefix. -/
def MarkRel (gate : Loc) (mark : Event → Bool) (flag : Bool) (es : List Event) : Prop :=
  flag = true → ∃ j e, j < es.length ∧ es[j]? = some e ∧ mark e = true ∧
    okPolls gate (es.take j) = okPolls gate es

/-- A step without a successful gate poll raises the flag only at a marked event. -/
theorem MarkRel.step {gate : Loc} {mark : Event → Bool} {flag flag' : Bool} {es : List Event}
    {e : Event} (h : MarkRel gate mark flag es)
    (hok : okPoll gate e = false) (hs : flag' = true → mark e = true ∨ flag = true) :
    MarkRel gate mark flag' (es ++ [e]) := by
  intro hf
  rcases hs hf with hm | hfl
  · refine ⟨es.length, e, by simp, by simp, hm, ?_⟩
    rw [List.take_left' rfl, okPolls_snoc, hok]
    simp
  · obtain ⟨j, e', hj, he', hm, hc⟩ := h hfl
    refine ⟨j, e', by simp; omega, by rw [List.getElem?_append_left hj]; exact he', hm, ?_⟩
    rw [List.take_append_of_le_length hj.le, okPolls_snoc, hok, hc]
    simp

end PTX.Flow
