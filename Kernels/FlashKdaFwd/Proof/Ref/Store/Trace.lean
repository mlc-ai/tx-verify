-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Shapes
public import Kernels.FlashKdaFwd.Proof.Ref.Chain
public import Kernels.FlashKdaFwd.Proof.Thread.Sound

@[expose] public section

/-! # Store phase: the invariant along a thread's trace

* `step_at`: from the invariant at a position and a successor of the generated machine
  (`Thread.next … = some (some s')`), the successor is at a successor position of the phase
  (`Step`), or (from the entry or an arrival: `Pos.canExit`) at the exit, and its ledger is
  the old one plus `evDelta pos e`, what the position's event counts. It joins the step
  lemmas of `Steps.lean` and `Family.lean` with the machine's form equations
  (`Thread.next_<site>`); the four element reads of a vector load only change the site.
* `next_at`: **no dead control transition, no breakpoint**: at an invariant state the machine
  has a successor STATE for the event the position fires, except that it declares the thread
  dead after an element read whose bytes do not rebuild to a value, or after the fourth element
  read when the four loaded words do not unpack into pairs of 16-bit halves (`Pos.isRead`).
  These are conditions on the data that the reads returned; the value layer excludes them.
* `event_shape`: the exact event (`EvX`) of an event at a followed state with the invariant of a
  position; `store_good`: event, successor and ledger together.
* `store_inv`: **from a state that satisfies the entry condition `In` at index `k0`, every
  later followed state before an event satisfies `Inv`, or the thread has passed a state that
  satisfies `Out`.** Hypotheses: the precondition, consistency, and that the thread is launched.
  `traces` is the same statement as a link of the chain of phases (`Ref/Chain.lean`).
* `store_followed`: **the successor of an invariant state is followed** (the machine does not
  give up), for every event. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}

/-- One more event in the ledger. -/
theorem ledOf_snoc {k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    ledOf P g ((X.tr g).take (k + 1)) = ledOf P g ((X.tr g).take k) + ledEv P g e := by
  simp only [ledOf, ledEv, Led.add_def, okPolls, arrivals, count_snoc _ he]

/-- The positions of the four element reads of a vector load. -/
def Pos.isRead : Pos → Prop
  | .ld0 .. | .ld1 .. | .ld2 .. | .ld3 .. => True
  | _ => False

/-- The positions from which the phase can be left: the entry (a lane other than lane 0, or an
empty sequence) and the arrival of the last tile. -/
def Pos.canExit : Pos → Prop
  | .entry | .arrive _ => True
  | _ => False

/-- **The successor of an invariant state**: at a successor position, or (from the entry or an
arrival only) at the exit. -/
theorem step_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (hr : RefAt P g pos ⟨pos.site, w, p, x⟩) {e : Event} {s' : D}
    (hn : Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some s')) :
    Succ P g pos (evDelta pos e) s' ∨ (pos.canExit ∧ Done P g pos (evDelta pos e) s') := by
  cases pos with
  | entry =>
    obtain rfl := Option.some.inj (Option.some.inj
      ((next_bar_5 (L := L) (g := g) _ _ _ _).symm.trans hn))
    exact (st_entry hpre hr).imp_right fun h => ⟨trivial, h⟩
  | wait t =>
    have hn' := (next_mbarWait_9 (L := L) (g := g) _ _ _ _).symm.trans hn
    obtain ⟨pc, kd⟩ := e
    cases kd <;> (try (simp at hn'; done))
    rename_i l q ok acq sc
    obtain rfl := Option.some.inj (Option.some.inj hn')
    cases ok <;> exact .inl (st_wait hpre hg t _ hr)
  | ts t i => exact .inl (step_ts hpre t i hr hn)
  | commit t =>
    obtain rfl := Option.some.inj (Option.some.inj
      ((next_bulkCommit_0 (L := L) (g := g) _ _ _ _).symm.trans hn))
    exact .inl (st_commit hpre t hr)
  | ld0 t row c =>
    have hn' := (next_load_177 (L := L) (g := g) _ _ _ _).symm.trans hn
    obtain ⟨pc, kd⟩ := e
    cases kd <;> (try (simp at hn'; done))
    dsimp only at hn'
    split at hn'
    · obtain rfl := Option.some.inj (Option.some.inj hn')
      exact .inl ⟨.ld1 t row c _, ⟨rfl, (row_same hr.keep hr.pos).1,
        (row_same hr.keep hr.pos).2⟩, (by led_of t [evDelta]), Step.ld0 t row c _⟩
    · cases hn'
  | ld1 t row c v0 =>
    have hn' := (next_loadEl1_0 (L := L) (g := g) _ _ _ _ v0).symm.trans hn
    obtain ⟨pc, kd⟩ := e
    cases kd <;> (try (simp at hn'; done))
    dsimp only at hn'
    split at hn'
    · obtain rfl := Option.some.inj (Option.some.inj hn')
      exact .inl ⟨.ld2 t row c v0 _, ⟨rfl, (row_same hr.keep hr.pos).1,
        (row_same hr.keep hr.pos).2⟩, (by led_of t [evDelta]), Step.ld1 t row c v0 _⟩
    · cases hn'
  | ld2 t row c v0 v1 =>
    have hn' := (next_loadEl2_0 (L := L) (g := g) _ _ _ _ v0 v1).symm.trans hn
    obtain ⟨pc, kd⟩ := e
    cases kd <;> (try (simp at hn'; done))
    dsimp only at hn'
    split at hn'
    · obtain rfl := Option.some.inj (Option.some.inj hn')
      exact .inl ⟨.ld3 t row c v0 v1 _, ⟨rfl, (row_same hr.keep hr.pos).1,
        (row_same hr.keep hr.pos).2⟩, (by led_of t [evDelta]), Step.ld2 t row c v0 v1 _⟩
    · cases hn'
  | ld3 t row c v0 v1 v2 =>
    have hn' := (next_loadEl3_0 (L := L) (g := g) _ _ _ _ v0 v1 v2).symm.trans hn
    obtain ⟨pc, kd⟩ := e
    cases kd <;> (try (simp at hn'; done))
    dsimp only at hn'
    split at hn'
    · unfold across at hn'
      split_ifs at hn'
      obtain rfl := Option.some.inj (Option.some.inj hn')
      exact .inl ⟨.gst t row c 0, ⟨rfl, (row_same hr.keep hr.pos).1,
        (row_same hr.keep hr.pos).2⟩, (by led_of t [evDelta]), Step.ld3 t row c v0 v1 v2⟩
    · cases hn'
  | gst t row c j => exact .inl (step_gst hpre hg t row c j hr hn)
  | bwait t =>
    obtain ⟨d', e', hs⟩ := st_bwait hpre hg t hr
    have hn' := (next_bulkWait_0 (L := L) (g := g) _ _ _ _).symm.trans hn
    rw [e'] at hn'
    obtain rfl := Option.some.inj (Option.some.inj hn')
    exact .inl hs
  | arrive t =>
    obtain rfl := Option.some.inj (Option.some.inj
      ((next_mbarArrive_6 (L := L) (g := g) _ _ _ _).symm.trans hn))
    exact (st_arrive hpre t hr).imp_right fun h => ⟨trivial, h⟩

/-- **No dead control transition, no breakpoint**: at an invariant state, for the event the
position fires, the machine has a successor state; only after an element read may it declare
the thread dead (bytes that do not rebuild, or loaded words that do not unpack: data
conditions). In particular the breakpoints 2981 and 3095 are not reached. -/
theorem next_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (hr : RefAt P g pos ⟨pos.site, w, p, x⟩) {e : Event} (hev : EvX P g pos x e) :
    (∃ d', Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d')) ∨
      (pos.isRead ∧ Thread.next L g ⟨pos.site, w, p, x⟩ e = none) := by
  cases pos with
  | entry => exact .inl ⟨_, next_bar_5 (L := L) (g := g) _ _ _ _⟩
  | wait t =>
    obtain ⟨ok, rfl⟩ := hev
    exact .inl ⟨_, next_mbarWait_9 (L := L) (g := g) _ _ _ _⟩
  | ts t i => exact .inl (next_ts t i e)
  | commit t => exact .inl ⟨_, next_bulkCommit_0 (L := L) (g := g) _ _ _ _⟩
  | ld0 t row c =>
    obtain ⟨bs, -, rfl⟩ := hev
    have hn := next_load_177 (L := L) (g := g) w p x ⟨3020, .rd (rdAcc P g t row c 0) bs⟩
    dsimp only at hn
    cases hv : rebuild 3 bs with
    | ok v =>
      rw [hv] at hn
      exact .inl ⟨_, hn⟩
    | error f =>
      rw [hv] at hn
      exact .inr ⟨trivial, hn⟩
  | ld1 t row c v0 =>
    obtain ⟨bs, -, rfl⟩ := hev
    have hn := next_loadEl1_0 (L := L) (g := g) w p x ⟨3020, .rd (rdAcc P g t row c 1) bs⟩ v0
    dsimp only at hn
    cases hv : rebuild 3 bs with
    | ok v =>
      rw [hv] at hn
      exact .inl ⟨_, hn⟩
    | error f =>
      rw [hv] at hn
      exact .inr ⟨trivial, hn⟩
  | ld2 t row c v0 v1 =>
    obtain ⟨bs, -, rfl⟩ := hev
    have hn := next_loadEl2_0 (L := L) (g := g) w p x ⟨3020, .rd (rdAcc P g t row c 2) bs⟩ v0 v1
    dsimp only at hn
    cases hv : rebuild 3 bs with
    | ok v =>
      rw [hv] at hn
      exact .inl ⟨_, hn⟩
    | error f =>
      rw [hv] at hn
      exact .inr ⟨trivial, hn⟩
  | ld3 t row c v0 v1 v2 =>
    obtain ⟨bs, -, rfl⟩ := hev
    have hn := next_loadEl3_0 (L := L) (g := g) w p x ⟨3020, .rd (rdAcc P g t row c 3) bs⟩
      v0 v1 v2
    dsimp only at hn
    cases hv : rebuild 3 bs with
    | ok v =>
      rw [hv] at hn
      dsimp only at hn
      unfold across at hn
      split_ifs at hn
      · exact .inl ⟨_, hn⟩
      · exact .inr ⟨trivial, hn⟩
    | error f =>
      rw [hv] at hn
      exact .inr ⟨trivial, hn⟩
  | gst t row c j => exact .inl (next_gst t row c j e)
  | bwait t =>
    obtain ⟨d', e', -⟩ := st_bwait hpre hg t hr
    exact .inl ⟨d', (next_bulkWait_0 (L := L) (g := g) _ _ _ _).trans e'⟩
  | arrive t => exact .inl ⟨_, next_mbarArrive_6 (L := L) (g := g) _ _ _ _⟩

/-- The machine does not give up at an invariant state, whatever the event. -/
theorem next_ne (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (hr : RefAt P g pos ⟨pos.site, w, p, x⟩) (e : Event) :
    Thread.next L g ⟨pos.site, w, p, x⟩ e ≠ some none := by
  have some_ne : ∀ {o : Option (Option D)} {d' : D}, o = some (some d') → o ≠ some none := by
    rintro o d' rfl h
    cases h
  cases pos with
  | entry => exact some_ne (next_bar_5 (L := L) (g := g) _ _ _ _)
  | wait t =>
    rw [show Thread.next L g ⟨(Pos.wait t).site, w, p, x⟩ e = _ from
      next_mbarWait_9 (L := L) (g := g) w p x e]
    split <;> (intro h; cases h)
  | ts t i =>
    obtain ⟨d', h⟩ := next_ts (L := L) (g := g) (w := w) (p := p) (x := x) t i e
    exact some_ne h
  | commit t => exact some_ne (next_bulkCommit_0 (L := L) (g := g) _ _ _ _)
  | ld0 t row c =>
    rw [show Thread.next L g ⟨(Pos.ld0 t row c).site, w, p, x⟩ e = _ from
      next_load_177 (L := L) (g := g) w p x e]
    repeat' split
    all_goals (intro h; cases h)
  | ld1 t row c v0 =>
    rw [show Thread.next L g ⟨(Pos.ld1 t row c v0).site, w, p, x⟩ e = _ from
      next_loadEl1_0 (L := L) (g := g) w p x e v0]
    repeat' split
    all_goals (intro h; cases h)
  | ld2 t row c v0 v1 =>
    rw [show Thread.next L g ⟨(Pos.ld2 t row c v0 v1).site, w, p, x⟩ e = _ from
      next_loadEl2_0 (L := L) (g := g) w p x e v0 v1]
    repeat' split
    all_goals (intro h; cases h)
  | ld3 t row c v0 v1 v2 =>
    rw [show Thread.next L g ⟨(Pos.ld3 t row c v0 v1 v2).site, w, p, x⟩ e = _ from
      next_loadEl3_0 (L := L) (g := g) w p x e v0 v1 v2]
    split
    · split
      · exact across_ne _ _
      · intro h; cases h
    · intro h; cases h
  | gst t row c j =>
    obtain ⟨d', h⟩ := next_gst (L := L) (g := g) (w := w) (p := p) (x := x) t row c j e
    exact some_ne h
  | bwait t =>
    obtain ⟨d', e', -⟩ := st_bwait hpre hg t hr
    exact some_ne ((next_bulkWait_0 (L := L) (g := g) _ _ _ _).trans e')
  | arrive t => exact some_ne (next_mbarArrive_6 (L := L) (g := g) _ _ _ _)

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **The exact event at a followed state** with the invariant of a position. -/
theorem event_shape {k : Nat} {e : Event} {s : D} {pos : Pos} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hr : RefAt P g pos s) :
    EvX P g pos s.x e := by
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_site (fun g hg => Thread.sound hpre hg) hX he hσ
  exact ev_at hpre hg pos hr hat hc hf

/-- **An event at a state of the invariant**: the position with its register facts and ledger,
the exact event, and that the machine does not give up. -/
theorem store_good {k : Nat} {e : Event} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    ∃ pos, RefAt P g pos s ∧
      ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) pos ∧ EvX P g pos s.x e ∧
      ((∃ d', Thread.next L g s e = some (some d')) ∨
        (pos.isRead ∧ Thread.next L g s e = none)) := by
  obtain ⟨pos, hr, hl⟩ := hI
  have hev := event_shape hpre hX hg he hσ hr
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  exact ⟨pos, hr, hl, hev, next_at hpre hg pos hr hev⟩

omit hX in
/-- **The successor of an invariant state is followed**: the machine does not give up there,
for any event. -/
theorem store_followed {k : Nat} {e : Event} {s : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    Thread.next L g s e ≠ some none := by
  obtain ⟨pos, hr, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  exact next_ne hpre hg pos hr e

/-- **One step of the invariant**, with the successor relation of the positions: from an event
that is not undefined behaviour and a successor state of the machine. -/
theorem inv_step_at {k : Nat} {e : Event} {s s' : D} {pos : Pos} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hr : RefAt P g pos s)
    (hl : ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) pos)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hn : Thread.next L g s e = some (some s')) :
    (∃ pos', RefAt P g pos' s' ∧
        ledOf P g ((X.tr g).take (k + 1)) = led (P.length (seqOf P g)) pos' ∧
        Step (P.length (seqOf P g)) pos pos') ∨ (pos.canExit ∧ Out P X g (k + 1) s') := by
  have hd := ledEv_ev ((event_shape hpre hX hg he hσ hr).ev hub)
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  rcases step_at hpre hg pos hr hn with ⟨pos', h1, h2, h3⟩ | ⟨hc, h1, h2⟩
  · exact .inl ⟨pos', h1, by rw [ledOf_snoc he, hl, hd, h2], h3⟩
  · exact .inr ⟨hc, h1, by rw [ledOf_snoc he, hl, hd, h2]⟩

/-- **One step of the invariant.** -/
theorem inv_step {k : Nat} {e : Event} {s s' : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hn : Thread.next L g s e = some (some s')) :
    Inv P X g (k + 1) s' ∨ Out P X g (k + 1) s' := by
  obtain ⟨pos, hr, hl⟩ := hI
  rcases inv_step_at hpre hX hg he hσ hr hl hub hn with ⟨pos', h1, h2, -⟩ | ⟨-, h⟩
  · exact .inl ⟨pos', h1, h2⟩
  · exact .inr h

/-- **The invariant of the store phase along a trace**: after a state with the entry condition
at index `k0`, every followed state before an event has the invariant, or the thread has passed
the exit (at an index from `k0` on). -/
theorem store_inv {k0 : Nat} {s0 : D}
    (h0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0) {k : Nat}
    {s : D} (hk0 : k0 ≤ k) (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P X g k s ∨ ∃ j s1, k0 ≤ j ∧ j ≤ k ∧ Frame.stateAt (code L) X g j = some (some s1) ∧
      Out P X g j s1 := by
  have hpos : 0 < k0 := by
    rcases Nat.eq_zero_or_pos k0 with rfl | h
    · have := hin.2
      simp [ledOf, ledEntry] at this
    · exact h
  have key := phase_inv (C := code L) (fun g hg => Thread.sound hpre hg) hX
    (fun k s => k < k0 ∨ Inv P X g k s) (fun j s => k0 ≤ j ∧ Out P X g j s) (.inl hpos) (by
      intro k e s s' t ins o he hσ hI hat hc hf hub hn
      by_cases h1 : k + 1 < k0
      · exact .inl (.inl h1)
      · rcases hI with hlt | hI
        · have hσ' : Frame.stateAt (code L) X g (k + 1) = some (some s') := by
            rw [Frame.stateAt_succ he, hσ]
            exact hn
          obtain rfl : k + 1 = k0 := by omega
          obtain rfl : s' = s0 := Option.some.inj (Option.some.inj (hσ'.symm.trans h0))
          exact .inl (.inr hin.inv)
        · rcases inv_step hpre hX hg he hσ hI hub hn with h | h
          · exact .inl (.inr h)
          · exact .inr ⟨by omega, h⟩) k s hk hσ
  rcases key with (hlt | hI) | ⟨j, hj, s1, h1, h2, h3⟩
  · omega
  · exact .inl hI
  · exact .inr ⟨j, s1, h2, hj, h1, h3⟩

end

/-- **The store phase as a link of the chain of phases** (`Ref/Chain.lean`): its entry
condition, invariant and exit condition; the entry index is not used. -/
def phase (P : Params) (L : Launch) (X : Execution) (g : Nat) : Ref.Phase (code L) g where
  In := fun k d => In P X g k d
  Inv := fun _ k d => Inv P X g k d
  Out := fun _ k d => Out P X g k d

/-- **The store phase traces**: `store_inv` in the form of the chain. The entry condition
contains `warp g = 5`; there is no other hypothesis than the precondition, consistency and that
the thread is launched. -/
theorem traces (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) : (phase P L X g).Traces X := by
  intro k0 s0 k s h0 hin hk0 hk hσ
  exact store_inv hpre hX hg h0 hin hk0 hk hσ

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
