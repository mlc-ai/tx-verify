-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Shapes
public import Kernels.FlashKdaFwd.Proof.Ref.Chain

@[expose] public section

/-! # The reference invariant of the CarryLoad phase along every thread

`carry_inv`: in a consistent execution, for a launched thread whose Conversion phase ended
before its event `k0` (`In`: the Conversion's exit condition at `k0`), the state of the
thread's machine before each later event `k` satisfies the invariant of the CarryLoad phase
(`Inv P X g k0 k`: a position, its registers and pointer slots, the ledger, and `k = k0 +` the
number of events of the position), or the thread has left the phase (`Left`: the exit
condition `Out` held at event `k0 + len g`, at the state before the `bar.sync 0` of
instruction 1402).

`event_at`: the event at a state of the invariant is the closed-form event of its position
(`Ev`); it is never undefined behaviour (`carry_noUb`).

`carry_ok`: at a state of the invariant, under the **data condition** of the event (`DataOk`:
the four bytes that a carry load reads have a value), the machine's successor is a state: the
thread is not dead and the machine does not give up. The data condition is what the value
layer owes (the bytes are those of a binary32 payload of the initial state). Everything else
is proved here: the address of every load is in range and aligned, and every pointer run
continues.

`exit_event`, `exit_next`: at the exit state the event is the `bar.sync 0` of instruction 1402
and the successor is a state, with no condition.

Hypotheses: the precondition `Pre`, consistency, the thread is launched. The soundness of the
machine is `Thread.sound`; tracking is not assumed.

The file ends with the phase in the form of `Ref/Chain.lean` (`phase`, `traces`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- **The data condition of the event `e`** at a state of the phase: when it is a read (a carry
load), its bytes have a value. The value layer proves it; the reference layer needs it only to
say that the thread goes on. -/
def DataOk (e : Event) : Prop :=
  ∀ a bs, e.kind = .rd a bs → ∃ v, ldVal .same 32 bs = .ok v

/-- One more event in the startup's ledger of a prefix. -/
theorem ledOf_succ {k : Nat} (he : X.get (g, k) = some e) :
    Startup.ledOf ((X.tr g).take (k + 1)) =
      Startup.ledOf ((X.tr g).take k) + Startup.ledEv e := by
  simp only [Startup.ledOf, Startup.ledEv, Startup.Led.add_def, count_snoc _ he]

/-- An event of the phase leaves the ledger as it is. -/
theorem led_keep {k : Nat} {pos : Pos} (he : X.get (g, k) = some e) (hev : Ev P g pos e)
    (hl : Startup.ledOf ((X.tr g).take k) = ledExit g) :
    Startup.ledOf ((X.tr g).take (k + 1)) = ledExit g := by
  rw [ledOf_succ he, hl, hev.led]
  rfl

/-! ### One step -/

/-- **The successor of a position**: the next state is at a position with one more event of
the phase before it, or it is the exit state and the position was the proxy fence. -/
theorem good_at (hpre : Pre P L mem0) (pos : Pos) {d' : D}
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩)
    (hn : Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d')) :
    (∃ pos', RefAt P g pos' d' ∧ done g pos' = done g pos + 1) ∨
      (Exit P g d' ∧ pos = .fence) := by
  cases pos with
  | ld j =>
    obtain ⟨f, hnx, hf⟩ := st_ld hpre j h e
    rw [hnx] at hn
    obtain ⟨a, bs, v, -, -, rfl⟩ := ldNext0_some hn
    exact .inl (hf v)
  | fence =>
    obtain ⟨hnx, hE⟩ := st_fence (L := L) (e := e) h
    have hn' := hnx.symm.trans hn
    obtain rfl := Option.some.inj (Option.some.inj hn')
    exact .inr ⟨hE, rfl⟩

/-- **Under the data condition the successor is a state.** -/
theorem ok_at (hpre : Pre P L mem0) (pos : Pos) (h : RefAt P g pos ⟨pos.site, w, p, x⟩)
    (hev : Ev P g pos e) (hdata : DataOk e) :
    ∃ d', Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d') := by
  cases pos with
  | ld j =>
    obtain ⟨bs, -, rfl⟩ := hev
    obtain ⟨v, hv⟩ := hdata _ bs rfl
    obtain ⟨f, hnx, -⟩ := st_ld (L := L) hpre j h
      ⟨765 + 5 * j.val, .rd { loc := ⟨.shared, cta g, ldAddr P g j.val⟩, size := 4 } bs⟩
    exact ⟨f v, hnx.trans (ldNext0_ok rfl hv)⟩
  | fence => exact ⟨_, (st_fence (L := L) (e := e) h).1⟩

/-! ### Along the trace -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hg

/-- The step of the phase's induction. -/
theorem inv_step {k0 k : Nat} {s s' : D} (he : X.get (g, k) = some e)
    (hI : Inv P X g k0 k s) (hat : (code L g).AtD s t)
    (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hn : Thread.next L g s e = some (some s')) :
    Inv P X g k0 (k + 1) s' ∨ (k + 1 = k0 + len g ∧ Out P X g (k + 1) s') := by
  obtain ⟨pos, hr, hl, hd⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  have hev := ev_at hpre hg pos hr hat hc hf
  have hled := led_keep he hev hl
  rcases good_at hpre pos hr hn with ⟨pos', h1, h2⟩ | ⟨h1, rfl⟩
  · exact .inl ⟨pos', h1, hled, by omega⟩
  · have hfe : e = ⟨1401, .fenceProxy (.async (some (.shared .cta))) none⟩ := hev
    refine .inr ⟨?_, h1, hled, Nat.succ_pos k, ?_⟩
    · simp only [done, len] at hd ⊢
      split_ifs at hd ⊢ <;> omega
    · rw [Nat.add_sub_cancel, he, hfe]

include hX

/-- **The reference invariant of the CarryLoad phase**: for a thread that entered the phase
before its event `k0`, the state of its machine before each later event `k` is at a position of
the phase with the position's registers, ledger and event count, or the thread has left the
phase through its exit, which it reached before its event `k0 + len g`. -/
theorem carry_inv {k0 : Nat} {s0 : D}
    (hσ0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0)
    {k : Nat} {s : D} (hk0 : k0 ≤ k) (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P X g k0 k s ∨ Left P X g L k0 k := by
  obtain ⟨pos0, hr0, hd0⟩ := entry_at hin.1
  have h0 : Inv P X g k0 k0 s0 := ⟨pos0, hr0, hin.2, by omega⟩
  rcases phase_inv_from (C := code L) (fun g hg => Thread.sound hpre hg) hX hσ0
      (fun k s => Inv P X g k0 k s) (fun k s => k = k0 + len g ∧ Out P X g k s) h0
      (fun k e s s' t ins o _ he _ hI hat hc hf _ hn => inv_step hpre hg he hI hat hc hf hn)
      k s hk0 hk hσ with h | ⟨j, -, hj, s1, h1, rfl, h2⟩
  · exact .inl h
  · exact .inr ⟨hj, s1, h1, h2⟩

/-- **An event at a state of the invariant** is the closed-form event of the state's position,
which has `k - k0` events of the phase before it. -/
theorem event_at {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    ∃ pos, RefAt P g pos s ∧ Ev P g pos e ∧ k = k0 + done g pos := by
  obtain ⟨pos, hr, -, hd⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_site (fun g hg => Thread.sound hpre hg) hX he hσ
  exact ⟨pos, hr, ev_at hpre hg pos hr hat hc hf, hd⟩

/-- **No event of the phase is undefined behaviour**, whatever the data. -/
theorem carry_noUb {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  obtain ⟨pos, -, hev, -⟩ := event_at hpre hX hg he hσ hI
  exact hev.noUb

/-- **Under the data condition the thread goes on** from a state of the invariant: the event
is not undefined behaviour and the machine's successor is a state. -/
theorem carry_ok {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hdata : DataOk e) :
    (∀ pc f, e ≠ ⟨pc, .ub f⟩) ∧ ∃ s', Thread.next L g s e = some (some s') := by
  obtain ⟨pos, hr, hev, -⟩ := event_at hpre hX hg he hσ hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  exact ⟨hev.noUb, ok_at hpre pos hr hev hdata⟩

/-- **One step from a state of the invariant**: when the machine's successor is a state, it
is a state of the invariant, or it is the exit state reached at event `k0 + len g`. -/
theorem inv_next {k0 k : Nat} {s s' : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hn : Thread.next L g s e = some (some s')) :
    Inv P X g k0 (k + 1) s' ∨ (k + 1 = k0 + len g ∧ Out P X g (k + 1) s') := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_site (fun g hg => Thread.sound hpre hg) hX he hσ
  exact inv_step hpre hg he hI hat hc hf hn

omit hg in
/-- **The event at the exit state** is the `bar.sync 0` of instruction 1402. -/
theorem exit_event {k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (ho : Exit P g s) : e = barEv := by
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = .bar 5 := ho.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_site (fun g hg => Thread.sound hpre hg) hX he hσ
  exact ev_exit hc hf

omit hpre hX hg in
/-- **The successor of the exit state is a state**: the transition of the barrier at 1402 has
no condition. -/
theorem exit_next {s : D} (ho : Exit P g s) (e : Event) :
    Thread.next L g s e = some (some (after_bar_5 L g s)) := by
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = .bar 5 := ho.site
  exact st_bar

end

/-! ### The phase, for the chain of the run -/

/-- **The CarryLoad phase of thread `g`** in the form of `Ref/Chain.lean`: the entry is the
exit of the Conversion phase; the exit (the state at `bar_5`, before its event) is reached
exactly `len g` events after the entry. -/
def phase (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g where
  In k s := In P X g k s
  Inv k0 k s := Inv P X g k0 k s
  Out k0 j s := j = k0 + len g ∧ Out P X g j s

theorem traces (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) : (phase P L X g).Traces X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  rcases carry_inv hpre hX hg h0 hin hk0 hk hs with h | ⟨hj, s1, h1, h2⟩
  · exact .inl h
  · exact .inr ⟨k0 + len g, s1, Nat.le_add_right _ _, hj, h1, rfl, h2⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
