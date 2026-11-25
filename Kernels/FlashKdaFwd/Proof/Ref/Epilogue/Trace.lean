-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Sites
public import Kernels.FlashKdaFwd.Proof.Ref.Chain
public import Kernels.FlashKdaFwd.Proof.Thread.Sound

@[expose] public section

/-! # Epilogue phase: the invariant along every thread

`epilogue_all`, `epilogue_inv`: in a consistent execution under the precondition, when a
launched thread is at a followed state that satisfies the entry condition of the epilogue
before its event `k0` (`In`: the site `bar_7`, the registers of `Entry`, six `bar.sync 0`),
then before each of its later events its machine is at a state (the machine follows the thread
through the whole epilogue: this is proved, not assumed) and that state satisfies the invariant
`Inv … k0 k` of `Inv.lean`: a position of the thread's role with its registers,
`k = k0 + ord g pos`, the number of `bar.sync 0`, the history of the phase's earlier events,
and unchanged counts of the classes of events the epilogue does not make. `epilogue_weak`: the
part of it that also holds at the state after the thread's last event (`InvW`). `traces` is
`epilogue_inv` in the form of `Ref/Chain.lean` (`phase`: the epilogue as a `Ref.Phase`; its
exit condition is `False`, because the invariant covers the last position, the state before
the `ret` event, and no state follows that event).

At a state of the invariant (`step_at`):

* the event the thread fires is the exact event `EvX` of the position (`Shapes.lean`): the
  closed-form event `Ev`, or, at a store whose carry register holds a value that a 32-bit store
  cannot write, an undefined-behaviour event;
* the machine's successor is a state at the next position of the role (`nxt`), for **every**
  event, also an undefined-behaviour one: no transition of the phase is dead or a give-up. The
  pointer runs of the stores continue because the base pointer is a generic pointer into the
  thread's own window and every move stays in it; there is no data condition on a transition.
  After `ret` the machine stops (`Thread.next … = none`).

`epilogue_ok` and `epilogue_followed` state this for a followed state with the invariant:
the event is not undefined behaviour (given, at a store, a storable carry value), and the
successor is not a give-up.

Hypotheses, stated exactly: `hpre : Pre P L mem0`; `hX : Consistent L kernel Assumptions.all
mem0 X`; `hg : g < L.threads`. The soundness of the machine is the thread layer's theorem
`Thread.sound hpre hg`; tracking (`Frame.Tracked`) is not assumed. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- The machines of the launched threads are sound. -/
theorem sounds (hpre : Pre P L mem0) : ∀ g < L.threads, (code L g).Sound :=
  fun _ hg => Thread.sound hpre hg

/-- A closed-form event of the phase is a `bar.sync 0` exactly at the three barriers. -/
theorem ev_isBar {pos : Pos} (h : Ev P L g pos e) : Execution.isBarId 0 e = pos.isBar := by
  cases pos with
  | st j =>
    obtain ⟨bs, rfl⟩ := h
    rfl
  | _ =>
    simp only [Ev] at h
    subst h
    rfl

/-- An exact event of a position is a `bar.sync 0` exactly at the three barriers. -/
theorem evx_isBar {pos : Pos} (h : EvX P L g pos x e) : Execution.isBarId 0 e = pos.isBar := by
  cases pos with
  | st j =>
    rcases h with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩ <;> rfl
  | _ =>
    simp only [EvX] at h
    exact ev_isBar h

/-- **One step from a position**: the exact event, and (unless the position is the exit) the
machine's successor state at the next position of the role, whatever the event. -/
theorem step_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩) (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t)
    (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    EvX P L g pos x e ∧ (pos ≠ .exit →
      ∃ d', Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d') ∧ RefAt P g (nxt g pos) d') := by
  cases pos with
  | st j => exact ⟨ev_st_at hpre hg j h hat hc hf, fun _ => next_st_at hpre j h e⟩
  | ts i => exact ⟨ev_ts_at hpre hg i h hat hc hf, fun _ => next_ts_at hpre i h e⟩
  | bar7 =>
    refine ⟨ev_plain (P := P) .bar7 hc hf (fun _ h' => by cases h') (fun _ h' => by cases h'),
      fun _ => ?_⟩
    obtain ⟨d', h1, h2⟩ := st_bar7 hpre hg h
    exact ⟨d', (Thread.next_bar_7 w p x e).trans h1, h2⟩
  | fence =>
    exact ⟨ev_plain (P := P) .fence hc hf (fun _ h' => by cases h') (fun _ h' => by cases h'),
      fun _ => ⟨_, Thread.next_fenceProxy_3 w p x e, st_fence h⟩⟩
  | bar8 =>
    exact ⟨ev_plain (P := P) .bar8 hc hf (fun _ h' => by cases h') (fun _ h' => by cases h'),
      fun _ => ⟨_, Thread.next_bar_8 w p x e, st_bar8 hpre hg h⟩⟩
  | commit =>
    exact ⟨ev_plain (P := P) .commit hc hf (fun _ h' => by cases h') (fun _ h' => by cases h'),
      fun _ => ⟨_, Thread.next_bulkCommit_1 w p x e, st_commit h⟩⟩
  | bwait =>
    exact ⟨ev_plain (P := P) .bwait hc hf (fun _ h' => by cases h') (fun _ h' => by cases h'),
      fun _ => ⟨_, Thread.next_bulkWait_1 w p x e, st_bwait h⟩⟩
  | bar9 =>
    exact ⟨ev_plain (P := P) .bar9 hc hf (fun _ h' => by cases h') (fun _ h' => by cases h'),
      fun _ => ⟨_, Thread.next_bar_9 w p x e, st_bar9 h⟩⟩
  | exit =>
    exact ⟨ev_plain (P := P) .exit hc hf (fun _ h' => by cases h') (fun _ h' => by cases h'),
      fun h' => absurd rfl h'⟩

/-! ### Along the trace -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **The event at a state of the invariant**: the exact event of the position of the state,
with the concrete position. -/
theorem event_at {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g k0 k s) :
    ∃ pos, RefAt P g pos s ∧ OnPath g pos ∧ k = k0 + ord g pos ∧
      ((X.tr g).take k).countP (Execution.isBarId 0) = bars pos ∧ Trail P L X g k0 pos ∧
      EvX P L g pos s.x e := by
  obtain ⟨pos, hr, hon, hk, hb, htr, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  exact ⟨pos, hr, hon, hk, hb, htr, (step_at hpre hg pos hr hat hc hf).1⟩

/-- **The invariant is kept by a step** whose event is not undefined behaviour. -/
theorem inv_step {k0 k : Nat} {s s' : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g k0 k s)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hn : Thread.next L g s e = some (some s')) :
    Inv P L X g k0 (k + 1) s' := by
  obtain ⟨pos, hr, hon, hk, hb, htr, hq⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  obtain ⟨hex, hnx⟩ := step_at hpre hg pos hr hat hc hf
  have hev := hex.ev hub
  have hne : pos ≠ .exit := by
    rintro rfl
    have hx : Thread.next L g ⟨Pos.exit.site, w, p, x⟩ e = none := Thread.next_exit_0 w p x e
    rw [hx] at hn
    cases hn
  obtain ⟨d', hd, hr'⟩ := hnx hne
  rw [hd] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  refine ⟨nxt g pos, hr', onPath_nxt hon, ?_, ?_, ?_, ?_⟩
  · rw [ord_nxt hon hne, hk]
    omega
  · rw [count_snoc _ he, hb, bars_nxt pos hne, ev_isBar hev]
  · intro q hq' hlt
    rw [ord_nxt hon hne] at hlt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
    · exact htr q hq' h1
    · obtain rfl := ord_inj hq' hon h1
      exact ⟨e, by rw [← hk]; exact he, hev, by rw [← hk]; exact hb⟩
  · intro c hc
    rw [count_snoc c he, hq c hc, hc pos e hev]
    simp

/-- **The machine follows a thread through the epilogue, with the invariant**: from a followed
state with the entry condition before the thread's event `k0`, before each later event of the
thread the machine is at a state, and that state satisfies the invariant. -/
theorem epilogue_all {k0 : Nat} {s0 : D}
    (h0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0) {k : Nat}
    (hk0 : k0 ≤ k) (hk : k < (X.tr g).length) :
    ∃ s, Frame.stateAt (code L) X g k = some (some s) ∧ Inv P L X g k0 k s := by
  induction k, hk0 using Nat.le_induction with
  | base => exact ⟨s0, h0, hin.inv⟩
  | succ k hk0 ih =>
    obtain ⟨s, hσ, hI⟩ := ih (by omega)
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k + 1]? = some e' := ⟨_, List.getElem?_eq_getElem hk⟩
    have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
      rintro pc f rfl
      have := ub_last hX he he'
      omega
    obtain ⟨pos, hr, hon, hkp, hb, htr, hex⟩ := event_at hpre hX hg he hσ hI
    have hev := hex.ev hub
    have hne : pos ≠ .exit := by
      rintro rfl
      have hlast := Execution.exit_last hX hg (hev ▸ he)
      omega
    obtain ⟨site, w, p, x⟩ := s
    obtain rfl : site = pos.site := hr.site
    obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
    obtain ⟨d', hd, -⟩ := (step_at hpre hg pos hr hat hc hf).2 hne
    have hσ' : Frame.stateAt (code L) X g (k + 1) = some (some d') := by
      rw [Frame.stateAt_succ he, hσ]
      exact hd
    exact ⟨d', hσ', inv_step hpre hX hg he hσ hI hub hd⟩

/-- **The reference invariant of the epilogue**: from a followed state with the entry
condition before the thread's event `k0`, the state before each later event of the thread
satisfies the invariant. -/
theorem epilogue_inv {k0 : Nat} {s0 : D}
    (h0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0) {k : Nat}
    {s : D} (hk0 : k0 ≤ k) (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) : Inv P L X g k0 k s := by
  obtain ⟨s', hσ', hI⟩ := epilogue_all hpre hX hg h0 hin hk0 hk
  rw [hσ] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  exact hI

/-- **The weak invariant at every followed state of the epilogue, also the one after the
thread's last event**: the position, its registers, its ordinal and the number of
`bar.sync 0`. -/
theorem epilogue_weak {k0 : Nat} {s0 : D}
    (h0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0) {k : Nat}
    {s : D} (hk0 : k0 ≤ k) (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) : InvW P X g k0 k s := by
  rcases Nat.lt_or_ge k (X.tr g).length with hlt | hge
  · exact (epilogue_inv hpre hX hg h0 hin hk0 hlt hσ).weak
  rcases Nat.eq_or_lt_of_le hk0 with rfl | hlt0
  · rw [h0] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    exact hin.inv (L := L).weak
  -- the state after the last event `k - 1` of the thread
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨s1, hσ1, hI⟩ := epilogue_all hpre hX hg h0 hin (k := k) (by omega) (by omega)
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨pos, hr, hon, hkp, hb, htr, hex⟩ := event_at hpre hX hg he hσ1 hI
  obtain ⟨site, w, p, x⟩ := s1
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ1
  rw [Frame.stateAt_succ he, hσ1] at hσ
  have hn : Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some s) := hσ
  have hne : pos ≠ .exit := by
    rintro rfl
    have hx : Thread.next L g ⟨Pos.exit.site, w, p, x⟩ e = none := Thread.next_exit_0 w p x e
    rw [hx] at hn
    cases hn
  obtain ⟨d', hd, hr'⟩ := (step_at hpre hg pos hr hat hc hf).2 hne
  rw [hd] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  refine ⟨nxt g pos, hr', onPath_nxt hon, ?_, ?_⟩
  · rw [ord_nxt hon hne, hkp]
    omega
  · rw [count_snoc _ he, hb, bars_nxt pos hne, evx_isBar hex]

/-- **At a state of the epilogue the thread's event is not undefined behaviour and the
machine's successor is a state** (unless the event is the `ret`), given that at a store the
carry register holds a value a 32-bit store can write (`hv`; the value layer's fact). -/
theorem epilogue_ok {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g k0 k s)
    (hv : ∀ j, s.site = (Pos.st j).site → ∃ v, storeValue 32 (s.x (stSrc j.val)) = .ok v) :
    (∀ pc f, e ≠ ⟨pc, .ub f⟩) ∧
      (s.site ≠ .exit 0 → ∃ s', Thread.next L g s e = some (some s')) := by
  obtain ⟨pos, hr, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  obtain ⟨hex, hnx⟩ := step_at hpre hg pos hr hat hc hf
  refine ⟨hex.noUb fun j hj => hv j (by rw [hj]), fun hne => ?_⟩
  obtain ⟨d', hd, -⟩ := hnx (by rintro rfl; exact hne rfl)
  exact ⟨d', hd⟩

/-- **The machine follows the thread through the epilogue**: at a state of the invariant the
successor along any event is not a give-up. -/
theorem epilogue_followed {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g k0 k s) :
    Thread.next L g s e ≠ some none := by
  obtain ⟨pos, hr, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  obtain ⟨-, hnx⟩ := step_at hpre hg pos hr hat hc hf
  by_cases hne : pos = .exit
  · subst hne
    have hx : Thread.next L g ⟨Pos.exit.site, w, p, x⟩ e = none := Thread.next_exit_0 w p x e
    rw [hx]
    intro h
    cases h
  · obtain ⟨d', hd, -⟩ := hnx hne
    rw [hd]
    intro h
    cases h

end

/-! ### In the form of `Ref/Chain.lean` -/

/-- **The epilogue as a phase of a thread's run**: entry `In`, invariant `Inv`, and no exit
condition (the invariant holds up to the state before the `ret` event, after which the thread
has no state). -/
def phase (P : Params) (L : Launch) (X : Execution) (g : Nat) : Ref.Phase (code L) g where
  In := In P X g
  Inv := Inv P L X g
  Out := fun _ _ _ => False

/-- **The theorem of the epilogue**, in the form that chains with the other phases. -/
theorem traces (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) : (phase P L X g).Traces X :=
  fun _ _ _ _ h0 hin hk0 hk hσ => .inl (epilogue_inv hpre hX hg h0 hin hk0 hk hσ)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
