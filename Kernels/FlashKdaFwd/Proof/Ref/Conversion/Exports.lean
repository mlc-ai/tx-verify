-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Contract
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds.Count
public import Kernels.FlashKdaFwd.Proof.Ref.Swizzle
public import Kernels.FlashKdaFwd.Proof.Top.Wire

@[expose] public section

/-! # What the Conversion phase exports to the contracts

Every theorem is about an event of a launched thread `g` at a state of the phase's invariant
(`hI : Inv P X g k0 k s`: the thread entered the phase before its event `k0`, and `s` is the
followed state before its event `k`); `conversion_inv` / `traces` (`Trace.lean`) say that every
followed state from the entry to the exit of the phase is such a state. The assembly lifts the
statements to all events through the chain of the phases.

* **Events** (`event_at`): the position of the state and the closed form of its event.
* **Memory** (`Touch`, `touch_conversion`, `memTouches_conversion`): an operation of the phase
  touches either the four bytes of the FP32 buffer at the swizzled address of an element
  `el < 16384` (a load), or the two bytes of slot `el` of `state_acc`, for an element that the
  thread owns (a store: `convOwner el = tid g`). `memSpaces_conversion` and
  `sharedFrame_conversion` are the fields of `Top.DirectFacts` for these operations.
* **`state_acc`** (`Protocol.StateAccFacts`): `stateAcc_phase` (an access of a byte of
  `state_acc` is a write of the own block with three `bar.sync 0` before it) and
  `stateAcc_owner` (two such accesses of one byte belong to one thread). Asynchronous
  operations are not issued in the phase (`async_conversion`), which is the phase's share of
  `thread_only`.
* **The buffer region** (`Protocol.UnionFacts.thread`): `union_early`: an access of a byte of
  the buffer region is a read of the own block with three `bar.sync 0` before it, after the
  thread's successful poll of the state barrier: the class `early`.
* **The value layer's `ConvRef`** (`Values/Ends/Contract.lean`): `conv_load` (at the `j`-th
  load site the event is the read of the four bytes at the swizzled address of an element,
  with three `bar.sync 0` before it, and if the next event is a write it is the write of that
  element's slot) and `conv_store` (a write event of the phase is the event after a state at a
  load site). They are stated with `swzN`, which is the value layer's `swzAddr` by definition,
  and with `L.sharedBase`.
* **Progress and the bound** (`Progress.RefProgress`): `bar0_conversion` (the count of
  `bar.sync 0` is that of the instruction index), `barStep_conversion` (a barrier event leads
  to a later instruction), `doneOf` / `leftOf` (the events of the phase behind and ahead of a
  state, as functions of the state: its site and the pair-index register), `done_state`,
  `left_dec_conversion`.
* **No undefined behaviour, no dead state** (the control half): `conversion_ok`
  (`Trace.lean`), under the data condition `DataOk` of the value layer; `ub_conversion`: an
  undefined-behaviour event of the phase is a store whose register does not convert.
* **Coverage** (`conv_cover`, with `Arith.lean: slot_cover`, `slotOf_owner`): a thread that
  left the phase has made, for each of its elements, the read of the FP32 entry and the write
  of the slot, at event indices fixed by the element's ordinal; each of the 16384 slots of a
  block is element `convOrd e` of the thread `convOwner e`.
* **Counts the phase does not change** (`count_conversion`, `PhaseKind`, `class_…`): for the
  ledgers of the later phases, whose classes (polls and arrivals per mbarrier, tensor loads
  and stores, matrix events, the named barrier) have the same counts at the phase's exit as
  at its entry. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before bar0Pcs InStateAcc InUnion InShared Bar)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The position of an event -/

theorem Ev.rd {pos : Pos} {d : D} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (h : Ev P g pos d ⟨pc, .rd a bs⟩) :
    ∃ j u, pos = .ld j u ∧ pc = (Pos.ld j u).site.pc ∧
      a = { loc := ⟨.shared, cta g, rdAddr P (slotOf g (elemIx j.val u))⟩, size := 4 } := by
  cases pos with
  | fence => cases h
  | ld j u =>
    obtain ⟨bs', -, h⟩ := h
    cases h
    exact ⟨j, u, rfl, rfl, rfl⟩
  | st j u => rcases h with ⟨v', -, h⟩ | ⟨f, -, h⟩ <;> cases h
  | bar j => cases h

theorem Ev.wr {pos : Pos} {d : D} {pc : Nat} {a : Acc} {bs : List Byte}
    (h : Ev P g pos d ⟨pc, .wr a bs⟩) :
    ∃ j u, pos = .st j u ∧
      a = { loc := ⟨.shared, cta g, wrAddr P (slotOf g (elemIx j.val u))⟩, size := 2 } := by
  cases pos with
  | fence => cases h
  | ld j u =>
    obtain ⟨bs', -, h⟩ := h
    cases h
  | st j u =>
    rcases h with ⟨v', -, h⟩ | ⟨f, -, h⟩ <;> cases h
    exact ⟨j, u, rfl, rfl⟩
  | bar j => cases h

theorem Ev.bar {pos : Pos} {d : D} {pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (h : Ev P g pos d ⟨pc, .bar id cnt m⟩) : ∃ j, pos = .bar j := by
  cases pos with
  | fence => cases h
  | ld j u =>
    obtain ⟨bs', -, h⟩ := h
    cases h
  | st j u => rcases h with ⟨v', -, h⟩ | ⟨f, -, h⟩ <;> cases h
  | bar j => exact ⟨j, rfl⟩

/-- The kinds of events the phase makes. -/
def PhaseKind (e : Event) : Prop :=
  (∃ a bs, e.kind = .rd a bs) ∨ (∃ a bs, e.kind = .wr a bs) ∨ (∃ f, e.kind = .ub f) ∨
    e.kind = .fenceProxy (.async (some (.shared .cta))) none ∨ e.kind = .bar 0 none .sync

theorem Ev.phaseKind {pos : Pos} {d : D} {e : Event} (h : Ev P g pos d e) : PhaseKind e := by
  cases pos with
  | fence => subst h; exact .inr (.inr (.inr (.inl rfl)))
  | ld j u =>
    obtain ⟨bs, -, rfl⟩ := h
    exact .inl ⟨_, _, rfl⟩
  | st j u =>
    rcases h with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩
    · exact .inr (.inl ⟨_, _, rfl⟩)
    · exact .inr (.inr (.inl ⟨_, rfl⟩))
  | bar j => subst h; exact .inr (.inr (.inr (.inr rfl)))

/-- `phase_class`: a class of events (a Boolean predicate defined by cases on the kind) that
contains none of the kinds of the phase's events. -/
macro "phase_class" : tactic => `(tactic| (
  rintro ⟨pc, kd⟩ h
  rcases h with ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨f, h⟩ | h | h <;> (simp only at h; subst h; rfl)))

/-- The element of a load or store position, with its bound and its owner. -/
theorem elem_facts {j : Fin 10} {u : Nat} (h : Round g j.val u) :
    slotOf g (elemIx j.val u) < 16384 ∧ convOwner (slotOf g (elemIx j.val u)) = tid g :=
  ⟨elem_lt j.isLt h, (slotOf_owner (elemIx_lt j.isLt h)).2.1⟩

/-- No conversion load is one of the 21 loads of the offsets array (the only sites at which
the machine can give up). -/
theorem conv_no_offset : ∀ j : Fin 10, offsetLoads.contains (21 + j.val) = false := by decide

/-- The ten load sites are at ten instructions. -/
theorem load_pc_inj : ∀ j j' : Fin 10,
    (Pos.ld j 0).site.pc = (Pos.ld j' 0).site.pc → j = j' := by decide

/-- A state of the invariant at the `j`-th load site is at a position `ld j u`. -/
theorem pos_of_load {pos : Pos} {d : D} {j : Fin 10} (hr : RefAt P g pos d)
    (hs : d.site = .load ⟨21 + j.val, by omega⟩) : ∃ u, pos = .ld j u := by
  have h := hr.site.symm.trans hs
  cases pos with
  | ld j' u =>
    simp only [Pos.site, Site.load.injEq, Fin.mk.injEq] at h
    exact ⟨u, by rw [Fin.ext (show j'.val = j.val by omega)]⟩
  | fence => simp [Pos.site] at h
  | st j' u => simp [Pos.site] at h
  | bar j' => simp [Pos.site] at h

/-- A state of the invariant at the `j`-th store site is at a position `st j u`. -/
theorem pos_of_store {pos : Pos} {d : D} {j : Fin 10} (hr : RefAt P g pos d)
    (hs : d.site = .store ⟨j.val, by omega⟩) : ∃ u, pos = .st j u := by
  have h := hr.site.symm.trans hs
  cases pos with
  | st j' u =>
    simp only [Pos.site, Site.store.injEq, Fin.mk.injEq] at h
    exact ⟨u, by rw [Fin.ext h]⟩
  | fence => simp [Pos.site] at h
  | ld j' u => simp [Pos.site] at h
  | bar j' => simp [Pos.site] at h

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **An event of the phase**: the position of the state before it, with the ledger and the
event count, and the event in closed form. -/
theorem event_at {k0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    ∃ pos, RefAt P g pos s ∧ Startup.ledOf ((X.tr g).take k) = led g pos ∧
      k = k0 + done g pos ∧ Ev P g pos s e := by
  obtain ⟨pos, hr, hl, hd, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_site (fun g hg => Thread.sound hpre hg) hX he hσ
  exact ⟨pos, hr, hl, hd, ev_at hpre hg pos hr hat hc hf⟩

/-- **One step of the phase**: the machine's successor along the thread's event is the state
before the next event; it is in the phase, or it is the exit, `len g` events after the
entry. -/
theorem conversion_next {k0 k : Nat} {s s' : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hn : Thread.next L g s e = some (some s')) :
    Frame.stateAt (code L) X g (k + 1) = some (some s') ∧
      (Inv P X g k0 (k + 1) s' ∨ (k + 1 = k0 + len g ∧ Out P X g (k + 1) s')) := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_site (fun g hg => Thread.sound hpre hg) hX he hσ
  refine ⟨?_, inv_step hpre hg he hI hat hc hf hn⟩
  rw [Frame.stateAt_succ he, hσ]
  exact hn

/-! ### Memory -/

/-- **What an operation of the phase touches**: the four bytes of the FP32 buffer at the
swizzled address of an element, or the two bytes of the slot of an element that the thread
owns. -/
def Touch (P : Params) (g : Nat) (a : Acc) : Prop :=
  (∃ el < 16384, a = { loc := ⟨.shared, cta g, rdAddr P el⟩, size := 4 }) ∨
    ∃ el < 16384, convOwner el = tid g ∧
      a = { loc := ⟨.shared, cta g, wrAddr P el⟩, size := 2 }

/-- **What an event of the phase accesses**; it issues no asynchronous operation. -/
theorem touch_conversion {k0 k : Nat} {e : Event} {a : Acc} {s : D}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k0 k s) (ha : AccessOf e a ∨ AsyncOf e a) : Touch P g a := by
  obtain ⟨pos, hr, -, -, hev⟩ := event_at hpre hX hg he hσ hI
  cases pos with
  | fence =>
    subst hev
    rcases ha with ha | ha <;> exact ha.elim
  | ld j u =>
    obtain ⟨bs, -, rfl⟩ := hev
    rcases ha with ha | ha
    · exact .inl ⟨_, (elem_facts (ld_round hr.pos)).1, ha⟩
    · exact ha.elim
  | st j u =>
    rcases hev with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩
    · rcases ha with ha | ha
      · obtain ⟨h1, h2⟩ := elem_facts (st_round hr.pos)
        exact .inr ⟨_, h1, h2, ha⟩
      · exact ha.elim
    · rcases ha with ha | ha <;> exact ha.elim
  | bar j =>
    subst hev
    rcases ha with ha | ha <;> exact ha.elim

/-- **The phase issues no asynchronous operation**: an operation whose issuing event is fired
at a state of the phase is the thread's own access. -/
theorem async_conversion {k0 k : Nat} {e : Event} {a : Acc} {s : D}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k0 k s) : ¬ AsyncOf e a := by
  intro ha
  obtain ⟨pos, hr, -, -, hev⟩ := event_at hpre hX hg he hσ hI
  cases pos with
  | fence => subst hev; exact ha.elim
  | ld j u => obtain ⟨bs, -, rfl⟩ := hev; exact ha.elim
  | st j u => rcases hev with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩ <;> exact ha.elim
  | bar j => subst hev; exact ha.elim

/-- **What a memory operation issued in the phase touches** (`Execution.MemTouches`). -/
theorem memTouches_conversion {r : AsyncCopy.Ref} {a : Acc} {k0 k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    Touch P g a := by
  rcases ht with ⟨w, hi⟩ | ⟨i, bs, hri, pc, hnc⟩
  · obtain ⟨e, he, ha⟩ := Frame.intent_issuer hi
    rw [hr] at he
    exact touch_conversion hpre hX hg he hσ hI ha
  · subst hri
    have hi : i = (g, k) := hr
    subst hi
    exact touch_conversion hpre hX hg hnc hσ hI (.inl rfl)

/-- **`DirectFacts.memSpaces` for the Conversion phase.** -/
theorem memSpaces_conversion {r : AsyncCopy.Ref} {a : Acc} {k0 k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    a.loc.space = .shared ∨ a.loc.space = .global := by
  rcases memTouches_conversion hpre hX hg hr ht hσ hI with ⟨el, -, rfl⟩ | ⟨el, -, -, rfl⟩ <;>
    exact .inl rfl

/-- **`DirectFacts.sharedFrame` for the Conversion phase**: the phase touches bytes of the
data part of the window of the thread's own block. -/
theorem sharedFrame_conversion {r : AsyncCopy.Ref} {a : Acc} {k0 k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    a.loc.cta = g / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304 := by
  rcases memTouches_conversion hpre hX hg hr ht hσ hI with ⟨el, hel, rfl⟩ | ⟨el, hel, -, rfl⟩
  · obtain ⟨h1, h2, -, -⟩ := rdAddr_frame hpre hel
    exact ⟨(block_div hpre).symm, by simp only; omega, by simp only; omega⟩
  · obtain ⟨h1, h2, -, -⟩ := wrAddr_frame hpre hel
    exact ⟨(block_div hpre).symm, by simp only; omega, by simp only; omega⟩

/-! ### The accesses, by region -/

/-- **An access of the phase**: three `bar.sync 0` before it; a read of the four bytes at the
swizzled address of an element, or a write of the two bytes of the slot of an element that the
thread owns. -/
theorem access_conversion {k0 k : Nat} {a : Acc} {w : Bool} {s : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (h : X.Access (g, k) a w) :
    bar0Before X (g, k) = 3 ∧
      ((w = false ∧ ∃ el < 16384, a = { loc := ⟨.shared, cta g, rdAddr P el⟩, size := 4 }) ∨
        (w = true ∧ ∃ el < 16384, convOwner el = tid g ∧
          a = { loc := ⟨.shared, cta g, wrAddr P el⟩, size := 2 })) := by
  have hb : ∀ pos : Pos, Startup.ledOf ((X.tr g).take k) = led g pos →
      (∀ j, pos ≠ .bar j) → bar0Before X (g, k) = 3 := by
    intro pos hl hne
    have h1 : bar0Before X (g, k) = (Startup.ledOf ((X.tr g).take k)).bars := rfl
    rw [h1, hl]
    cases pos with
    | bar j => exact absurd rfl (hne j)
    | _ => rfl
  rcases h with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
  · obtain ⟨pos, hr, hl, -, hev⟩ := event_at hpre hX hg he hσ hI
    obtain ⟨j, u, rfl, -, rfl⟩ := hev.rd
    exact ⟨hb _ hl nofun, .inl ⟨rfl, _, (elem_facts (ld_round hr.pos)).1, rfl⟩⟩
  · obtain ⟨pos, hr, hl, -, hev⟩ := event_at hpre hX hg he hσ hI
    obtain ⟨j, u, rfl, rfl⟩ := hev.wr
    obtain ⟨h1, h2⟩ := elem_facts (st_round hr.pos)
    exact ⟨hb _ hl nofun, .inr ⟨rfl, _, h1, h2, rfl⟩⟩
  · obtain ⟨pos, hr, hl, -, hev⟩ := event_at hpre hX hg he hσ hI
    exfalso
    cases pos with
    | fence => cases hev
    | ld j u =>
      obtain ⟨bs', -, h⟩ := hev
      cases h
    | st j u => rcases hev with ⟨v', -, h⟩ | ⟨f, -, h⟩ <;> cases h
    | bar j => cases hev

/-- **`StateAccFacts.phase` for the Conversion phase**: an access of a byte of `state_acc` is
a write, by a thread of the byte's block, with three `bar.sync 0` before it, of the slot of an
element that the thread owns. -/
theorem stateAcc_phase {k0 k c : Nat} {a : Acc} {w : Bool} {l : Loc} {s : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (h : X.Access (g, k) a w) (hc : a.Covers l) (hl : InStateAcc L c l) :
    g < L.threads ∧ c = g / L.block ∧ bar0Before X (g, k) = 3 ∧ w = true ∧
      ∃ el < 16384, convOwner el = tid g ∧
        a = { loc := ⟨.shared, cta g, wrAddr P el⟩, size := 2 } := by
  obtain ⟨hb, hw⟩ := access_conversion hpre hX hg hσ hI h
  obtain ⟨h1, h2, h3, h4⟩ := hc
  obtain ⟨l1, l2, l3, l4⟩ := hl
  rw [hpre.sharedBase] at l3 l4
  rcases hw with ⟨-, el, hel, rfl⟩ | ⟨rfl, el, hel, ho, rfl⟩
  · have := (rdAddr_frame hpre hel).1
    simp only at h3
    omega
  · refine ⟨hg, ?_, hb, rfl, el, hel, ho, rfl⟩
    rw [block_div hpre, ← l2, h2]

/-- **`UnionFacts.thread` for the Conversion phase**: an access of a byte of the buffer region
is a read by a thread of the byte's block, after its successful poll of the state barrier,
with three `bar.sync 0` before it: the class `early`. -/
theorem union_early {O : Protocol.Owners} {k0 k c : Nat} {a : Acc} {w : Bool} {l : Loc}
    {s0 s : D} (hσ0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0)
    (hk0 : k0 ≤ k) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k0 k s) (h : X.Access (g, k) a w) (hc : a.Covers l)
    (hl : InUnion L c l) :
    g / L.block = c ∧ 1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take k) ∧
      Protocol.ThreadClass L X O c g k w l := by
  obtain ⟨hb, hw⟩ := access_conversion hpre hX hg hσ hI h
  obtain ⟨h1, h2, h3, h4⟩ := hc
  obtain ⟨l1, l2, l3, l4⟩ := hl
  rw [hpre.sharedBase] at l3 l4
  have hleft : Startup.Left P L X g k := ⟨k0, hk0, s0, hσ0, hin⟩
  have hpoll := Startup.Left.statePolled hpre hX hg hleft
  rcases hw with ⟨rfl, el, hel, rfl⟩ | ⟨-, el, hel, -, rfl⟩
  · have hcg : g / L.block = c := by rw [block_div hpre, ← l2, h2]
    rw [hcg] at hpoll
    exact ⟨hcg, hpoll, .early rfl (by omega)⟩
  · have := (wrAddr_frame hpre hel).2.1
    simp only at h3 h4
    omega

/-! ### The value layer's `ConvRef` and `StoreCtl` -/

/-- **`ConvRef.load` for a state of the phase**: at the `j`-th load site the event is the read
of the four bytes at the swizzled address of an element `el`, with three `bar.sync 0` before
it; and if the thread's next event is a write, it is the write of the two bytes of slot `el`
of `state_acc`. (`swzN` is the value layer's `swzAddr`.) -/
theorem conv_load {k0 k : Nat} {s : D} {e : Event} (j : Fin 10) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hs : s.site = .load ⟨21 + j.val, by omega⟩) :
    ∃ el < 16384, ∃ a bs, e = ⟨s.site.pc, .rd a bs⟩ ∧ a.size = 4 ∧
      a.loc = ⟨.shared, g / L.block, swzN (L.sharedBase + 32768 + 4 * el)⟩ ∧
      bar0Before X (g, k) = 3 ∧
      ∀ pc' a' bs', X.get (g, k + 1) = some ⟨pc', .wr a' bs'⟩ →
        a'.size = 2 ∧ a'.loc = ⟨.shared, g / L.block, L.sharedBase + 2 * el⟩ := by
  obtain ⟨pos, hr, hl, hd, hev⟩ := event_at hpre hX hg he hσ hI
  obtain ⟨u, rfl⟩ := pos_of_load hr hs
  obtain ⟨bs, -, rfl⟩ := hev
  have hrd := ld_round hr.pos
  have hlt := (elem_facts hrd).1
  have hbar : bar0Before X (g, k) = 3 := by
    have h1 : bar0Before X (g, k) = (Startup.ledOf ((X.tr g).take k)).bars := rfl
    rw [h1, hl]
    rfl
  refine ⟨slotOf g (elemIx j.val u), hlt, _, bs, by rw [hr.site], rfl, ?_, hbar, ?_⟩
  · rw [block_div hpre, hpre.sharedBase]
    rfl
  · intro pc' a' bs' he'
    rcases Frame.fired (fun g hg => Thread.sound hpre hg) hX he' with
      ⟨σ, o, hσ', -⟩ | ⟨-, pc, f, h⟩
    swap
    · cases h
    rw [Frame.stateAt_succ he, hσ] at hσ'
    have hn : Thread.next L g s _ = some σ := hσ'
    cases σ with
    | none =>
      exfalso
      obtain ⟨j0, hj0, hc0, -⟩ := Thread.next_giveUp (L := L) (g := g) s _ hn
      rw [hs] at hj0
      cases hj0
      have hc1 : offsetLoads.contains (21 + j.val) = true := hc0
      rw [conv_no_offset j] at hc1
      cases hc1
    | some s' =>
      obtain ⟨hσ1, hstep⟩ := conversion_next hpre hX hg he hσ hI hn
      rcases hstep with hI' | ⟨hk1, -⟩
      · obtain ⟨pos', hr', hl', hd', hev'⟩ := event_at hpre hX hg he' hσ1 hI'
        obtain ⟨j', u', rfl, rfl⟩ := hev'.wr
        have hix : elemIx j'.val u' = elemIx j.val u := by
          simp only [done] at hd hd'
          omega
        rw [hix, block_div hpre, hpre.sharedBase]
        exact ⟨rfl, rfl⟩
      · exfalso
        have := elemIx_lt j.isLt hrd
        simp only [done, len] at hd hk1
        omega

/-- **The state before a store is the load of its element**: a state of the invariant at the
`j`-th store site is the successor of a followed state at the `j`-th load site. -/
theorem store_pred {k0 k : Nat} {s0 s : D} {j : Fin 10}
    (hσ0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hs : s.site = .store ⟨j.val, by omega⟩) :
    ∃ k1 d0, k = k1 + 1 ∧ Frame.stateAt (code L) X g k1 = some (some d0) ∧
      d0.site = .load ⟨21 + j.val, by omega⟩ := by
  obtain ⟨pos, hr, hl, hd, hlink⟩ := hI
  obtain ⟨u, rfl⟩ := pos_of_store hr hs
  obtain ⟨bs, v, y, hk, hget, -⟩ := hlink
  have hix := elemIx_lt j.isLt (st_round hr.pos)
  simp only [done] at hd
  obtain ⟨d0, hσ1⟩ := followed_of_le hσ (Nat.sub_le k 1)
  have hlen : k - 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  rcases conversion_inv hpre hX hg hσ0 hin (by omega) hlen hσ1 with hI1 | ⟨hle, -⟩
  · obtain ⟨pos1, hr1, -, -, hev1⟩ := event_at hpre hX hg hget hσ1 hI1
    obtain ⟨j', u', rfl, hpc, -⟩ := hev1.rd
    obtain rfl : j = j' := load_pc_inj j j' hpc
    exact ⟨k - 1, d0, by omega, hσ1, hr1.site⟩
  · exfalso
    simp only [len] at hle
    omega

/-- **`ConvRef.store` for a state of the phase**: a write event has three `bar.sync 0` before
it and is the event after a followed state at a load site. -/
theorem conv_store {k0 k pc : Nat} {s0 s : D} {a : Acc} {bs : List Byte}
    (hσ0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    bar0Before X (g, k) = 3 ∧ ∃ k1 d, ∃ j : Fin 10, k = k1 + 1 ∧
      Frame.stateAt (code L) X g k1 = some (some d) ∧
      d.site = .load ⟨21 + j.val, by omega⟩ := by
  obtain ⟨pos, hr, hl, -, hev⟩ := event_at hpre hX hg he hσ hI
  obtain ⟨j, u, rfl, -⟩ := hev.wr
  have hbar : bar0Before X (g, k) = 3 := by
    have h1 : bar0Before X (g, k) = (Startup.ledOf ((X.tr g).take k)).bars := rfl
    rw [h1, hl]
    rfl
  obtain ⟨k1, d0, h1, h2, h3⟩ := store_pred hpre hX hg hσ0 hin hσ hI (j := j) hr.site
  exact ⟨hbar, k1, d0, j, h1, h2, h3⟩

/-- **`StoreCtl.conv` for a state of the phase** (the control half of a conversion store): a
state at the `j`-th store site is the successor of a followed state at the `j`-th load site,
and if the register it stores converts to a 16-bit value, the event is the write of that
value's bytes: the address does not fault. (`nrReg j` is the register `%rs(7 + j)`.) -/
theorem store_ctl {k0 k : Nat} {s0 s : D} {e : Event} (j : Fin 10)
    (hσ0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hs : s.site = .store ⟨j.val, by omega⟩) (he : X.get (g, k) = some e) :
    (∃ k1 d0, k = k1 + 1 ∧ Frame.stateAt (code L) X g k1 = some (some d0) ∧
      d0.site = .load ⟨21 + j.val, by omega⟩) ∧
    ∀ v', storeValue 16 (s.x (nrReg j.val)) = .ok v' →
      ∃ a, e = ⟨s.site.pc, .wr a v'.toBytes⟩ := by
  refine ⟨store_pred hpre hX hg hσ0 hin hσ hI hs, fun v' hv' => ?_⟩
  obtain ⟨pos, hr, -, -, hev⟩ := event_at hpre hX hg he hσ hI
  obtain ⟨u, rfl⟩ := pos_of_store hr hs
  rcases hev with ⟨v0, hv0, rfl⟩ | ⟨f, hf, -⟩
  · obtain rfl : v0 = v' := Except.ok.inj (hv0.symm.trans hv')
    exact ⟨_, by rw [hr.site]⟩
  · rw [hv'] at hf
    cases hf

/-! ### Undefined behaviour, and the counts the phase does not change -/

/-- **An undefined-behaviour event of the phase** is the event of a store whose register does
not convert to 16 bits (a data fault: the value layer excludes it). Loads, fences and barriers
of the phase are never undefined behaviour. -/
theorem ub_conversion {k0 k pc : Nat} {f : Fault} {s : D}
    (he : X.get (g, k) = some ⟨pc, .ub f⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    ∃ j : Fin 10, s.site = .store ⟨j.val, by omega⟩ ∧
      storeValue 16 (s.x (nrReg j.val)) = .error f := by
  obtain ⟨pos, hr, -, -, hev⟩ := event_at hpre hX hg he hσ hI
  cases pos with
  | fence => cases hev
  | ld j u =>
    obtain ⟨bs, -, h⟩ := hev
    cases h
  | st j u =>
    rcases hev with ⟨v', -, h⟩ | ⟨f', hf, h⟩
    · cases h
    · cases h
      exact ⟨j, hr.site, hf⟩
  | bar j => cases hev

/-- **Count transport through the phase**: a class of events that contains none of the kinds
of the phase's events (reads, writes, the proxy fence, `bar.sync 0`, undefined behaviour) has
the same count before any followed state of the phase, up to the exit, as at the entry. -/
theorem count_conversion (c : Event → Bool) (hc : ∀ e, PhaseKind e → c e = false)
    {k0 k : Nat} {s0 s : D} (hσ0 : Frame.stateAt (code L) X g k0 = some (some s0))
    (hin : In P X g k0 s0) (hk0 : k0 ≤ k) (hkl : k ≤ k0 + len g)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c := by
  refine countP_take_eq c hk0 fun i e hji hik he => ?_
  obtain ⟨d, hσi⟩ := followed_of_le hσ (show i ≤ k by omega)
  have hlen : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases conversion_inv hpre hX hg hσ0 hin hji hlen hσi with hI | ⟨hle, -⟩
  · obtain ⟨pos, -, -, -, hev⟩ := event_at hpre hX hg he hσi hI
    exact hc e hev.phaseKind
  · omega

/-! ### Coverage: a thread that left the phase has converted all its elements -/

/-- **The events of a thread that left the phase.** For a thread that entered the phase before
its event `k0` and has left it, and for each `i` below the number of its elements: event
`k0 + 1 + 2 i` is the read of the four bytes at the swizzled address of its `i`-th element, and
event `k0 + 2 + 2 i` is the write of the two bytes of that element's slot of `state_acc`.
(With `slot_cover`: every slot of the block has a write by its owner before the owner's fourth
`bar.sync 0`.) -/
theorem conv_cover {k0 k : Nat} {s0 : D}
    (hσ0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0)
    (hleft : Left P X g L k0 k) (hk : k < (X.tr g).length) {i : Nat} (hi : i < 2 * pairs g) :
    (∃ pc bs, X.get (g, k0 + (1 + 2 * i)) = some ⟨pc,
      .rd { loc := ⟨.shared, cta g, rdAddr P (slotOf g i)⟩, size := 4 } bs⟩) ∧
    ∃ pc bs, X.get (g, k0 + (2 + 2 * i)) = some ⟨pc,
      .wr { loc := ⟨.shared, cta g, wrAddr P (slotOf g i)⟩, size := 2 } bs⟩ := by
  obtain ⟨hle, s1, hσ1, -⟩ := hleft
  have key : ∀ n, n < len g → ∃ d e, Frame.stateAt (code L) X g (k0 + n) = some (some d) ∧
      X.get (g, k0 + n) = some e ∧ Inv P X g k0 (k0 + n) d := by
    intro n hn
    obtain ⟨d, hd⟩ := followed_of_le hσ1 (show k0 + n ≤ k0 + len g by omega)
    have hl : k0 + n < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0 + n]? = some e := ⟨_, List.getElem?_eq_getElem hl⟩
    rcases conversion_inv hpre hX hg hσ0 hin (Nat.le_add_right _ _) hl hd with hI | ⟨h, -⟩
    · exact ⟨d, e, hd, he, hI⟩
    · omega
  have hlen : len g = 3 + 4 * pairs g := rfl
  constructor
  · obtain ⟨d, e, hd, he, hI⟩ := key (1 + 2 * i) (by omega)
    obtain ⟨pos, hr, -, hdone, hev⟩ := event_at hpre hX hg he hd hI
    cases pos with
    | fence => simp only [done] at hdone; omega
    | ld j u =>
      simp only [done] at hdone
      obtain ⟨bs, -, rfl⟩ := hev
      have hix : elemIx j.val u = i := by omega
      rw [hix] at he
      exact ⟨_, bs, he⟩
    | st j u => simp only [done] at hdone; omega
    | bar j => simp only [done] at hdone; omega
  · obtain ⟨d, e, hd, he, hI⟩ := key (2 + 2 * i) (by omega)
    obtain ⟨pos, hr, -, hdone, hev⟩ := event_at hpre hX hg he hd hI
    cases pos with
    | fence => simp only [done] at hdone; omega
    | ld j u => simp only [done] at hdone; omega
    | st j u =>
      simp only [done] at hdone
      have hix : elemIx j.val u = i := by omega
      rcases hev with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩
      · rw [hix] at he
        exact ⟨_, _, he⟩
      · exfalso
        obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k0 + (2 + 2 * i) + 1]? = some e' :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have := ub_last hX he he'
        omega
    | bar j =>
      have := j.isLt
      simp only [done] at hdone
      omega

/-! ### Progress and the bound -/

/-- **`RefProgress.barStep` for the two barriers of the phase** (instructions 620 and 621): a
barrier event is a `bar.sync 0`, fired at sub-step 0, and the next state is at a later
instruction. -/
theorem barStep_conversion {k0 k pc bid : Nat} {cnt : Option Nat} {m : BarMode} {s s' : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (he : X.get (g, k) = some ⟨pc, .bar bid cnt m⟩)
    (hσ' : Frame.stateAt (code L) X g (k + 1) = some (some s')) :
    s.site.sub = 0 ∧ s.site.pc < s'.site.pc ∧ bid = 0 := by
  obtain ⟨pos, hr, -, -, hev⟩ := event_at hpre hX hg he hσ hI
  obtain ⟨j, rfl⟩ := hev.bar
  have hid : bid = 0 := by
    cases hev
    rfl
  have hn : Thread.next L g s ⟨pc, .bar bid cnt m⟩ = some (some s') := by
    rw [Frame.stateAt_succ he, hσ] at hσ'
    exact hσ'
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = (Pos.bar j).site := hr.site
  fin_cases j
  · have h1 := (Thread.next_bar_3 w p x _).symm.trans hn
    obtain rfl := Option.some.inj (Option.some.inj h1)
    exact ⟨rfl, (show (Site.bar 3).pc < (Site.bar 4).pc by decide), hid⟩
  · obtain ⟨d0, h1, hE⟩ := st_bar_1 hpre hg hr
    have h2 := ((Thread.next_bar_4 w p x _).symm.trans hn).symm.trans h1
    obtain rfl := Option.some.inj (Option.some.inj h2)
    refine ⟨rfl, ?_, hid⟩
    rw [hE.site]
    split_ifs
    · exact (show (Site.bar 4).pc < (Site.load 31).pc by decide)
    · exact (show (Site.bar 4).pc < (Site.fenceProxy 1).pc by decide)

end

/-! ### The events of the phase behind and ahead of a state, as functions of the state -/

/-- **`RefProgress.bar0` for the Conversion phase**: the number of `bar.sync 0` before a state
is the number of `bar.sync 0` instructions before its instruction. -/
theorem bar0_conversion {k0 k : Nat} {s : D} (hI : Inv P X g k0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨pos, hr, hl, -⟩ := hI
  have h1 : ((X.tr g).take k).countP (Execution.isBarId 0) = (led g pos).bars :=
    congrArg Startup.Led.bars hl
  rw [h1, hr.site]
  cases pos with
  | fence => rfl
  | ld j u => fin_cases j <;> rfl
  | st j u => fin_cases j <;> rfl
  | bar j => fin_cases j <;> rfl

/-- The ordinal of the first pair of the current round, read off the pair-index register
`%r1795`. -/
def uOf (g : Nat) (d : D) : Nat := ((d.w 2101).toNat - warp g) / 6

/-- **The number of events of the phase behind a state**, as a function of the state (its site
and, at a load or a store, the pair-index register). -/
def doneOf (g : Nat) (d : D) : Nat :=
  match d.site with
  | .load j => 1 + 2 * elemIx (j.val - 21) (uOf g d)
  | .store j => 2 + 2 * elemIx j.val (uOf g d)
  | .bar j => 1 + 4 * pairs g + (j.val - 3)
  | _ => 0

/-- **The number of events of the phase ahead of a state** (to the phase's exit). -/
def leftOf (g : Nat) (d : D) : Nat := len g - doneOf g d

theorem ld_idx {j : Fin 10} {u : Nat} {d : D} (h : AtPos P g (.ld j u) d) :
    d.w 2101 = W (pairIx g u) := by
  fin_cases j <;> first | exact h.2.1.2.2.2 | exact h.2.1.2

theorem st_idx {j : Fin 10} {u : Nat} {d : D} (h : AtPos P g (.st j u) d) :
    d.w 2101 = W (pairIx g u) := by
  fin_cases j <;> first | exact h.2.1.2.2.2 | exact h.2.1.2

theorem uOf_eq {u : Nat} {d : D} (hw : d.w 2101 = W (pairIx g u)) (hu : u < 2 ^ 32) :
    uOf g d = u := by
  have hwp := warp_lt g
  unfold uOf
  rw [hw, toNat_W (by unfold pairIx; omega)]
  unfold pairIx
  omega

/-- At a state of the invariant the function of the state is the position's count. -/
theorem doneOf_eq {pos : Pos} {d : D} (hr : RefAt P g pos d) : doneOf g d = done g pos := by
  unfold doneOf
  rw [hr.site]
  cases pos with
  | fence => rfl
  | ld j u =>
    have hlt := round_lt j.isLt (ld_round hr.pos)
    have hu := uOf_eq (ld_idx hr.pos) (by unfold pairs head at hlt; split_ifs at hlt <;> omega)
    show 1 + 2 * elemIx (21 + j.val - 21) (uOf g d) = 1 + 2 * elemIx j.val u
    rw [Nat.add_sub_cancel_left, hu]
  | st j u =>
    have hlt := round_lt j.isLt (st_round hr.pos)
    have hu := uOf_eq (st_idx hr.pos) (by unfold pairs head at hlt; split_ifs at hlt <;> omega)
    show 2 + 2 * elemIx j.val (uOf g d) = 2 + 2 * elemIx j.val u
    rw [hu]
  | bar j =>
    show 1 + 4 * pairs g + (3 + j.val - 3) = 1 + 4 * pairs g + j.val
    rw [Nat.add_sub_cancel_left]

theorem done_lt {pos : Pos} {d : D} (hr : RefAt P g pos d) : done g pos < len g := by
  cases pos with
  | fence => simp only [done, len]; omega
  | ld j u =>
    have := elemIx_lt j.isLt (ld_round hr.pos)
    simp only [done, len]
    omega
  | st j u =>
    have := elemIx_lt j.isLt (st_round hr.pos)
    simp only [done, len]
    omega
  | bar j =>
    have := j.isLt
    simp only [done, len]
    omega

/-- **The position in the phase is a function of the state**: a state of the invariant before
event `k` has `doneOf g d` events of the phase behind it, fewer than the phase has. -/
theorem done_state {k0 k : Nat} {d : D} (hI : Inv P X g k0 k d) :
    k = k0 + doneOf g d ∧ doneOf g d < len g := by
  obtain ⟨pos, hr, -, hd, -⟩ := hI
  rw [doneOf_eq hr]
  exact ⟨hd, done_lt hr⟩

/-- **`RefProgress.left_dec` for the Conversion phase**: a step from a state of the invariant
leads to a state of the invariant with one event less ahead, or to the exit of the phase from
a state with one event ahead. -/
theorem left_dec_conversion (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) {k0 k : Nat}
    {s s' : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hn : Thread.next L g s e = some (some s')) :
    (Inv P X g k0 (k + 1) s' ∧ leftOf g s' + 1 = leftOf g s) ∨
      (k + 1 = k0 + len g ∧ Out P X g (k + 1) s' ∧ leftOf g s = 1) := by
  obtain ⟨h1, h2⟩ := done_state hI
  rcases (conversion_next hpre hX hg he hσ hI hn).2 with hI' | ⟨hk, hout⟩
  · obtain ⟨h3, h4⟩ := done_state hI'
    refine .inl ⟨hI', ?_⟩
    unfold leftOf
    omega
  · refine .inr ⟨hk, hout, ?_⟩
    unfold leftOf
    omega

/-! ### One owner per slot -/

/-- **`StateAccFacts.owner` for the Conversion phase**: two accesses of one byte of
`state_acc`, each at a state of the invariant of its thread, belong to one thread (an element
has one converting thread, `convOwner`). -/
theorem stateAcc_owner (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {h : Nat} (hg : g < L.threads) (hh : h < L.threads) {k0 k k0' k' c : Nat} {s s' : D}
    {a b : Acc} {w w' : Bool} {l : PTX.Loc}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hσ' : Frame.stateAt (code L) X h k' = some (some s')) (hI' : Inv P X h k0' k' s')
    (ha : X.Access (g, k) a w) (hb : X.Access (h, k') b w') (hca : a.Covers l)
    (hcb : b.Covers l) (hl : InStateAcc L c l) : g = h := by
  obtain ⟨-, -, -, -, el, hel, ho, rfl⟩ := stateAcc_phase hpre hX hg hσ hI ha hca hl
  obtain ⟨-, -, -, -, el', hel', ho', rfl⟩ := stateAcc_phase hpre hX hh hσ' hI' hb hcb hl
  obtain ⟨-, a2, a3, a4⟩ := hca
  obtain ⟨-, b2, b3, b4⟩ := hcb
  simp only [wrAddr] at a3 a4 b3 b4
  have he : el = el' := by omega
  subst he
  have hc : cta g = cta h := a2.symm.trans b2
  have ht : tid g = tid h := ho.symm.trans ho'
  unfold cta at hc
  unfold tid at ht
  omega

/-! ### Classes of events the phase does not make

For `count_conversion`: the phase makes no successful poll, no arrival on an mbarrier, no
tensor load issue, no matrix event, no arrival at a named barrier other than barrier 0, no
tensor store, no group commit and no shuffle. -/

theorem class_okPoll (m : PTX.Loc) : ∀ e, PhaseKind e → okPoll m e = false := by phase_class

theorem class_arrivesOn (m : PTX.Loc) : ∀ e, PhaseKind e → arrivesOn m e = false := by
  phase_class

theorem class_issuesTo (m : PTX.Loc) : ∀ e, PhaseKind e → issuesTo m e = false := by
  phase_class

theorem class_isMatrix : ∀ e, PhaseKind e → isMatrix e = false := by phase_class

theorem class_isBar8 : ∀ e, PhaseKind e → Execution.isBarId 8 e = false := by phase_class

theorem class_isTensorStore : ∀ e, PhaseKind e → isTensorStore e = false := by phase_class

theorem class_isCommit : ∀ e, PhaseKind e → isCommit e = false := by phase_class

theorem class_isShfl : ∀ e, PhaseKind e → Execution.isShfl e = false := by phase_class

/-- The swizzle of this phase is the reference layer's `swzAbs` (and the value layer's
`swzAddr`), by definition. -/
theorem swzN_eq_swzAbs : swzN = Ref.swzAbs := rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
