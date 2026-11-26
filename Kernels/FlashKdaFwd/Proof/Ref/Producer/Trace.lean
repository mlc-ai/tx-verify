-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.LoadsA
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.LoadsB
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.LoadsC
public import Kernels.FlashKdaFwd.Proof.Thread.Sound

@[expose] public section

/-! # The reference invariant of the Producer phase along a thread of the load warp

`producer_inv`: in a consistent execution, let a thread of the load warp be at the phase's entry
before its event `k0` (the state at `bar_5` with the entry facts and the entry ledger:
`Entry`, `ledEntry` of `Interface.lean`). Then before each of its later events the state of its
machine satisfies the invariant of the phase (`Inv`: a position, its register facts, its
ledger), or the thread has left the phase through its exit (`Out` held at an earlier position:
the state at `bar_7` with the exit facts and the exit ledger).

`producer_good`: at a state of the invariant, the event the thread fires is the closed-form
event of the position (`Ev`), the machine has a successor state for it, and that state is a
successor of the position. So in this phase the machine never stops following a thread
(`producer_followed`) and never declares it dead: no control transition of the phase is dead,
and no breakpoint site is reached (the successor of a position is a position or the exit, and no
position is at a breakpoint).

Hypotheses, stated exactly: `hpre : Pre P L mem0` (the launch facts and ranges; with it the
generated machine is sound, `Thread.sound`, which gives the concrete state and the firing fact
of each event; tracking is not assumed); consistency `hX`; `hg : g < L.threads`;
`hw : warp g = 4` (the thread is in the load warp). No hypothesis about returned values is
needed in this phase: it has no election and no shuffle, and the flags of the lane-0 check come
from the entry.

The proof is one step per position (`good_at`: the case analysis over the positions; the 210
load positions are in the generated files `LoadsA.lean`, `LoadsB.lean`, `LoadsC.lean`) and the
induction along the trace (`phase_from`, the variant of `phase_inv` of `Ref/Lib.lean` that
starts at a given trace position). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-! ### The induction of a phase that starts at a given trace position -/

/-- **A phase invariant from a trace position on.** If the invariant `I` holds for the state
before event `k0`, and every step from a state with `I` leads to a state with `I` or to the
exit condition `E`, then before every later event `I` holds or `E` held at an earlier
position. -/
theorem phase_from {K : Kernel} {A : List Assumption} {C : (g : Nat) → Flow.Code K A L g}
    (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
    (I E : Nat → (C g).D → Prop) {k0 : Nat} {s0 : (C g).D}
    (h0 : Frame.stateAt C X g k0 = some (some s0)) (hI0 : I k0 s0)
    (hs : ∀ (k : Nat) (e : Event) (s s' : (C g).D) (t : TState) (ins : Instr)
      (o : Option TState), X.get (g, k) = some e → Frame.stateAt C X g k = some (some s) →
      I k s → (C g).AtD s t → K.code[(C g).pc s]? = some ins →
      Fires ((C g).pc s) (eventTmpl A L g t ins.op) e o → (∀ pc f, e ≠ ⟨pc, .ub f⟩) →
      (C g).next s e = some (some s') → I (k + 1) s' ∨ E (k + 1) s') :
    ∀ k s, k0 ≤ k → k < (X.tr g).length → Frame.stateAt C X g k = some (some s) →
      I k s ∨ ∃ j ≤ k, ∃ s1, Frame.stateAt C X g j = some (some s1) ∧ E j s1 := by
  have key := phase_inv (C := C) (X := X) (g := g) hC hX (fun k s => k < k0 ∨ I k s) E
    (by
      rcases Nat.eq_zero_or_pos k0 with rfl | hpos
      · rw [Frame.stateAt_zero] at h0
        obtain rfl := Option.some.inj (Option.some.inj h0)
        exact .inr hI0
      · exact .inl hpos)
    (by
      intro k e s s' t ins o he hσ hI hat hc hf hub hn
      rcases hI with hlt | hI
      · rcases Nat.lt_or_ge (k + 1) k0 with h1 | h1
        · exact .inl (.inl h1)
        · have hk : k + 1 = k0 := by omega
          have hσ' : Frame.stateAt C X g (k + 1) = some (some s') := by
            rw [Frame.stateAt_succ he, hσ]
            exact hn
          rw [hk, h0] at hσ'
          obtain rfl := Option.some.inj (Option.some.inj hσ')
          exact .inl (.inr (hk ▸ hI0))
      · rcases hs k e s s' t ins o he hσ hI hat hc hf hub hn with h | h
        · exact .inl (.inr h)
        · exact .inr h)
  intro k s hk0 hk hσ
  rcases key k s hk hσ with (hlt | hI) | hE
  · omega
  · exact .inl hI
  · exact .inr hE

/-! ### One step from every position -/

/-- **Every position of the phase is good for the event fired at it.** -/
theorem good_at (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warp g = 4) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩) (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t)
    (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g pos w p x e := by
  cases pos with
  | entry => exact good_entry hpre hg hw h hc hf
  | poll c u =>
    fin_cases c
    · exact good_poll0 hpre h hat hc hf
    · exact good_poll1 hpre h hat hc hf
    · exact good_poll2 hpre h hat hc hf
  | arrive c u =>
    fin_cases c
    · exact good_arrive0 hpre hg h hat hc hf
    · exact good_arrive1 hpre hg h hat hc hf
    · exact good_arrive2 hpre hg h hat hc hf
  | load c u i =>
    fin_cases c
    · exact good_loadA hpre hg u i h hat hc hf
    · exact good_loadB hpre hg u i h hat hc hf
    · exact good_loadC hpre hg u i h hat hc hf
  | tail j =>
    fin_cases j
    · exact good_tail0 hpre h hat hc hf
    · exact good_tail1 hpre h hat hc hf
    · exact good_tail2 hpre h hat hc hf

/-- One more event in the ledger of a prefix. -/
theorem ledOf_succ {k : Nat} (he : X.get (g, k) = some e) :
    ledOf L (g / L.block) ((X.tr g).take (k + 1)) =
      ledOf L (g / L.block) ((X.tr g).take k) + ledEv L (g / L.block) e := by
  simp only [ledOf, ledEv, Led.add_def, okPolls, arrivals, count_snoc _ he]

/-- The thread machine of every launched thread is sound under the precondition. -/
theorem machineSound (hpre : Pre P L mem0) : ∀ g < L.threads, (code L g).Sound :=
  fun _ hg => Thread.sound hpre hg

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) (hw : warp g = 4)
include hpre hX hg hw

/-- **An event at a state of the invariant**: the position is good for it. -/
theorem producer_good {k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g k s) :
    ∃ pos w p x, s = ⟨pos.site, w, p, x⟩ ∧ RefAt P g pos s ∧
      ledOf L (g / L.block) ((X.tr g).take k) = led P g pos ∧ Good P L g pos w p x e := by
  obtain ⟨pos, hr, hl⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (machineSound hpre) hX he hσ
  exact ⟨pos, w, p, x, rfl, hr, hl, good_at hpre hg hw pos hr hat hc hf⟩

/-- The step of the induction. -/
theorem inv_step {k : Nat} {s s' : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g k s)
    (hn : Thread.next L g s e = some (some s')) :
    Inv P L X g (k + 1) s' ∨ Out P L X g (k + 1) s' := by
  obtain ⟨pos, w, p, x, rfl, hr, hl, -, d', hd', hsucc⟩ :=
    producer_good hpre hX hg hw he hσ hI
  rw [hd'] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  rcases hsucc with ⟨pos', h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨pos', h1, by rw [ledOf_succ he, hl, h2]⟩
  · exact .inr ⟨h1, by rw [ledOf_succ he, hl, h2]⟩

/-- **The reference invariant of the Producer phase.** From the entry before event `k0`: before
each later event of the thread the state of its machine is at a position of the phase with the
position's register facts and ledger, or the thread has left the phase through its exit. -/
theorem producer_inv {k0 : Nat} {s0 : D}
    (h0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hE : Entry P g s0)
    (hL0 : ledOf L (g / L.block) ((X.tr g).take k0) = ledEntry g)
    {k : Nat} {s : D} (hk0 : k0 ≤ k) (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P L X g k s ∨ ∃ j ≤ k, ∃ s1, Frame.stateAt (code L) X g j = some (some s1) ∧
      Out P L X g j s1 := by
  have hI0 : Inv P L X g k0 s0 :=
    ⟨.entry, ⟨hE.site, hE.tid, hE.p85, hE.p86, hE.p87, hE.p88, hE.scan, hE.elected⟩, hL0⟩
  refine phase_from (C := code L) (machineSound hpre) hX (Inv P L X g) (Out P L X g) h0 hI0 ?_
    k s hk0 hk hσ
  intro k e s s' t ins o he hσ hI _ _ _ _ hn
  exact inv_step hpre hX hg hw he hσ hI hn

/-- **The machine follows the thread through the Producer phase**: at a state of the invariant
the successor along the thread's event is a state. -/
theorem producer_followed {k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g k s) :
    ∃ s', Thread.next L g s e = some (some s') := by
  obtain ⟨pos, w, p, x, rfl, -, -, -, d', hd', -⟩ :=
    producer_good hpre hX hg hw he hσ hI
  exact ⟨d', hd'⟩

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
