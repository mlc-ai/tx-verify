-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Shapes
public import Kernels.FlashKdaFwd.Proof.Ref.Chain

@[expose] public section

/-! # The reference invariant of the Conversion phase along every thread

`conversion_inv`: in a consistent execution, for a launched thread whose startup phase ended
before its event `k0` (`In`: the startup's exit condition `Startup.Out` at `k0`), the state of
the thread's machine before each later event `k` satisfies the invariant of the Conversion
phase (`Inv P X g k0 k`: a position, its registers and pointer slots, the ledger, `k = k0 +`
the number of events of the position, and at a store the link to its load), or the thread has
left the phase (`Left`: the exit condition `Out` held at event `k0 + len g`).

`conversion_ok`: at a state of the invariant, under the **data condition** of the event
(`DataOk`), the event is not undefined behaviour and the machine's successor is a state (the
thread is not dead, the machine does not give up). The data condition is what the value layer
owes: at a load, the four bytes read have a value (`ldVal`) that `cvt.rn.bf16.f32` narrows
without a fault; at a store, the narrowed value converts to 16 bits (`storeValue`). Everything
else is proved here: addresses in range and aligned, every pointer condition, the clearing
run.

Hypotheses: the precondition `Pre`, consistency, the thread is launched. The soundness of the
machine is `Thread.sound`; tracking is not assumed.

The file ends with the phase in the form of `Ref/Chain.lean` (`phase`, `traces`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-! ### The machine's successor at the ten loads, in the form `ldNext` -/

theorem next_ld_0 : Thread.next L g ⟨.load 21, w, p, x⟩ e = ldNext e
    (fun v => Run.r427_cond (valueOf ⟨.load 21, w, p, valueEx x [(539, v)]⟩))
    (fun v => after_load_21 L g ⟨.load 21, w, p, x⟩ v) := rfl

theorem next_ld_1 : Thread.next L g ⟨.load 22, w, p, x⟩ e = ldNext e
    (fun v => Run.r444_cond (valueOf ⟨.load 22, w, p, valueEx x [(540, v)]⟩))
    (fun v => after_load_22 L g ⟨.load 22, w, p, x⟩ v) := rfl

theorem next_ld_2 : Thread.next L g ⟨.load 23, w, p, x⟩ e = ldNext e
    (fun v => Run.r474_cond (valueOf ⟨.load 23, w, p, valueEx x [(564, v)]⟩))
    (fun v => after_load_23 L g ⟨.load 23, w, p, x⟩ v) := rfl

theorem next_ld_3 : Thread.next L g ⟨.load 24, w, p, x⟩ e = ldNext e
    (fun v => Run.r491_cond (valueOf ⟨.load 24, w, p, valueEx x [(565, v)]⟩))
    (fun v => after_load_24 L g ⟨.load 24, w, p, x⟩ v) := rfl

theorem next_ld_4 : Thread.next L g ⟨.load 25, w, p, x⟩ e = ldNext e
    (fun v => Run.r514_cond (valueOf ⟨.load 25, w, p, valueEx x [(566, v)]⟩))
    (fun v => after_load_25 L g ⟨.load 25, w, p, x⟩ v) := rfl

theorem next_ld_5 : Thread.next L g ⟨.load 26, w, p, x⟩ e = ldNext e
    (fun v => Run.r531_cond (valueOf ⟨.load 26, w, p, valueEx x [(567, v)]⟩))
    (fun v => after_load_26 L g ⟨.load 26, w, p, x⟩ v) := rfl

theorem next_ld_6 : Thread.next L g ⟨.load 27, w, p, x⟩ e = ldNext e
    (fun v => Run.r554_cond (valueOf ⟨.load 27, w, p, valueEx x [(568, v)]⟩))
    (fun v => after_load_27 L g ⟨.load 27, w, p, x⟩ v) := rfl

theorem next_ld_7 : Thread.next L g ⟨.load 28, w, p, x⟩ e = ldNext e
    (fun v => Run.r571_cond (valueOf ⟨.load 28, w, p, valueEx x [(569, v)]⟩))
    (fun v => after_load_28 L g ⟨.load 28, w, p, x⟩ v) := rfl

theorem next_ld_8 : Thread.next L g ⟨.load 29, w, p, x⟩ e = ldNext e
    (fun v => Run.r594_cond (valueOf ⟨.load 29, w, p, valueEx x [(570, v)]⟩))
    (fun v => after_load_29 L g ⟨.load 29, w, p, x⟩ v) := rfl

theorem next_ld_9 : Thread.next L g ⟨.load 30, w, p, x⟩ e = ldNext e
    (fun v => Run.r611_cond (valueOf ⟨.load 30, w, p, valueEx x [(571, v)]⟩))
    (fun v => after_load_30 L g ⟨.load 30, w, p, x⟩ v) := rfl

/-! ### One step -/

/-- **One step from a position** along the event `e` of trace position `k`: the successor is
at a position of the phase, with the ledger advanced by the event, one more event behind it
and, at a store, the link to the load; or it is the exit. -/
def Step (P : Params) (X : Execution) (g k : Nat) (pos : Pos) (e : Event) (d' : D) : Prop :=
  (∃ pos', RefAt P g pos' d' ∧ led g pos' = led g pos + Startup.ledEv e ∧
    done g pos' = done g pos + 1 ∧ (X.get (g, k) = some e → Link P X g (k + 1) pos' d')) ∨
  (Exit P g d' ∧ ledExit g = led g pos + Startup.ledEv e ∧ len g = done g pos + 1)

/-- **The data condition of the event `e` at a state `d`** of the phase: the bytes a load
returns have a value that `cvt.rn.bf16.f32` narrows without a fault, and the narrowed value
that a store writes converts to 16 bits. The value layer proves it; the reference layer needs
it only to say that the thread goes on. -/
def DataOk (d : D) (e : Event) : Prop :=
  (∀ a bs, e.kind = .rd a bs → ∃ v y, ldVal .same 32 bs = .ok v ∧ Rules.narrowE [v] = .ok y) ∧
  ∀ j : Fin 10, d.site = (Pos.st j 0).site → ∃ v', storeValue 16 (d.x (nrReg j.val)) = .ok v'

/-- A position that is no store has no link. -/
theorem link_of_ne {pos : Pos} {d : D} {k : Nat} (h : ∀ j u, pos ≠ .st j u) :
    Link P X g k pos d := by
  cases pos with
  | st j u => exact absurd rfl (h j u)
  | _ => trivial

variable {k : Nat} {pos : Pos} {d' : D}

/-- A step at a site whose successor does not depend on the event. -/
theorem step_of_succ {oo : Option (Option D)} {δ : Startup.Led}
    (hnx : Thread.next L g ⟨pos.site, w, p, x⟩ e = oo)
    (hs : ∃ d0, oo = some (some d0) ∧ Succ P g pos δ d0) (hδ : Startup.ledEv e = δ)
    (hn : Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d')) : Step P X g k pos e d' := by
  obtain ⟨d0, h1, pos', h2, h3, h4, h5⟩ := hs
  rw [hnx, h1] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  exact .inl ⟨pos', h2, by rw [h3, hδ], h4, fun _ => link_of_ne h5⟩

/-- A step at a load: the successor is the store of the same element, with its link. -/
theorem step_of_ld {j : Fin 10} {u : Nat} {c : Value → Prop} {f : Value → D}
    (hnx : Thread.next L g ⟨(Pos.ld j u).site, w, p, x⟩ e = ldNext e c f)
    (hev : Ev P g (.ld j u) ⟨(Pos.ld j u).site, w, p, x⟩ e)
    (hc : ∀ v, c v → ∃ y, Rules.narrowE [v] = .ok y)
    (hst : ∀ v, RefAt P g (.st j u) (f v) ∧
      (f v).x (nrReg j.val) = okVal (.bits 32 0) (Rules.narrowE [v]))
    (hn : Thread.next L g ⟨(Pos.ld j u).site, w, p, x⟩ e = some (some d')) :
    Step P X g k (.ld j u) e d' := by
  rw [hnx] at hn
  obtain ⟨a, bs, v, hk, hv, hcv, rfl⟩ := ldNext_some hn
  obtain ⟨y, hy⟩ := hc v hcv
  obtain ⟨bs', -, rfl⟩ := hev
  obtain rfl : bs' = bs := by
    simp only [Kind.rd.injEq] at hk
    exact hk.2
  refine .inl ⟨.st j u, (hst v).1, rfl, by simp only [done]; omega, fun he => ?_⟩
  exact ⟨bs', v, y, Nat.succ_pos k, he, hv, hy, (hst v).2.trans (okVal_of_ok hy)⟩

theorem ledEv_wr {j : Fin 10} {u : Nat} {d : D} (hev : Ev P g (.st j u) d e) :
    Startup.ledEv e = led0 := by
  rcases hev with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩ <;> rfl

set_option maxRecDepth 8000 in
/-- **Every position of the phase keeps the invariant**: the machine's successor along the
event fired at a state of the invariant is a step of the phase. -/
theorem good_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩) (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t)
    (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hn : Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d')) :
    Step P X g k pos e d' := by
  have hev := ev_at hpre hg pos h hat hc hf
  cases pos with
  | fence =>
    exact step_of_succ (Thread.next_fenceProxy_0 w p x _) (st_fence hpre hg h)
      (by rw [show e = _ from hev]; rfl) hn
  | ld j u =>
    fin_cases j
    · exact step_of_ld next_ld_0 hev (fun v hv => hv.1) (fun v => st_ld_0 hpre v h) hn
    · exact step_of_ld next_ld_1 hev (fun v hv => hv.1) (fun v => st_ld_1 hpre v h) hn
    · exact step_of_ld next_ld_2 hev (fun v hv => hv.1) (fun v => st_ld_2 hpre v h) hn
    · exact step_of_ld next_ld_3 hev (fun v hv => hv.1) (fun v => st_ld_3 hpre v h) hn
    · exact step_of_ld next_ld_4 hev (fun v hv => hv.1) (fun v => st_ld_4 hpre v h) hn
    · exact step_of_ld next_ld_5 hev (fun v hv => hv.1) (fun v => st_ld_5 hpre v h) hn
    · exact step_of_ld next_ld_6 hev (fun v hv => hv.1) (fun v => st_ld_6 hpre v h) hn
    · exact step_of_ld next_ld_7 hev (fun v hv => hv.1) (fun v => st_ld_7 hpre v h) hn
    · exact step_of_ld next_ld_8 hev (fun v hv => hv.1) (fun v => st_ld_8 hpre v h) hn
    · exact step_of_ld next_ld_9 hev (fun v hv => hv.1) (fun v => st_ld_9 hpre v h) hn
  | st j u =>
    have hδ := ledEv_wr hev
    fin_cases j
    · exact step_of_succ (Thread.next_store_0 w p x _) (st_st_0 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_1 w p x _) (st_st_1 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_2 w p x _) (st_st_2 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_3 w p x _) (st_st_3 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_4 w p x _) (st_st_4 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_5 w p x _) (st_st_5 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_6 w p x _) (st_st_6 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_7 w p x _) (st_st_7 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_8 w p x _) (st_st_8 hpre hg h) hδ hn
    · exact step_of_succ (Thread.next_store_9 w p x _) (st_st_9 hpre hg h) hδ hn
  | bar j =>
    fin_cases j
    · exact step_of_succ (Thread.next_bar_3 w p x _) ⟨_, rfl, st_bar_0 h⟩
        (by rw [show e = _ from hev]; rfl) hn
    · obtain ⟨d0, h1, hE⟩ := st_bar_1 hpre hg h
      have hn' := ((Thread.next_bar_4 w p x e).symm.trans hn).symm.trans h1
      obtain rfl := Option.some.inj (Option.some.inj hn')
      refine .inr ⟨hE, by rw [show e = _ from hev]; rfl, ?_⟩
      simp only [len, done, finVal]
      omega

set_option maxRecDepth 8000 in
/-- **Under the data condition the thread goes on**: the event is not undefined behaviour and
the machine's successor is a state. -/
theorem ok_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩) (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t)
    (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hdata : DataOk ⟨pos.site, w, p, x⟩ e) :
    (∀ pc f, e ≠ ⟨pc, .ub f⟩) ∧ ∃ d', Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d') := by
  have hev := ev_at hpre hg pos h hat hc hf
  cases pos with
  | fence =>
    obtain ⟨d0, h1, -⟩ := st_fence hpre hg h
    refine ⟨(by rw [show e = _ from hev]; intro _ _ h'; cases h'), d0, ?_⟩
    exact (Thread.next_fenceProxy_0 w p x e).trans h1
  | ld j u =>
    obtain ⟨bs, -, rfl⟩ := hev
    obtain ⟨v, y, hv, hy⟩ := hdata.1 _ bs rfl
    refine ⟨(fun _ _ h' => by cases h'), ?_⟩
    fin_cases j
    · exact ⟨_, next_ld_0.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_1.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_2.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_3.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_4.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_5.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_6.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_7.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_8.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
    · exact ⟨_, next_ld_9.trans (ldNext_ok rfl hv ⟨⟨y, hy⟩, trivial⟩)⟩
  | st j u =>
    obtain ⟨v', hv'⟩ := hdata.2 j rfl
    have hnu : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
      rcases hev with ⟨v0, -, rfl⟩ | ⟨f, hf', -⟩
      · intro _ _ h'; cases h'
      · rw [hv'] at hf'; cases hf'
    refine ⟨hnu, ?_⟩
    fin_cases j
    · obtain ⟨d0, h1, -⟩ := st_st_0 hpre hg h
      exact ⟨d0, (Thread.next_store_0 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_1 hpre hg h
      exact ⟨d0, (Thread.next_store_1 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_2 hpre hg h
      exact ⟨d0, (Thread.next_store_2 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_3 hpre hg h
      exact ⟨d0, (Thread.next_store_3 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_4 hpre hg h
      exact ⟨d0, (Thread.next_store_4 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_5 hpre hg h
      exact ⟨d0, (Thread.next_store_5 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_6 hpre hg h
      exact ⟨d0, (Thread.next_store_6 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_7 hpre hg h
      exact ⟨d0, (Thread.next_store_7 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_8 hpre hg h
      exact ⟨d0, (Thread.next_store_8 w p x _).trans h1⟩
    · obtain ⟨d0, h1, -⟩ := st_st_9 hpre hg h
      exact ⟨d0, (Thread.next_store_9 w p x _).trans h1⟩
  | bar j =>
    refine ⟨(by rw [show e = _ from hev]; intro _ _ h'; cases h'), ?_⟩
    fin_cases j
    · exact ⟨_, Thread.next_bar_3 w p x _⟩
    · obtain ⟨d0, h1, -⟩ := st_bar_1 hpre hg h
      exact ⟨d0, (Thread.next_bar_4 w p x _).trans h1⟩

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
  obtain ⟨pos, hr, hl, hd, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  have hled : Startup.ledOf ((X.tr g).take (k + 1)) =
      Startup.ledOf ((X.tr g).take k) + Startup.ledEv e := by
    simp only [Startup.ledOf, Startup.ledEv, Startup.Led.add_def, count_snoc _ he]
  rcases good_at (X := X) (k := k) hpre hg pos hr hat hc hf hn with
    ⟨pos', h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact .inl ⟨pos', h1, by rw [hled, hl, h2], by omega, h4 he⟩
  · exact .inr ⟨by omega, h1, by rw [hled, hl, h2]⟩

include hX

/-- **The reference invariant of the Conversion phase**: for a thread that entered the phase
before its event `k0`, the state of its machine before each later event `k` is at a position of
the phase with the position's registers, ledger, event count and link, or the thread has left
the phase through its exit, which it reached before its event `k0 + len g`. -/
theorem conversion_inv {k0 : Nat} {s0 : D}
    (hσ0 : Frame.stateAt (code L) X g k0 = some (some s0)) (hin : In P X g k0 s0)
    {k : Nat} {s : D} (hk0 : k0 ≤ k) (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P X g k0 k s ∨ Left P X g L k0 k := by
  have h0 : Inv P X g k0 k0 s0 := ⟨.fence, entry_at hin.1, hin.2, rfl, trivial⟩
  rcases phase_inv_from (C := code L) (fun g hg => Thread.sound hpre hg) hX hσ0
      (fun k s => Inv P X g k0 k s) (fun k s => k = k0 + len g ∧ Out P X g k s) h0
      (fun k e s s' t ins o _ he _ hI hat hc hf _ hn => inv_step hpre hg he hI hat hc hf hn)
      k s hk0 hk hσ with h | ⟨j, -, hj, s1, h1, rfl, h2⟩
  · exact .inl h
  · exact .inr ⟨hj, s1, h1, h2⟩

/-- **Under the data condition the thread goes on** from a state of the invariant: the event
is not undefined behaviour and the machine's successor is a state. -/
theorem conversion_ok {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hdata : DataOk s e) :
    (∀ pc f, e ≠ ⟨pc, .ub f⟩) ∧ ∃ s', Thread.next L g s e = some (some s') := by
  obtain ⟨pos, hr, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (fun g hg => Thread.sound hpre hg) hX he hσ
  exact ok_at hpre hg pos hr hat hc hf hdata

end

/-! ### The phase, for the chain of the run -/

/-- **The Conversion phase of thread `g`** in the form of `Ref/Chain.lean`: the entry is the
exit of the startup phase; the exit is reached exactly `len g` events after the entry. -/
def phase (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g where
  In k s := In P X g k s
  Inv k0 k s := Inv P X g k0 k s
  Out k0 j s := j = k0 + len g ∧ Out P X g j s

theorem traces (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) : (phase P L X g).Traces X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  rcases conversion_inv hpre hX hg h0 hin hk0 hk hs with h | ⟨hj, s1, h1, h2⟩
  · exact .inl h
  · exact .inr ⟨k0 + len g, s1, Nat.le_add_right _ _, hj, h1, rfl, h2⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
