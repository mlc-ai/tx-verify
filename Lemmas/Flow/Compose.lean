-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Polls

@[expose] public section

/-! # Composing role machines into a thread's machine

A proof tool. A thread's code machine follows the thread through a prologue and then one of
several roles, each proved on its own as a code machine. A role's machine `C` sits inside the
thread's machine `C'` through a map of states `f` (`Embeds`) when each state's instruction,
sub-step, accumulator and facts are the role's, the role's invariant implies the thread's, and
the thread's successors are the role's, mapped. A role state's obligation is then the thread
state's (`Embeds.stepAt`), and a concrete state of a role state is one of its image
(`Embeds.good`).

A role's first state has the registers the prologue left at the role's entry, valued by the
prologue's table; the role values them by its own table. The facts of the entry are the role's
when the two tables agree on the registers live there (`at_congr`).

A run invariant of a thread's machine that only continuing events keep (`Fires … (some u)`, the
events a role's step lemmas speak of) holds at the state before each event of the thread's run
(`Code.run_inv_live`): an event that ends the thread is its last. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

/-- Facts read off a table hold for another table that agrees with it on the registers. -/
theorem holds_factsFrom_congr {R : Nat → Option Value} {live : List Nat} {v v' : Nat → Value}
    (h : Holds R (factsFrom live v)) (hv : ∀ r ∈ live, v r = v' r) :
    Holds R (factsFrom live v') :=
  holds_of_pointwise fun r hr => (hv r hr) ▸ holds_mem h (mem_factsFrom hr)

/-- A concrete state of the live registers valued by `v` is one of them valued by `v'` when
the two agree there. -/
theorem at_congr {t : TState} {pc : Nat} {live : List Nat} {v v' : Nat → Value}
    (h : At t pc (factsFrom live v)) (hv : ∀ r ∈ live, v r = v' r) :
    At t pc (factsFrom live v') :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, holds_factsFrom_congr h.2.2.2.2 hv⟩

namespace Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The code machine `C` sits inside `C'` through `f`. -/
structure Embeds (C C' : Code K A L g) (f : C.D → C'.D) : Prop where
  pc : ∀ d, C'.pc (f d) = C.pc d
  sub : ∀ d, C'.sub (f d) = C.sub d
  acc : ∀ d, C'.acc (f d) = C.acc d
  facts : ∀ d, C'.facts (f d) = C.facts d
  inv : ∀ d, C.inv d → C'.inv (f d)
  next : ∀ d e, C'.next (f d) e = (C.next d e).map (Option.map f)

variable {C C' : Code K A L g} {f : C.D → C'.D}

theorem Embeds.atD (h : Embeds C C' f) {d : C.D} {t : TState} : C'.AtD (f d) t ↔ C.AtD d t := by
  simp only [AtD, h.pc, h.sub, h.acc, h.facts]

/-- A concrete state of a role state is one of its image. -/
theorem Embeds.good (h : Embeds C C' f) {d : C.D} {t : TState} (hg : C.Good (some d) t) :
    C'.Good (some (f d)) t :=
  ⟨h.atD.2 hg.1, h.inv d hg.2⟩

/-- **A role state's obligation is its image's**, where the thread's invariant gives the
role's. -/
theorem Embeds.stepAt (h : Embeds C C' f) {d : C.D} (hinv : C'.inv (f d) → C.inv d)
    (hs : C.StepAt d) : C'.StepAt (f d) where
  site hi := by rw [h.pc, h.facts]; exact hs.site (hinv hi)
  step := by
    intro t e u ins ha hi hc hf
    rw [h.pc] at hc hf
    rcases hs.step ins (h.atD.1 ha) (hinv hi) hc hf with
      (hn | ⟨d', t', hn, hr, hg⟩) | ⟨hn, hd⟩
    · exact .inl (.inl (by rw [h.next, hn]; rfl))
    · exact .inl (.inr ⟨f d', t', by rw [h.next, hn]; rfl, hr, h.good hg⟩)
    · exact .inr ⟨by rw [h.next, hn]; rfl, hd⟩

/-- Along a trace, an invariant kept by the continuing events holds at the state before each
event. -/
theorem _root_.PTX.Flow.Machine.Trace.live_induction {M : Machine K A L g} {σ : M.St}
    {es : List Event} (h : M.Trace σ es) (Q : M.St → List Event → Prop) {pre : List Event}
    (h0 : Q σ pre)
    (hs : ∀ σ pre e σ' u, Q σ pre → M.Fired σ e (some u) → M.next σ e = some σ' →
      Q σ' (pre ++ [e])) :
    ∀ j < es.length, ∀ τ, M.after σ (es.take j) = some τ → Q τ (pre ++ es.take j) := by
  induction h generalizing pre with
  | nil => intro j hj; simp at hj
  | step hf hn _ ih =>
    intro j hj τ hτ
    cases j with
    | zero => simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at hτ; subst hτ
              simpa using h0
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some] at hτ
      have := ih (hs _ _ _ _ _ h0 hf hn) j (by simp at hj; omega) τ hτ
      simpa using this
  | last _ =>
    intro j hj τ hτ
    obtain rfl : j = 0 := by simp at hj; omega
    simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at hτ; subst hτ
    simpa using h0
  | dead _ hn _ _ =>
    intro j hj τ hτ
    cases j with
    | zero => simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at hτ; subst hτ
              simpa using h0
    | succ j => simp [Machine.after_cons, hn] at hτ

/-- **A run invariant kept by the continuing events** holds at the state before each event of a
run of a sound code machine. -/
theorem run_inv_live {C : Code K A L g} (hC : C.Sound) {es : List Event}
    (htr : C.toMachine.Trace (some C.init) es) (J : C.D → List Event → Prop)
    (h0 : J C.init [])
    (hs : ∀ {d d' : C.D} {pre : List Event} {e : Event} {t u : TState} {ins : Instr},
      J d pre → C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
      Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) → C.next d e = some (some d') →
      J d' (pre ++ [e])) :
    ∀ j < es.length, ∀ d, C.toMachine.after (some C.init) (es.take j) = some (some d) →
      J d (es.take j) := by
  have h := Machine.Trace.live_induction htr (fun σ es => ∀ d, σ = some d → J d es)
    (pre := []) (fun d hd => by cases hd; exact h0) ?_
  · intro j hj d hd
    simpa using h j hj _ hd d rfl
  intro σ pre e σ' u hq hf hn d' hd'
  subst hd'
  cases σ with
  | none => cases hn
  | some d =>
    obtain ⟨t, ins, hat, hinv, hc, hfire⟩ := Code.fired_site hC hf
    exact hs (hq d rfl) hat hinv hc hfire hn

end Code
end
end PTX.Flow
