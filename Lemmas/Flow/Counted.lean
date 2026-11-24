-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Ledger
public import Lemmas.Flow.TraceInduction

@[expose] public section

/-! # A ghost ledger on a site machine

A proof tool, generic over the kernel. `C.counted cls` is the machine `C` with a ghost counter per
class `c : κ` of events: its states are a state of `C` and the counts, and a step adds one to
every class of the event it takes. Program counter, facts, invariant and the stop decisions are
those of `C`, so its step obligations are those of `C` (`counted_steps`, `counted_sound`) and so is
its shape table (`Shape.counted`). A count is a field of the state by construction: along a
thread it is the number of the thread's events of the class so far (`Frame.count_eq`), with no
step lemma per count. A closed form of a count at a site is a conjunct of the role's reference
invariant. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

namespace Code

/-- The counts after an event: one more for every class of the event. -/
def bump {κ : Type} (cls : κ → Event → Bool) (n : κ → Nat) (e : Event) : κ → Nat :=
  fun c => n c + if cls c e then 1 else 0

/-- The machine `C` with a ghost count of the events of each class `c`. -/
@[reducible] def counted (C : Code K A L g) {κ : Type} (cls : κ → Event → Bool) : Code K A L g where
  D := C.D × (κ → Nat)
  init := (C.init, fun _ => 0)
  pc := fun d => C.pc d.1
  facts := fun d => C.facts d.1
  sub := fun d => C.sub d.1
  acc := fun d => C.acc d.1
  inv := fun d => C.inv d.1
  next := fun d e => (C.next d.1 e).map (Option.map fun d' => (d', bump cls d.2 e))

variable {C : Code K A L g} {κ : Type} {cls : κ → Event → Bool}

@[simp] theorem counted_pc (d : (C.counted cls).D) : (C.counted cls).pc d = C.pc d.1 := rfl

@[simp] theorem counted_inv (d : (C.counted cls).D) : (C.counted cls).inv d = C.inv d.1 := rfl

theorem counted_next (d : C.D) (n : κ → Nat) (e : Event) :
    (C.counted cls).next (d, n) e = (C.next d e).map (Option.map fun d' => (d', bump cls n e)) :=
  rfl

/-- A step of the counted machine: a step of `C`, with the counts bumped. -/
theorem counted_next_some {d : C.D} {n : κ → Nat} {e : Event} {d' : (C.counted cls).D}
    (h : (C.counted cls).next (d, n) e = some (some d')) :
    C.next d e = some (some d'.1) ∧ d'.2 = bump cls n e := by
  rw [counted_next] at h
  cases hn : C.next d e with
  | none => rw [hn] at h; cases h
  | some σ =>
    cases σ with
    | none => rw [hn] at h; cases h
    | some d₁ =>
      rw [hn] at h
      cases h
      exact ⟨rfl, rfl⟩

theorem counted_next_none_iff {d : C.D} {n : κ → Nat} {e : Event} :
    (C.counted cls).next (d, n) e = some none ↔ C.next d e = some none := by
  rw [counted_next]
  match C.next d e with
  | none => simp
  | some none => simp
  | some (some _) => simp

theorem counted_next_eq_none_iff {d : C.D} {n : κ → Nat} {e : Event} :
    (C.counted cls).next (d, n) e = none ↔ C.next d e = none := by
  rw [counted_next]
  match C.next d e with
  | none => simp
  | some none => simp
  | some (some _) => simp

theorem counted_atD {d : (C.counted cls).D} {t : TState} :
    (C.counted cls).AtD d t ↔ C.AtD d.1 t := Iff.rfl

/-- **The step obligations of the counted machine** are those of `C`. -/
theorem counted_steps {d : C.D} (h : C.StepAt d) (n : κ → Nat) : (C.counted cls).StepAt (d, n) where
  site := h.site
  step := by
    intro t e u ins hat hinv hc hf
    rcases h.step ins hat hinv hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
    · exact .inl (.inl (by rw [counted_next, hn]; rfl))
    · exact .inl (.inr ⟨(d', bump cls n e), t', by rw [counted_next, hn]; rfl, hl, hg⟩)
    · exact .inr ⟨by rw [counted_next, hn]; rfl, hd⟩

/-- **The counted machine of a sound machine is sound.** -/
theorem counted_sound (hC : C.Sound) : (C.counted cls).Sound where
  start := hC.start
  steps := fun d => counted_steps (hC.steps d.1) d.2

/-- An event the counted machine fires from a state is one the machine fires from it (promoted
from the tml-fa4 output warp's proof). -/
theorem counted_fired {d : C.D} {n : κ → Nat} {e : Event} {o : Option TState} :
    (C.counted cls).toMachine.Fired (some (d, n)) e o ↔ C.toMachine.Fired (some d) e o :=
  Iff.rfl

/-- The shape table of `C` is the counted machine's. -/
theorem Shape.counted {Ev : C.D → Event → Prop} (hS : C.Shape Ev) :
    (C.counted cls).Shape (fun d e => Ev d.1 e) :=
  fun hat hi hc hf => hS hat hi hc hf

end Code

/-! ### Invariants of a ghost ledger along a run

Promoted from FlashMLA (`Proof/Lib/Ledger.lean`, lane-F). A run of a code machine is a run of its
counted machine (`Code.trace_counted`), whose state after a list of events carries the counts of
that list (`Code.counted_after_map`). An invariant of the counted machine's states, preserved by
every step that the machine follows, holds at every state of a run with the counts of the events
before it (`Code.ledger`). `ringUses S s k` counts the uses of slot `s` of an `S`-slot ring among
the first `k` items. -/

namespace Code

variable {C : Code K A L g} {κ : Type} {cls : κ → Event → Bool}

omit cls in
theorem after_none_eq (C : Code K A L g) (es : List Event) : C.toMachine.after none es = some none
  := by
  induction es with
  | nil => rfl
  | cons e es ih => exact ih

/-- The counted machine after a list of events is the machine after it, with the counts of the
list added. -/
theorem counted_after_map (es : List Event) (σ : Option C.D) (n : κ → Nat) :
    (C.counted cls).toMachine.after (σ.map (·, n)) es =
      (C.toMachine.after σ es).map
        (Option.map fun d => (d, fun c => n c + es.countP (cls c))) := by
  induction es generalizing σ n with
  | nil => cases σ <;> rfl
  | cons e es ih =>
    cases σ with
    | none =>
      simp only [Option.map_none]
      rw [after_none_eq, after_none_eq]
      rfl
    | some d =>
      show ((C.counted cls).next (d, n) e).bind _ = ((C.next d e).bind _).map _
      rw [counted_next]
      cases C.next d e with
      | none => rfl
      | some σ' =>
        have := ih σ' (bump cls n e)
        change (C.counted cls).toMachine.after (σ'.map (·, bump cls n e)) es =
          (C.toMachine.after σ' es).map _
        rw [this]
        congr 2
        funext d'
        congr 1
        funext c
        simp only [bump, List.countP_cons]
        omega

/-- A run of a machine is a run of its counted machine. -/
theorem trace_counted {σ : C.toMachine.St} {es : List Event} (h : C.toMachine.Trace σ es)
    (n : κ → Nat) : (C.counted cls).toMachine.Trace (Option.map (·, n) σ) es := by
  induction h generalizing n with
  | nil => exact .nil _
  | @step σ σ' e es u hf hn _ ih =>
    cases σ with
    | none =>
      cases hn
      exact .step hf rfl (ih n)
    | some d =>
      refine .step (σ' := Option.map (·, bump cls n e) σ') hf ?_ (ih _)
      change (C.counted cls).next (d, n) e = _
      rw [counted_next]
      change C.next d e = some σ' at hn
      rw [hn]
      rfl
  | @last σ e hf => cases σ <;> exact .last hf
  | @dead σ e es u hf hn hl hu =>
    cases σ with
    | none => cases hn
    | some d =>
      refine .dead hf ?_ hl hu
      change (C.counted cls).next (d, n) e = none
      rw [counted_next]
      change C.next d e = none at hn
      rw [hn]
      rfl

/-- **A ledger invariant.** An invariant `I` of a state and its counts that holds initially and
is preserved by every followed step holds at every state of a run, with the counts of the
events before it. -/
theorem ledger (I : C.D → (κ → Nat) → Prop) (h0 : I C.init fun _ => 0)
    (hs : ∀ d n e o d', C.toMachine.Fired (some d) e o → C.next d e = some (some d') →
      I d n → I d' (bump cls n e))
    {es : List Event} (ht : C.toMachine.Trace (some C.init) es) {j : Nat} {d : C.D}
    (hj : C.toMachine.after (some C.init) (es.take j) = some (some d)) :
    I d fun c => (es.take j).countP (cls c) := by
  have ht' := trace_counted (cls := cls) ht fun _ => 0
  have hj' := counted_after_map (cls := cls) (es.take j) (some C.init) fun _ => 0
  rw [hj] at hj'
  simp only [Option.map_some, Nat.zero_add] at hj'
  refine ht'.prefix_induction (fun σ _ => ∀ dn, σ = some dn → I dn.1 dn.2)
    (fun dn h => by cases h; exact h0) ?_ j _ hj' _ rfl
  intro σ _ e σ' o ih hf hn dn' hσ'
  subst hσ'
  cases σ with
  | none => cases hn
  | some dn =>
    obtain ⟨hn', h2⟩ := counted_next_some (C := C) (d := dn.1) (n := dn.2) hn
    rw [h2]
    exact hs dn.1 dn.2 e o dn'.1 hf hn' (ih dn rfl)

end Code

/-- The uses of slot `s` of an `S`-slot ring among the first `k` items, item `b` taking slot
`b % S`. -/
def ringUses (S s k : Nat) : Nat := (k + (S - 1 - s)) / S

theorem ringUses_zero {S s : Nat} (h : s < S) : ringUses S s 0 = 0 :=
  Nat.div_eq_of_lt (by omega)

private theorem div_small {S m : Nat} (h : m < 2 * S) :
    m / S = if S ≤ m then 1 else 0 := by
  split
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/-- The uses by quotient and remainder. -/
private theorem ringUses_qr {S s q r : Nat} (h : s < S) (hr : r < S) :
    ringUses S s (S * q + r) = q + if s < r then 1 else 0 := by
  unfold ringUses
  rw [Nat.add_assoc, Nat.mul_add_div (by omega), div_small (by omega)]
  split <;> split <;> omega

private theorem ringUses_split {S s k : Nat} (h : s < S) :
    ringUses S s k = k / S + if s < k % S then 1 else 0 := by
  conv => lhs; rw [← Nat.div_add_mod k S]
  exact ringUses_qr h (Nat.mod_lt k (by omega))

theorem ringUses_succ {S s : Nat} (h : s < S) (k : Nat) :
    ringUses S s (k + 1) = ringUses S s k + if k % S = s then 1 else 0 := by
  have hm := Nat.mod_lt k (by omega : 0 < S)
  rw [← Nat.div_add_mod k S]
  generalize k / S = q
  generalize k % S = r at hm
  rw [ringUses_qr h hm, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hm]
  by_cases hw : r + 1 = S
  · rw [Nat.add_assoc, hw, show S * q + S = S * (q + 1) + 0 by rw [Nat.mul_add]; omega,
      ringUses_qr h (by omega)]
    split_ifs <;> omega
  · rw [Nat.add_assoc, ringUses_qr h (by omega)]
    split_ifs <;> omega

theorem ringUses_here {S s k : Nat} (h : k % S = s) (hs : s < S) : ringUses S s k = k / S := by
  rw [ringUses_split hs]
  simp [h]

end
end PTX.Flow
