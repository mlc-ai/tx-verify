-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.InstructionProjection
public import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Proof
open PTX
noncomputable section

/-- Events agree on source position and control fields, before data values are proved. -/
inductive EventShape : Event → Event → Prop
  | read (pc a bs cs) : EventShape ⟨pc, .rd a bs⟩ ⟨pc, .rd a cs⟩
  | nc (pc a bs cs) : EventShape ⟨pc, .nc a bs⟩ ⟨pc, .nc a cs⟩
  | write (pc a bs cs) : EventShape ⟨pc, .wr a bs⟩ ⟨pc, .wr a cs⟩
  | bar (pc id) (count : Option Nat := none) :
      EventShape ⟨pc, .bar id count⟩ ⟨pc, .bar id count⟩
  | shfl (pc m a a' b c v ok v' ok') :
      EventShape ⟨pc, .shfl m a b c v ok⟩ ⟨pc, .shfl m a' b c v' ok'⟩
  | exit (pc) : EventShape ⟨pc, .exit⟩ ⟨pc, .exit⟩

/-- A trace follows a witness's event shapes until it stops or faults. -/
inductive ShapePrefix : List Event → List Event → Prop
  | nil (l) : ShapePrefix [] l
  | fault (pc f l) : ShapePrefix [⟨pc, .ub f⟩] l
  | cons {e f l r} : EventShape e f → ShapePrefix l r → ShapePrefix (e :: l) (f :: r)

def NoUb (l : List Event) : Prop := ∀ pc f, ⟨pc, .ub f⟩ ∉ l

def OptionControl (S : Nat → Bool) : Option TState → Option TState → Prop
  | none, none => True
  | some t, some u => t.fault ≠ none ∨ u.fault ≠ none ∨ ControlAgree S t u
  | _, _ => False

namespace OutRelated
variable {S : Nat → Bool} {o : Out} {m m' : Tmpl}

theorem stopped (h : OutRelated S o (.ev m')) (hgood : ∀ f, m' ≠ .ub f) :
    ∃ m, o = .ev m := by
  cases h
  all_goals first | exact ⟨_, rfl⟩ | exact (hgood _ rfl).elim

theorem fires {pc pc' : Nat} {e e' : Event} {r r' : Option TState}
    (h : OutRelated S (.ev m) (.ev m')) (hp : pc = pc')
    (he : Fires pc m e r) (he' : Fires pc' m' e' r') :
    (∃ p f, e = ⟨p, .ub f⟩) ∨ (∃ p f, e' = ⟨p, .ub f⟩) ∨
      (EventShape e e' ∧ OptionControl S r r') := by
  subst hp
  cases h with
  | fault_left f => exact .inl ⟨_, f, he.1⟩
  | fault_right _ f => exact .inr (.inl ⟨_, f, he'.1⟩)
  | read h =>
    obtain ⟨bs, _, rfl, rfl⟩ := he
    obtain ⟨cs, _, rfl, rfl⟩ := he'
    exact .inr (.inr ⟨.read .., h bs cs⟩)
  | nc h =>
    obtain ⟨bs, _, rfl, rfl⟩ := he
    obtain ⟨cs, _, rfl, rfl⟩ := he'
    exact .inr (.inr ⟨.nc .., h bs cs⟩)
  | write h =>
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := he'
    exact .inr (.inr ⟨.write .., .inr (.inr h)⟩)
  | bar h =>
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := he'
    exact .inr (.inr ⟨.bar _ _ _, .inr (.inr h)⟩)
  | shfl h =>
    obtain ⟨v, ok, rfl, rfl⟩ := he; obtain ⟨v', ok', rfl, rfl⟩ := he'
    exact .inr (.inr ⟨.shfl .., .inr (.inr (h v ok v' ok'))⟩)
  | exit =>
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := he'
    exact .inr (.inr ⟨.exit .., trivial⟩)

end OutRelated


theorem fires_some_not_ub {pc : Nat} {m : Tmpl} {e : Event} {t : TState}
    (h : Fires pc m e (some t)) : ∀ pc' f, e ≠ ⟨pc', .ub f⟩ := by
  intro pc' f he
  subst he
  cases m <;> simp [Fires] at h

end
end PTX.Proof
