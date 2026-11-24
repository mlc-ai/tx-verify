-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Determinism

@[expose] public section

/-!
# Local runs

A proof tool, not part of the model. Between two events a thread performs local steps
only. `run n t` is `n` of them (`tauStep` computes one), so a kernel proof can compute a
whole segment by evaluation. `Next t t1 m` says the local steps from `t` stop at `t1`,
whose instruction performs an event from template `m`.
-/

namespace PTX

noncomputable section

section
variable (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat)

/-- One local step, or `none` if the instruction performs an event. -/
def tauStep (t : TState) : Option TState :=
  match out K A L g t with
  | .tau t' => some t'
  | .ev _ => none

def run : Nat → TState → Option TState
  | 0, t => some t
  | n + 1, t => (tauStep K A L g t).bind (run n)

/-- The local steps from `t` stop at `t1`, which performs an event from template `m`. -/
structure Next (t t1 : TState) (m : Tmpl) : Prop where
  steps : Relation.ReflTransGen (Tau K A L g) t t1
  stop : out K A L g t1 = .ev m

end

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem tauStep_iff {t t' : TState} : tauStep K A L g t = some t' ↔ Tau K A L g t t' := by
  unfold tauStep Tau; cases out K A L g t <;> simp

theorem run_rtg : ∀ {n : Nat} {t t' : TState}, run K A L g n t = some t' →
    Relation.ReflTransGen (Tau K A L g) t t'
  | 0, t, t', h => by simp only [run, Option.some.injEq] at h; subst h; exact .refl
  | n + 1, t, t', h => by
    simp only [run] at h
    cases hs : tauStep K A L g t with
    | none => simp [hs] at h
    | some t1 =>
      rw [hs, Option.bind_some] at h
      exact .head (tauStep_iff.mp hs) (run_rtg h)

theorem run_add : ∀ (m n : Nat) (t : TState),
    run K A L g (m + n) t = (run K A L g m t).bind (run K A L g n)
  | 0, n, t => by simp [run]
  | m + 1, n, t => by
    rw [show m + 1 + n = (m + n) + 1 by omega, run, run]
    cases tauStep K A L g t <;> simp [run_add m n]

theorem run_comp {m n : Nat} {t0 t1 t2 : TState} (h1 : run K A L g m t0 = some t1)
    (h2 : run K A L g n t1 = some t2) : run K A L g (m + n) t0 = some t2 := by
  rw [run_add, h1]; exact h2

end

end

end PTX
