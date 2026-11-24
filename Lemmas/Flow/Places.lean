-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code

@[expose] public section

/-! # Counts as closed forms in the places a state has passed

A proof tool (review item 11, the shared part of tml-fa4's `Correction/Ref.lean` and
`Softmax/Ref.lean`). A role's ledger count of a class is a closed form in its state: the number of
the class's signal points (`pts`, program counters) the state has passed in the current pass
(`before s q`) plus the rounds done times the class's points inside a round (`inRound`)
(`Places.passed`). The ledger relation is then kept by two kinds of move, each checked once per
site by an evaluated table:

* a move inside a pass (`Places.passed_move`): the successor has passed exactly the points the
  state had passed and its own point;
* the end of a round (`Places.passed_rmove`): one more round done, and the successor has passed
  exactly the points outside the round the state had passed, and its own point when outside.

A move's count changes by one exactly when the state's point is one of the class's. -/

namespace PTX.Flow.Places

/-- The points of `pts` a state at `s` with `r` rounds done has passed. -/
def passed {σ : Type} (before : σ → Nat → Bool) (inRound : Nat → Bool) (pts : List Nat) (s : σ)
    (r : Nat) : Nat :=
  pts.countP (before s) + r * pts.countP inRound

theorem countP_or_eq {p : Nat → Bool} {a : Nat} {l : List Nat} (hp : p a = false)
    (hl : l.Nodup) :
    l.countP (fun q => p q || q == a) = l.countP p + if a ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.countP_cons, ih hl.2, List.mem_cons]
    by_cases hx : x = a
    · subst hx
      simp [hp, hl.1]
    · have : (x == a) = false := by simpa using hx
      simp only [this, Bool.or_false]
      by_cases ha : a ∈ l
      · simp [ha, Ne.symm hx]; omega
      · simp [ha, Ne.symm hx]

theorem countP_congr' {p q : Nat → Bool} {l : List Nat} (h : ∀ x ∈ l, p x = q x) :
    l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, h x (by simp), ih fun y hy => h y (by simp [hy])]

theorem countP_split (p q : Nat → Bool) (l : List Nat) :
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, ih]
    cases p x <;> cases q x <;> simp <;> omega

variable {σ : Type} {before : σ → Nat → Bool} {inRound : Nat → Bool} {pc : σ → Nat}
  {pts : List Nat}

/-- **A move inside a pass** adds the state's point to the count when it is one of the class's
points. -/
theorem passed_move (hself : ∀ s, before s (pc s) = false) (hnd : pts.Nodup) {s s' : σ}
    (hm : ∀ q ∈ pts, before s' q = (before s q || q == pc s)) (r : Nat) :
    passed before inRound pts s' r =
      passed before inRound pts s r + if pc s ∈ pts then 1 else 0 := by
  unfold passed
  rw [countP_congr' hm, countP_or_eq (hself s) hnd]
  omega

/-- **The end of a round**: one more round done, the round's points start again, and the state's
point is added when it is one of the class's points. -/
theorem passed_rmove (hself : ∀ s, before s (pc s) = false) (hnd : pts.Nodup) {s s' : σ}
    (hm : ∀ q ∈ pts, before s' q = ((before s q || q == pc s) && !inRound q))
    (hin : ∀ q ∈ pts, inRound q = ((before s q || q == pc s) && inRound q)) (r : Nat) :
    passed before inRound pts s' (r + 1) =
      passed before inRound pts s r + if pc s ∈ pts then 1 else 0 := by
  unfold passed
  have h3 := countP_split (fun q => before s q || q == pc s) inRound pts
  rw [countP_or_eq (hself s) hnd] at h3
  rw [countP_congr' hm, countP_congr' hin, Nat.add_mul, one_mul]
  omega

end PTX.Flow.Places
