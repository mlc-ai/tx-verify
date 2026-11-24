-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.RefSucc

@[expose] public section

/-! # The softmax machine's successors: the P part -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The arrivals at the correction warps' named barrier. -/
theorem succOk_narr (r : Rd) : SuccOk p L g (.narr r) := by
  intro v k acc e d' h
  cases r <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The P stores. -/
theorem succOk_pst (r : Rd) (q : Fin 4) : SuccOk p L g (.pst r q) := by
  intro v k acc e d' h
  cases r <;> fin_cases q
  all_goals simp only [succ, pstNext, Fin.isValue, Fin.zero_eta, Fin.mk_one, D.mk'] at h
  all_goals first
    | (split at h <;> (simp only [Option.some.injEq] at h; subst h))
    | (simp only [Option.some.injEq] at h; subst h)
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The store waits. -/
theorem succOk_pwst (r : Rd) (j : Fin 2) : SuccOk p L g (.pwst r j) := by
  intro v k acc e d' h
  cases r <;> fin_cases j <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The arrivals between the P stores. -/
theorem succOk_parr (r : Rd) : SuccOk p L g (.parr r) := by
  intro v k acc e d' h
  cases r <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The warp barriers. -/
theorem succOk_pws (r : Rd) : SuccOk p L g (.pws r) := by
  intro v k acc e d' h
  cases r <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The elections. -/
theorem succOk_pel (r : Rd) : SuccOk p L g (.pel r) := by
  intro v k acc e d' h
  cases r <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The elected lane's arrivals. -/
theorem succOk_parr2 (r : Rd) : SuccOk p L g (.parr2 r) := by
  intro v k acc e d' h
  cases r <;> sc_split
  all_goals sc_close

/-- A property of both branches of a conditional state. -/
theorem ite_P {P : D → Prop} {c : Bool} {a b : D} (ha : P a) (hb : P b) : P (D.ite c a b) := by
  unfold D.ite; cases c
  · exact hb
  · exact ha

/-- The step facts at the end of a round. -/
theorem pwend_move (r : Rd) (v : V) (k : Fin 4) (acc : List Value) (e : Event)
    (hnw : ∀ m par a sc, e.kind ≠ .wait m par false a sc) :
    MoveFacts L g ⟨.pwend r, v, k, acc⟩ (afterRound p L g ⟨.pwend r, v, k, acc⟩ r) e := by
  cases r <;>
  refine ⟨?_, ?_, fun _ => hnw, fun h => absurd h (by dsimp only; decide),
    fun h => absurd h (by dsimp only; decide), fun h => absurd h (by dsimp only; decide), ?_,
    fun h => absurd h (by dsimp only; decide)⟩ <;>
  simp only [afterRound, afterFirst, afterBias, afterPlain, plainEntry]
  all_goals repeat' (first
    | refine ite_P (P := fun x => x.site ∈ nexts (lz L g) _) ?_ ?_
    | refine ite_P (P := fun x => x.k = kIn x.site) ?_ ?_
    | refine ite_P (P := fun x => x.site.noTile = true → x.v.ppar = Epilogue.i32 1 ∨
        ((Site.pwend _).noTile = true ∧ x.v.ppar = v.ppar)) ?_ ?_)
  all_goals first
    | (dsimp only [D.mk']; generalize lz L g = b; cases b <;> decide)
    | (intro h; exact absurd h (by dsimp only [D.mk']; decide))
    | (dsimp only [D.mk', kIn]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The closing polls. -/
theorem succOk_pwend (r : Rd) : SuccOk p L g (.pwend r) := by
  intro v k acc e d' h
  simp only [succ] at h
  split at h
  · rename_i m par ok a sc hk
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact .inl ⟨rfl, rfl, rfl, .inl ⟨_, _, _, _, hk⟩⟩
    · simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact .inr (pwend_move r v k acc e fun m' par' a' sc' hw => by rw [hk] at hw; cases hw)
  · cases h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
