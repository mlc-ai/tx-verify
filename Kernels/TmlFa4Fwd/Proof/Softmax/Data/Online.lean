-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.LaterSums
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Masked

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
noncomputable section

/-- The fold for any sequence of data states joined by the three running statistics. -/
theorem fold_states {p L m} (hp : Pre p L m) (g n : Nat) (hn : 0 < n)
    (v : Nat → V) (r : Nat → Rd) (first : r 0 = .first)
    (later : ∀ u, u+1 < n → r (u+1) ≠ .first)
    (carryStats : ∀ u, u+1 < n →
      (v (u+1)).mf = finE (maximum p L g (v u) (r u)) ∧
      (v (u+1)).mr = (maximum p L g (v u) (r u)).toReal ∧
      (v (u+1)).rs = sumAfter p L g (v u) (r u)) :
    Values.Fold n (fun u i => weight p (score p L g (v u) (r u) i))
      (fun u => P p L g (v u) (r u)) (fun u => scale p (maximum p L g (v u) (r u)))
      (fun u => factor p (v u) (r u)) (sumAfter p L g (v (n-1)) (r (n-1))) := by
  let M u := maximum p L g (v u) (r u)
  let x u := score p L g (v u) (r u)
  have masked (u : Nat) (hu : u < n) (hb : M u = ⊥) : ∀ t ≤ u, ∀ i < 128, x t i = ⊥ := by
    induction u with
    | zero =>
      intro t ht i hi
      have et : t = 0 := by omega
      subst t
      simp only [M, first] at hb
      simpa only [x, first] using first_masked p L g (v 0) hb hi
    | succ u ih =>
      have hr := later u hu
      dsimp only [M] at hb
      cases h : r (u+1) with
      | first => exact (hr h).elim
      | plain => rw [h] at hb; exact (EReal.coe_ne_bot _ hb).elim
      | bias =>
        rw [h] at hb
        obtain ⟨hprev, hnow⟩ := bias_masked p L g _ hb
        have hflag := (carryStats u hu).1
        rw [hprev] at hflag
        have hbot : M u = ⊥ := by
          simpa only [M, finE, decide_eq_false_iff_not, not_not] using hflag.symm
        intro t ht i hi
        rcases Nat.eq_or_lt_of_le ht with rfl | ht
        · simpa only [x, h] using hnow i hi
        · exact ih (by omega) hbot t (by omega) i hi
  apply fold_of_rounds p n hn M x _ (fun u => sumAfter p L g (v u) (r u))
  · simp only [first, sumAfter, M, x, rowSumT_eq, zero_add]
    exact first_sum hp g _
  · intro u hu
    have hrs := (carryStats u hu).2.2
    rw [← hrs]
    have he : (probability p (M (u+1)) ∘ x (u+1)) = P p L g (v (u+1)) (r (u+1)) := by
      funext i; rfl
    rw [he]
    cases hr : r (u+1) with
    | first => exact (later u hu hr).elim
    | bias => exact bias_sum hp g (v (u+1))
    | plain => exact plain_sum hp g (v (u+1))
  · intro u hu
    by_cases hb : M u = ⊥
    · exact Or.inr (masked u (by omega) hb)
    · left
      obtain ⟨hf,hm,_⟩ := carryStats u hu
      have hf' : (v (u+1)).mf = true := hf.trans (decide_eq_true hb)
      rw [factor_ratio p L g _ _ (later u hu) hf', hm]
      simp only [M, scale, EReal.toReal_coe]
  · exact fun u _ => factor_le p (v u) (r u)

/-- The initial round is masked. Each subsequent round chooses the bias or plain path. -/
def roundAt (bias : Nat → Bool) : Nat → Rd
  | 0 => .first
  | u+1 => bif bias u then .bias else .plain

/-- Start a round with its actual input registers, carrying the preceding machine's statistics. -/
def roundState (p : Params) (L : Launch) (g : Nat) (bias : Nat → Bool) (input : Nat → V) : Nat → V
  | 0 => input 0
  | u+1 =>
    let v := roundState p L g bias input u
    let tail := (afterRound p L g (D.mk' (.pwend (roundAt bias u)) v) (roundAt bias u)).v
    { input (u+1) with mf := tail.mf, mr := tail.mr, rs := tail.rs }

/-- The protocol's five fold fields from the state inputs alone, for every nonempty prefix. -/
theorem online {p L m} (hp : Pre p L m) (g n : Nat) (hn : 0 < n)
    (bias : Nat → Bool) (input : Nat → V) :
    let v := roundState p L g bias input
    let r := roundAt bias
    Values.Fold n (fun u i => weight p (score p L g (v u) (r u) i))
      (fun u => P p L g (v u) (r u)) (fun u => scale p (maximum p L g (v u) (r u)))
      (fun u => factor p (v u) (r u)) (sumAfter p L g (v (n-1)) (r (n-1))) := by
  apply fold_states hp g n hn _ _ rfl
  · intro u _
    change (bif bias u then Rd.bias else Rd.plain) ≠ Rd.first
    cases bias u <;> decide
  · intro u _
    exact afterRound_stats p L g (D.mk' (.pwend (roundAt bias u))
      (roundState p L g bias input u)) (roundAt bias u)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
