-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.GateOrder
import Mathlib.Tactic

/-! Error of the compiled operand formation: binary32 products, external query scale,
and the final conversion to bfloat16 on each side of the query-key matrix product. -/
@[expose] public section
namespace FlashKda.GatedOperands
open PTX RootContract GatePair
noncomputable section

def band (x : ℝ) : Prop := x = 0 ∨ (1:ℝ)/2^120 ≤ |x| ∧ |x| ≤ 2^120
def single (x : ℝ) : Option ℚ := (format.roundFtz .rn true x).bind FVal.num

theorem single_value {x : ℝ} (hx : band x) :
    ∃ y : ℚ, single x = some y ∧ |(y:ℝ)-x| ≤ |x|/16777216 := by
  rcases hx with rfl | ⟨lo,hi⟩
  · refine ⟨0,?_,by norm_num⟩
    have round : format.round .rn .inf 0 false = some (.zero false) :=
      Layout.round_zero (eb := 8) (mb := 23) (sp := .ieee) (by trivial)
    simp [single,Layout.roundFtz,round,Layout.flush,FVal.num]
  · obtain ⟨f,lf,_,word,err⟩ := signed_anchor lo hi
    let v := OperandRound.signed x (magnitude f)
    have floor : format.minNormal ≤ magnitude low := by decide +kernel
    have high : format.minNormal ≤ magnitude f :=
      floor.trans ((Layout.magnitude_strictMono 8 23).monotone lf)
    have norm : |v| = magnitude f := by
      dsimp [v,OperandRound.signed]
      split <;> simp [abs_of_nonneg (Layout.magnitude_nonneg ..)]
    have keep : format.subnormal v = false := by simp [Layout.subnormal,norm,not_lt.mpr high]
    have small : (format.minNormal : ℝ) ≤ |x| := by
      apply le_trans _ lo
      have h : format.minNormal ≤ (1:ℚ)/2^120 := by decide +kernel
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).2 h
    refine ⟨v,?_,err⟩
    change format.round .rn .inf x false = some (.fin v) at word
    simp [single,Layout.roundFtz,word,not_lt.mpr small,Layout.flush,keep,FVal.num]

def Single (x : ℝ) (y : ℚ) : Prop := band x ∧ single x = some y
def Brain (x : ℝ) (y : ℚ) : Prop := OperandRound.inRange x ∧ OperandRound.rounded x = some y

theorem single_err {x y} (h : Single x y) : |(y:ℝ)-x| ≤ (1/16777216)*|x| := by
  obtain ⟨w,same,err⟩ := single_value h.1
  obtain rfl := Option.some.inj (same.symm.trans h.2)
  linarith

private theorem brain_err {x y} (h : Brain x y) : |(y:ℝ)-x| ≤ (1/256)*|x| := by
  obtain ⟨w,same,err⟩ := OperandRound.value x h.1
  exact (Option.some.inj (same.symm.trans h.2)) ▸ err

private theorem chain {a b c u v : ℝ} (hv : 0 ≤ v)
    (first : |b-a| ≤ u*|a|) (last : |c-b| ≤ v*|b|) :
    |c-a| ≤ (u+v+u*v)*|a| := by
  have t := abs_add_le (b-a) a
  rw [sub_add_cancel] at t
  have size : |b| ≤ (1+u)*|a| := by linarith
  have e := last.trans (mul_le_mul_of_nonneg_left size hv)
  calc
    _ ≤ |c-b|+|b-a| := abs_sub_le c b a
    _ ≤ _ := by nlinarith only [e,first]

/-- Normalized query and key values are supplied at the gate multiplication site, after
their own binary32 normalization. Exact-zero products and either sign are covered. -/
theorem score {d : ℕ} (q k z w a b : Chunk.Row d) (scale : ℝ)
    (qd qs ki aq bk : Fin d → ℚ) (hz : ∀ i, |z i| ≤ 120)
    (hw : ∀ i, |w i| ≤ 120) (ordered : ∀ i, z i ≤ w i)
    (decay : ∀ i, GatePair.allowed (z i) (a i))
    (restore : ∀ i, GatePair.allowed (-w i) (b i))
    (query : ∀ i, Single (q i*a i) (qd i))
    (scaled : ∀ i, Single ((qd i:ℝ)*scale) (qs i))
    (key : ∀ i, Single (k i*b i) (ki i))
    (queryBf : ∀ i, Brain (qs i:ℝ) (aq i)) (keyBf : ∀ i, Brain (ki i:ℝ) (bk i)) :
    |Chunk.dot (fun i => (aq i:ℝ)) (fun i => (bk i:ℝ)) - scale*GatePair.ideal q k z w| ≤
      (783/100000)*|scale| * ∑ i, |q i*k i| := by
  let u : ℝ := 1/16777216
  let e : ℝ := 1/256
  let total := (u+u+u*u)+e+(u+u+u*u)*e
  have hu : 0 ≤ u := by norm_num [u]
  have he : 0 ≤ e := by norm_num [e]
  have ht : 0 ≤ total := by positivity
  have queryErr i : |(aq i:ℝ)-(scale*q i)*a i| ≤ total*|(scale*q i)*a i| := by
    have first : |(qd i:ℝ)*scale-(q i*a i)*scale| ≤ u*|(q i*a i)*scale| := by
      rw [← sub_mul,abs_mul,abs_mul]
      simpa [u,mul_assoc] using
        mul_le_mul_of_nonneg_right (single_err (query i)) (abs_nonneg scale)
    have two := chain hu first (single_err (scaled i))
    have three := chain he two (brain_err (queryBf i))
    simpa only [mul_comm scale (q i),mul_assoc,mul_comm scale (a i)] using three
  have keyErr i : |(bk i:ℝ)-k i*b i| ≤ total*|k i*b i| := by
    apply (chain he (single_err (key i)) (brain_err (keyBf i))).trans
    exact mul_le_mul_of_nonneg_right (by norm_num [total,u,e]) (abs_nonneg _)
  have d0 := GatePair.causal (fun i => scale*q i) k z w a b _ _ ht hz hw
    ordered decay restore queryErr keyErr
  have identity : GatePair.ideal (fun i => scale*q i) k z w = scale*GatePair.ideal q k z w := by
    simp only [GatePair.ideal,Finset.mul_sum,mul_assoc]
  have factor : ∑ i, |scale*q i*k i| = |scale| * ∑ i, |q i*k i| := by
    simp only [Finset.mul_sum,mul_assoc,abs_mul]
  rw [identity,factor,← mul_assoc] at d0
  apply d0.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
  exact mul_le_mul_of_nonneg_right (by norm_num [total,u,e]) (abs_nonneg _)

/-- Earlier and later positions name counts of updates since the start of a 16-token
tile. Range and order follow from the actual rounded update relation at every coordinate. -/
theorem from_prefixes {d : ℕ} (q k a b : Chunk.Row d) (s : Nat → Fin d → ℚ)
    {gateScale : ℚ} (lo : -29/4 ≤ gateScale) (hi : gateScale ≤ 0)
    {j t : Nat} (previous : j ≤ t) (fit : t ≤ 16) (start : ∀ i, s 0 i = 0)
    (steps : ∀ n < t, ∀ i, GateRange.Update gateScale (s n i) (s (n+1) i))
    (scale : ℝ) (qd qs ki aq bk : Fin d → ℚ)
    (decay : ∀ i, GatePair.allowed (s t i:ℝ) (a i))
    (restore : ∀ i, GatePair.allowed (-(s j i:ℝ)) (b i))
    (query : ∀ i, Single (q i*a i) (qd i)) (scaled : ∀ i, Single ((qd i:ℝ)*scale) (qs i))
    (key : ∀ i, Single (k i*b i) (ki i))
    (queryBf : ∀ i, Brain (qs i:ℝ) (aq i)) (keyBf : ∀ i, Brain (ki i:ℝ) (bk i)) :
    |Chunk.dot (fun i => (aq i:ℝ)) (fun i => (bk i:ℝ)) -
      scale*GatePair.ideal q k (fun i => (s t i:ℝ)) (fun i => (s j i:ℝ))| ≤
      (783/100000)*|scale| * ∑ i, |q i*k i| := by
  have history (n : Nat) (hn : n ≤ t) (i : Fin d) : GateRange.Prefix gateScale n (s n i) := by
    induction n with
    | zero => rw [start]; exact .zero
    | succ n ih => exact .next (ih (by omega)) (steps n (by omega) i)
  have bound (n : Nat) (hn : n ≤ t) (i : Fin d) : |(s n i:ℝ)| ≤ 120 := by
    obtain ⟨l,h⟩ := GateRange.bounded_prefix lo hi (hn.trans fit) (history n hn i)
    have n16 : (n:ℚ) ≤ 16 := by exact_mod_cast hn.trans fit
    rw [abs_le]
    constructor
    · exact_mod_cast (show (-120:ℚ) ≤ s n i by linarith)
    · exact_mod_cast (show s n i ≤ (120:ℚ) by linarith)
  apply score _ _ _ _ _ _ scale qd qs ki aq bk (bound t le_rfl) (bound j previous)
    _ decay restore query scaled key queryBf keyBf
  intro i
  exact_mod_cast GateRange.ordered lo hi (fun n => s n i) (start i) t fit
    (fun n hn => steps n hn i) previous le_rfl

end
end FlashKda.GatedOperands
