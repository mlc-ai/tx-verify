-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Loaded

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
noncomputable section

/-- Recover the score in a successor state from the element of the actual Tensor Memory load. -/
theorem score_load (p L g r) (c : Fin 4) (v k acc) (e : Event) {a vals sh}
    (hk : e.kind = .tc (.ld a vals sh)) (hs : Values.F32s vals) :
    ∃ d', succ p L g ⟨.sld r c,v,k,acc⟩ e = some (some d') ∧
      ∀ i < 32, ∀ hi : i < vals.length, vals[i] = .float .f32 (d'.v.score (32*c.val+i)) := by
  obtain ⟨xs,hxs⟩ := flAll_some_of hs
  let v' := {v with sv := Function.update v.sv c xs}
  have read (i : Nat) (hi : i < 32) (hn : i < vals.length) :
      vals[i] = .float .f32 (v'.score (32*c.val+i)) := by
    have hc : (⟨(32*c.val+i)/32%4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = c :=
      Fin.ext (by change (32*c.val+i)/32%4 = c.val; have := c.isLt; omega)
    have he := flAll_get hxs hn (.pred false)
    simpa only [V.score, v', hc, Function.update_self, show (32*c.val+i)%32 = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using he
  cases r <;> simp only [succ, hk, hxs] <;> exact ⟨_, rfl, read⟩

/-- The bias half of the eight columns updated by one completed bias load. -/
theorem bias_load (p L g v) (c : Fin 16) (ws : List Value) {j : Nat} (hj : j < 8) :
    loadedBias p L g (recordBias v c ws) .bias (8*c.val+j) = halfOf ws j := by
  have hc : (⟨(8*c.val+j)/8%16, Nat.mod_lt _ (by decide)⟩ : Fin 16) = c :=
    Fin.ext (by change (8*c.val+j)/8%16 = c.val; have := c.isLt; omega)
  simp only [loadedBias, bpf, recordBias, hc, show (8*c.val+j)%8 = j by omega, Function.update_self]
  cases halfOf ws j <;> rfl

/-- The five fold fields directly in terms of loaded score and bias operands. -/
theorem loaded_fold {p L m} (hp : Pre p L m) (g n : Nat) (hn : 0 < n)
    (bias : Nat → Bool) (input : Nat → V) :
    let v := roundState p L g bias input
    let r := roundAt bias
    let D := rowData p L g n v r
    Values.Fold n (fun u i => weight p (adjusted p ((v u).score i)
      (loadedBias p L g (v u) (r u) i))) D.P D.c D.f D.rs ∧
      D.c (n-1) = (2 : ℝ) ^ (-(abiFloat p.scaleLog2Bits * D.rm)) := by
  refine ⟨?_, last_scale _ _ _ _ _ _⟩
  simpa only [loaded_score, rowData] using online hp g n hn bias input

/-- A masked read at an otherwise attended key distinguishes machine and tile weights. -/
theorem masked_weight_ne (p L g v r) (t : Values.Tile) (row u i : Nat) (S : Nat → Nat → ℝ)
    (hread : loadedBias p L g v r i = none) (hkey : t.key u i < p.keyCount t.batch row) :
    weight p (score p L g v r i) ≠ Values.weightOf p t row S u i := by
  rw [loaded_score, hread]
  simp only [adjusted, weight, ite_true, Values.weightOf, hkey]
  exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne

/-- The plain round retains its reference maximum for a small positive increase. -/
theorem plain_keeps_smaller (p : Params) (v : V) (hm : v.mf = true)
    (hinc : v.mr < foldPT v.mr v.score)
    (hsmall : (scl p : ℝ) * (foldPT v.mr v.score - v.mr) ≤ 8) :
    maxR p v = v.mr ∧ maxR p v < foldPT v.mr v.score ∧ factor p v .plain = 1 := by
  have h : keepP p v = true := by
    simp only [keepP, Assumption.erealCompare, decide_eq_true_eq, EReal.coe_le_coe_iff]
    linarith
  simp only [maxR, hm, h, ite_true, factor, carry, Bool.cond_true, hinc, and_self]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
