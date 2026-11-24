-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk5WStep
public import Kernels.InklingRelDecode.Proof.Thread.SmStgC
public import Kernels.InklingRelDecode.Proof.Thread.SmTotG
public import Lemmas.Flow.MaxSwap

@[expose] public section

/-!
# The shared numbers after the exchange of the row maximum, on any words

The successor of the shuffle of the row maximum is `D.afterS`: the state of the real numbers
(`D.afterMax`) on score words, the state of Core's outcomes (`D.afterMaxT`) otherwise. Both record
the same new maximum, decision and `alpha` (and its real number): the outcomes `D.t1`, `D.t6`,
`D.t8` of pcs 1839 to 1846 (`afterS_mn`, `afterS_kp`, `afterS_al`, `afterS_alr`; on score words by
`afterMax_t1`, `afterMax_t6`, `afterMax_t8`, the outcomes of the ten scalar instructions on the
values of extended reals). These depend on the state only through the entry numbers, the running
maximum and the outcome `D.t1` of `max.f32 %r1061, %r1453, %r1059, %r1060`, which does not depend
on the order of the thread's maximum and the received one (`Flow.maxE_swap`). So two lanes with
the same entry numbers and running maximum that receive each other's maximum have the same shared
numbers and `alpha` after the exchange, whatever their words (`afterS_pf`, `afterS_al_pair`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lk

noncomputable section
set_option maxRecDepth 100000

/-- The word the shuffle of the row maximum sends: `ownV` of the 64 words. -/
abbrev D.ownW (d : D) : Value := ownV fun k => (d.stg.fsv k).1

/-! ### The scalars on score words -/

theorem setpE_ereal {c : FCmp} {cmp : Cmp} {va vb : Value} {x y : EReal}
    (hc : fcmpBase c = some cmp) (ha : readEReal .f32 va = some (.ok x))
    (hb : readEReal .f32 vb = some (.ok y)) :
    setpE c false va vb = .ok (erealCompare cmp x y) := by
  unfold setpE idealSetp
  simp [hc, ha, hb, bindRead, pure, Except.pure]

theorem subE_ereal {va vb : Value} {x y z : EReal} (ha : readEReal .f32 va = some (.ok x))
    (hb : readEReal .f32 vb = some (.ok y)) (hz : addEReal x (-y) = some z) :
    subE false va vb = .ok (erealValue .f32 z) := by
  unfold subE idealSub
  simp [ha, hb, hz, bindRead, pure, Except.pure]

theorem mulE_ereal {va vb : Value} {x y z : EReal} (ha : readEReal .f32 va = some (.ok x))
    (hb : readEReal .f32 vb = some (.ok y)) (hz : mulEReal x y = some z) :
    mulE false va vb = .ok (erealValue .f32 z) := by
  unfold mulE idealMul
  simp [ha, hb, hz, bindRead, pure, Except.pure]

theorem movE_ok4 {v : Value} (h : v.bytes = 4) : movE v = .ok v := by
  simp [movE, h]

section
variable {d : D} {r : Value} (hA : StA d r)
include hA

theorem t1_real : d.t1 r = erealValue .f32 (d.mnE (eOf r)) := by
  have hown : d.ownE ≠ ⊤ := lt_top_iff_ne_top.mp (cmaxW_lt_top hA.w _)
  have hmax : maxE [d.m, erealValue .f32 d.ownE, r] =
      .ok (erealValue .f32 (d.mnE (eOf r))) := by
    have := maxE_ereal3 hA.m.ne_top hown hA.r.ne_top
    rw [hA.m.eval, hA.r.eval] at this
    exact this
  simp only [D.t1, D.t1E, ownV_fsv hA.w, hmax, okVal]

theorem t2_real : d.t2 r = decide (d.mnE (eOf r) = ⊥) := by
  unfold D.t2 D.t2E
  rw [t1_real hA, setpE_ereal rfl (readEReal_erealValue hA.E_ne_top) readEReal_inf]
  rfl

theorem t3_real : d.t3 r = m1064V (d.mnE (eOf r)) := by
  unfold D.t3 D.t3E m1064V
  rw [t2_real hA]
  by_cases hb : d.mnE (eOf r) = ⊥
  · simp only [hb, decide_true, ↓reduceIte]
    rfl
  · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [t1_real hA, movE_ok4 (readEReal_f32_bytes (readEReal_erealValue hA.E_ne_top))]
    rfl

theorem t4_real : d.t4 r = erealValue .f32 (d.dE (eOf r)) := by
  have hadd : addEReal (eOf d.m) (-(mSE (d.mnE (eOf r)))) = some (d.dE (eOf r)) := by
    unfold addEReal D.dE D.mE
    rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
    rintro (⟨hx, -⟩ | ⟨-, h⟩)
    · exact hA.m.ne_top hx
    · exact mSE_ne_bot (EReal.neg_eq_top_iff.mp h)
  unfold D.t4 D.t4E
  rw [t3_real hA, subE_ereal (readEReal_sw hA.m) (readEReal_m1064 hA.E_ne_top) hadd]
  rfl

theorem t5_real : d.t5 r = erealValue .f32 (d.aE (eOf r)) := by
  have hs : (0 : ℝ) < slOf d.e := sl_pos hA.ok
  have hmul : mulEReal (slOf d.e : EReal) (d.dE (eOf r)) = some (d.aE (eOf r)) := by
    unfold mulEReal D.aE
    rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hs.ne' (by exact_mod_cast h)
    · rcases h with h | h
      · exact EReal.coe_ne_top _ h
      · exact EReal.coe_ne_bot _ h
  unfold D.t5 D.t5E
  have hsl : readEReal .f32 (.float .f32 (slOf d.e)) = some (.ok (slOf d.e : EReal)) := by
    simp [readEReal, pure, Except.pure]
  rw [t4_real hA, mulE_ereal hsl (readEReal_erealValue hA.dE_ne_top) hmul]
  rfl

theorem t6_real : d.t6 r = d.keepB (eOf r) := by
  unfold D.t6 D.t6E D.keepB
  rw [t5_real hA, setpE_ereal rfl (readEReal_erealValue hA.aE_ne_top) readEReal_m8, hA.aE_eq]
  simp only [okB, erealCompare, Softmax.Keep, ge_iff_le]
  exact decide_eq_decide.mpr Iff.rfl

theorem t7_real : d.t7 r = .float .f32 (Softmax.pow2 (d.aE (eOf r))) := by
  simp only [D.t7, D.t7E, t5_real hA, ex2E_ereal hA.aE_ne_top, okVal]

theorem t8_real : d.t8 r = d.alV (eOf r) := by
  unfold D.t8 D.t8E D.alV
  rw [t6_real hA, t7_real hA, hA.aE_eq]
  unfold D.keepB
  by_cases hk : Softmax.Keep (d.aLog (eOf r))
  · simp only [hk, decide_true, ↓reduceIte]
    rfl
  · simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl

end

/-! ### The successor's fields -/

theorem afterS_e (L : Launch) (g : Nat) (d : D) (r : Value) : (d.afterS L g r).e = d.e := by
  unfold D.afterS; split <;> rfl

theorem afterS_m (L : Launch) (g : Nat) (d : D) (r : Value) : (d.afterS L g r).m = d.m := by
  unfold D.afterS; split <;> rfl

theorem afterS_site (L : Launch) (g : Nat) (d : D) (r : Value) :
    (d.afterS L g r).site = .shfl6 := by
  unfold D.afterS; split <;> rfl

theorem afterS_i (L : Launch) (g : Nat) (d : D) (r : Value) : (d.afterS L g r).i = d.i := by
  unfold D.afterS; split <;> rfl

/-- **The successor's new maximum, decision, `alpha` and its real number** are the outcomes of
the scalar instructions, in both cases. -/
theorem afterS_scal (L : Launch) (g : Nat) {d : D} (r : Value) (hok : d.e.Ok) :
    (d.afterS L g r).stg.mn = d.t1 r ∧ (d.afterS L g r).stg.kp = d.t6 r ∧
      (d.afterS L g r).stg.al = d.t8 r ∧ (d.afterS L g r).stg.alr = alrOf (d.t8 r) := by
  unfold D.afterS
  split
  · rename_i hR
    have hA : StA d r := ⟨hR.1, hR.2.1, hR.2.2, hok⟩
    refine ⟨(t1_real hA).symm, (t6_real hA).symm, (t8_real hA).symm, ?_⟩
    rw [t8_real hA, alrOf_eq (readEReal_alV d (eOf r))]
    rfl
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### Two lanes that receive each other's maximum -/

theorem t1_swap {d d' : D} (hm : d.m = d'.m) : d.t1 d'.ownW = d'.t1 d.ownW := by
  unfold D.t1 D.t1E
  rw [hm]
  exact (maxE_swap _ _ _).okVal _

theorem t68_congr {d d' : D} {r r' : Value} (he : d.e = d'.e) (hm : d.m = d'.m)
    (h1 : d.t1 r = d'.t1 r') : d.t6 r = d'.t6 r' ∧ d.t8 r = d'.t8 r' := by
  have h3 : d.t3 r = d'.t3 r' := by unfold D.t3 D.t3E D.t2 D.t2E; rw [h1]
  have h5 : d.t5 r = d'.t5 r' := by simp only [D.t5, D.t5E, D.t4, D.t4E, h3, he, hm]
  have h6 : d.t6 r = d'.t6 r' := by simp only [D.t6, D.t6E, h5]
  refine ⟨h6, ?_⟩
  simp only [D.t8, D.t8E, D.t7, D.t7E, h5, h6]

/-- **The partners' shared numbers after the exchange of the row maximum**, on any words. -/
theorem afterS_pf (L : Launch) {g g' : Nat} {d d' : D} (h : pf d = pf d') (hok : d.e.Ok)
    (hok' : d'.e.Ok) : pf (d.afterS L g d'.ownW) = pf (d'.afterS L g' d.ownW) := by
  unfold pf at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨he, hm, -, -⟩ := h
  have h1 := t1_swap (d := d) (d' := d') hm
  obtain ⟨h6, -⟩ := t68_congr he hm h1
  obtain ⟨a1, a2, -, -⟩ := afterS_scal L g d'.ownW hok
  obtain ⟨b1, b2, -, -⟩ := afterS_scal L g' d.ownW hok'
  unfold pf
  rw [afterS_e, afterS_e, afterS_m, afterS_m, a1, a2, b1, b2, he, hm, h1, h6]

/-- **The partners' `alpha` after the exchange of the row maximum**, on any words. -/
theorem afterS_al_pair (L : Launch) {g g' : Nat} {d d' : D} (he : d.e = d'.e) (hm : d.m = d'.m)
    (hok : d.e.Ok) (hok' : d'.e.Ok) :
    (d.afterS L g d'.ownW).stg.al = (d'.afterS L g' d.ownW).stg.al ∧
      (d.afterS L g d'.ownW).stg.alr = (d'.afterS L g' d.ownW).stg.alr := by
  have h1 := t1_swap (d := d) (d' := d') hm
  obtain ⟨-, h8⟩ := t68_congr he hm h1
  obtain ⟨-, -, a3, a4⟩ := afterS_scal L g d'.ownW hok
  obtain ⟨-, -, b3, b4⟩ := afterS_scal L g' d.ownW hok'
  exact ⟨by rw [a3, b3, h8], by rw [a4, b4, h8]⟩

/-! ### The step of the exchange -/

/-- **A followed step of the exchange of the row maximum** goes to `D.afterS` of the received
word. -/
theorem next_shfl5_eq {L : Launch} {g : Nat} {d d' : D} {e : Event} (hs : d.site = .shfl5)
    (hn : next L g d e = some (some d')) :
    ∃ m av bv cv r o, e.kind = .shfl m av bv cv r o ∧ d' = d.afterS L g r := by
  simp only [next, hs] at hn
  split at hn
  · rename_i m av bv cv r o hk
    refine ⟨m, av, bv, cv, r, o, hk, ?_⟩
    unfold D.afterS
    split_ifs at hn ⊢ <;> exact (Option.some.inj (Option.some.inj hn)).symm
  · cases hn

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
