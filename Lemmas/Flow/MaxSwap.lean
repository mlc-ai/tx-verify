-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatDat

@[expose] public section

/-! # `max.f32` of three sources does not depend on the order of the last two

A proof tool. `max.f32 d, a, b, c` combines its sources from the left (`minMaxOp`), and the ideal
reading (ASM-IDEAL) reads them in the extended reals, declining on a NaN. The outcome (`maxE`)
has the same value and faults at the same operands when `b` and `c` are swapped (`maxE_swap`):

* where all three read as extended reals, `max (max x y) z` is symmetric in `y`, `z`;
* where one reads as a NaN, the Core rule `max_num` gives the larger of the non-NaN data (`-0`
  below `+0`), an opaque NaN when all are NaN; this is a commutative and associative operation on
  the data `classify` gives, which never contain the datum `.fin 0` (`classify_nz`);
* where one does not read (no `.f32` datum), both orders fault (possibly with another fault).

`minMax_comm`, `minMax_assoc` are the facts about `FVal.minMax`. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ### The data `classify` gives -/

/-- A datum other than the number `0` written as `.fin` (the decoder writes it `.zero`). -/
def _root_.PTX.FVal.Nz : FVal → Prop
  | .fin q => q ≠ 0
  | _ => True

theorem fieldVal_nz (eb mb F : Nat) (neg : Bool) : (Layout.fieldVal eb mb F neg).Nz := by
  unfold Layout.fieldVal
  split_ifs with hF hn
  · trivial
  · exact neg_ne_zero.mpr (Layout.magnitude_pos (eb := eb) (mb := mb) (Nat.pos_of_ne_zero hF)).ne'
  · exact (Layout.magnitude_pos (eb := eb) (mb := mb) (Nat.pos_of_ne_zero hF)).ne'

theorem decode_nz {eb mb : Nat} {signed : Bool} {sp : Specials} {n : Nat} {v : FVal}
    (h : (Layout.binary eb mb signed sp).decode n = some v) : v.Nz := by
  rcases Layout.decode_binary_cases h with h1 | h1 | ⟨h1, -⟩ <;> subst h1
  · trivial
  · exact fieldVal_nz _ _ _ _
  · trivial

theorem classify_nz {fmt : FloatFmt} {v : Value} {x : FVal} (h : classify fmt v = .ok x) :
    x.Nz := by
  unfold classify at h
  split at h
  · split_ifs at h
    cases h; trivial
  · split at h
    · split_ifs at h
      split at h
      · rename_i y hy
        cases h
        cases fmt <;> exact decode_nz hy
      · cases h
    · cases h

/-! ### `max_num` on the data -/

/-- `max_num` (`FVal.minMax true false`). -/
def mx (x y : FVal) : FVal := FVal.minMax true false x y

macro "fcases" x:ident : tactic => `(tactic| rcases $x:ident with ⟨_ | _⟩ | _ | ⟨_ | _⟩ | _)

/-- Unfold `FVal.lt` to propositions, then the numbers. -/
macro "ltp" : tactic => `(tactic| (
  simp only [FVal.lt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true, ← Bool.not_eq_true, not_or, not_and] at *
  simp_all [FVal.toRat, FVal.Nz, FVal.isNaN]))

theorem lt_irrefl (x : FVal) : ¬ FVal.lt true x x = true := by
  fcases x <;> ltp

theorem lt_asymm {x y : FVal} (h : FVal.lt true x y = true) : ¬ FVal.lt true y x = true := by
  fcases x <;> fcases y <;> ltp <;> linarith

theorem lt_trans {x y z : FVal} (h1 : FVal.lt true x y = true) (h2 : FVal.lt true y z = true) :
    FVal.lt true x z = true := by
  fcases x <;> fcases y <;> fcases z <;> ltp <;> linarith

theorem lt_total {x y : FVal} (hx : x.isNaN = false) (hy : y.isNaN = false) (nx : x.Nz)
    (ny : y.Nz) (hne : x ≠ y) : FVal.lt true x y = true ∨ FVal.lt true y x = true := by
  fcases x <;> fcases y <;>
    simp only [FVal.lt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] <;>
    simp only [FVal.toRat] <;> simp_all [FVal.Nz, FVal.isNaN] <;>
    (first | exact lt_or_gt_of_ne hne | exact lt_or_gt_of_ne nx | exact lt_or_gt_of_ne ny |
      exact (lt_or_gt_of_ne nx).symm | exact (lt_or_gt_of_ne ny).symm |
      exact fun h => nx h.symm | exact fun h => ny h.symm | exact Ne.symm nx | exact Ne.symm ny |
      skip)

theorem lt_tri {x y : FVal} (hx : x.isNaN = false) (hy : y.isNaN = false) (nx : x.Nz)
    (ny : y.Nz) : FVal.lt true x y = true ∨ x = y ∨ FVal.lt true y x = true := by
  by_cases h : x = y
  · exact .inr (.inl h)
  · rcases lt_total hx hy nx ny h with h | h
    · exact .inl h
    · exact .inr (.inr h)

theorem mx_num {x y : FVal} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    mx x y = if FVal.lt true y x then x else y := by
  simp [mx, FVal.minMax, hx, hy]

theorem mx_nanL {x y : FVal} (hx : x.isNaN = true) :
    mx x y = if y.isNaN then .nan none else y := by
  cases hy : y.isNaN <;> simp [mx, FVal.minMax, hx, hy]

theorem mx_nanR {x y : FVal} (hx : x.isNaN = false) (hy : y.isNaN = true) : mx x y = x := by
  simp [mx, FVal.minMax, hx, hy]

theorem mx_isNaN {x y : FVal} : (mx x y).isNaN = (x.isNaN && y.isNaN) := by
  cases hx : x.isNaN <;> cases hy : y.isNaN
  · rw [mx_num hx hy]; split <;> simp [hx, hy]
  · rw [mx_nanR hx hy, hx]; rfl
  · rw [mx_nanL hx, hy]; simp [hy]
  · rw [mx_nanL hx, hy]; rfl

theorem mx_nz {x y : FVal} (nx : x.Nz) (ny : y.Nz) : (mx x y).Nz := by
  cases hx : x.isNaN <;> cases hy : y.isNaN
  · rw [mx_num hx hy]; split <;> assumption
  · rw [mx_nanR hx hy]; exact nx
  · rw [mx_nanL hx, hy]; exact ny
  · rw [mx_nanL hx, hy]; trivial

theorem mx_comm {x y : FVal} (nx : x.Nz) (ny : y.Nz) : mx x y = mx y x := by
  cases hx : x.isNaN <;> cases hy : y.isNaN
  · rw [mx_num hx hy, mx_num hy hx]
    rcases lt_tri hx hy nx ny with h | rfl | h
    · simp [h, lt_asymm h]
    · rfl
    · simp [h, lt_asymm h]
  · rw [mx_nanR hx hy, mx_nanL hy, hx]; rfl
  · rw [mx_nanL hx, mx_nanR hy hx, hy]; rfl
  · rw [mx_nanL hx, mx_nanL hy, hx, hy]; rfl

/-- `m` is a datum of `S` that no datum of `S` is above. -/
def Top (m : FVal) (S : List FVal) : Prop := m ∈ S ∧ ∀ u ∈ S, ¬ FVal.lt true m u = true

theorem top_unique {S : List FVal} (hS : ∀ u ∈ S, u.isNaN = false ∧ u.Nz) {m m' : FVal}
    (h : Top m S) (h' : Top m' S) : m = m' := by
  by_contra hne
  obtain ⟨a, b⟩ := hS m h.1
  obtain ⟨a', b'⟩ := hS m' h'.1
  rcases lt_total a a' b b' hne with hl | hl
  · exact h.2 m' h'.1 hl
  · exact h'.2 m h.1 hl

theorem notlt_trans {a b c : FVal} (ha : a.isNaN = false) (hb : b.isNaN = false)
    (na : a.Nz) (nb : b.Nz) (h1 : ¬ FVal.lt true a b = true) (h2 : ¬ FVal.lt true b c = true) :
    ¬ FVal.lt true a c = true := by
  intro h
  by_cases e : a = b
  · subst e; exact h2 h
  · rcases lt_total ha hb na nb e with hl | hl
    · exact h1 hl
    · exact h2 (lt_trans hl h)

theorem mx_top {x y : FVal} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    (mx x y = x ∨ mx x y = y) ∧ ¬ FVal.lt true (mx x y) x = true ∧
      ¬ FVal.lt true (mx x y) y = true := by
  rw [mx_num hx hy]
  split
  · rename_i h
    exact ⟨.inl rfl, lt_irrefl x, lt_asymm h⟩
  · rename_i h
    exact ⟨.inr rfl, h, lt_irrefl y⟩

theorem mx_top3 {x y z : FVal} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hz : z.isNaN = false) (nx : x.Nz) (ny : y.Nz) (nz : z.Nz) :
    Top (mx (mx x y) z) [x, y, z] := by
  have hn : (mx x y).isNaN = false := by rw [mx_isNaN, hx]; rfl
  obtain ⟨e1, a1, b1⟩ := mx_top hx hy
  obtain ⟨e2, a2, b2⟩ := mx_top hn hz
  have nn : (mx x y).Nz := mx_nz nx ny
  have hm : (mx (mx x y) z).isNaN = false := by rw [mx_isNaN, hn]; rfl
  have nm : (mx (mx x y) z).Nz := by rcases e2 with e | e <;> rw [e] <;> first | exact nn | exact nz
  refine ⟨?_, fun u hu => ?_⟩
  · rcases e2 with e | e <;> rw [e]
    · rcases e1 with e' | e' <;> rw [e'] <;> simp
    · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact notlt_trans hm hn nm nn a2 a1
    · exact notlt_trans hm hn nm nn a2 b1
    · exact b2

theorem mx_assoc {x y z : FVal} (nx : x.Nz) (ny : y.Nz) (nz : z.Nz) :
    mx (mx x y) z = mx x (mx y z) := by
  cases hx : x.isNaN <;> cases hy : y.isNaN <;> cases hz : z.isNaN
  · rw [mx_comm nx (mx_nz ny nz)]
    have hyz : (mx y z).isNaN = false := by rw [mx_isNaN, hy]; rfl
    have t1 := mx_top3 hx hy hz nx ny nz
    have t2 := mx_top3 hy hz hx ny nz nx
    have hS : ∀ u ∈ [x, y, z], u.isNaN = false ∧ u.Nz := by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> exact ⟨‹_›, ‹_›⟩
    refine top_unique hS t1 ⟨?_, fun u hu => t2.2 u ?_⟩
    · have := t2.1; simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢; tauto
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu ⊢; tauto
  · have h1 : (mx x y).isNaN = false := by rw [mx_isNaN, hx]; rfl
    rw [mx_nanR h1 hz, mx_nanR hy hz]
  · rw [mx_nanR hx hy, mx_nanL hy, hz]; rfl
  · rw [mx_nanR hx hy, mx_nanR hx hz, mx_nanL hy, hz]
    simp only [↓reduceIte]
    exact (mx_nanR hx rfl).symm
  · have h1 : (mx y z).isNaN = false := by rw [mx_isNaN, hy]; rfl
    rw [mx_nanL hx, hy, mx_nanL hx, h1]; rfl
  · rw [mx_nanL hx, hy, mx_nanL hx, mx_isNaN, hy, hz]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  · rw [mx_nanL hx, hy, mx_nanL hy, hz]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [mx_nanL rfl, hz, mx_nanL hx, hz]
  · rw [mx_nanL hx, hy, mx_nanL hy, hz]
    simp only [↓reduceIte]
    rw [mx_nanL rfl, hz, mx_nanL hx]; rfl

theorem mx_swap {a b c : FVal} (na : a.Nz) (nb : b.Nz) (nc : c.Nz) :
    mx (mx a b) c = mx (mx a c) b := by
  rw [mx_assoc na nb nc, mx_comm nb nc, ← mx_assoc na nc nb]

/-! ### The Core rule of `max.f32` of three sources -/

theorem maxI_lane (x y z : FVal) :
    FloatInstr.lane maxI [x, y, z] = some (.val (mx (mx x y) z)) := by
  simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.flushIn, minMaxOp, mx,
    ty1]

theorem coreFloat_max3 (a b c : Value) :
    coreFloat maxI [a, b, c] = (do
      let x ← classify .f32 a
      let y ← classify .f32 b
      let z ← classify .f32 c
      pure ((mx (mx x y) z).toValue .f32)) := by
  simp only [coreFloat, ty1, show List.range 1 = [0] from rfl, List.mapM_cons, List.mapM_nil,
    floatLane, bind, Except.bind, pure, Except.pure, ite_true]
  cases classify .f32 a <;> cases classify .f32 b <;> cases classify .f32 c <;>
    simp [maxI_lane, throw, throwThe, MonadExceptOf.throw]

/-- Two outcomes are both faults, or the same value. -/
def SameOk (e e' : Exec Value) : Prop := ∀ v, e = .ok v ↔ e' = .ok v

theorem SameOk.toBool {e e' : Exec Value} (h : SameOk e e') : e.toBool = e'.toBool := by
  rcases e with x | v <;> rcases e' with x' | v'
  · rfl
  · exact absurd ((h v').2 rfl) (by simp)
  · exact absurd ((h v).1 rfl) (by simp)
  · rfl

theorem SameOk.okVal {e e' : Exec Value} (h : SameOk e e') (dflt : Value) :
    okVal dflt e = okVal dflt e' := by
  rcases e with x | v <;> rcases e' with x' | v'
  · rfl
  · exact absurd ((h v').2 rfl) (by simp)
  · exact absurd ((h v).1 rfl) (by simp)
  · rw [(h v).1 rfl]

theorem coreFloat_max3_swap (a b c : Value) :
    SameOk (coreFloat maxI [a, b, c]) (coreFloat maxI [a, c, b]) := by
  intro v
  rw [coreFloat_max3, coreFloat_max3]
  rcases ha : classify .f32 a with e | x <;> simp only [bind, Except.bind]
  rcases hb : classify .f32 b with e | y <;> rcases hc : classify .f32 c with e' | z <;>
    simp [pure, Except.pure]
  rw [mx_swap (classify_nz ha) (classify_nz hb) (classify_nz hc)]

theorem readEReal_error_classify {v : Value} {e : Fault}
    (h : readEReal .f32 v = some (.error e)) : classify .f32 v = .error e := by
  unfold readEReal at h
  split at h
  · split_ifs at h
    · simp [pure, Except.pure] at h
    · simp only [readEReal.ofDatum] at h
      split at h <;> simp_all [pure, Except.pure]
  · simp only [readEReal.ofDatum] at h
    split at h <;> simp_all [pure, Except.pure]

theorem coreFloat_max3_error_b {a b c : Value} {e : Fault} (h : classify .f32 b = .error e) :
    ∀ v, coreFloat maxI [a, b, c] ≠ .ok v := by
  intro v
  rw [coreFloat_max3]
  rcases classify .f32 a with e | x <;> simp [bind, Except.bind, h]

theorem coreFloat_max3_error_c {a b c : Value} {e : Fault} (h : classify .f32 c = .error e) :
    ∀ v, coreFloat maxI [a, b, c] ≠ .ok v := by
  intro v
  rw [coreFloat_max3]
  rcases classify .f32 a with e | x <;> rcases classify .f32 b with e | y <;>
    simp [bind, Except.bind, h]

/-- **`max.f32 d, a, b, c` does not depend on the order of `b` and `c`**: the same value, or a
fault in both orders. -/
theorem maxE_swap (a b c : Value) : SameOk (maxE [a, b, c]) (maxE [a, c, b]) := by
  intro v
  unfold maxE idealMax
  rcases ha : readEReal .f32 a with _ | (ea | x) <;> simp only [bindRead, ha]
  · exact coreFloat_max3_swap a b c v
  rcases hb : readEReal .f32 b with _ | (eb | y) <;>
    rcases hc : readEReal .f32 c with _ | (ec | z) <;> simp only [bindRead, hb, hc]
  all_goals first
    | exact coreFloat_max3_swap a b c v
    | (simp only [pure, Except.pure]; rw [max_assoc, max_comm y z, ← max_assoc])
    | (have := coreFloat_max3_error_b (a := a) (b := c) (c := b)
        (readEReal_error_classify hc) v; simp [this]; done)
    | (have := coreFloat_max3_error_b (a := a) (b := b) (c := c)
        (readEReal_error_classify hb) v; simp [this]; done)
    | (have := coreFloat_max3_error_c (a := a) (b := b) (c := c)
        (readEReal_error_classify hc) v; simp [this]; done)
    | (have := coreFloat_max3_error_c (a := a) (b := c) (c := b)
        (readEReal_error_classify hb) v; simp [this]; done)
    | simp

end

end PTX.Flow
