-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Ex2Core
public import Lemmas.Flow.FmaPairCore
public import Lemmas.Flow.OutLit
import Lemmas.Flow.Step.RuleStep
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The conditions of a generated run, by kinds of values

A proof tool (kernel-side, for promotion next to `Lemmas/Flow/OutLit.lean`). A generated run
(`Tools/out_gen.py`) is a piece under the condition `xCond V items`: each item's outcome is no
fault. This file decides the condition by evaluation: a *kind* (`Kd`) is a set of values (`Kd.Has`),
and each item kind maps the kinds of its sources to the kind of its destination, or rejects them
(`kItem`). `kRun` runs the items over a kind per register; when it accepts, every item's condition
holds and every register after the run has its kind (`kRun_sound`), for every start value whose
registers have their kinds. Checking `kOk K items = true` is a kernel evaluation on literals.

Kinds of four-byte values (`SK`, ordered `pw ≤ nn ≤ fl ≤ ni ≤ w4`) are *clean* (four bytes, no
slice, a pattern within 32 bits, `Clean`) and read, as the ideal assumption reads an `.f32`
operand, as a positive real (`pw`), a real `≥ 0` (`nn`), a real (`fl`), a real or the pattern of
`-∞` (`ni`), or anything (`w4`). `pr k` is a pair whose two halves have kind `k`, `h16` a `bf16`
payload or the masked pattern `0xFF80`. The two role readings of `XItem.fn` items are given by
their specification (`WidenSpec`, `PackSpec`), checked once per function (`kFns`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- The pattern of `.f32` negative infinity. -/
abbrev negInf32 : Value := .bits 32 (BitVec.ofNat 64 4286578688)

/-- A four-byte value that is no slice and whose pattern fits 32 bits. -/
def Clean (v : Value) : Prop :=
  v.bytes = 4 ∧ (∀ w o n, v ≠ .slice w o n) ∧ (∀ w x, v = .bits w x → x.toNat < 2 ^ 32)

/-- Kinds of four-byte values. -/
inductive SK where
  | pw | nn | fl | ni | w4
  deriving DecidableEq

namespace SK

def rank : SK → Nat
  | pw => 0 | nn => 1 | fl => 2 | ni => 3 | w4 => 4

def le (a b : SK) : Bool := Nat.ble a.rank b.rank

def max (a b : SK) : SK := if a.le b then b else a

/-- The values of a kind. -/
def Has : SK → Value → Prop
  | pw, v => Clean v ∧ ∃ r : ℝ, 0 < r ∧ readEReal .f32 v = some (.ok (r : EReal))
  | nn, v => Clean v ∧ ∃ r : ℝ, 0 ≤ r ∧ readEReal .f32 v = some (.ok (r : EReal))
  | fl, v => Clean v ∧ ∃ r : ℝ, readEReal .f32 v = some (.ok (r : EReal))
  | ni, v => (Clean v ∧ ∃ r : ℝ, readEReal .f32 v = some (.ok (r : EReal))) ∨ v = negInf32
  | w4, v => Clean v

end SK

/-- Kinds of register values. -/
inductive Kd where
  | no | h16
  | s (k : SK)
  | pr (k : SK)
  deriving DecidableEq

/-- The values of a kind (`no`: any value). -/
def Kd.Has : Kd → Value → Prop
  | .no, _ => True
  | .h16, v => (∃ r, v = .float .bf16 r) ∨ v = .bits 16 (BitVec.ofNat 64 0xFF80)
  | .s k, v => k.Has v
  | .pr k, v => UnpackOk v ∧ k.Has (splitValue 64 v).1 ∧ k.Has (splitValue 64 v).2

/-! ### Facts about the kinds -/

theorem clean_float (r : ℝ) : Clean (.float .f32 r) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro _ _ _ h; cases h
  · intro _ _ h; cases h

theorem clean_negInf : Clean negInf32 := by
  refine ⟨rfl, ?_, ?_⟩
  · intro _ _ _ h; cases h
  · intro _ _ h; cases h; decide

theorem readEReal_float (r : ℝ) : readEReal .f32 (.float .f32 r) = some (.ok (r : EReal)) := by
  simp [readEReal, pure, Except.pure]

theorem readEReal_negInf : readEReal .f32 negInf32 = some (.ok ⊥) := by
  have hz := classify_bits (fmt := .f32) (n := 0xFF800000) (x := .inf true) (by decide) (by decide)
  change readEReal.ofDatum (classify .f32 (.bits 32 (BitVec.ofNat 64 0xFF800000))) = some (.ok ⊥)
  change classify .f32 (.bits 32 (BitVec.ofNat 64 0xFF800000)) = .ok (.inf true) at hz
  rw [hz]
  rfl

theorem erealValue_bot : erealValue .f32 ⊥ = negInf32 := by
  unfold erealValue
  simp only [bot_ne_top, ↓reduceIte]
  rfl

theorem SK.clean : ∀ {k : SK} {v : Value}, k.Has v → Clean v
  | .pw, _, h => h.1
  | .nn, _, h => h.1
  | .fl, _, h => h.1
  | .ni, _, h => by
    rcases h with h | rfl
    · exact h.1
    · exact clean_negInf
  | .w4, _, h => h

/-- The reading of a value of a kind up to `ni`: a real, or `⊥` for the kinds that admit `-∞`. -/
theorem SK.reads : ∀ {k : SK} {v : Value}, k.le .ni = true → k.Has v →
    (∃ r : ℝ, readEReal .f32 v = some (.ok (r : EReal))) ∨ readEReal .f32 v = some (.ok ⊥)
  | .pw, _, _, h => .inl (let ⟨r, _, h⟩ := h.2; ⟨r, h⟩)
  | .nn, _, _, h => .inl (let ⟨r, _, h⟩ := h.2; ⟨r, h⟩)
  | .fl, _, _, h => .inl h.2
  | .ni, _, _, h => by
    rcases h with h | rfl
    · exact .inl h.2
    · exact .inr readEReal_negInf
  | .w4, _, h, _ => by cases h

theorem SK.reads_fl : ∀ {k : SK} {v : Value}, k.le .fl = true → k.Has v →
    ∃ r : ℝ, readEReal .f32 v = some (.ok (r : EReal))
  | .pw, _, _, h => let ⟨r, _, h⟩ := h.2; ⟨r, h⟩
  | .nn, _, _, h => let ⟨r, _, h⟩ := h.2; ⟨r, h⟩
  | .fl, _, _, h => h.2
  | .ni, _, h, _ => by cases h
  | .w4, _, h, _ => by cases h

theorem SK.reads_nn : ∀ {k : SK} {v : Value}, k.le .nn = true → k.Has v →
    ∃ r : ℝ, 0 ≤ r ∧ readEReal .f32 v = some (.ok (r : EReal))
  | .pw, _, _, h => let ⟨r, hr, h⟩ := h.2; ⟨r, hr.le, h⟩
  | .nn, _, _, h => h.2
  | .fl, _, h, _ => by cases h
  | .ni, _, h, _ => by cases h
  | .w4, _, h, _ => by cases h

theorem SK.reads_pw : ∀ {k : SK} {v : Value}, k.le .pw = true → k.Has v →
    ∃ r : ℝ, 0 < r ∧ readEReal .f32 v = some (.ok (r : EReal))
  | .pw, _, _, h => h.2
  | .nn, _, h, _ => by cases h
  | .fl, _, h, _ => by cases h
  | .ni, _, h, _ => by cases h
  | .w4, _, h, _ => by cases h

/-- A value of the ideal arithmetic with a finite result has every kind its sign allows. -/
theorem has_float_fl (r : ℝ) : SK.fl.Has (.float .f32 r) := ⟨clean_float r, r, readEReal_float r⟩

theorem has_float_nn {r : ℝ} (h : 0 ≤ r) : SK.nn.Has (.float .f32 r) :=
  ⟨clean_float r, r, h, readEReal_float r⟩

theorem SK.mono : ∀ {a b : SK} {v : Value}, a.le b = true → a.Has v → b.Has v := by
  intro a b v hab h
  cases a <;> cases b <;> simp only [le, rank, Nat.ble_eq] at hab <;> try omega
  all_goals first
    | exact SK.clean h
    | exact ⟨h.1, let ⟨r, hr, e⟩ := h.2; ⟨r, hr.le, e⟩⟩
    | exact ⟨h.1, let ⟨r, _, e⟩ := h.2; ⟨r, e⟩⟩
    | exact .inl ⟨h.1, let ⟨r, _, e⟩ := h.2; ⟨r, e⟩⟩
    | exact .inl h

/-! ### Lanes: the extended reals of the kinds -/

/-- The extended reals a value of kind `k` (up to `ni`) reads as. -/
def SK.Lane : SK → EReal → Prop
  | pw, x => ∃ r : ℝ, 0 < r ∧ x = r
  | nn, x => ∃ r : ℝ, 0 ≤ r ∧ x = r
  | fl, x => ∃ r : ℝ, x = r
  | ni, x => (∃ r : ℝ, x = r) ∨ x = ⊥
  | w4, _ => False

theorem SK.lane_of : ∀ {k : SK} {v : Value}, k.le .ni = true → k.Has v →
    ∃ x, readEReal .f32 v = some (.ok x) ∧ k.Lane x
  | .pw, _, _, h => let ⟨r, hr, e⟩ := h.2; ⟨r, e, r, hr, rfl⟩
  | .nn, _, _, h => let ⟨r, hr, e⟩ := h.2; ⟨r, e, r, hr, rfl⟩
  | .fl, _, _, h => let ⟨r, e⟩ := h.2; ⟨r, e, r, rfl⟩
  | .ni, _, _, h => by
    rcases h with h | rfl
    · obtain ⟨r, e⟩ := h.2
      exact ⟨r, e, .inl ⟨r, rfl⟩⟩
    · exact ⟨⊥, readEReal_negInf, .inr rfl⟩
  | .w4, _, h, _ => by cases h

theorem SK.has_erealValue : ∀ {k : SK} {x : EReal}, k.Lane x → k.Has (erealValue .f32 x)
  | .pw, _, ⟨r, hr, e⟩ => by
    subst e; rw [erealValue_coe]; exact ⟨clean_float r, r, hr, readEReal_float r⟩
  | .nn, _, ⟨r, hr, e⟩ => by
    subst e; rw [erealValue_coe]; exact ⟨clean_float r, r, hr, readEReal_float r⟩
  | .fl, _, ⟨r, e⟩ => by
    subst e; rw [erealValue_coe]; exact ⟨clean_float r, r, readEReal_float r⟩
  | .ni, _, h => by
    rcases h with ⟨r, e⟩ | e
    · subst e; rw [erealValue_coe]; exact .inl ⟨clean_float r, r, readEReal_float r⟩
    · subst e; rw [erealValue_bot]; exact .inr rfl
  | .w4, _, h => h.elim

theorem SK.lane_fl : ∀ {k : SK} {x : EReal}, k.le .fl = true → k.Lane x → ∃ r : ℝ, x = r
  | .pw, _, _, ⟨r, _, e⟩ => ⟨r, e⟩
  | .nn, _, _, ⟨r, _, e⟩ => ⟨r, e⟩
  | .fl, _, _, h => h
  | .ni, _, h, _ => by cases h
  | .w4, _, h, _ => by cases h

theorem SK.lane_nn : ∀ {k : SK} {x : EReal}, k.le .nn = true → k.Lane x →
    ∃ r : ℝ, 0 ≤ r ∧ x = r
  | .pw, _, _, ⟨r, hr, e⟩ => ⟨r, hr.le, e⟩
  | .nn, _, _, h => h
  | .fl, _, h, _ => by cases h
  | .ni, _, h, _ => by cases h
  | .w4, _, h, _ => by cases h

theorem SK.lane_pw : ∀ {k : SK} {x : EReal}, k.le .pw = true → k.Lane x →
    ∃ r : ℝ, 0 < r ∧ x = r
  | .pw, _, _, h => h
  | .nn, _, h, _ => by cases h
  | .fl, _, h, _ => by cases h
  | .ni, _, h, _ => by cases h
  | .w4, _, h, _ => by cases h

/-! ### The kind of each item's destination -/

namespace SK

theorem iteT {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem iteF {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

def mulK (a b : SK) : Option SK :=
  if a.le fl && b.le fl then some (if a.le nn && b.le nn then nn else fl)
  else if a == ni && b.le pw then some ni else none

def addK (a b : SK) : Option SK :=
  if a.le fl && b.le fl then some (if a.le nn && b.le nn then nn else fl) else none

def subK (a b : SK) : Option SK := if a.le fl && b.le fl then some fl else none

def fmaK (a b c : SK) : Option SK :=
  if a.le fl && b.le fl && c.le fl then some (if a.le nn && b.le nn && c.le nn then nn else fl)
  else if a == ni && b.le pw && c.le fl then some ni else none

def ex2K (a : SK) : Option SK := if a.le ni then some nn else none

theorem ni_of_some_mul {a b c : SK} (h : mulK a b = some c) : a.le ni = true ∧ b.le ni = true := by
  cases a <;> cases b <;> simp [mulK, le, rank] at h ⊢

theorem lane_mul {a b c : SK} {x y : EReal} (h : mulK a b = some c) (hx : a.Lane x)
    (hy : b.Lane y) : ∃ z, mulEReal x y = some z ∧ c.Lane z := by
  unfold mulK at h
  by_cases h1 : (a.le fl && b.le fl) = true
  · rw [iteT h1] at h
    simp only [Bool.and_eq_true] at h1
    obtain ⟨r, rfl⟩ := lane_fl h1.1 hx
    obtain ⟨s, rfl⟩ := lane_fl h1.2 hy
    refine ⟨_, mulEReal_coe r s, ?_⟩
    obtain rfl := Option.some.inj h.symm
    by_cases h2 : (a.le nn && b.le nn) = true
    · rw [iteT h2]
      simp only [Bool.and_eq_true] at h2
      obtain ⟨r', hr, e⟩ := lane_nn h2.1 hx
      obtain ⟨s', hs, e'⟩ := lane_nn h2.2 hy
      rw [EReal.coe_eq_coe_iff] at e e'
      subst e e'
      exact ⟨_, mul_nonneg hr hs, rfl⟩
    · rw [iteF h2]; exact ⟨_, rfl⟩
  · rw [iteF h1] at h
    by_cases h2 : (a == ni && b.le pw) = true
    · rw [iteT h2] at h
      obtain rfl := Option.some.inj h.symm
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨rfl, hb⟩ := h2
      obtain ⟨s, hs, rfl⟩ := lane_pw hb hy
      rcases hx with ⟨r, rfl⟩ | rfl
      · exact ⟨_, mulEReal_coe r s, .inl ⟨_, rfl⟩⟩
      · exact ⟨⊥, mulEReal_bot_pos hs, .inr rfl⟩
    · rw [iteF h2] at h; cases h

theorem lane_add {a b c : SK} {x y : EReal} (h : addK a b = some c) (hx : a.Lane x)
    (hy : b.Lane y) : ∃ z, addEReal x y = some z ∧ c.Lane z := by
  unfold addK at h
  by_cases h1 : (a.le fl && b.le fl) = true
  · rw [iteT h1] at h
    simp only [Bool.and_eq_true] at h1
    obtain ⟨r, rfl⟩ := lane_fl h1.1 hx
    obtain ⟨s, rfl⟩ := lane_fl h1.2 hy
    refine ⟨_, addEReal_coe r s, ?_⟩
    obtain rfl := Option.some.inj h.symm
    by_cases h2 : (a.le nn && b.le nn) = true
    · rw [iteT h2]
      simp only [Bool.and_eq_true] at h2
      obtain ⟨r', hr, e⟩ := lane_nn h2.1 hx
      obtain ⟨s', hs, e'⟩ := lane_nn h2.2 hy
      rw [EReal.coe_eq_coe_iff] at e e'
      subst e e'
      exact ⟨_, add_nonneg hr hs, rfl⟩
    · rw [iteF h2]; exact ⟨_, rfl⟩
  · rw [iteF h1] at h; cases h

theorem lane_sub {a b c : SK} {x y : EReal} (h : subK a b = some c) (hx : a.Lane x)
    (hy : b.Lane y) : ∃ z, addEReal x (-y) = some z ∧ c.Lane z := by
  unfold subK at h
  by_cases h1 : (a.le fl && b.le fl) = true
  · rw [iteT h1] at h
    simp only [Bool.and_eq_true] at h1
    obtain ⟨r, rfl⟩ := lane_fl h1.1 hx
    obtain ⟨s, rfl⟩ := lane_fl h1.2 hy
    obtain rfl := Option.some.inj h.symm
    exact ⟨_, addEReal_coe_neg r s, _, rfl⟩
  · rw [iteF h1] at h; cases h

theorem addEReal_bot_coe (z : ℝ) : addEReal ⊥ (z : EReal) = some ⊥ := by
  simp [addEReal]

theorem lane_fma {a b c d : SK} {x y z : EReal} (h : fmaK a b c = some d) (hx : a.Lane x)
    (hy : b.Lane y) (hz : c.Lane z) :
    ∃ w, (mulEReal x y).bind (addEReal · z) = some w ∧ d.Lane w := by
  unfold fmaK at h
  by_cases h1 : (a.le fl && b.le fl && c.le fl) = true
  · rw [iteT h1] at h
    simp only [Bool.and_eq_true] at h1
    obtain ⟨r, rfl⟩ := lane_fl h1.1.1 hx
    obtain ⟨s, rfl⟩ := lane_fl h1.1.2 hy
    obtain ⟨q, rfl⟩ := lane_fl h1.2 hz
    refine ⟨_, by rw [mulEReal_coe, Option.bind_some, addEReal_coe], ?_⟩
    obtain rfl := Option.some.inj h.symm
    by_cases h2 : (a.le nn && b.le nn && c.le nn) = true
    · rw [iteT h2]
      simp only [Bool.and_eq_true] at h2
      obtain ⟨r', hr, e⟩ := lane_nn h2.1.1 hx
      obtain ⟨s', hs, e'⟩ := lane_nn h2.1.2 hy
      obtain ⟨q', hq, e''⟩ := lane_nn h2.2 hz
      rw [EReal.coe_eq_coe_iff] at e e' e''
      subst e e' e''
      exact ⟨_, add_nonneg (mul_nonneg hr hs) hq, rfl⟩
    · rw [iteF h2]; exact ⟨_, rfl⟩
  · rw [iteF h1] at h
    by_cases h2 : (a == ni && b.le pw && c.le fl) = true
    · rw [iteT h2] at h
      obtain rfl := Option.some.inj h.symm
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨rfl, hb⟩, hc⟩ := h2
      obtain ⟨s, hs, rfl⟩ := lane_pw hb hy
      obtain ⟨q, rfl⟩ := lane_fl hc hz
      rcases hx with ⟨r, rfl⟩ | rfl
      · exact ⟨_, by rw [mulEReal_coe, Option.bind_some, addEReal_coe], .inl ⟨_, rfl⟩⟩
      · exact ⟨⊥, by rw [mulEReal_bot_pos hs, Option.bind_some, addEReal_bot_coe], .inr rfl⟩
    · rw [iteF h2] at h; cases h

theorem le_ni_of_mulK {a b c : SK} (h : mulK a b = some c) : c.le ni = true := by
  cases a <;> cases b <;> simp [mulK, le, rank] at h <;> subst h <;> rfl

theorem le_ni_of_addK {a b c : SK} (h : addK a b = some c) : c.le ni = true := by
  cases a <;> cases b <;> simp [addK, le, rank] at h <;> subst h <;> rfl

theorem le_ni_of_subK {a b c : SK} (h : subK a b = some c) : c.le ni = true := by
  cases a <;> cases b <;> simp [subK, le, rank] at h <;> subst h <;> rfl

theorem le_ni_of_fmaK {a b c d : SK} (h : fmaK a b c = some d) : d.le ni = true := by
  cases a <;> cases b <;> cases c <;> simp [fmaK, le, rank] at h <;> subst h <;> rfl

theorem args_of_addK {a b c : SK} (h : addK a b = some c) : a.le ni = true ∧ b.le ni = true := by
  cases a <;> cases b <;> simp [addK, le, rank] at h ⊢

theorem args_of_subK {a b c : SK} (h : subK a b = some c) : a.le ni = true ∧ b.le ni = true := by
  cases a <;> cases b <;> simp [subK, le, rank] at h ⊢

theorem args_of_fmaK {a b c d : SK} (h : fmaK a b c = some d) :
    a.le ni = true ∧ b.le ni = true ∧ c.le ni = true := by
  cases a <;> cases b <;> cases c <;> simp [fmaK, le, rank] at h ⊢

end SK

/-! ### The outcomes on values of the kinds -/

theorem pairRead_of_reads {v : Value} {x0 x1 : EReal}
    (h0 : readEReal .f32 (splitValue 64 v).1 = some (.ok x0))
    (h1 : readEReal .f32 (splitValue 64 v).2 = some (.ok x1)) :
    pairRead v = some (.ok (x0, x1)) := by
  simp only [pairRead, h0, h1, pure, Except.pure]

theorem mulE_reads {fz : Bool} {va vb : Value} {x y z : EReal}
    (hx : readEReal .f32 va = some (.ok x)) (hy : readEReal .f32 vb = some (.ok y))
    (hz : mulEReal x y = some z) : mulE fz va vb = .ok (erealValue .f32 z) := by
  simp only [mulE, idealMul, hx, hy, bindRead, hz, Option.map_some, pure, Except.pure]

theorem subE_reads {fz : Bool} {va vb : Value} {x y z : EReal}
    (hx : readEReal .f32 va = some (.ok x)) (hy : readEReal .f32 vb = some (.ok y))
    (hz : addEReal x (-y) = some z) : subE fz va vb = .ok (erealValue .f32 z) := by
  simp only [subE, idealSub, hx, hy, bindRead, hz, Option.map_some, pure, Except.pure]

theorem addE_reads {fz : Bool} {va vb : Value} {x y z : EReal}
    (hx : readEReal .f32 va = some (.ok x)) (hy : readEReal .f32 vb = some (.ok y))
    (hz : addEReal x y = some z) : floatE (addI fz) [va, vb] = .ok (erealValue .f32 z) := by
  simp only [floatE, idealVal, hx, hy, bindRead, hz, Option.map_some, pure, Except.pure]

theorem add2E_reads {va vb : Value} {x0 x1 y0 y1 z0 z1 : EReal}
    (hx : pairRead va = some (.ok (x0, x1))) (hy : pairRead vb = some (.ok (y0, y1)))
    (hz0 : addEReal x0 y0 = some z0) (hz1 : addEReal x1 y1 = some z1) :
    add2E va vb = .ok (.pair (erealValue .f32 z0) (erealValue .f32 z1)) := by
  simp only [add2E, idealAdd2, hx, hy, bindRead, hz0, hz1, pure, Except.pure]

theorem fma2E_reads {va vb vc : Value} {x0 x1 y0 y1 z0 z1 w0 w1 : EReal}
    (hx : pairRead va = some (.ok (x0, x1))) (hy : pairRead vb = some (.ok (y0, y1)))
    (hz : pairRead vc = some (.ok (z0, z1)))
    (hw0 : (mulEReal x0 y0).bind (addEReal · z0) = some w0)
    (hw1 : (mulEReal x1 y1).bind (addEReal · z1) = some w1) :
    fma2E va vb vc = .ok (.pair (erealValue .f32 w0) (erealValue .f32 w1)) := by
  simp only [fma2E, idealFma2, hx, hy, hz, bindRead, hw0, hw1, pure, Except.pure]

theorem ex2E_real {fz : Bool} {v : Value} {r : ℝ}
    (h : readEReal .f32 v = some (.ok (r : EReal))) :
    ex2E fz v = .ok (.float .f32 (Real.rpow 2 r)) := by
  simp only [ex2E, ex2Val, finiteVal, h, bindRead, EReal.coe_ne_top, EReal.coe_ne_bot, or_self,
    ↓reduceIte, EReal.toReal_coe, pure, Except.pure]

theorem ex2E_negInf (fz : Bool) : ex2E fz negInf32 = .ok (.float .f32 0) := by
  have h : ex2Val negInf32 = none := by
    simp [ex2Val, finiteVal, readEReal_negInf, bindRead]
  have hc : coreFloat (ex2I fz) [negInf32] = .ok (FVal.toValue .f32 (.zero false)) := by
    cases fz <;> rfl
  unfold ex2E
  rw [h]
  exact hc

/-- A pair of two clean values splits back into them. -/
theorem split_join_clean {a b : Value} (ha : Clean a) (hb : Clean b) :
    splitValue 64 (joinValue a b) = (a, b) := by
  obtain ⟨ha4, has, hab⟩ := ha
  obtain ⟨hb4, hbs, hbb⟩ := hb
  cases a with
  | slice w o n => exact absurd rfl (has w o n)
  | bits w x =>
    cases b with
    | bits w' y =>
      simp only [Value.bytes] at ha4 hb4
      have hx := hab w x rfl
      have hy := hbb w' y rfl
      unfold joinValue
      by_cases hw : w = w' ∧ 2 * w ≤ 64
      · obtain ⟨rfl, hw2⟩ := hw
        have h32 : w = 32 := by omega
        subst h32
        simp only [and_self, Nat.reduceMul, Nat.reduceLeDiff, ↓reduceIte, splitValue,
          Nat.reduceDiv, Prod.mk.injEq, Value.bits.injEq, true_and]
        constructor
        · apply BitVec.eq_of_toNat_eq
          rw [truncBits32_toNat, toNat_or_shl32_lo, Nat.mod_eq_of_lt hx]
        · apply BitVec.eq_of_toNat_eq
          rw [truncBits32_toNat, BitVec.toNat_ofNat,
            Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64), toNat_or_shl32_hi hx,
            Nat.mod_eq_of_lt hy]
      · simp only [hw, ↓reduceIte, splitValue]
    | _ => rfl
  | _ =>
    cases b with
    | slice w o n =>
      simp only [joinValue]
      all_goals rfl
    | _ => rfl

theorem join_has {ka kb : SK} {a b : Value} (ha : ka.Has a) (hb : kb.Has b) :
    (Kd.pr (SK.max ka kb)).Has (joinValue a b) := by
  have ca := SK.clean ha
  have cb := SK.clean hb
  have hs := split_join_clean ca cb
  refine ⟨unpackOk_join ca.1 cb.1 ca.2.1, ?_, ?_⟩
  · rw [hs]
    unfold SK.max
    split
    · exact SK.mono (by assumption) ha
    · exact SK.mono (by cases ka <;> cases kb <;> simp_all [SK.le, SK.rank]) ha
  · rw [hs]
    unfold SK.max
    split
    · exact hb
    · exact SK.mono (by cases ka <;> cases kb <;> simp_all [SK.le, SK.rank]) hb

theorem pair_has {k : SK} {a b : Value} (ha : k.Has a) (hb : k.Has b) :
    (Kd.pr k).Has (.pair a b) := by
  have ca := SK.clean ha
  have cb := SK.clean hb
  exact ⟨⟨by simp [Value.bytes, ca.1, cb.1], ca.1, cb.1⟩, ha, hb⟩

/-! ### The checker -/

/-- What the role's reading of a widening (`cvt.f32.bf16`) gives on a `bf16` half. -/
def WidenSpec (f : List Value → Exec Value) : Prop :=
  ∀ h, Kd.h16.Has h → ∃ v, f [h] = .ok v ∧ SK.ni.Has v

/-- What the role's reading of a pack (`cvt.rn.bf16x2.f32`) gives on two reals. -/
def PackSpec (f : List Value → Exec Value) : Prop :=
  ∀ a b, SK.fl.Has a → SK.fl.Has b → ∃ v, f [a, b] = .ok v ∧ SK.w4.Has v

/-- What a reading of `max.f32` (two or three sources) gives on values of one kind `fl` or `ni`:
a value of that kind. -/
def MaxSpec (f : List Value → Exec Value) : Prop :=
  ∀ k : SK, (k = .fl ∨ k = .ni) → ∀ vs : List Value, (vs.length = 2 ∨ vs.length = 3) →
    (∀ v ∈ vs, k.Has v) → ∃ r, f vs = .ok r ∧ k.Has r

/-- The kind of a maximum: `fl` when every source is at most `fl`, `ni` when every source is at
most `ni`. -/
def SK.maxK (ks : List SK) : Option SK :=
  if ks.all (·.le .fl) then some .fl else if ks.all (·.le .ni) then some .ni else none

theorem SK.of_maxK {ks : List SK} {z : SK} (h : SK.maxK ks = some z) :
    (z = .fl ∨ z = .ni) ∧ ∀ k ∈ ks, k.le z = true := by
  unfold SK.maxK at h
  split_ifs at h with h1 h2 <;> simp only [Option.some.injEq] at h <;> subst h
  · exact ⟨.inl rfl, fun k hk => List.all_eq_true.mp h1 k hk⟩
  · exact ⟨.inr rfl, fun k hk => List.all_eq_true.mp h2 k hk⟩

theorem SK.lane_max {k : SK} (hk : k = .fl ∨ k = .ni) {x y : EReal} (hx : k.Lane x)
    (hy : k.Lane y) : k.Lane (Max.max x y) := by
  rcases hk with rfl | rfl
  · obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨Max.max r s, coe_max⟩
  · rcases hx with ⟨r, rfl⟩ | rfl
    · rcases hy with ⟨s, rfl⟩ | rfl
      · exact .inl ⟨Max.max r s, coe_max⟩
      · exact .inl ⟨r, max_eq_left bot_le⟩
    · rw [max_eq_right bot_le]; exact hy

/-- The ideal outcome of `max.f32` meets the specification. -/
theorem maxE_maxSpec : MaxSpec maxE := by
  intro k hk vs hl hv
  have hni : k.le .ni = true := by rcases hk with rfl | rfl <;> rfl
  rcases hl with hl | hl
  · match vs, hl with
    | [a, b], _ =>
      obtain ⟨x, hxa, lx⟩ := SK.lane_of hni (hv a (by simp))
      obtain ⟨y, hyb, ly⟩ := SK.lane_of hni (hv b (by simp))
      refine ⟨erealValue .f32 (max x y), ?_, SK.has_erealValue (SK.lane_max hk lx ly)⟩
      unfold maxE
      simp only [idealMax, hxa, hyb, bindRead, pure, Except.pure]
  · match vs, hl with
    | [a, b, c], _ =>
      obtain ⟨x, hxa, lx⟩ := SK.lane_of hni (hv a (by simp))
      obtain ⟨y, hyb, ly⟩ := SK.lane_of hni (hv b (by simp))
      obtain ⟨z, hzc, lz⟩ := SK.lane_of hni (hv c (by simp))
      refine ⟨erealValue .f32 (max (max x y) z), ?_,
        SK.has_erealValue (SK.lane_max hk (SK.lane_max hk lx ly) lz)⟩
      unfold maxE
      simp only [idealMax, hxa, hyb, hzc, bindRead, pure, Except.pure]

/-- The specification a role reading must meet, by its number of sources. -/
def XItem.FnOk : XItem → Prop
  | .base _ => True
  | .fn _ _ [_] f => WidenSpec f
  | .fn (.float _) _ [_, _] f => MaxSpec f
  | .fn (.float _) _ [_, _, _] f => MaxSpec f
  | .fn _ _ [_, _] f => PackSpec f
  | .fn .. => True

/-- The role readings of a run meet their specifications. -/
def kFns : List XItem → Prop
  | [] => True
  | it :: its => it.FnOk ∧ kFns its

/-- The kinds after an item, or `none` when the item is not accepted on its sources' kinds. -/
def kItem (K : Nat → Kd) : XItem → Option (Nat → Kd)
  | .base (.mul _ d a b) => match K a, K b with
    | .s x, .s y => (SK.mulK x y).map fun z => Function.update K d (.s z)
    | _, _ => none
  | .base (.add _ d a b) => match K a, K b with
    | .s x, .s y => (SK.addK x y).map fun z => Function.update K d (.s z)
    | _, _ => none
  | .base (.sub _ d a b) => match K a, K b with
    | .s x, .s y => (SK.subK x y).map fun z => Function.update K d (.s z)
    | _, _ => none
  | .base (.fma2 d a b c) => match K a, K b, K c with
    | .pr x, .pr y, .pr z => (SK.fmaK x y z).map fun w => Function.update K d (.pr w)
    | _, _, _ => none
  | .base (.add2 d a b) => match K a, K b with
    | .pr x, .pr y => (SK.addK x y).map fun z => Function.update K d (.pr z)
    | _, _ => none
  | .base (.ex2 _ d a) => match K a with
    | .s x => (SK.ex2K x).map fun z => Function.update K d (.s z)
    | _ => none
  | .base (.pack d a b) => match K a, K b with
    | .s x, .s y => some (Function.update K d (.pr (SK.max x y)))
    | _, _ => none
  | .base (.unpack lo hi a) => match K a with
    | .pr x => some (Function.update (Function.update K lo (.s x)) hi (.s x))
    | _ => none
  | .base (.mov d a) => match K a with
    | .s x => some (Function.update K d (.s x))
    | _ => none
  | .fn _ d [a] _ => match K a with
    | .h16 => some (Function.update K d (.s .ni))
    | _ => none
  | .fn (.float _) d [a, b] _ => match K a, K b with
    | .s x, .s y => (SK.maxK [x, y]).map fun z => Function.update K d (.s z)
    | _, _ => none
  | .fn (.float _) d [a, b, c] _ => match K a, K b, K c with
    | .s x, .s y, .s z => (SK.maxK [x, y, z]).map fun w => Function.update K d (.s w)
    | _, _, _ => none
  | .fn _ d [a, b] _ => match K a, K b with
    | .s x, .s y => if x.le .fl && y.le .fl then some (Function.update K d (.s .w4)) else none
    | _, _ => none
  | _ => none

/-- The kinds after a run, or `none` when an item is not accepted. -/
def kRun (K : Nat → Kd) : List XItem → Option (Nat → Kd)
  | [] => some K
  | it :: its => (kItem K it).bind fun K' => kRun K' its

/-- The run is accepted on the kinds `K`. -/
def kOk (K : Nat → Kd) (items : List XItem) : Bool := (kRun K items).isSome

/-- The kinds after a run (the start kinds if it is not accepted). -/
def kOut (K : Nat → Kd) (items : List XItem) : Nat → Kd := (kRun K items).getD K

/-- The kinds of a literal list, `no` elsewhere. -/
def kOf (l : List (Nat × Kd)) : Nat → Kd := fun r => (l.lookup r).getD .no

/-- The kinds `K` on the registers `keys`, `no` elsewhere. -/
def kOn (keys : List Nat) (K : Nat → Kd) : Nat → Kd := fun r => if keys.contains r then K r else .no

theorem has_update {K : Nat → Kd} {V : Nat → Value} (hV : ∀ r, (K r).Has (V r)) {d : Nat}
    {k : Kd} {v : Value} (h : k.Has v) :
    ∀ r, ((Function.update K d k) r).Has ((Function.update V d v) r) := by
  intro r
  by_cases e : r = d
  · subst e; simp only [Function.update_self]; exact h
  · simp only [Function.update_of_ne e]; exact hV r

theorem upd_one (V : Nat → Value) (it : XItem) {d : Nat} {v : Value} (h : it.vals V = [(d, v)]) :
    it.upd V = Function.update V d v := by
  simp only [XItem.upd, h, List.foldl_cons, List.foldl_nil]

theorem okVal_ok {dflt v : Value} {E : Exec Value} (h : E = .ok v) : okVal dflt E = v := by
  rw [h]; rfl

/-- **One item**: accepted on the kinds of its sources, its condition holds and its destinations
get their kinds. -/
theorem kItem_sound {K K' : Nat → Kd} {V : Nat → Value} {it : XItem} (h : kItem K it = some K')
    (hV : ∀ r, (K r).Has (V r)) (hf : it.FnOk) :
    it.cond V ∧ ∀ r, (K' r).Has (it.upd V r) := by
  cases it with
  | base it =>
    cases it with
    | mul fz d a b =>
      simp only [kItem] at h
      have ha := hV a; have hb := hV b
      revert h ha hb
      cases K a <;> cases K b <;> intro h ha hb <;> simp only [reduceCtorEq] at h
      rename_i x y
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hxn, hyn⟩ := SK.ni_of_some_mul hz
      obtain ⟨xa, hxa, lx⟩ := SK.lane_of hxn ha
      obtain ⟨xb, hxb, ly⟩ := SK.lane_of hyn hb
      obtain ⟨w, hw, lw⟩ := SK.lane_mul hz lx ly
      have he := mulE_reads (fz := fz) hxa hxb hw
      refine ⟨⟨_, he⟩, ?_⟩
      rw [upd_one V _ rfl]
      exact has_update hV (by rw [okVal_ok he]; exact SK.has_erealValue lw)
    | add fz d a b =>
      simp only [kItem] at h
      have ha := hV a; have hb := hV b
      revert h ha hb
      cases K a <;> cases K b <;> intro h ha hb <;> simp only [reduceCtorEq] at h
      rename_i x y
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hxn, hyn⟩ := SK.args_of_addK hz
      obtain ⟨xa, hxa, lx⟩ := SK.lane_of hxn ha
      obtain ⟨xb, hxb, ly⟩ := SK.lane_of hyn hb
      obtain ⟨w, hw, lw⟩ := SK.lane_add hz lx ly
      have he := addE_reads (fz := fz) hxa hxb hw
      refine ⟨⟨_, he⟩, ?_⟩
      rw [upd_one V _ rfl]
      exact has_update hV (by rw [okVal_ok he]; exact SK.has_erealValue lw)
    | sub fz d a b =>
      simp only [kItem] at h
      have ha := hV a; have hb := hV b
      revert h ha hb
      cases K a <;> cases K b <;> intro h ha hb <;> simp only [reduceCtorEq] at h
      rename_i x y
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hxn, hyn⟩ := SK.args_of_subK hz
      obtain ⟨xa, hxa, lx⟩ := SK.lane_of hxn ha
      obtain ⟨xb, hxb, ly⟩ := SK.lane_of hyn hb
      obtain ⟨w, hw, lw⟩ := SK.lane_sub hz lx ly
      have he := subE_reads (fz := fz) hxa hxb hw
      refine ⟨⟨_, he⟩, ?_⟩
      rw [upd_one V _ rfl]
      exact has_update hV (by rw [okVal_ok he]; exact SK.has_erealValue lw)
    | fma2 d a b c =>
      simp only [kItem] at h
      have ha := hV a; have hb := hV b; have hc := hV c
      revert h ha hb hc
      cases K a <;> cases K b <;> cases K c <;> intro h ha hb hc <;>
        simp only [reduceCtorEq] at h
      rename_i x y z
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hxn, hyn, hzn⟩ := SK.args_of_fmaK hw
      obtain ⟨x0, hx0, lx0⟩ := SK.lane_of hxn ha.2.1
      obtain ⟨x1, hx1, lx1⟩ := SK.lane_of hxn ha.2.2
      obtain ⟨y0, hy0, ly0⟩ := SK.lane_of hyn hb.2.1
      obtain ⟨y1, hy1, ly1⟩ := SK.lane_of hyn hb.2.2
      obtain ⟨z0, hz0, lz0⟩ := SK.lane_of hzn hc.2.1
      obtain ⟨z1, hz1, lz1⟩ := SK.lane_of hzn hc.2.2
      obtain ⟨w0, hw0, lw0⟩ := SK.lane_fma hw lx0 ly0 lz0
      obtain ⟨w1, hw1, lw1⟩ := SK.lane_fma hw lx1 ly1 lz1
      have he := fma2E_reads (pairRead_of_reads hx0 hx1) (pairRead_of_reads hy0 hy1)
        (pairRead_of_reads hz0 hz1) hw0 hw1
      refine ⟨⟨_, he⟩, ?_⟩
      rw [upd_one V _ rfl]
      exact has_update hV (by
        rw [okVal_ok he]; exact pair_has (SK.has_erealValue lw0) (SK.has_erealValue lw1))
    | add2 d a b =>
      simp only [kItem] at h
      have ha := hV a; have hb := hV b
      revert h ha hb
      cases K a <;> cases K b <;> intro h ha hb <;> simp only [reduceCtorEq] at h
      rename_i x y
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hxn, hyn⟩ := SK.args_of_addK hw
      obtain ⟨x0, hx0, lx0⟩ := SK.lane_of hxn ha.2.1
      obtain ⟨x1, hx1, lx1⟩ := SK.lane_of hxn ha.2.2
      obtain ⟨y0, hy0, ly0⟩ := SK.lane_of hyn hb.2.1
      obtain ⟨y1, hy1, ly1⟩ := SK.lane_of hyn hb.2.2
      obtain ⟨w0, hw0, lw0⟩ := SK.lane_add hw lx0 ly0
      obtain ⟨w1, hw1, lw1⟩ := SK.lane_add hw lx1 ly1
      have he := add2E_reads (pairRead_of_reads hx0 hx1) (pairRead_of_reads hy0 hy1) hw0 hw1
      refine ⟨⟨_, he⟩, ?_⟩
      rw [upd_one V _ rfl]
      exact has_update hV (by
        rw [okVal_ok he]; exact pair_has (SK.has_erealValue lw0) (SK.has_erealValue lw1))
    | ex2 fz d a =>
      simp only [kItem] at h
      have ha := hV a
      revert h ha
      cases K a <;> intro h ha <;> simp only [reduceCtorEq] at h
      rename_i x
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      have hx : x.le .ni = true := by unfold SK.ex2K at hz; split at hz <;> simp_all
      have hz' : z = .nn := by unfold SK.ex2K at hz; split at hz <;> simp_all
      subst hz'
      have key : ∃ v, ex2E fz (V a) = .ok v ∧ SK.nn.Has v := by
        have hni : SK.ni.Has (V a) := SK.mono hx ha
        rcases hni with ⟨-, r, hr⟩ | e
        · exact ⟨_, ex2E_real hr, has_float_nn (Real.rpow_nonneg (by norm_num) r)⟩
        · rw [e]; exact ⟨_, ex2E_negInf fz, has_float_nn le_rfl⟩
      obtain ⟨v, he, hv⟩ := key
      refine ⟨⟨_, he⟩, ?_⟩
      rw [upd_one V _ rfl]
      exact has_update hV (by rw [okVal_ok he]; exact hv)
    | pack d a b =>
      simp only [kItem] at h
      have ha := hV a; have hb := hV b
      revert h ha hb
      cases K a <;> cases K b <;> intro h ha hb <;> simp only [reduceCtorEq] at h
      rename_i x y
      obtain rfl := Option.some.inj h.symm
      have ca := SK.clean ha
      have cb := SK.clean hb
      refine ⟨⟨ca.1, cb.1⟩, ?_⟩
      rw [upd_one V _ rfl]
      exact has_update hV (join_has ha hb)
    | unpack lo hi a =>
      simp only [kItem] at h
      have ha := hV a
      revert h ha
      cases K a <;> intro h ha <;> simp only [reduceCtorEq] at h
      rename_i x
      obtain rfl := Option.some.inj h.symm
      refine ⟨ha.1, ?_⟩
      simp only [XItem.upd, XItem.vals, OItem.vals, List.foldl_cons, List.foldl_nil]
      exact has_update (has_update hV (k := .s x) ha.2.1) (k := .s x) ha.2.2
    | mov d a =>
      simp only [kItem] at h
      have ha := hV a
      revert h ha
      cases K a <;> intro h ha <;> simp only [reduceCtorEq] at h
      rename_i x
      obtain rfl := Option.some.inj h.symm
      refine ⟨(SK.clean ha).1, ?_⟩
      rw [upd_one V _ rfl]
      exact has_update hV ha
    | _ => simp [kItem] at h
  | fn op d srcs f =>
    cases op
    case float i =>
      match srcs, hf, h with
      | [a], hf, h =>
        simp only [kItem] at h
        have ha := hV a
        revert h ha
        cases K a <;> intro h ha <;> simp only [reduceCtorEq] at h
        obtain rfl := Option.some.inj h.symm
        obtain ⟨v, he, hv⟩ := hf (V a) ha
        refine ⟨⟨v, he⟩, ?_⟩
        rw [upd_one V _ rfl]
        exact has_update hV (by show SK.ni.Has (okVal _ (f [V a])); rw [okVal_ok he]; exact hv)
      | [a, b], hf, h =>
        simp only [kItem] at h
        have ha := hV a; have hb := hV b
        revert h ha hb
        cases K a <;> cases K b <;> intro h ha hb <;> simp only [reduceCtorEq] at h
        rename_i x y
        obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hk, hle⟩ := SK.of_maxK hz
        obtain ⟨v, he, hv⟩ := hf z hk [V a, V b] (.inl rfl) (by
          intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact SK.mono (hle x (by simp)) ha
          · exact SK.mono (hle y (by simp)) hb)
        refine ⟨⟨v, he⟩, ?_⟩
        rw [upd_one V _ rfl]
        exact has_update hV (by show z.Has (okVal _ (f [V a, V b])); rw [okVal_ok he]; exact hv)
      | [a, b, c], hf, h =>
        simp only [kItem] at h
        have ha := hV a; have hb := hV b; have hc := hV c
        revert h ha hb hc
        cases K a <;> cases K b <;> cases K c <;> intro h ha hb hc <;>
          simp only [reduceCtorEq] at h
        rename_i x y z
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hk, hle⟩ := SK.of_maxK hw
        obtain ⟨v, he, hv⟩ := hf w hk [V a, V b, V c] (.inr rfl) (by
          intro u hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl
          · exact SK.mono (hle x (by simp)) ha
          · exact SK.mono (hle y (by simp)) hb
          · exact SK.mono (hle z (by simp)) hc)
        refine ⟨⟨v, he⟩, ?_⟩
        rw [upd_one V _ rfl]
        exact has_update hV (by
          show w.Has (okVal _ (f [V a, V b, V c])); rw [okVal_ok he]; exact hv)
      | [], _, h => simp [kItem] at h
      | _ :: _ :: _ :: _ :: _, _, h => simp [kItem] at h
    all_goals
      match srcs, hf, h with
      | [a], hf, h =>
        simp only [kItem] at h
        have ha := hV a
        revert h ha
        cases K a <;> intro h ha <;> simp only [reduceCtorEq] at h
        obtain rfl := Option.some.inj h.symm
        obtain ⟨v, he, hv⟩ := hf (V a) ha
        refine ⟨⟨v, he⟩, ?_⟩
        rw [upd_one V _ rfl]
        exact has_update hV (by show SK.ni.Has (okVal _ (f [V a])); rw [okVal_ok he]; exact hv)
      | [a, b], hf, h =>
        simp only [kItem] at h
        have ha := hV a; have hb := hV b
        revert h ha hb
        cases K a <;> cases K b <;> intro h ha hb <;> simp only [reduceCtorEq] at h
        rename_i x y
        by_cases hc : (x.le .fl && y.le .fl) = true
        · rw [SK.iteT hc] at h
          obtain rfl := Option.some.inj h.symm
          simp only [Bool.and_eq_true] at hc
          obtain ⟨v, he, hv⟩ := hf (V a) (V b) (SK.mono hc.1 ha) (SK.mono hc.2 hb)
          refine ⟨⟨v, he⟩, ?_⟩
          rw [upd_one V _ rfl]
          exact has_update hV (by
            show SK.w4.Has (okVal _ (f [V a, V b])); rw [okVal_ok he]; exact hv)
        · rw [SK.iteF hc] at h; cases h
      | [], _, h => simp [kItem] at h
      | _ :: _ :: _ :: _, _, h => simp [kItem] at h

/-- **A run**: accepted on the kinds of the start values, every item's condition holds and every
register after the run has its kind. -/
theorem kRun_sound : ∀ {K K' : Nat → Kd} {V : Nat → Value} {items : List XItem},
    kRun K items = some K' → (∀ r, (K r).Has (V r)) → kFns items →
    xCond V items ∧ ∀ r, (K' r).Has (xFinal V items r)
  | K, K', V, [], h, hV, _ => by
    simp only [kRun, Option.some.injEq] at h
    subst h
    exact ⟨trivial, hV⟩
  | K, K', V, it :: its, h, hV, hf => by
    simp only [kRun] at h
    obtain ⟨K1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c1, k1⟩ := kItem_sound h1 hV hf.1
    obtain ⟨c2, k2⟩ := kRun_sound h2 k1 hf.2
    exact ⟨⟨c1, c2⟩, k2⟩

theorem lookupD_factsFrom {live : List Nat} {V : Nat → Value} {r : Nat} (h : r ∈ live) :
    lookupD (factsFrom live V) r = V r := by
  induction live with
  | nil => cases h
  | cons q live ih =>
    by_cases e : r = q
    · subst e; simp [lookupD, factsFrom]
    · have hm : r ∈ live := (List.mem_cons.mp h).resolve_left e
      have hb : (r == q) = false := by simpa using e
      have := ih hm
      simp only [lookupD, factsFrom, List.map_cons, List.lookup, hb] at this ⊢
      exact this

/-- **A piece of a generated run**: accepted on the kinds `K` of its start facts' values, its
condition holds, and the values of its end facts `G` have the kinds after the run (`kOn` the
registers of `G`), when `G` states the values after the run (`hG`, the piece's own check). -/
theorem kpiece {F G : List (Nat × Value)} {items : List XItem} {K : Nat → Kd}
    (hG : factsFrom (G.map Prod.fst) (xFinal (lookupD F) items) = G)
    (hk : kOk K items = true) (hV : ∀ r, (K r).Has (lookupD F r)) (hf : kFns items) :
    xCond (lookupD F) items ∧ ∀ r, (kOn (G.map Prod.fst) (kOut K items) r).Has (lookupD G r) := by
  obtain ⟨K', hK'⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨hc, hk'⟩ := kRun_sound hK' hV hf
  refine ⟨hc, fun r => ?_⟩
  unfold kOn kOut
  rw [hK']
  by_cases hm : (G.map Prod.fst).contains r = true
  · rw [SK.iteT hm, Option.getD_some, ← hG,
      lookupD_factsFrom (by simpa using hm)]
    exact hk' r
  · rw [SK.iteF hm]; trivial

theorem mem_of_lookupK {α : Type} : ∀ {ys : List (Nat × α)} {r : Nat} {v : α},
    ys.lookup r = some v → (r, v) ∈ ys
  | [], _, _, h => by cases h
  | (q, w) :: ys, r, v, h => by
    by_cases e : r = q
    · subst e
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h; simp
    · have hb : (r == q) = false := by simpa using e
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (mem_of_lookupK h)

/-- The start of a run: the kinds of a literal list, given the kinds of the listed registers'
values, for facts of a value function on registers including the listed ones. -/
theorem kstart {l : List (Nat × Kd)} {live : List Nat} {V : Nat → Value}
    (hl : (l.map Prod.fst).all (live.contains ·) = true)
    (hV : ∀ p ∈ l, p.2.Has (V p.1)) : ∀ r, (kOf l r).Has (lookupD (factsFrom live V) r) := by
  intro r
  unfold kOf
  cases hr : l.lookup r with
  | none => trivial
  | some k =>
    have hm := mem_of_lookupK hr
    have hin : r ∈ live := by
      have := List.all_eq_true.mp hl r (List.mem_map_of_mem (f := Prod.fst) hm)
      simpa using this
    rw [Option.getD_some, lookupD_factsFrom hin]
    exact hV (r, k) hm

/-- The kinds `K` of the registers `keys` as a literal list (registers of kind `no` left out). -/
def kList (keys : List Nat) (K : Nat → Kd) : List (Nat × Kd) :=
  keys.filterMap fun r => if K r = .no then none else some (r, K r)

theorem kOf_kList {keys : List Nat} {K : Nat → Kd} {V : Nat → Value}
    (h : ∀ r, (kOn keys K r).Has (V r)) : ∀ r, (kOf (kList keys K) r).Has (V r) := by
  intro r
  unfold kOf
  cases hr : (kList keys K).lookup r with
  | none => trivial
  | some k =>
    have hm := mem_of_lookupK hr
    simp only [kList, List.mem_filterMap] at hm
    obtain ⟨r', hr', he⟩ := hm
    split at he
    · cases he
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := h r'
      simp only [kOn, List.contains_iff_mem.mpr hr', ↓reduceIte] at this
      exact this

/-- **A piece of a generated run with literal kinds**: `kpiece`, the kinds after the piece given
as the literal list `kList`, so that the next piece's check evaluates a literal. -/
theorem kpiece_list {F G : List (Nat × Value)} {items : List XItem} {K : Nat → Kd}
    (hG : factsFrom (G.map Prod.fst) (xFinal (lookupD F) items) = G)
    (hk : kOk K items = true) (hV : ∀ r, (K r).Has (lookupD F r)) (hf : kFns items) :
    xCond (lookupD F) items ∧
      ∀ r, (kOf (kList (G.map Prod.fst) (kOut K items)) r).Has (lookupD G r) :=
  let h := kpiece hG hk hV hf
  ⟨h.1, kOf_kList h.2⟩

/-- The literal kinds `L'` after a piece are those the checker gives on the end facts' registers. -/
def kNext (L : List (Nat × Kd)) (items : List XItem) (keys : List Nat) (L' : List (Nat × Kd)) :
    Bool :=
  L'.all fun q => keys.contains q.1 && decide (kOut (kOf L) items q.1 = q.2)

/-- **A piece of a generated run with literal kinds before and after** (`kpiece`): the literal
kinds `L'` after the piece are checked against the checker's (`kNext`), so that no kinds function
is unfolded outside the checks. -/
theorem kpiece_lit {F G : List (Nat × Value)} {items : List XItem} {L L' : List (Nat × Kd)}
    (hG : factsFrom (G.map Prod.fst) (xFinal (lookupD F) items) = G)
    (hk : kOk (kOf L) items = true) (hV : ∀ r, (kOf L r).Has (lookupD F r)) (hf : kFns items)
    (hL' : kNext L items (G.map Prod.fst) L' = true) :
    xCond (lookupD F) items ∧ ∀ r, (kOf L' r).Has (lookupD G r) := by
  obtain ⟨hc, hk'⟩ := kpiece hG hk hV hf
  refine ⟨hc, fun r => ?_⟩
  unfold kOf
  cases hr : L'.lookup r with
  | none => trivial
  | some k =>
    have hm := mem_of_lookupK hr
    have := List.all_eq_true.mp hL' (r, k) hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have h := hk' r
    simp only [kOn, this.1, ↓reduceIte, this.2] at h
    exact h

/-- The checks of the pieces of a run in order, each from the literal kinds after the pieces
before it (one evaluation for the whole run). -/
def kChain (K : Nat → Kd) : List (List XItem × List Nat) → Bool
  | [] => true
  | (items, keys) :: rest => kOk K items && kChain (kOf (kList keys (kOut K items))) rest

end
end PTX.Flow
