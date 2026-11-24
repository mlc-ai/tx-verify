-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run
public import Lemmas.Assumption.Facts

@[expose] public section

/-! # Register facts

A proof tool. Register facts (`Holds`) and value shorthands (`b32`, `b64`, `gl`, `fl`, `h16`).
`At t pc F` is a thread state at the start of instruction `pc` whose registers satisfy `F`. It
holds after one instruction that writes no register (`At.next`) or one register (`At.set`) and
after a branch on a predicate fact (`run_bra`); facts are dropped by `At.mono`, with
`at_select` closing the kept facts by lookup. `holds_facts` splits a `Holds` goal into one
equation per fact. -/

namespace PTX.Proof
open PTX

/-- Every listed register holds the listed value. -/
def Holds (regs : Nat → Option Value) : List (Nat × Value) → Prop
  | [] => True
  | (r, v) :: rest => regs r = some v ∧ Holds regs rest

@[simp] theorem holds_nil (regs : Nat → Option Value) : Holds regs [] := trivial
@[simp] theorem holds_cons (regs : Nat → Option Value) (r : Nat) (v : Value) (l) :
    Holds regs ((r, v) :: l) ↔ regs r = some v ∧ Holds regs l := Iff.rfl
@[simp] theorem holds_append (regs : Nat → Option Value) (l l' : List (Nat × Value)) :
    Holds regs (l ++ l') ↔ Holds regs l ∧ Holds regs l' := by
  induction l with
  | nil => simp
  | cons p l ih => obtain ⟨r, v⟩ := p; simp [ih, and_assoc]

/-- Registers listed in `F`, then `R`. Lets a segment be evaluated by `rfl`: lookups of
listed registers reduce, and `override_eq` removes it again. -/
def override (F : List (Nat × Value)) (R : Nat → Option Value) :
    Nat → Option Value := fun r =>
  match F.lookup r with
  | some v => some v
  | none => R r

theorem override_eq {F : List (Nat × Value)} {R : Nat → Option Value}
    (h : Holds R F) : override F R = R := by
  funext r
  induction F with
  | nil => rfl
  | cons p F ih =>
    obtain ⟨r', v⟩ := p
    obtain ⟨h1, h2⟩ := h
    unfold override at ih ⊢
    by_cases e : r = r'
    · subst e; simp [List.lookup, h1]
    · simp only [List.lookup, show (r == r') = false from by simpa using e]
      exact ih h2

def gl (a : Nat) : Loc := ⟨.global, 0, a⟩
def b32 (n : Nat) : Value := .bits 32 (BitVec.ofNat 64 n)
def b64 (n : Nat) : Value := .bits 64 (BitVec.ofNat 64 n)
def fl (v : ℝ) : Value := .float .f32 v
def h16 (v : ℝ) : Value := .float .f16 v

theorem truncBits_ofNat {w n : Nat} (h : n < 2 ^ w) (hw : w ≤ 64) :
    truncBits w (BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  have : n < 2 ^ 64 := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hw)
  rw [truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The finite number of a datum is the number it holds. -/
theorem FVal.finite_of_num {x : FVal} {q : ℚ} (h : x.num = some q) :
    x.finite = .ok (q : ℝ) := by
  cases x <;> simp [FVal.num, FVal.finite, pure, Except.pure] at h ⊢
  · rw [← h]; simp
  · rw [h]

/-- A 32-bit pattern read as `f32` is the number it encodes. -/
theorem valFloat_b32 {b : Nat} {q : ℚ} (hb : b < 2 ^ 64) (h : f32Value b = some q) :
    valFloat .f32 (b32 b) = .ok (q : ℝ) := by
  rw [f32Value, FloatFmt.decode, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, hn⟩ := h
  have hc : classify .f32 (b32 b) = .ok x := by
    simpa [b32, FloatFmt.bytes] using classify_bits (fmt := .f32) hb hx
  rw [valFloat_of_classify (fmt := .f32) (v := b32 b) (x := x) (by intro f y hh; cases hh) hc,
    FVal.finite_of_num hn]

theorem holds_mem {R : Nat → Option Value} {l : List (Nat × Value)} (h : Holds R l)
    {r : Nat} {v : Value} (hm : (r, v) ∈ l) : R r = some v := by
  induction l with
  | nil => simp at hm
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hm with e | e
    · rw [← e] at h1; exact h1
    · exact ih h2 e

/-- A register fact by lookup: `l.lookup r = some v` is closed by `rfl` (it compares keys
only), so a proof never unfolds the fact table with `simp`. -/
theorem holds_lookup {R : Nat → Option Value} {l : List (Nat × Value)} (h : Holds R l)
    {r : Nat} {v : Value} (hl : l.lookup r = some v) : R r = some v := by
  induction l with
  | nil => simp at hl
  | cons p l ih =>
    obtain ⟨r', v'⟩ := p
    obtain ⟨h1, h2⟩ := h
    by_cases e : r = r'
    · subst e; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl; rw [← hl];
      exact h1
    · simp only [List.lookup, show (r == r') = false from by simpa using e] at hl
      exact ih h2 hl


/-- Kernel parameters with the listed ones made explicit, so that evaluation can read them. -/
def withParams (ps : List (String × Nat)) (f : String → Option (BitVec 64)) :
    String → Option (BitVec 64) := fun p =>
  match ps.lookup p with
  | some v => some (BitVec.ofNat 64 v)
  | none => f p

theorem withParams_eq {ps : List (String × Nat)} {f : String → Option (BitVec 64)}
    (h : ∀ p v, (p, v) ∈ ps → f p = some (BitVec.ofNat 64 v)) : withParams ps f = f := by
  funext p
  unfold withParams
  induction ps with
  | nil => rfl
  | cons q ps ih =>
    obtain ⟨q, v⟩ := q
    by_cases e : p = q
    · subst e
      simp only [List.lookup, beq_self_eq_true]
      exact (h p v (by simp)).symm
    · simp only [List.lookup, show (p == q) = false from by simpa using e]
      exact ih (fun p' v' hm => h p' v' (List.mem_cons_of_mem _ hm))

/-- A launch whose listed parameters are explicit. -/
def explicitParams (L : Launch) (ps : List (String × Nat)) : Launch :=
  { L with params := withParams ps L.params }

theorem explicitParams_eq {L : Launch} {ps : List (String × Nat)}
    (h : ∀ p v, (p, v) ∈ ps → L.params p = some (BitVec.ofNat 64 v)) : explicitParams L ps = L := by
  unfold explicitParams; rw [withParams_eq h]

theorem trunc_mad (a b c : Nat) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) * truncBits 32 (BitVec.ofNat 64 b) +
      truncBits 32 (BitVec.ofNat 64 c)) = BitVec.ofNat 64 ((a * b + c) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul]
  have h : (2:Nat) ^ 32 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by decide)
  have h2 : (2:Nat) ^ 32 < 2 ^ 64 := by decide
  simp only [Nat.mod_mod_of_dvd _ h,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) h2.le)]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ h, ← Nat.add_mod, Nat.add_mod (a * b), Nat.mul_mod a b,
    ← Nat.add_mod]
  rw [Nat.add_mod _ c, Nat.add_mod _ (c % 2 ^ 32), Nat.mod_mod]

theorem holds_update {R : Nat → Option Value} {F : List (Nat × Value)} {r : Nat}
    {x : Option Value} (h : Holds R F) (hr : ∀ p ∈ F, p.1 ≠ r) : Holds (Function.update R r x) F :=
      by
  induction F with
  | nil => trivial
  | cons p F ih =>
    obtain ⟨r', v⟩ := p
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ih h2 (fun q hq => hr q (List.mem_cons_of_mem _ hq))⟩
    rw [Function.update_of_ne (hr (r', v) (by simp))]; exact h1

/-- Thread state at the start of an instruction, with register facts `F`. -/
def At (t : TState) (pc : Nat) (F : List (Nat × Value)) : Prop :=
  t.pc = pc ∧ t.sub = 0 ∧ t.acc = [] ∧ t.fault = none ∧ Holds t.regs F

/-- Close `Holds` goals fact by fact: by evaluation, or leave an equation on the value. -/
theorem holds_cons_of {regs : Nat → Option Value} {r : Nat} {v v' : Value}
    {l : List (Nat × Value)} (h : regs r = some v') (e : v' = v) (rest : Holds regs l) :
    Holds regs ((r, v) :: l) := ⟨e ▸ h, rest⟩

/-- Split a `Holds` goal into one equation per fact, between the computed value and the
stated one; close the equations whose two sides are syntactically equal, leave the rest. -/
macro "holds_facts" : tactic => `(tactic| repeat' (first
  | exact trivial
  | (refine holds_cons_of rfl ?_ ?_; try with_reducible rfl)))

theorem At.next {t : TState} {pc : Nat} {F : List (Nat × Value)} (h : At t pc F) :
    At (PTX.next t) (pc + 1) F :=
  ⟨congrArg (· + 1) h.1, h.2⟩

theorem At.set {t : TState} {pc : Nat} {F : List (Nat × Value)} {r : Nat} {v : Value}
    (h : At t pc F) (hr : ∀ p ∈ F, p.1 ≠ r) :
    At (PTX.next (setReg t r v)) (pc + 1) ((r, v) :: F) :=
  ⟨congrArg (· + 1) h.1, h.2.1, h.2.2.1, h.2.2.2.1, Function.update_self ..,
    holds_update h.2.2.2.2 hr⟩

theorem At.mono {t : TState} {pc : Nat} {F G : List (Nat × Value)} (h : At t pc F)
    (hG : Holds t.regs G) : At t pc G :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hG⟩

/-- A conditional branch on a predicate fact keeps every register fact. No assumption of `A`
names the branch (`hL`), since the local step consults the assumptions before the Core rule. -/
theorem run_bra {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc target : Nat} {p : Nat} {F : List (Nat × Value)} {uni : Bool}
    (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩) (pick : Bool) (h : At t pc F)
    (hp : t.regs p = some (.pred pick))
    (hL : ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    ∃ u, run K A L g 1 t = some u ∧ At u (if pick then target else pc + 1) F := by
  cases pick with
  | false =>
    refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind,
      pure, Except.pure]
  | true =>
    refine ⟨{t with pc := target}, ?_, rfl, h.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind, pure,
      Except.pure, hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, execBranch, Op.isLocal]

/-- `At t pc G` from `h : At t pc F` when every fact of `G` is a fact of `F`, found by lookup. -/
macro "at_select" h:term : tactic => `(tactic| (
  refine At.mono $h ?_
  repeat' (first | exact trivial | refine ⟨holds_lookup ($h).2.2.2.2 rfl, ?_⟩)))

theorem readFloat_reg {t : TState} {fmt : FloatFmt} {r : Nat} {v : Value} (h : t.regs r = some v) :
    readFloat t fmt (.reg r) = valFloat fmt v := by
  cases v <;> simp [readFloat, valFloat, readReg, h, bind, Except.bind, pure, Except.pure]

end PTX.Proof
