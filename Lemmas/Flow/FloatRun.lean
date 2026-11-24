-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Segment
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Widen
public import Lemmas.Assumption.Facts

@[expose] public section

/-! # Floating steps that evaluation does not decide

A proof tool, for segments cut at checkpoints (`Seg`). Evaluating a segment (`seg_fp`) decides
each step by computation; it stops at a floating operand whose number is not computable, such
as a register holding the bits of a kernel parameter (`valFloat .f32 (.bits 32 b)`), and it does
not run a step an assumption selects as a whole segment (`segmentExact`). These pieces take
such steps by lemmas instead, from facts with explicit values in front of a table
(`valueEx base ex`, the first explicit value of a register, else its table value), to the same
form with the written registers in front:

* `Seg.set1`: one step that writes one register; `Seg.fmul` for `mul.f32` and `Seg.fsetpImm` for
  `setp` against a finite constant, when the operands read as numbers (`valFloat … = .ok x`).
* `Seg.fmas` (`FmaRun`): a run of `fma.rn.f32x2 q, a, c, z` products by the same pairs `c` and
  `z`, each optionally after the pack of its source pair and followed by the unpack of the
  product.
* `Seg.segTwo`, `Seg.segTwoAt`: a two-lane `segmentExact` instance (`run_segmentExact_two`).

`holds_ext` carries the facts across: a register that is written gets its explicit value, any
other live register keeps the value it had. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- The value of `r`: its first explicit value in `ex`, else its value in `base`. -/
def valueEx (base : Nat → Value) (ex : List (Nat × Value)) (r : Nat) : Value :=
  (ex.lookup r).getD (base r)

theorem lookup_append_some {ys ex : List (Nat × Value)} {r : Nat} {v : Value}
    (h : ys.lookup r = some v) : (ys ++ ex).lookup r = some v := by
  induction ys with
  | nil => cases h
  | cons p ys ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.lookup, List.cons_append] at h ⊢
    split at h
    · exact h
    · exact ih h

theorem lookup_append_none {ys ex : List (Nat × Value)} {r : Nat}
    (h : r ∉ ys.map Prod.fst) : (ys ++ ex).lookup r = ex.lookup r := by
  induction ys with
  | nil => rfl
  | cons p ys ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup, List.cons_append]
    have : (r == k) = false := beq_false_of_ne h.1
    rw [this]
    exact ih h.2

theorem lookup_of_mem_keys {ys : List (Nat × Value)} {r : Nat} (h : r ∈ ys.map Prod.fst) :
    ∃ v, ys.lookup r = some v := by
  induction ys with
  | nil => cases h
  | cons p ys ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.lookup]
    split
    · exact ⟨w, rfl⟩
    · rename_i hne
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp at hne
      · exact ih h

/-- **The facts after written registers**: the registers `ys` names hold their first value in
`ys`; every other register outside `W` keeps its value. Each live register at the end is named
by `ys`, or is neither written nor dead at the start. -/
theorem holds_ext {R R' : Nat → Option Value} {base : Nat → Value}
    {ex ys : List (Nat × Value)} {liveS liveT W : List Nat}
    (h : Holds R (factsFrom liveS (valueEx base ex)))
    (hframe : ∀ r, r ∉ W → R' r = R r)
    (hys : ∀ r ∈ ys.map Prod.fst, R' r = ys.lookup r)
    (hcov : ∀ r ∈ liveT, r ∈ ys.map Prod.fst ∨ (r ∉ W ∧ r ∈ liveS)) :
    Holds R' (factsFrom liveT (valueEx base (ys ++ ex))) := by
  refine holds_of_pointwise fun r hr => ?_
  by_cases hk : r ∈ ys.map Prod.fst
  · obtain ⟨v, hv⟩ := lookup_of_mem_keys hk
    rw [hys r hk, hv, valueEx, lookup_append_some hv]
    rfl
  · rcases hcov r hr with hk' | ⟨hw, hs⟩
    · exact absurd hk' hk
    rw [hframe r hw, holds_mem h (mem_factsFrom hs), valueEx, valueEx, lookup_append_none hk]

/-! ### One written register -/

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **One step that writes one register**, from facts with explicit values to the same form
with the written register in front. -/
theorem Seg.set1 {pc d : Nat} {op : Op} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} {v : Value} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom liveS (valueEx base ex)) →
      execLocalA A L g t op = .ok (PTX.next (setReg t d v)))
    (hcov : ∀ r ∈ liveT, r ∈ [d] ∨ (r ∉ [d] ∧ r ∈ liveS)) :
    Seg K A L g 1 pc (factsFrom liveS (valueEx base ex)) (pc + 1)
      (factsFrom liveT (valueEx base ([(d, v)] ++ ex))) := by
  intro t h
  refine ⟨_, run_local hc hl h (hex t h), congrArg (· + 1) h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  refine holds_ext (W := [d]) h.2.2.2.2 (fun r hr => ?_) (fun r hr => ?_) hcov
  · simp only [PTX.next, setReg]
    exact Function.update_of_ne (by simpa using hr) _ _
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    subst hr
    simp [PTX.next, setReg]

/-- `mul.f32` of two registers that read as numbers. -/
theorem exec_fmul {t : TState} {d a b : Nat} {va vb : Value} {x y : ℝ}
    (hI : IdealAt A (.mul .f32) L g t) (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hx : valFloat .f32 va = .ok x) (hy : valFloat .f32 vb = .ok y) :
    execLocalA A L g t (.float {
        op := .mul, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .reg b] }) =
      .ok (PTX.next (setReg t d (.float .f32 (x * y)))) := by
  have hbr : readERealOpnd t .f32 (.reg a) = some (.ok (x : EReal)) := by
    rw [readERealOpnd_reg ha]; exact readEReal_of_valFloat hx
  have hbi : readERealOpnd t .f32 (.reg b) = some (.ok (y : EReal)) := by
    rw [readERealOpnd_reg hb]; exact readEReal_of_valFloat hy
  have hmul : mulEReal (x : EReal) (y : EReal) = some ((x * y : ℝ) : EReal) := by
    rw [Assumption.mulEReal, ite_eq_right (by simp)]
    push_cast
    ring
  have hval : erealValue .f32 ((x * y : ℝ) : EReal) = .float .f32 (x * y) := by
    unfold erealValue
    rw [ite_eq_right (EReal.coe_ne_top (x * y)), ite_eq_right (EReal.coe_ne_bot (x * y))]
    rfl
  have hop : FloatForm.ofOp (.float {
      op := .mul, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .reg b] }) =
      some (.mul .f32) := by
    simp [FloatForm.ofOp]
  have hex : execIdealFloat L g t (.float {
      op := .mul, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .reg b] }) =
      some (.ok (PTX.next (setReg t d (erealValue .f32 ((x * y : ℝ) : EReal))))) := by
    simp only [execIdealFloat, hbr, hbi, bindRead, hmul, pure, Except.pure, Option.map_some]
  rw [hI _ hop _ hex, hval]

/-- **`mul.f32` of two registers that read as numbers**, as a piece. -/
theorem Seg.fmul {pc d a b : Nat} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} {x y : ℝ}
    (hc : K.code[pc]? = some ⟨none, (.float {
      op := .mul, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .reg b] })⟩)
    (hI : ∀ t : TState, t.pc = pc → IdealAt A (.mul .f32) L g t)
    (ha : a ∈ liveS) (hb : b ∈ liveS)
    (hx : valFloat .f32 (valueEx base ex a) = .ok x)
    (hy : valFloat .f32 (valueEx base ex b) = .ok y)
    (hcov : ∀ r ∈ liveT, r ∈ [d] ∨ (r ∉ [d] ∧ r ∈ liveS)) :
    Seg K A L g 1 pc (factsFrom liveS (valueEx base ex)) (pc + 1)
      (factsFrom liveT (valueEx base ([(d, .float .f32 (x * y))] ++ ex))) :=
  Seg.set1 hc rfl (fun t h => exec_fmul (hI t h.1) (holds_mem h.2.2.2.2 (mem_factsFrom ha))
    (holds_mem h.2.2.2.2 (mem_factsFrom hb)) hx hy) hcov

/-- `setp` of a register that reads as a number against a finite constant. -/
theorem exec_fsetpImm {t : TState} {fc : FCmp} {cmp : Cmp} {ftz : Bool} {d a b : Nat}
    {v : Value} {x y : ℝ}
    (hfc : fc = .ord cmp ∨ fc = .unord cmp)
    (hinf : isInfConst (.f32imm b) = false) (hI : IdealAt A (.setp .f32) L g t)
    (ha : t.regs a = some v) (hx : valFloat .f32 v = .ok x)
    (hy : valFloat .f32 (.bits 32 (BitVec.ofNat 64 b)) = .ok y) :
    execLocalA A L g t (.float {
        op := .setp fc none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
        srcs := [.reg a, .f32imm b] }) =
      .ok (PTX.next (setReg t d (.pred (erealCompare cmp (x : EReal) (y : EReal))))) := by
  have hbr : readERealOpnd t .f32 (.reg a) = some (.ok (x : EReal)) := by
    rw [readERealOpnd_reg ha]; exact readEReal_of_valFloat hx
  have hbi : readERealOpnd t .f32 (.f32imm b) = some (.ok (y : EReal)) := by
    simpa [readERealOpnd] using readEReal_of_valFloat hy
  have hop : FloatForm.ofOp (.float {
      op := .setp fc none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
      srcs := [.reg a, .f32imm b] }) = some (.setp .f32) := by
    have hinf' : isInfConst (.reg a) = false := rfl
    rcases hfc with rfl | rfl <;> simp [FloatForm.ofOp, hinf, hinf']
  have hex : execIdealFloat L g t (.float {
      op := .setp fc none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
      srcs := [.reg a, .f32imm b] }) =
      some (.ok (PTX.next (setReg t d
        (.pred (erealCompare cmp (x : EReal) (y : EReal)))))) := by
    rcases hfc with rfl | rfl <;>
      simp only [execIdealFloat, hbr, hbi, bindRead, pure, Except.pure]
  rw [hI _ hop _ hex]

/-- **`setp` against a finite constant**, as a piece. -/
theorem Seg.fsetpImm {pc d a b : Nat} {fc : FCmp} {cmp : Cmp} {ftz : Bool}
    {liveS liveT : List Nat} {base : Nat → Value} {ex : List (Nat × Value)} {x y : ℝ}
    (hc : K.code[pc]? = some ⟨none, (.float {
      op := .setp fc none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
      srcs := [.reg a, .f32imm b] })⟩)
    (hfc : fc = .ord cmp ∨ fc = .unord cmp)
    (hinf : isInfConst (.f32imm b) = false)
    (hI : ∀ t : TState, t.pc = pc → IdealAt A (.setp .f32) L g t) (ha : a ∈ liveS)
    (hx : valFloat .f32 (valueEx base ex a) = .ok x)
    (hy : valFloat .f32 (.bits 32 (BitVec.ofNat 64 b)) = .ok y)
    (hcov : ∀ r ∈ liveT, r ∈ [d] ∨ (r ∉ [d] ∧ r ∈ liveS)) :
    Seg K A L g 1 pc (factsFrom liveS (valueEx base ex)) (pc + 1)
      (factsFrom liveT (valueEx base
        ([(d, .pred (erealCompare cmp (x : EReal) (y : EReal)))] ++ ex))) :=
  Seg.set1 hc rfl (fun t h => exec_fsetpImm hfc hinf (hI t h.1)
    (holds_mem h.2.2.2.2 (mem_factsFrom ha)) hx hy) hcov

/-- A `setp` against negative infinity of a number: `x ≠ -∞` holds. -/
theorem erealCompare_ne_bot (x : ℝ) : erealCompare .ne (x : EReal) ⊥ = true := by
  simp [erealCompare]


/-! ### A two-lane segment -/

/-- The registers a two-lane instance writes with their values: the outputs, then the
constants a defining shape sets. -/
def segVals {σ : Type} [DecidableEq σ] (m : SegMatch σ) (fn : ℝ → ℝ) (o₀ o₁ : σ)
    (x₀ x₁ : ℝ) : List (Nat × Value) :=
  [(m.regOf o₀, .float .f32 (fn x₀)), (m.regOf o₁, .float .f32 (fn x₁))] ++
    (if m.shape.defines then m.shape.consts.map fun p => (m.regOf p.1, p.2) else [])

/-- The registers of `segVals`. -/
def segKeys {σ : Type} [DecidableEq σ] (m : SegMatch σ) (o₀ o₁ : σ) : List Nat :=
  [m.regOf o₀, m.regOf o₁] ++
    (if m.shape.defines then m.shape.consts.map fun p => m.regOf p.1 else [])

theorem segVals_keys {σ : Type} [DecidableEq σ] {m : SegMatch σ} {fn : ℝ → ℝ} {o₀ o₁ : σ}
    {x₀ x₁ : ℝ} : (segVals m fn o₀ o₁ x₀ x₁).map Prod.fst = segKeys m o₀ o₁ := by
  unfold segVals segKeys
  split <;> simp

theorem foldl_update_get {β : Type} {f : β → Nat} {v : β → Value} :
    ∀ (l : List β) (rs : Nat → Option Value) {x : β}, (l.map f).Nodup → x ∈ l →
      (l.foldl (fun rs y => Function.update rs (f y) (some (v y))) rs) (f x) = some (v x)
  | [], _, _, _, hx => by cases hx
  | y :: l, rs, x, hnd, hx => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact foldl_update_last l rfl (fun z hz he => hnd.1 z hz he)
    · exact foldl_update_get l _ hnd.2 hx

theorem lookup_map_get {β : Type} {f : β → Nat} {v : β → Value} :
    ∀ (l : List β) {x : β}, (l.map f).Nodup → x ∈ l →
      (l.map fun y => (f y, v y)).lookup (f x) = some (v x)
  | [], _, _, hx => by cases hx
  | y :: l, x, hnd, hx => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [List.map_cons, List.lookup]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : f x ≠ f y := fun he => hnd.1 x hx he
      rw [beq_false_of_ne hne]
      exact lookup_map_get l hnd.2 hx

/-- A register no slot writes, no output names and (for a defining shape) no constant names
keeps its value. -/
theorem segRegs_keep {σ : Type} [DecidableEq σ] {m : SegMatch σ} {t : TState}
    {outs : List (Nat × Value)} {r : Nat} (hw : ∀ s ∈ m.shape.writes, m.regOf s ≠ r)
    (ho : ∀ p ∈ outs, p.1 ≠ r) (hk : m.shape.defines → ∀ p ∈ m.shape.consts, m.regOf p.1 ≠ r) :
    segRegs m t outs r = t.regs r := by
  unfold segRegs
  simp only
  rw [foldl_update_other (f := Prod.fst) (v := fun p => some p.2) outs ho]
  split
  · rename_i hd
    refine (foldl_update_other (β := σ × Value) (f := fun p => m.regOf p.1)
      (v := fun p => some p.2) _ (hk hd)).trans ?_
    exact foldl_update_other (f := m.regOf) (v := fun _ => none) _ hw
  · exact foldl_update_other (f := m.regOf) (v := fun _ => none) _ hw

/-- The constants a defining shape sets. -/
theorem segRegs_const {σ : Type} [DecidableEq σ] {m : SegMatch σ} {t : TState}
    {outs : List (Nat × Value)} {p : σ × Value} (hd : m.shape.defines = true)
    (hp : p ∈ m.shape.consts) (hnd : (m.shape.consts.map fun p => m.regOf p.1).Nodup)
    (ho : ∀ q ∈ outs, q.1 ≠ m.regOf p.1) : segRegs m t outs (m.regOf p.1) = some p.2 := by
  unfold segRegs
  simp only [hd, ↓reduceIte]
  rw [foldl_update_other (f := Prod.fst) (v := fun p => some p.2) outs ho]
  exact foldl_update_get (f := fun p => m.regOf p.1) (v := Prod.snd) _ _ hnd hp

/-- **A two-lane instance of a `segmentExact` template, as a piece**: the outputs receive the
template's function of their inputs, a defining shape sets its constants, the other
registers it writes are dead at the end and every other live register keeps its value. -/
theorem Seg.segTwo {σ : Type} [DecidableEq σ] {name why : String} {T : SegTemplate σ}
    {sites : List Nat} {A₁ A₂ : List Assumption} {m : SegMatch σ} {pc : Nat} {op : Op}
    {i₀ o₀ i₁ o₁ : σ} {x₀ x₁ : ℝ} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hs : sites.contains pc = true) (hm : T.matchAt K pc = some m)
    (hio : m.shape.io = [(i₀, o₀), (i₁, o₁)])
    (hcst : m.shape.defines = true ∨ ((∀ p ∈ m.shape.consts, m.regOf p.1 ∈ liveS) ∧
      m.shape.consts.map (fun p => valueEx base ex (m.regOf p.1)) = m.shape.consts.map Prod.snd))
    (hi₀ : m.regOf i₀ ∈ liveS) (hx₀ : valFloat .f32 (valueEx base ex (m.regOf i₀)) = .ok x₀)
    (hi₁ : m.regOf i₁ ∈ liveS) (hx₁ : valFloat .f32 (valueEx base ex (m.regOf i₁)) = .ok x₁)
    (hnd : (segKeys m o₀ o₁).Nodup)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys m o₀ o₁ ∨
      (r ∉ segKeys m o₀ o₁ ++ m.shape.writes.map m.regOf ∧ r ∈ liveS))
    (hA₁ : SegFreePc A₁ pc) :
    Seg K (A₁ ++ segmentExact K name T sites why :: A₂) L g 1 pc
      (factsFrom liveS (valueEx base ex)) m.stop
      (factsFrom liveT (valueEx base (segVals m T.fn o₀ o₁ x₀ x₁ ++ ex))) := by
  intro t h
  have hR := h.2.2.2.2
  have hcst' : m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (m.regOf p.1) = some p.2 := by
    rcases hcst with hd | ⟨hin, heq⟩
    · exact .inl hd
    · refine .inr fun p hp => ?_
      rw [holds_mem hR (mem_factsFrom (hin p hp))]
      have := congrArg (fun l => l[m.shape.consts.idxOf p]?) heq
      simp only [List.getElem?_map, List.getElem?_idxOf hp, Option.map_some] at this
      exact congrArg some (Option.some.inj this)
  refine ⟨_, run_segmentExact_two (F := factsFrom liveS (valueEx base ex)) hc hl h hs hm hio
    hcst' (mem_factsFrom hi₀) hx₀ (mem_factsFrom hi₁) hx₁ hA₁, rfl, rfl, rfl, h.2.2.2.1, ?_⟩
  simp only [segKeys, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    not_or] at hnd
  have hne : m.regOf o₀ ≠ m.regOf o₁ := hnd.1.1
  refine holds_ext (W := segKeys m o₀ o₁ ++ m.shape.writes.map m.regOf) hR
    (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_append, not_or, List.mem_map, not_exists, not_and] at hr
    refine segRegs_keep (fun s hs he => hr.2 s hs he) (fun q hq => ?_) (fun hd q hq he => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact fun he => hr.1 (by simp only at he; simp [segKeys, ← he])
      · exact fun he => hr.1 (by simp only at he; simp [segKeys, ← he])
    · exact hr.1 (by simp only [segKeys, hd, ↓reduceIte]; simp only [List.mem_append,
        List.mem_map]; exact .inr ⟨q, hq, he⟩)
  · rw [segVals_keys] at hr
    simp only [segKeys, List.cons_append, List.nil_append, List.mem_cons] at hr
    show segRegs m t _ r = _
    rcases hr with rfl | rfl | hr
    · rw [(segRegs_two_out (m := m) (t := t)).2 hne]
      simp [segVals]
    · rw [(segRegs_two_out (m := m) (t := t)).1]
      simp [segVals, List.lookup, beq_false_of_ne (Ne.symm hne)]
    · split at hr
      · rename_i hd
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
        simp only [hd, ↓reduceIte] at hnd
        have h0 : m.regOf p.1 ≠ m.regOf o₀ := fun he =>
          hnd.1.2 (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
        have h1 : m.regOf p.1 ≠ m.regOf o₁ := fun he =>
          hnd.2.1 (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
        rw [segRegs_const hd hp hnd.2.2 (fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact Ne.symm h0
          · exact Ne.symm h1)]
        simp only [segVals, hd, ↓reduceIte, List.cons_append, List.nil_append, List.lookup,
          beq_false_of_ne h0, beq_false_of_ne h1]
        exact (lookup_map_get (f := fun p => m.regOf p.1) (v := Prod.snd) _ hnd.2.2 hp).symm
      · cases hr
  · rw [segVals_keys]
    exact hcov r hr

/-- `Seg.segTwo` for a list `A` given as `A₁ ++ a :: A₂` with `a` the `segmentExact`. -/
theorem Seg.segTwoAt {σ : Type} [DecidableEq σ] {name why : String} {T : SegTemplate σ}
    {sites : List Nat} {a : Assumption} {A A₁ A₂ : List Assumption} {m : SegMatch σ} {pc : Nat}
    {op : Op} {i₀ o₀ i₁ o₁ : σ} {x₀ x₁ : ℝ} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} (ha : a = segmentExact K name T sites why)
    (hA : A = A₁ ++ a :: A₂) (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hs : sites.contains pc = true) (hm : T.matchAt K pc = some m)
    (hio : m.shape.io = [(i₀, o₀), (i₁, o₁)])
    (hcst : m.shape.defines = true ∨ ((∀ p ∈ m.shape.consts, m.regOf p.1 ∈ liveS) ∧
      m.shape.consts.map (fun p => valueEx base ex (m.regOf p.1)) = m.shape.consts.map Prod.snd))
    (hi₀ : m.regOf i₀ ∈ liveS) (hx₀ : valFloat .f32 (valueEx base ex (m.regOf i₀)) = .ok x₀)
    (hi₁ : m.regOf i₁ ∈ liveS) (hx₁ : valFloat .f32 (valueEx base ex (m.regOf i₁)) = .ok x₁)
    (hnd : (segKeys m o₀ o₁).Nodup)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys m o₀ o₁ ∨
      (r ∉ segKeys m o₀ o₁ ++ m.shape.writes.map m.regOf ∧ r ∈ liveS))
    (hA₁ : SegFreePc A₁ pc) :
    Seg K A L g 1 pc (factsFrom liveS (valueEx base ex)) m.stop
      (factsFrom liveT (valueEx base (segVals m T.fn o₀ o₁ x₀ x₁ ++ ex))) := by
  subst ha hA
  exact Seg.segTwo hc hl hs hm hio hcst hi₀ hx₀ hi₁ hx₁ hnd hcov hA₁

end
end PTX.Flow
