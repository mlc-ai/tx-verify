-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Thread.Tmpl
public import Lemmas.Flow.Async
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Cvt
public import Lemmas.Flow.FloatOp
public import Lemmas.Flow.Widen

@[expose] public section

/-! # The steps of a thread

Each site as a step of the abstract machine: after its event, local steps reach a concrete
state of the successor, evaluating the local code by segments; or the thread is dead and the
machine stops. The input load continues to the shared store when its bytes rebuild to a 4-byte
value; the barrier branches on the thread's index in its CTA; a read of the reduction loop adds
the cell's `f32` reading to the accumulator and branches on the loop index. -/

namespace PTX.Kernels.BlockSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {g : Nat}

/-- The continuation of a step: a concrete state of the successor, or a dead state where the
machine stops. -/
abbrev Cont (A B : Nat) (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  (∃ d' t', next g d e = some (some d') ∧ Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧
      At t' d'.site.pc (facts A B L g d') ∧ Inv d') ∨
    (next g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u)

/-- The value-table reduction used after evaluating a segment. -/
macro "bs_values" : tactic =>
  `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- The input load: bytes that rebuild to a 4-byte value reach the shared store. -/
theorem step_input (hpre : Pre L A B x mem0) (hg : g < L.threads) {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hs : d.site = .input) (h : At t d.site.pc (facts A B L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont A B L g d e u := by
  obtain ⟨s, v, i, acc, sm⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
  rw [tmpl_input hpre hg h] at hf
  obtain ⟨bs, hbl, rfl, hu⟩ := hf
  cases hu
  have hbase := hpre.sharedRange
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok w =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    have hframe : ∀ r, r ∉ [8] → (setReg t 8 w).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [setReg, Function.update_of_ne hr]
    have h10 : At { setReg t 8 w with pc := t.pc + 1, sub := 0, acc := [] } (Flow.load_0 + 1)
        (factsAt A B L g (Flow.load_0 + 1) ⟨.share, w, i, acc, sm⟩) := by
      refine ⟨by simp only [h.1]; rfl, rfl, rfl, by simpa [setReg] using h.2.2.2.1, ?_⟩
      change Holds (setReg t 8 w).regs _
      frame_fp h.2.2.2.2, hframe
      exact ⟨by simp only [setReg, Function.update_self]; rfl, trivial⟩
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 3
        { setReg t 8 w with pc := t.pc + 1, sub := 0, acc := [] } = some t' ∧
        At t' Site.share.pc (facts A B L g ⟨.share, w, i, acc, sm⟩) := by
      seg_fp h10 using
        bs_values
        all_goals seg_close
    by_cases hw : w.bytes = 4
    · exact .inl ⟨⟨.share, w, i, acc, sm⟩, t', by simp [next, hv, hw], run_rtg hr, ht',
        ⟨fun _ => hw, by simp, by simp⟩⟩
    · exfalso
      exact hw (by rw [rebuild_bytes_eq_length 3 bs w hv, hbl])

/-- The shared store reaches the barrier. -/
theorem step_share {d : D} {t u : TState} {e : Event} {ins : Instr} (hs : d.site = .share)
    (hi : Inv d) (h : At t d.site.pc (facts A B L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont A B L g d e u := by
  obtain ⟨s, v, i, acc, sm⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
  obtain ⟨a, bs, rfl, rfl⟩ := fires_st rfl hf
  refine .inl ⟨⟨.bar, v, i, acc, sm⟩, _, by simp [next], .refl, ?_,
    ⟨by simp, by simp, by simp⟩⟩
  refine ⟨by simp [afterStore, h.1]; rfl, by simp [afterStore], by simpa [afterStore] using h.2.2.1,
    by simpa [afterStore] using h.2.2.2.1, ?_⟩
  simp only [afterStore, List.length_singleton, h.2.1, Nat.zero_add, Nat.lt_irrefl, ↓reduceIte]
  exact Flow.holds_factsFrom_mono (live := Flow.live Site.share.pc)
    (live' := Flow.live Site.bar.pc) h.2.2.2.2 (by table_decide)

/-- The initial accumulator, `0f00000000`, holds its bit pattern; read as `f32` it is `0`. -/
theorem valFloat_zero : valFloat .f32 (PTX.Proof.b32 0) = .ok 0 := by
  have h : FloatFmt.f32.layout.decode 0 = some (.zero false) := by
    simp [FloatFmt.layout, Layout.decode, Layout.fieldVal]
  have hc : classify .f32 (PTX.Proof.b32 0) = .ok (.zero false) := by
    simpa [PTX.Proof.b32, FloatFmt.bytes] using classify_bits (fmt := .f32) (by norm_num) h
  rw [valFloat_of_classify (fmt := .f32) (v := PTX.Proof.b32 0) (x := .zero false)
    (by intro f y hh; cases hh) hc]
  simp [FVal.finite, pure, Except.pure]

/-- The block-sum assumption gives no rule to a branch. -/
theorem prod_localRule_bra (L : Launch) (g : Nat) (t : TState) (target : Nat) (uni : Bool) :
    ∀ a ∈ [Assumptions.idealAdd], a.localRule L g t (.bra target uni) = none := by
  intro a ha
  simp only [List.mem_singleton] at ha
  subst a
  simp only [Assumptions.idealAdd]
  exact Assumption.idealReal_localRule_none (by intro f hf; cases hf)

/-- The barrier: thread 0 of the CTA enters the reduction loop, every other thread exits. -/
theorem step_bar (hpre : Pre L A B x mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bar) (h : At t d.site.pc (facts A B L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont A B L g d e u := by
  obtain ⟨s, v, i, acc, sm⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
  rw [tmpl_bar] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have hbase := hpre.sharedRange
  have h15 : At (PTX.next t) (Flow.bar_0 + 1)
      (factsAt A B L g (Flow.bar_0 + 1) ⟨.bar, v, i, acc, sm⟩) :=
    At.mono (At.next h) (Flow.holds_factsFrom_mono h.2.2.2.2 (by table_decide))
  obtain ⟨t16, hr, h16⟩ : ∃ t', run kernel Prod L g 1 (PTX.next t) = some t' ∧
      At t' Flow.bra_16 (factsAt A B L g Flow.bra_16 ⟨.bar, v, i, acc, sm⟩) := by
    seg_fp h15 using
      bs_values
      all_goals seg_close
  obtain ⟨u1, hr1, hu1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_16
    (decide (g % 256 ≠ 0)) h16 (reg_of h16 (by table_decide)) (prod_localRule_bra L g _ _ _)
  by_cases hz : g % 256 = 0
  · have hd : decide (g % 256 ≠ 0) = false := by simp [hz]
    rw [hd] at hu1
    simp only [Bool.false_eq_true, ↓reduceIte] at hu1
    have h17 : At u1 (Flow.bra_16 + 1)
        (factsAt A B L g (Flow.bra_16 + 1) ⟨.bar, v, i, acc, sm⟩) :=
      At.mono hu1 (Flow.holds_factsFrom_mono hu1.2.2.2.2 (by table_decide))
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3 u1 = some t' ∧
        At t' Site.sum.pc (facts A B L g ⟨.sum, v, 0, PTX.Proof.b32 0, 0⟩) := by
      seg_fp h17 using
        bs_values
        all_goals seg_close
    exact .inl ⟨⟨.sum, v, 0, PTX.Proof.b32 0, 0⟩, t', by simp [next, hz],
      run_rtg (run_comp (run_comp hr hr1) hr'), ht',
      ⟨by simp, fun _ => ⟨by simp, readEReal_of_valFloat valFloat_zero⟩, by simp⟩⟩
  · have hd : decide (g % 256 ≠ 0) = true := by simp [hz]
    rw [hd] at hu1
    simp only [↓reduceIte] at hu1
    exact .inl ⟨⟨.exit, v, i, acc, sm⟩, u1, by simp [next, hz], run_rtg (run_comp hr hr1),
      At.mono hu1 (Flow.holds_factsFrom_mono hu1.2.2.2.2 (by table_decide)),
      ⟨by simp, by simp, by simp⟩⟩

/-- The state after the read of a cell returned the scalar `w`. -/
def load1 (t : TState) (w : Value) : TState :=
  { setReg t 12 w with pc := t.pc + 1, sub := 0, acc := [] }

/-- The accumulator register `%r15` of the loop's add holds the abstract accumulator. -/
theorem load1_acc (h : At t Site.sum.pc (facts A B L g ⟨.sum, v, i, acc, sm⟩)) :
    (load1 t w).regs 15 = some acc := by
  have := reg_of (d := ⟨.sum, v, i, acc, sm⟩) h (r := 15) (by table_decide)
  simp only [load1, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    Function.update_of_ne]
  rw [this]
  bs_values

/-- The register `%r12` of the loop's add holds the word the read returned. -/
theorem load1_word (t : TState) (w : Value) : (load1 t w).regs 12 = some w := by
  simp [load1, setReg]

/-- The code of the loop's add is the `add.f32` of the two registers. -/
theorem load1_code (h : At t Site.sum.pc (facts A B L g ⟨.sum, v, i, acc, sm⟩)) :
    kernel.code[(load1 t w).pc]? = some ⟨none, fadd .f32 15 (.reg 15) (.reg 12)⟩ := by
  simp only [load1, h.1]
  exact Flow.code_21

/-- The state after the read is unfaulted when the state before it was. -/
theorem load1_fault (h : At t Site.sum.pc (facts A B L g ⟨.sum, v, i, acc, sm⟩)) :
    (load1 t w).fault = none := by
  simpa [load1, setReg] using h.2.2.2.1

/-- **The Core rule of the loop's `add.f32` is `noRule`**, whatever the operands: the decoded
instruction carries `rnd := none` and `FloatInstr.arith` starts from `f.rnd.map
FloatRound.mode`. -/
theorem exec_fadd_noRule {t : TState} {d a b : Nat} {va vb : Value} {fa fb : FVal}
    (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hfa : classify .f32 va = .ok fa) (hfb : classify .f32 vb = .ok fb) :
    execLocal L g t (fadd .f32 d (.reg a) (.reg b)) = .error .noRule := by
  simp [execLocal, Op.rule, execFloat, FloatInstr.rule, FloatInstr.lane, FloatInstr.ieee,
    FloatInstr.arith, readValue, readReg, ty1, floatLane, boolCombine, hfa, hfb, ha, hb, throw,
    throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]

/-- The Core rule of the loop's `add.f32` never succeeds: a fault of `classify` is one too. -/
theorem core_fadd_faults {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    ∃ f, execLocal L g t (fadd .f32 d (.reg a) (.reg b)) = .error f := by
  cases hfa : classify .f32 va with
  | error e =>
    exact ⟨e, by simp [execLocal, Op.rule, execFloat, FloatInstr.rule, readValue, readReg, ty1,
      floatLane, boolCombine, hfa, ha, hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
      pure, Except.pure]⟩
  | ok fa =>
    cases hfb : classify .f32 vb with
    | error e =>
      exact ⟨e, by simp [execLocal, Op.rule, execFloat, FloatInstr.rule, readValue, readReg, ty1,
        floatLane, boolCombine, hfa, hfb, ha, hb, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind, pure, Except.pure]⟩
    | ok fb => exact ⟨_, exec_fadd_noRule ha hb hfa hfb⟩

/-- The ideal rule of the loop's add has no reading for the accumulator. -/
theorem idealFloat_none_left {d a b : Nat} {va : Value} {t : TState}
    (ha : t.regs a = some va) (h : Assumption.readEReal .f32 va = none) :
    Assumption.execIdealFloat L g t (fadd .f32 d (.reg a) (.reg b)) = none := by
  simp [Assumption.execIdealFloat, Assumption.bindRead, readERealOpnd_reg ha, h]

/-- The ideal rule of the loop's add has no reading for the word. -/
theorem idealFloat_none_right {d a b : Nat} {va vb : Value} {t : TState} {x : EReal}
    (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hx : Assumption.readEReal .f32 va = some (.ok x))
    (h : Assumption.readEReal .f32 vb = none) :
    Assumption.execIdealFloat L g t (fadd .f32 d (.reg a) (.reg b)) = none := by
  simp [Assumption.execIdealFloat, Assumption.bindRead, readERealOpnd_reg ha,
    readERealOpnd_reg hb, hx, h]

/-- The ideal rule of the loop's add has no sum for `∞ - ∞`. -/
theorem idealFloat_none_sum {d a b : Nat} {va vb : Value} {t : TState} {x y : EReal}
    (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hx : Assumption.readEReal .f32 va = some (.ok x))
    (hy : Assumption.readEReal .f32 vb = some (.ok y))
    (h : Assumption.addEReal x y = none) :
    Assumption.execIdealFloat L g t (fadd .f32 d (.reg a) (.reg b)) = none := by
  simp [Assumption.execIdealFloat, Assumption.bindRead, readERealOpnd_reg ha,
    readERealOpnd_reg hb, hx, hy, h]

/-- Where the ideal rule declines the loop's add it has no Core rule behind it, so the local step
faults. -/
theorem exec_fadd_decline {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hn : Assumption.execIdealFloat L g t (fadd .f32 d (.reg a) (.reg b)) = none) :
    ∃ f, execLocalA Prod L g t (fadd .f32 d (.reg a) (.reg b)) = .error f := by
  obtain ⟨g', hg'⟩ := core_fadd_faults (d := d) (L := L) (g := g) ha hb
  refine ⟨g', ?_⟩
  rw [execLocalA_noSegment (A := Prod) (by simp [Assumptions.idealAdd, Assumption.idealReal]),
    execLocalRule_of_none (A := Prod) (by
      intro a' ha'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl
      simp only [Assumptions.idealAdd, Assumption.idealReal]
      show (if Assumption.FloatForm.add .f32 ∈ [Assumption.FloatForm.add .f32] then
        Assumption.execIdealFloat L g t (fadd .f32 d (.reg a) (.reg b)) else none) = none
      rw [ite_eq_left (by simp), hn])]
  exact hg'

/-- **The ideal step of the loop's add**: with both operands read as extended reals and a sum for
them, the local step writes the sum. -/
theorem exec_fadd_ereal {v : Value} {x y r : EReal}
    (h : At t Site.sum.pc (facts A B L g ⟨.sum, v, i, acc, sm⟩)) {w : Value}
    (hx : Assumption.readEReal .f32 acc = some (.ok x))
    (hy : Assumption.readEReal .f32 w = some (.ok y))
    (hr : Assumption.addEReal x y = some r) :
    execLocalA Prod L g (load1 t w) (fadd .f32 15 (.reg 15) (.reg 12)) =
      .ok (PTX.next (setReg (load1 t w) 15 (Assumption.erealValue .f32 r))) := by
  have hr15 := load1_acc (v := v) (i := i) (acc := acc) (sm := sm) h (w := w)
  have hr12 := load1_word t w
  have hx' : Assumption.readERealOpnd (load1 t w) .f32 (.reg 15) = some (.ok x) := by
    rw [readERealOpnd_reg hr15]; exact hx
  have hy' : Assumption.readERealOpnd (load1 t w) .f32 (.reg 12) = some (.ok y) := by
    rw [readERealOpnd_reg hr12]; exact hy
  simp only [execLocalA, execLocalRule, execLocal, Assumptions.idealAdd, Assumption.idealReal,
    List.findSome?, Assumption.execIdealFloat, hx', hy', Assumption.bindRead, hr, pure,
    Except.pure]
  rfl

/-- The loop's add on its ideal step writes the sum. -/
theorem out_fadd {v : Value} {x y r : EReal}
    (h : At t Site.sum.pc (facts A B L g ⟨.sum, v, i, acc, sm⟩)) {w : Value}
    (hx : Assumption.readEReal .f32 acc = some (.ok x))
    (hy : Assumption.readEReal .f32 w = some (.ok y))
    (hr : Assumption.addEReal x y = some r) :
    out kernel Prod L g (load1 t w) =
      .tau (PTX.next (setReg (load1 t w) 15 (Assumption.erealValue .f32 r))) :=
  out_tau (load1_fault h) (load1_code h) rfl rfl (exec_fadd_ereal h hx hy hr)

/-- The loop's add where the ideal rule does not take the step kills the thread: a NaN operand has
no reading, `∞ - ∞` no sum, and a value of another width is a fault the ideal rule reads as one;
the Core rule is `noRule` behind a declined one. -/
theorem out_fadd_dead (h : At t Site.sum.pc (facts A B L g ⟨.sum, v, i, acc, sm⟩)) {w : Value}
    (hbad : ¬ ∃ x y r : EReal, Assumption.readEReal .f32 acc = some (.ok x) ∧
      Assumption.readEReal .f32 w = some (.ok y) ∧ Assumption.addEReal x y = some r) :
    ∃ f, out kernel Prod L g (load1 t w) = .ev (.ub f) := by
  have hr15 := load1_acc (v := v) (i := i) (acc := acc) (sm := sm) h (w := w)
  have hr12 := load1_word t w
  have hc := load1_code (v := v) (i := i) (acc := acc) (sm := sm) h (w := w)
  have hf := load1_fault (v := v) (i := i) (acc := acc) (sm := sm) h (w := w)
  cases ha : Assumption.readEReal .f32 acc with
  | none =>
    have hn := idealFloat_none_left (L := L) (g := g) (d := 15) (b := 12) hr15 ha
    obtain ⟨f, hfl⟩ := exec_fadd_decline (L := L) (g := g) hr15 hr12 hn
    exact ⟨f, out_ub hf hc rfl rfl hfl⟩
  | some ea =>
    cases ea with
    | error f =>
      obtain ⟨f', hfl⟩ := exec_fadd_error (A := Prod) (by
        simp only [Assumptions.idealAdd]
        exact Assumption.idealFor_head (by simp)) hr15 hr12 (Or.inl ⟨f, ha⟩)
      exact ⟨f', out_ub hf hc rfl rfl hfl⟩
    | ok x =>
      cases hb : Assumption.readEReal .f32 w with
      | none =>
        have hn := idealFloat_none_right (L := L) (g := g) (d := 15) (b := 12) hr15 hr12 ha hb
        obtain ⟨f, hfl⟩ := exec_fadd_decline (L := L) (g := g) hr15 hr12 hn
        exact ⟨f, out_ub hf hc rfl rfl hfl⟩
      | some eb =>
        cases eb with
        | error f =>
          obtain ⟨f', hfl⟩ := exec_fadd_error (A := Prod) (by
            simp only [Assumptions.idealAdd]
            exact Assumption.idealFor_head (by simp)) hr15 hr12 (Or.inr ⟨⟨x, ha⟩, f, hb⟩)
          exact ⟨f', out_ub hf hc rfl rfl hfl⟩
        | ok y =>
          cases hr : Assumption.addEReal x y with
          | none =>
            have hn := idealFloat_none_sum (L := L) (g := g) (d := 15) (b := 12) hr15 hr12
              ha hb hr
            obtain ⟨f, hfl⟩ := exec_fadd_decline (L := L) (g := g) hr15 hr12 hn
            exact ⟨f, out_ub hf hc rfl rfl hfl⟩
          | some r =>
            exact absurd ⟨x, y, r, ha, hb, hr⟩ hbad

/-- A read of the reduction loop: a cell with an extended-real reading is added to the
accumulator; the loop continues to the next cell, or after the last one reaches the output
store. A cell with no reading, or an add the ideal rule declines, stops the thread. -/
theorem step_sum (hpre : Pre L A B x mem0) (hg : g < L.threads) {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hs : d.site = .sum) (hi : Inv d)
    (h : At t d.site.pc (facts A B L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont A B L g d e u := by
  obtain ⟨s, v, i, acc, sm⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨hi256, hacc⟩ := hi.sum rfl
  simp only at hi256 hacc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_1)
  rw [tmpl_sum hpre hi256 h] at hf
  obtain ⟨bs, -, rfl, hu⟩ := hf
  cases hu
  have hbase := hpre.sharedRange
  have hrB := hpre.rangeB
  have hcg : g / 256 < L.grid := by
    have := hg; simp only [Launch.threads, hpre.block] at this; omega
  have hg32 : g < 2 ^ 32 := lt_of_lt_of_le hg hpre.threads32
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr
      ⟨by simp [next, readVal, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok w =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    cases ha : Assumption.readEReal .f32 acc with
    | none => exact absurd ha (by rw [hacc]; simp)
    | some ea =>
      cases ea with
      | error f => exact absurd ha (by rw [hacc]; simp)
      | ok xr =>
        have hxr : xr = sm := Except.ok.inj (Option.some.inj (ha.symm.trans hacc))
        rw [hxr] at ha
        cases hb : Assumption.readEReal .f32 w with
        | none =>
          obtain ⟨f, hf'⟩ :=
            out_fadd_dead (i := i) (acc := acc) (sm := sm) h (w := w) (by
              intro ⟨x', y', r, h1, h2, h3⟩; rw [hb] at h2; cases h2)
          exact .inr ⟨by simp [next, readVal, hv, hb],
            Machine.dead_of_ub (f := f) (by simpa [load1] using hf')⟩
        | some eb =>
          cases eb with
          | error f =>
            obtain ⟨f, hf'⟩ :=
              out_fadd_dead (i := i) (acc := acc) (sm := sm) h (w := w) (by
                intro ⟨x', y', r, h1, h2, h3⟩; rw [hb] at h2; cases h2)
            exact .inr ⟨by simp [next, readVal, hv, hb], Machine.dead_of_ub (f := f) (by
              simpa [load1] using hf')⟩
          | ok y =>
            cases hr : Assumption.addEReal sm y with
            | none =>
              obtain ⟨f, hf'⟩ :=
                out_fadd_dead (i := i) (acc := acc) (sm := sm) h (w := w) (by
                  intro ⟨x', y', r, h1, h2, h3⟩
                  rw [ha] at h1; cases h1
                  rw [hb] at h2; cases h2
                  rw [hr] at h3; cases h3)
              exact .inr ⟨by simp [next, readVal, hv, hb, hr], Machine.dead_of_ub (f := f) (by
                simpa [load1] using hf')⟩
            | some r =>
              have hout := out_fadd (i := i) (acc := acc) (sm := sm) h ha hb hr
              have hframe : ∀ r' : Nat, r' ∉ [12, 15] →
                  (PTX.next (setReg (load1 t w) 15 (Assumption.erealValue .f32 r))).regs r' =
                    t.regs r' := by
                intro r' hr'
                simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
                simp [PTX.next, load1, setReg, Function.update_of_ne hr'.1,
                  Function.update_of_ne hr'.2]
              have h23 : At (PTX.next (setReg (load1 t w) 15 (Assumption.erealValue .f32 r)))
                  (Flow.load_1 + 2)
                  (factsAt A B L g (Flow.load_1 + 2) ⟨.sum, v, i,
                    Assumption.erealValue .f32 r, r⟩) := by
                refine ⟨by simp only [PTX.next, load1, setReg, h.1]; rfl, rfl, rfl,
                  by simpa [PTX.next, load1, setReg] using h.2.2.2.1, ?_⟩
                frame_fp h.2.2.2.2, hframe

                exact ⟨by simp only [PTX.next, load1, setReg, Function.update_self]; rfl, trivial⟩
              obtain ⟨t25, hr25, h25⟩ : ∃ t', run kernel Prod L g 3
                  (PTX.next (setReg (load1 t w) 15 (Assumption.erealValue .f32 r))) =
                    some t' ∧
                  At t' Flow.bra_25 (factsAt A B L g Flow.bra_25 ⟨.sum, v, i + 1,
                    Assumption.erealValue .f32 r, r⟩) := by
                seg_fp h23 using
                  bs_values
                  all_goals seg_close
              obtain ⟨u1, hr1, hu1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g)
                Flow.code_25 (decide (i + 1 ≠ 256)) h25 (reg_of h25 (by table_decide))
                (prod_localRule_bra L g _ _ _)
              have hl : Relation.ReflTransGen (Tau kernel Prod L g) (load1 t w) u1 :=
                .head hout (run_rtg (run_comp hr25 hr1))
              by_cases hlt : i + 1 < 256
              · have hd : decide (i + 1 ≠ 256) = true := by simp; omega
                rw [hd] at hu1
                simp only [↓reduceIte] at hu1
                exact .inl ⟨⟨.sum, v, i + 1, Assumption.erealValue .f32 r, r⟩, u1,
                  by
                    simp only [next, readVal, hv, hb, hr, accOf]
                    simp [hlt], hl,
                  At.mono hu1 (Flow.holds_factsFrom_mono hu1.2.2.2.2 (by table_decide)),
                  ⟨by simp, fun _ => ⟨hlt, readEReal_erealValue r⟩, by simp⟩⟩
              · have hd : decide (i + 1 ≠ 256) = false := by simp; omega
                rw [hd] at hu1
                simp only [Bool.false_eq_true, ↓reduceIte] at hu1
                have h26 : At u1 (Flow.bra_25 + 1)
                    (factsAt A B L g (Flow.bra_25 + 1) ⟨.out, v, i + 1,
                      Assumption.erealValue .f32 r, r⟩) :=
                  At.mono hu1 (Flow.holds_factsFrom_mono hu1.2.2.2.2 (by table_decide))
                obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3 u1 = some t' ∧
                    At t' Site.out.pc (facts A B L g ⟨.out, v, i + 1,
                      Assumption.erealValue .f32 r, r⟩) := by
                  seg_fp h26 using
                    bs_values
                    all_goals seg_close
                exact .inl ⟨⟨.out, v, i + 1, Assumption.erealValue .f32 r, r⟩, t',
                  by
                    simp only [next, readVal, hv, hb, hr, accOf]
                    simp [hlt], hl.trans (run_rtg hr'), ht',
                  ⟨by simp, by simp, fun _ => ⟨rfl, show i + 1 = 256 by omega⟩⟩⟩

/-- The output store reaches the exit. -/
theorem step_out {d : D} {t u : TState} {e : Event} {ins : Instr} (hs : d.site = .out)
    (h : At t d.site.pc (facts A B L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont A B L g d e u := by
  obtain ⟨s, v, i, acc, sm⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_1)
  obtain ⟨a, bs, rfl, rfl⟩ := fires_st rfl hf
  refine .inl ⟨⟨.exit, v, i, acc, sm⟩, _, by simp [next], .refl, ?_, ⟨by simp, by simp, by simp⟩⟩
  refine ⟨by simp [afterStore, h.1]; rfl, by simp [afterStore], by simpa [afterStore] using h.2.2.1,
    by simpa [afterStore] using h.2.2.2.1, ?_⟩
  have hregs : (afterStore t [.reg 15]).regs = t.regs := by unfold afterStore; split <;> rfl
  rw [hregs]
  exact Flow.holds_factsFrom_mono (live := Flow.live Site.out.pc)
    (live' := Flow.live Site.exit.pc) h.2.2.2.2 (by table_decide)

end
end PTX.Kernels.BlockSum.Proof
