-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Spec
public import Kernels.RowSum.Assumptions
public import Kernels.RowSum.Flow.Sites
public import Kernels.RowSum.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.Local
public import Lemmas.Flow.Final
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.FloatOp
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.Widen

@[expose] public section

/-! # `row_sum`: the site machine of a thread

A thread whose row is out of range exits. Another thread loads the `K` elements of its row in
turn, adding each to the accumulator, then stores the sum and exits. The states are the event
instructions (`Site`); an abstract state also holds the iteration counter `i` and the
accumulator value `a`. The register facts at each site are the generated live registers valued by
one table (`values`). -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

/-- The event instructions of a thread. -/
inductive Site where
  | load | store | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .load => Flow.load_0 | .store => Flow.store_0 | .exit => Flow.exit_0

/-- The `ld.global.b32 %r11, [%rd23]` of the load site. -/
abbrev ldAcc : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .b 32,
    addr := { base := .reg 23 64 }, dsts := [some 11] }

/-- The `st.global.b32 [%rd22], %r13` of the store site. -/
abbrev stAcc : MemAccess :=
  { kind := .store, space := some .global, sem := .weak, elem := .int .b 32,
    addr := { base := .reg 22 64 }, srcs := [.reg 13] }

/-- An abstract state: the site, the number `i` of elements added, and the accumulator. -/
structure ThreadD where
  site : Site
  i : Nat
  a : Value

/-- `%r8` after `i` increments of `-K`, modulo `2^32`. -/
def cnt (K i : Nat) : Nat := (4294967296 + i - K) % 4294967296

/-- The value of every register a thread uses, at an abstract state. -/
def values (A B M K g : Nat) (d : ThreadD) : List (Nat × Value) :=
  [(1, .pred (decide (M ≤ g))), (2, .pred (decide (K = 0))), (3, .pred (decide (d.i ≠ K))), (5, b32
    g), (6, b32 K),
   (12, b32 (cnt K d.i)), (13, d.a), (15, b64 A), (16, b64 B), (22, b64 (B + 4 * g)),
   (23, b64 (A + 4 * (K * g + d.i)))]

def valueOf (A B M K g : Nat) (d : ThreadD) (r : Nat) : Value :=
  ((values A B M K g d).lookup r).getD (b32 0)

def factsAt (A B M K g pc : Nat) (d : ThreadD) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf A B M K g d)

abbrev facts (A B M K g : Nat) (d : ThreadD) : List (Nat × Value) :=
  factsAt A B M K g d.site.pc d

/-! ### The reading of an accumulator

The loop's only floating instruction, `add.f32 %r9, %r9, %r7`, is decoded with `rnd := none`
(`Flow.code_20`), and `FloatInstr.arith` starts from `f.rnd.map FloatRound.mode`: the Core rule of
the instruction is `noRule` for *every* operand, so the ideal-real assumption is its only rule.
That rule reads each operand as an extended real (`Assumption.readEReal`): a payload is its
number and an infinity is `⊤` or `⊥`, so an infinite element takes the step and the accumulator
becomes an infinity (`Assumption.erealValue`). A NaN has no reading there and `∞ - ∞` no sum
(`Assumption.addEReal`), which *declines* the rule; with no Core rule behind it, a declined add
is a fault — the manual's NaN result is never written. -/

/-- A finite number as a value of format `f32` reads back as itself. -/
theorem readEReal_erealValue_coe (x : ℝ) :
    Assumption.readEReal .f32 (Assumption.erealValue .f32 (x : EReal)) = some (.ok (x : EReal)) :=
  by
  have h : Assumption.erealValue .f32 (x : EReal) = .float .f32 x := by
    unfold Assumption.erealValue
    rw [ite_eq_right (EReal.coe_ne_top x), ite_eq_right (EReal.coe_ne_bot x)]
    simp
  rw [h]
  simp [Assumption.readEReal, pure, Except.pure]

/-- `+∞` as the bits of that infinity reads back as `⊤`. -/
theorem readEReal_erealValue_top :
    Assumption.readEReal .f32 (Assumption.erealValue .f32 ⊤) = some (.ok ⊤) := by
  have h : Assumption.erealValue .f32 ⊤ =
      .bits 32 (BitVec.ofNat 64 (FloatFmt.f32.layout.infPattern false)) := by
    unfold Assumption.erealValue
    rw [ite_eq_left rfl]
    rfl
  rw [h]
  have hd : FloatFmt.f32.layout.decode (FloatFmt.f32.layout.infPattern false) =
      some (.inf false) :=
    FloatFmt.decode_infPattern .f32 (by decide) false
  have hc : classify .f32 (.bits 32 (BitVec.ofNat 64
      (FloatFmt.f32.layout.infPattern false))) = .ok (.inf false) := by
    simpa [FloatFmt.bytes] using
      classify_bits (fmt := .f32) (n := FloatFmt.f32.layout.infPattern false) (x := .inf false)
        (by decide) hd
  simp only [Assumption.readEReal]
  rw [hc]
  rfl

/-- `-∞` as the bits of that infinity reads back as `⊥`. -/
theorem readEReal_erealValue_bot :
    Assumption.readEReal .f32 (Assumption.erealValue .f32 ⊥) = some (.ok ⊥) := by
  have h : Assumption.erealValue .f32 ⊥ =
      .bits 32 (BitVec.ofNat 64 (FloatFmt.f32.layout.infPattern true)) := by
    unfold Assumption.erealValue
    rw [ite_eq_right (by simp), ite_eq_left rfl]
    rfl
  rw [h]
  have hd : FloatFmt.f32.layout.decode (FloatFmt.f32.layout.infPattern true) = some (.inf true) :=
    FloatFmt.decode_infPattern .f32 (by decide) true
  have hc : classify .f32 (.bits 32 (BitVec.ofNat 64
      (FloatFmt.f32.layout.infPattern true))) = .ok (.inf true) := by
    simpa [FloatFmt.bytes] using
      classify_bits (fmt := .f32) (n := FloatFmt.f32.layout.infPattern true) (x := .inf true)
        (by decide) hd
  simp only [Assumption.readEReal]
  rw [hc]
  rfl

/-- **The value of an extended real reads back as that extended real**: the accumulator an ideal
step writes is one the next ideal step reads. -/
theorem readEReal_erealValue (x : EReal) :
    Assumption.readEReal .f32 (Assumption.erealValue .f32 x) = some (.ok x) := by
  rcases x with _ | _ | x
  · exact readEReal_erealValue_bot
  · exact readEReal_erealValue_top
  · exact readEReal_erealValue_coe x

/-- The accumulator after the first element: four bytes that read as an extended real, so that the
ideal add takes the step. The sum of a row is a number, or an infinity once an element is
infinite; a NaN never reaches a state, since the add that would write one is a fault. -/
def AccOk (a : Value) : Prop :=
  a.bytes = 4 ∧ ∃ r : EReal, Assumption.readEReal .f32 a = some (.ok r)

/-- The accumulator after the add of the read word `v`, when the ideal rule takes the step. -/
def addAcc (a v : Value) : Option Value :=
  match Assumption.readEReal .f32 a, Assumption.readEReal .f32 v with
  | some (.ok x), some (.ok y) => (Assumption.addEReal x y).map (Assumption.erealValue .f32)
  | _, _ => none

/-- The successor after event `e`. The load adds the word it read as the ideal rule reads it — a
number, or an infinity that makes the sum infinite — and stores after the last element. A word
whose bytes do not rebuild to a value, and an add the ideal rule declines (a NaN operand, or
`∞ - ∞`), fault the thread; the exit ends it. -/
def next (K : Nat) (d : ThreadD) (e : Event) : Option (Option ThreadD) :=
  match d.site with
  | .load => match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => (addAcc d.a v).map fun a' =>
        some ⟨if d.i + 1 < K then .load else .store, d.i + 1, a'⟩
      | .error _ => none
    | _ => none
  | .store => some (some ⟨.exit, d.i, d.a⟩)
  | .exit => none

/-- The facts every state of the machine keeps. -/
def Inv (M K g : Nat) (d : ThreadD) : Prop :=
  AccOk d.a ∧ (d.site = .load → d.i < K ∧ g < M) ∧ (d.site = .store → d.i = K ∧ g < M)

/-- The code machine of thread `g`. -/
def code (L : Launch) (A B M K g : Nat) : Code kernel Prod L g where
  D := ThreadD
  init := if M ≤ g then ⟨.exit, 0, b32 0⟩ else if K = 0 then ⟨.store, 0, b32 0⟩
    else ⟨.load, 0, b32 0⟩
  pc := fun d => d.site.pc
  facts := facts A B M K g
  inv := Inv M K g
  next := next K

macro "rs_values" : tactic =>
  `(tactic| simp only [valueOf, values, List.lookup_cons, Nat.reduceBEq, Option.getD_some,
    PTX.Flow.lookupLit, Option.getD_none])

/-- Evaluate a segment of the thread from `h` and close the facts of its end state. -/
syntax "rs_seg" term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rs_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      seg_fp $h using
        try rs_values
        all_goals seg_close [$extra,*]))

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} {g : Nat}

def ps (A B M K : Nat) : List (String × Nat) :=
  [("row_sum_param_0", A), ("row_sum_param_1", B), ("row_sum_param_2", M), ("row_sum_param_3", K)]

theorem params (hpre : Pre L A B M K x mem0) : explicitParams L (ps A B M K) = L :=
  explicitParams_eq (by
    intro p v hm
    simp only [ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hpre.param0, hpre.param1, hpre.param2, hpre.param3])

theorem row_le (hgM : g < M) {i : Nat} (hi : i ≤ K) : K * g + i ≤ M * K := by
  have := Nat.mul_le_mul_left K (show g + 1 ≤ M by omega)
  rw [Nat.mul_succ] at this; rw [Nat.mul_comm M]; omega

/-- The start state of the code: before the branch past the rows. -/
def d0 : ThreadD := ⟨.load, 0, b32 0⟩

set_option maxHeartbeats 4000000 in
/-- The opening code reaches the first event: the exit past the last row, else the store of an
empty row, else the first load. -/
theorem start (hpre : Pre L A B M K x mem0) (hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel Prod L g) {} t ∧
      At t (code L A B M K g).init.site.pc (facts A B M K g (code L A B M K g).init) := by
  have hpre' := hpre
  obtain ⟨_, _, _, _, hM32, hK32, hT, hbl, _, _, hrA, hrB, _, _, _⟩ := hpre'
  have hpL := params hpre
  have hone := hpre.oneDimLaunch
  have htid := Launch.oneDim_tidOf hone.1 g
  have hcta := Launch.oneDim_ctaidOf hone.1 (g / L.block)
  have hsum : g / L.block * L.block + g % L.block = g := Nat.div_add_mod' g L.block
  have hnx : L.ntid.x = L.block := by rw [hone.1.1]
  have hg32 : g < 2 ^ 32 := by omega
  have hgm : g % 2 ^ 32 = g := Nat.mod_eq_of_lt hg32
  have hbm : L.block % 2 ^ 32 = L.block := Nat.mod_eq_of_lt hbl
  have hcm : g / L.block % 2 ^ 32 = g / L.block :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self g L.block) hg32)
  have htm : g % L.block % 2 ^ 32 = g % L.block :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le g L.block) hg32)
  have hpm : g / L.block * L.block % 2 ^ 32 = g / L.block * L.block :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg32)
  have hsm : (g / L.block * L.block + g % L.block) % 2 ^ 32 = g := by rw [hsum, hgm]
  obtain ⟨t9, hr9, h9⟩ : ∃ t, run kernel Prod (explicitParams L (ps A B M K)) g 9 {} = some t ∧
      At t 9 (factsAt A B M K g 9 d0) := by
    -- The geometry facts (`htid`, `hcta`, `hnx`) rewrite `%ctaid`/`%ntid`/`%tid`,
    -- `truncBits_idem` and `trunc_mad` collapse the product's nested truncations to
    -- `(cta * ntid + tid) % 2 ^ 32`, and the `…m` facts are its parts' 32-bit truncations,
    -- which `omega` cannot derive (the product is nonlinear).
    seg_fp at_init using
      try rs_values
      all_goals seg_close
        [hpL, sregValue, truncBits_idem, trunc_mad, Nat.div_add_mod', Dim3.get, hsum, hgm, hbm,
          hcm, htm, hpm, hsm, hnx, htid, hcta, hg, hT, hbl]
  have hp : At t9 9 [(1, .pred (decide (M ≤ g))), (5, b32 g), (6, b32 K), (15, b64 A), (16, b64 B)]
    :=
    h9
  by_cases hM : M ≤ g
  · simp only [decide_eq_true hM] at hp
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod (explicitParams L (ps A B M K)) g 1 t9 =
        some t' ∧
        At t' 29 (factsAt A B M K g 29 ⟨.exit, 0, b32 0⟩) := by
      rs_seg hp
    rw [params hpre] at hr9 hr'
    exact ⟨t', run_rtg (run_comp hr9 hr'), by simp only [code, hM, ↓reduceIte]; exact ht'⟩
  · simp only [decide_eq_false hM] at hp
    obtain ⟨t12, hr12, h12⟩ : ∃ t', run kernel Prod (explicitParams L (ps A B M K)) g 3 t9 = some t'
      ∧
        At t' 12 (factsAt A B M K g 12 d0) := by
      rs_seg hp
    rw [params hpre] at hr9 hr12
    have hq : At t12 12 [(2, .pred (decide (K = 0))), (5, b32 g), (6, b32 K), (13, b32 0),
        (15, b64 A), (16, b64 B)] := by
      at_select h12
    by_cases hK0 : K = 0
    · simp only [decide_eq_true hK0] at hq
      obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4 t12 = some t' ∧
          At t' 28 (factsAt A B M K g 28 ⟨.store, 0, b32 0⟩) := by
        rs_seg hq
      exact
        ⟨t', run_rtg (run_comp hr9 (run_comp hr12 hr')),
          by simp only [code, hM, hK0, ↓reduceIte]; exact ht'⟩
    · simp only [decide_eq_false hK0] at hq
      obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 7 t12 = some t' ∧
          At t' 19 (factsAt A B M K g 19 ⟨.load, 0, b32 0⟩) := by
        rs_seg hq [cnt, truncBits_ofNat hK32 (by decide), truncBits_ofNat hg32 (by decide),
          toNat_ofNat_lt (show K < 2 ^ 64 by omega), toNat_ofNat_lt (show g < 2 ^ 64 by omega)]
      exact
        ⟨t', run_rtg (run_comp hr9 (run_comp hr12 hr')),
          by simp only [code, hM, hK0, ↓reduceIte]; exact ht'⟩

/-- The instruction at each site performs an event and has no guard. -/
theorem site_ok (d : ThreadD) : ∃ ins, kernel.code[d.site.pc]? = some ins ∧
    ins.op.isLocal = false ∧ Code.GuardTrue (facts A B M K g d) ins.guard := by
  obtain ⟨s, i, a⟩ := d
  cases s with
  | load => exact ⟨_, Flow.code_load_0, rfl, trivial⟩
  | store => exact ⟨_, Flow.code_store_0, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

theorem reg_at {d : ThreadD} {t : TState} {r : Nat} (h : At t d.site.pc (facts A B M K g d))
    (hl : r ∈ Flow.live d.site.pc) : t.regs r = some (valueOf A B M K g d r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- The state after the read of an element returned the scalar `v`. -/
def t20 (t : TState) (v : Value) : TState :=
  { setReg t 11 v with pc := t.pc + 1, sub := 0, acc := [] }

/-- The accumulator register `%r9` of the load site holds the abstract accumulator. -/
theorem reg13_t20 {i : Nat} {a : Value} {t : TState} (v : Value)
    (h : At t Site.load.pc (facts A B M K g ⟨.load, i, a⟩)) :
    (t20 t v).regs 13 = some a := by
  have := reg_at (d := ⟨.load, i, a⟩) h (r := 13) (by table_decide)
  simp only [t20, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
  rw [this]
  rs_values

/-- The register `%r7` of the load site holds the word the load returned. -/
theorem reg11_t20 (t : TState) (v : Value) : (t20 t v).regs 11 = some v := by
  simp [t20, setReg]

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

/-- The number of bytes of a value of an extended real. -/
theorem erealValue_bytes (r : EReal) : (Assumption.erealValue .f32 r).bytes = 4 := by
  unfold Assumption.erealValue
  repeat' split
  all_goals rfl

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
theorem exec_fadd_ereal {i : Nat} {a v : Value} {t : TState} {x y r : EReal}
    (h : At t Site.load.pc (facts A B M K g ⟨.load, i, a⟩))
    (ha : Assumption.readEReal .f32 a = some (.ok x))
    (hv : Assumption.readEReal .f32 v = some (.ok y))
    (hr : Assumption.addEReal x y = some r) :
    execLocalA Prod L g (t20 t v) (fadd .f32 13 (.reg 13) (.reg 11)) =
      .ok (PTX.next (setReg (t20 t v) 13 (Assumption.erealValue .f32 r))) := by
  have hr9 := reg13_t20 (A := A) (B := B) (M := M) (K := K) (g := g) v h
  have hr7 := reg11_t20 t v
  have hx : Assumption.readERealOpnd (t20 t v) .f32 (.reg 13) = some (.ok x) := by
    rw [readERealOpnd_reg hr9]; exact ha
  have hy : Assumption.readERealOpnd (t20 t v) .f32 (.reg 11) = some (.ok y) := by
    rw [readERealOpnd_reg hr7]; exact hv
  simp only [execLocalA, execLocalRule, execLocal, Assumptions.idealAdd, Assumption.idealReal,
    List.findSome?]
  simp only [Assumption.execIdealFloat, hx, hy, Assumption.bindRead, hr, pure, Except.pure]
  rfl

/-- The loop's add at the load site: on its ideal step it writes the sum. -/
theorem out_fadd {i : Nat} {a v : Value} {t : TState} {x y r : EReal}
    (h : At t Site.load.pc (facts A B M K g ⟨.load, i, a⟩))
    (ha : Assumption.readEReal .f32 a = some (.ok x))
    (hv : Assumption.readEReal .f32 v = some (.ok y))
    (hr : Assumption.addEReal x y = some r) :
    out kernel Prod L g (t20 t v) =
      .tau (PTX.next (setReg (t20 t v) 13 (Assumption.erealValue .f32 r))) :=
  out_tau h.2.2.2.1 (by simp only [t20, h.1]; exact Flow.code_20) rfl rfl
    (exec_fadd_ereal h ha hv hr)

/-- The loop's add at the load site where the ideal rule does not take the step kills the thread:
a NaN operand has no reading, `∞ - ∞` no sum, and a value of another width is a fault the ideal
rule reads as one; the Core rule is `noRule` behind a declined one. -/
theorem out_fadd_dead {i : Nat} {a v : Value} {t : TState}
    (h : At t Site.load.pc (facts A B M K g ⟨.load, i, a⟩))
    (hbad : ¬ ∃ x y r : EReal, Assumption.readEReal .f32 a = some (.ok x) ∧
      Assumption.readEReal .f32 v = some (.ok y) ∧ Assumption.addEReal x y = some r) :
    ∃ f, out kernel Prod L g (t20 t v) = .ev (.ub f) := by
  have hr9 := reg13_t20 (A := A) (B := B) (M := M) (K := K) (g := g) v h
  have hr7 := reg11_t20 t v
  have hc : kernel.code[(t20 t v).pc]? = some ⟨none, fadd .f32 13 (.reg 13) (.reg 11)⟩ := by
    simp only [t20, h.1]; exact Flow.code_20
  have hf20 : (t20 t v).fault = none := h.2.2.2.1
  have hI : Assumption.IdealFor Prod (.add .f32) := by
    simp only [Assumptions.idealAdd]
    exact Assumption.idealFor_head (by simp)
  cases ha : Assumption.readEReal .f32 a with
  | none =>
    have hn := idealFloat_none_left (L := L) (g := g) (d := 13) (b := 11) hr9 ha
    obtain ⟨f, hfl⟩ := exec_fadd_decline (L := L) (g := g) hr9 hr7 hn
    exact ⟨f, out_ub hf20 hc rfl rfl hfl⟩
  | some ea =>
    cases ea with
    | error f =>
      obtain ⟨f', hfl⟩ := exec_fadd_error (A := Prod) hI hr9 hr7 (Or.inl ⟨f, ha⟩)
      exact ⟨f', out_ub hf20 hc rfl rfl hfl⟩
    | ok x =>
      cases hb : Assumption.readEReal .f32 v with
      | none =>
        have hn := idealFloat_none_right (L := L) (g := g) (d := 13) (b := 11) hr9 hr7 ha hb
        obtain ⟨f, hfl⟩ := exec_fadd_decline (L := L) (g := g) hr9 hr7 hn
        exact ⟨f, out_ub hf20 hc rfl rfl hfl⟩
      | some eb =>
        cases eb with
        | error f =>
          obtain ⟨f', hfl⟩ := exec_fadd_error (A := Prod) hI hr9 hr7 (Or.inr ⟨⟨x, ha⟩, f, hb⟩)
          exact ⟨f', out_ub hf20 hc rfl rfl hfl⟩
        | ok y =>
          cases hr0 : Assumption.addEReal x y with
          | some r => exact absurd ⟨x, y, r, ha, hb, hr0⟩ hbad
          | none =>
            have hn := idealFloat_none_sum (L := L) (g := g) (d := 13) (b := 11) hr9 hr7 ha hb hr0
            obtain ⟨f, hfl⟩ := exec_fadd_decline (L := L) (g := g) hr9 hr7 hn
            exact ⟨f, out_ub hf20 hc rfl rfl hfl⟩

/-- What a step of the machine owes. -/
abbrev Step (L : Launch) (A B M K g : Nat) (d : ThreadD) (u : TState) (e : Event) : Prop :=
  ((code L A B M K g).next d e = some none ∨ ∃ d' t', (code L A B M K g).next d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ (code L A B M K g).Good (some d') t') ∨
    ((code L A B M K g).next d e = none ∧
      Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u)

/-- From the state after the loop's branch the machine reaches the successor's facts. -/
theorem good_of_24 {i : Nat} {a' : Value} {s0 t24 : TState} (hacc : AccOk a') (hi : i < K)
    (hgM : g < M) (hg32 : g < 2 ^ 32) (hstep : Relation.ReflTransGen (Tau kernel Prod L g) s0 t24)
    (h24 : At t24 24 (factsAt A B M K g 24 ⟨.load, i + 1, a'⟩)) :
    ∃ t', Relation.ReflTransGen (Tau kernel Prod L g) s0 t' ∧
      (code L A B M K g).Good (some ⟨if i + 1 < K then .load else .store, i + 1, a'⟩) t' := by
  have hq : At t24 24 [(3, .pred (decide (i + 1 ≠ K))), (5, b32 g), (12, b32 (cnt K (i + 1))),
      (13, a'), (16, b64 B), (23, b64 (A + 4 * (K * g + (i + 1))))] := by
    at_select h24
  by_cases hlt : i + 1 < K
  · simp only [decide_eq_true (show i + 1 ≠ K by omega)] at hq
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1 t24 = some t' ∧
        At t' 19 (factsAt A B M K g 19 ⟨.load, i + 1, a'⟩) := by
      rs_seg hq
    refine ⟨t', hstep.trans (run_rtg hr'), ?_, ?_⟩
    · simp only [code, hlt, ↓reduceIte]; exact ht'
    · exact ⟨hacc, fun _ => ⟨hlt, hgM⟩, fun h => by simp [hlt] at h⟩
  · have hiK : i + 1 = K := by omega
    simp only [hiK, ne_eq, not_true_eq_false, decide_false] at hq
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4 t24 = some t' ∧
        At t' 28 (factsAt A B M K g 28 ⟨.store, i + 1, a'⟩) := by
      rs_seg hq [truncBits_ofNat hg32 (by decide), toNat_ofNat_lt (show g < 2 ^ 64 by omega)]
    refine ⟨t', hstep.trans (run_rtg hr'), ?_, ?_⟩
    · simp only [code, hlt, ↓reduceIte]; exact ht'
    · exact ⟨hacc, fun h => by simp [hlt] at h, fun _ => ⟨hiK, hgM⟩⟩

set_option maxHeartbeats 4000000 in
/-- The read of an element adds it to the accumulator and continues the loop, or stores the sum
after the last element. -/
theorem step_load (hpre : Pre L A B M K x mem0) {i : Nat} {a : Value} {t u : TState} {e : Event}
    (hinv : Inv M K g ⟨.load, i, a⟩) (h : At t Site.load.pc (facts A B M K g ⟨.load, i, a⟩))
    (hf : Fires Site.load.pc (eventTmpl Prod L g t (.mem ldAcc)) e (some u)) :
    Step L A B M K g ⟨.load, i, a⟩ u e := by
  have hpre' := hpre
  obtain ⟨_, _, _, _, hM32, hK32, hT, hbl, _, _, hrA, hrB, _, _, _⟩ := hpre'
  obtain ⟨⟨hab, r, hr⟩, hl, -⟩ := hinv
  obtain ⟨hi, hgM⟩ : i < K ∧ g < M := hl rfl
  have hg32 : g < 2 ^ 32 := by omega
  obtain ⟨acc, bs, rfl, rfl⟩ := fires_load rfl rfl hf
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [code, next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    rw [show MemAccess.regs _ = [11] from rfl, afterLoad_ok h.2.1 h.2.2.1 hv]
    cases ha : Assumption.readEReal .f32 a with
    | none =>
      obtain ⟨f, hf'⟩ := out_fadd_dead (v := v) h (by
        intro ⟨x, y, r', h1, h2, h3⟩; rw [ha] at h1; cases h1)
      exact .inr ⟨by simp [code, next, hv, addAcc, ha], Machine.dead_of_ub hf'⟩
    | some ea =>
      cases ea with
      | error f =>
        obtain ⟨f, hf'⟩ := out_fadd_dead (v := v) h (by
          intro ⟨x, y, r', h1, h2, h3⟩; rw [ha] at h1; cases h1)
        exact .inr ⟨by simp [code, next, hv, addAcc, ha], Machine.dead_of_ub hf'⟩
      | ok x =>
        cases hb : Assumption.readEReal .f32 v with
        | none =>
          obtain ⟨f, hf'⟩ := out_fadd_dead (v := v) h (by
            intro ⟨x', y, r', h1, h2, h3⟩; rw [hb] at h2; cases h2)
          exact .inr ⟨by simp [code, next, hv, addAcc, ha, hb], Machine.dead_of_ub hf'⟩
        | some eb =>
          cases eb with
          | error f =>
            obtain ⟨f, hf'⟩ := out_fadd_dead (v := v) h (by
              intro ⟨x', y, r', h1, h2, h3⟩; rw [hb] at h2; cases h2)
            exact .inr ⟨by simp [code, next, hv, addAcc, ha, hb], Machine.dead_of_ub hf'⟩
          | ok y =>
            cases hr0 : Assumption.addEReal x y with
            | none =>
              obtain ⟨f, hf'⟩ := out_fadd_dead (v := v) h (by
                intro ⟨x', y', r', h1, h2, h3⟩
                rw [ha] at h1; cases h1
                rw [hb] at h2; cases h2
                rw [hr0] at h3; cases h3)
              exact .inr ⟨by simp [code, next, hv, addAcc, ha, hb, hr0], Machine.dead_of_ub hf'⟩
            | some r' =>
              have hout := out_fadd (L := L) h ha hb hr0
              have hn : (code L A B M K g).next ⟨.load, i, a⟩ ⟨Site.load.pc, .rd acc bs⟩ =
                  some (some ⟨if i + 1 < K then .load else .store, i + 1,
                    Assumption.erealValue .f32 r'⟩) := by
                simp [code, next, hv, addAcc, ha, hb, hr0]
              have hacc : AccOk (Assumption.erealValue .f32 r') :=
                ⟨erealValue_bytes r', r', readEReal_erealValue r'⟩
              have h21 : At (PTX.next (setReg (t20 t v) 13 (Assumption.erealValue .f32 r'))) 21
                  (factsAt A B M K g 21 ⟨.load, i, Assumption.erealValue .f32 r'⟩) := by
                refine ⟨by simp [PTX.next, setReg, t20, h.1]; rfl, by simp [PTX.next, setReg, t20],
                  by simp [PTX.next, setReg, t20],
                  by simpa [PTX.next, setReg, t20] using h.2.2.2.1, ?_⟩
                have hfr : ∀ r, r ∉ [11, 13] →
                    (PTX.next (setReg (t20 t v) 13 (Assumption.erealValue .f32 r'))).regs r =
                      t.regs r := by
                  intro r hr
                  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
                  simp [PTX.next, setReg, t20, hr]
                frame_fp h.2.2.2.2, hfr
                refine ⟨?_, trivial⟩
                simp only [PTX.next, setReg, t20, Function.update_self]
                rs_values
              obtain ⟨t24, hr24, h24⟩ : ∃ t', run kernel Prod L g 3
                  (PTX.next (setReg (t20 t v) 13 (Assumption.erealValue .f32 r'))) = some t' ∧
                  At t' 24 (factsAt A B M K g 24 ⟨.load, i + 1,
                    Assumption.erealValue .f32 r'⟩) := by
                rs_seg h21 [cnt]
              obtain ⟨t', h1, h2⟩ := good_of_24 (A := A) (B := B) (M := M) (K := K) (L := L)
                (g := g) (i := i) (a' := Assumption.erealValue .f32 r') hacc hi hgM hg32
                (.head hout (run_rtg hr24)) h24
              exact .inl (.inr ⟨_, t', hn, h1, h2⟩)

theorem accOk_z0 : AccOk (b32 0) := ⟨rfl, 0, readEReal_of_valFloat valFloat_z0⟩

theorem accOk_fl (s : ℝ) : AccOk (fl s) := ⟨rfl, s, rfl⟩

/-- The store advances to the `ret`. -/
theorem step_store {i : Nat} {a : Value} {t u : TState} {e : Event}
    (hinv : Inv M K g ⟨.store, i, a⟩) (h : At t Site.store.pc (facts A B M K g ⟨.store, i, a⟩))
    (hf : Fires Site.store.pc (eventTmpl Prod L g t (.mem stAcc)) e (some u)) :
    Step L A B M K g ⟨.store, i, a⟩ u e := by
  obtain ⟨acc, bs, rfl, rfl⟩ := fires_st rfl hf
  have hl : Flow.live Site.exit.pc = [] := by decide +kernel
  refine .inl (.inr ⟨⟨.exit, i, a⟩, _, rfl, .refl, ⟨?_, by simp [afterStore, h.2.1]; rfl,
    by show (afterStore t [.reg 13]).acc = []; simpa [afterStore, h.2.1] using h.2.2.1, by simpa
      [afterStore, h.2.1] using h.2.2.2.1, ?_⟩,
    ⟨hinv.1, fun h => by simp at h, fun h => by simp at h⟩⟩)
  · simp [afterStore, h.2.1, h.1]
    rfl
  · show Holds _ (factsAt A B M K g Site.exit.pc ⟨.exit, i, a⟩)
    simp only [factsAt, hl, Flow.factsFrom, List.map_nil]
    trivial

/-- Every site's event reaches its successor's facts. -/
theorem step (hpre : Pre L A B M K x mem0) {d : ThreadD} {t u : TState} {e : Event} {ins : Instr}
    (hinv : Inv M K g d) (h : At t d.site.pc (facts A B M K g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L A B M K g d u e := by
  obtain ⟨s, i, a⟩ := d
  cases s with
  | load =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    exact step_load hpre hinv h hf
  | store =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    exact step_store hinv h hf
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

theorem inv_init : Inv M K g (code L A B M K g).init := by
  simp only [code]
  split_ifs with h1 h2
  · exact ⟨accOk_z0, fun h => by simp at h, fun h => by simp at h⟩
  · exact ⟨accOk_z0, fun h => by simp at h, fun _ => ⟨h2.symm, by omega⟩⟩
  · exact ⟨accOk_z0, fun _ => ⟨by simp; omega, by omega⟩, fun h => by simp at h⟩

/-- Every thread of a launch satisfying the precondition is simulated by its code machine. -/
theorem sound (hpre : Pre L A B M K x mem0) (hg : g < L.threads) :
    (code L A B M K g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := start hpre hg
    exact ⟨t, hr, ht, inv_init⟩
  steps := fun d => ⟨fun _ => site_ok d, fun ins h hinv hc hf => step hpre hinv h hc hf⟩

end
end PTX.Kernels.RowSum.Proof
