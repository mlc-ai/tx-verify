-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.Combinators
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.Step.RuleStep
public import Lemmas.Isa.Rule
public import Lemmas.Flow.FloatWord
public meta import Lean

@[expose] public section

/-! # Local segments through control on symbolic values

A proof tool for the segments of site machines (`∃ n, Seg K A L g n s F b G`, the `seg` field of
`Code.Lands`). `seg_fp` evaluates a segment by kernel reduction, which stops at a conditional
branch or a `selp` whose predicate is a symbolic `Bool` (a comparison of the lane index, or of a
word the machine recorded). Nothing here is specific to a kernel.

* `seg_auto using tac` proves a segment whose control the evaluation decides: it finds the
  segment lengths by walking the code from `s` to `b` (taking both branches, passing guarded
  event instructions, stopping at unguarded ones), and closes `Seg … n …` with `tac`, the
  shortest length first.
* `seg_sym using tac` also proves a segment through such control. It walks from `s` to `b` on
  a symbolic state started from the facts `F`, and cuts the segment before each branch or `selp`
  whose predicate is not a literal, at the registers live there valued by the **walked state**
  (the terms the code computed from `F`, small closed terms evaluated; `Seg.comp_ex`), not by the
  end's table. So a branch's predicate is the code's term, and a condition the role writes in its
  transition decides it only when it is that term (up to `cheapDefEq`, then a budgeted
  `isDefEq`); a preamble whose computed terms differ from the role's table is cut once with the
  table's facts (`seg_cut`), after which the walk starts from the table's terms. At a branch it
  puts the predicate's literal value in front of the facts (`Seg.pred_ex`): the value a
  hypothesis in context decides, or both values in turn by a case split. A `selp` is one step
  from each literal value of its predicate to the destination holding `if c then x else y`. A
  successor that is an `if` is split first, so that its condition is a hypothesis. A guarded
  event instruction whose guard the walked state gives as false is a local skip and is passed; a
  guard that is no literal is decided first, as a branch's predicate is. Each piece is closed by
  `seg_auto using tac`; `tac` sees the hypotheses of the case splits. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A tensor-map prefetch as a one-step segment**: a hint with no effect on the state, given
that its register holds the generic pointer of a by-value parameter object the launch declares
(`hp`, `hok`), that no assumption gives it a rule (`hL`) and that none takes a segment there. -/
theorem Seg.prefetchTensorMap {pc w r : Nat} {gen : Bool} {name : String}
    {decl : ParamObjectDecl} {base : Nat} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .prefetchTensorMap gen w (.reg r)⟩)
    (hr : (r, .ptr w gen (.param name) 0) ∈ F) (hw : w = 32 ∨ w = 64)
    (hp : L.paramObjects name = some (decl, base))
    (hok : decl.name = name ∧ 0 < decl.bytes ∧ 0 < decl.alignment ∧ base % decl.alignment = 0 ∧
      base + decl.bytes ≤ 2 ^ w)
    (hL : ∀ t : TState, t.pc = pc →
      ∀ b ∈ A, b.localRule L g t (.prefetchTensorMap gen w (.reg r)) = none)
    (hA : Assumption.SegFreePc A pc) :
    Seg K A L g 1 pc F (pc + 1) F := by
  intro t ⟨htp, hs, ha, hf, hF⟩
  have he := exec_prefetchTensorMap (A := A) (L := L) (g := g) (t := t) (holds_mem hF hr) hw hp
    hok (hL t htp) (by rw [htp]; exact hA)
  refine ⟨next t, ?_, ⟨by simp [next, htp], hs, ha, hf, hF⟩⟩
  simp only [run, tauStep, out, htp, hf, hc, guardHolds, pure, Except.pure, ↓reduceIte, he,
    show (Op.prefetchTensorMap gen w (.reg r)).isLocal = true by rfl, Option.bind_some]

/-- Two segments that meet at a checkpoint, with their lengths existential. -/
theorem Seg.comp_ex {s q b : Nat} {F H G : List (Nat × Value)}
    (h1 : ∃ m, Seg K A L g m s F q H) (h2 : ∃ n, Seg K A L g n q H b G) :
    ∃ k, Seg K A L g k s F b G := by
  obtain ⟨m, h1⟩ := h1
  obtain ⟨n, h2⟩ := h2
  exact ⟨m + n, h1.comp h2⟩

/-- A predicate fact whose value is known to be `c'`: the segment from the facts with the literal
value in front. -/
theorem Seg.pred_ex {s b p : Nat} {c c' : Bool} {F G : List (Nat × Value)}
    (hp : (p, Value.pred c) ∈ F) (hc : c = c')
    (h : ∃ n, Seg K A L g n s ((p, .pred c') :: F) b G) : ∃ n, Seg K A L g n s F b G := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.weaken_start fun R hR => ⟨hc ▸ holds_mem hR hp, hR⟩⟩

/-- A `selp` destination restated as an `if` on the predicate, from its value when the predicate
holds. -/
theorem Seg.sel_pos {s b d w : Nat} {c : Bool} {x y : BitVec 64} {F G : List (Nat × Value)}
    (hc : c = true) (h : ∃ n, Seg K A L g n s F b ((d, .bits w x) :: G)) :
    ∃ n, Seg K A L g n s F b ((d, .bits w (if c = true then x else y)) :: G) := by
  rw [ite_eq_left hc]; exact h

/-- A `selp` destination restated as an `if` on the predicate, from its value when it fails. -/
theorem Seg.sel_neg {s b d w : Nat} {c : Bool} {x y : BitVec 64} {F G : List (Nat × Value)}
    (hc : ¬ c = true) (h : ∃ n, Seg K A L g n s F b ((d, .bits w y) :: G)) :
    ∃ n, Seg K A L g n s F b ((d, .bits w (if c = true then x else y)) :: G) := by
  rw [ite_eq_right hc]; exact h

/-- A floating `selp` destination restated as the conditional value, from its value when the
predicate holds (`sym_selp_value`). -/
theorem Seg.selv_pos {s b d : Nat} {c : Bool} {x y : Value} {F G : List (Nat × Value)}
    (hc : c = true) (h : ∃ n, Seg K A L g n s F b ((d, x) :: G)) :
    ∃ n, Seg K A L g n s F b ((d, if c = true then x else y) :: G) := by
  rw [ite_eq_left hc]; exact h

/-- A floating `selp` destination restated as the conditional value, from its value when the
predicate fails. -/
theorem Seg.selv_neg {s b d : Nat} {c : Bool} {x y : Value} {F G : List (Nat × Value)}
    (hc : ¬ c = true) (h : ∃ n, Seg K A L g n s F b ((d, y) :: G)) :
    ∃ n, Seg K A L g n s F b ((d, if c = true then x else y) :: G) := by
  rw [ite_eq_right hc]; exact h

/-- A piece whose start and end facts are restated (a case hypothesis substituted into
conditional values). -/
theorem Seg.facts_eq {s b : Nat} {F F' G G' : List (Nat × Value)} (hF : F = F') (hG : G = G')
    (h : ∃ n, Seg K A L g n s F' b G') : ∃ n, Seg K A L g n s F b G := by
  subst hF hG; exact h

/-- Fewer or restated facts at the end, with the length existential. -/
theorem Seg.weaken_end_ex {s b : Nat} {F G G' : List (Nat × Value)}
    (h : ∃ n, Seg K A L g n s F b G) (hG : ∀ R, Holds R G → Holds R G') :
    ∃ n, Seg K A L g n s F b G' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.weaken_end hG⟩

/-- A segment under an equal launch (one whose parameters are explicit, say). -/
theorem Seg.launch_ex {L' : Launch} (hL : L' = L) {s b : Nat} {F G : List (Nat × Value)}
    (h : ∃ n, Seg K A L' g n s F b G) : ∃ n, Seg K A L g n s F b G :=
  hL ▸ h

/-- The facts of a table from explicit facts, register by register. -/
theorem holds_factsFrom_of {R : Nat → Option Value} {live : List Nat} {val : Nat → Value}
    (h : AllP (fun r => R r = some (val r)) live) :
    Holds R (factsFrom live val) :=
  holds_of_pointwise (forall_mem_of_allP h)

/-- One fact from explicit facts: its register's explicit value, restated. -/
theorem holds_reg_of {R : Nat → Option Value} {E : List (Nat × Value)} {r : Nat} {v v' : Value}
    (hE : Holds R E) (hm : (r, v) ∈ E) (he : v = v') : R r = some v' :=
  he ▸ holds_mem hE hm

/-- Whether `div` of kind `k` and width `w` has a rule for the operands' bits, and its quotient's
bits then. -/
def divOk (k : IType) (w : Nat) (x y : BitVec 64) : Bool :=
  match intDiv k w x y with
  | .ok _ => true
  | .error _ => false

def divQ (k : IType) (w : Nat) (x y : BitVec 64) : BitVec 64 :=
  match intDiv k w x y with
  | .ok q => intBits w q
  | .error _ => 0

/-- No assumption gives the instruction `op` at `pc` a rule of its own. -/
def NoRuleAt (A : List Assumption) (L : Launch) (g pc : Nat) (op : Op) : Prop :=
  ∀ t : TState, t.pc = pc → ∀ a ∈ A, a.localRule L g t op = none

/-- **A `selp` into the conditional value**, as one local step: the predicate's fact, the
operands' values (any values of the type's width: payloads, written infinities, conditionals),
no assumption's rule for it and none taking a segment. -/
theorem Seg.selpV {pc d p : Nat} {ty : DType} {sat : Bool} {a b : Opnd} {c : Bool}
    {va vb : Value} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .int ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩⟩)
    (hp : (p, Value.pred c) ∈ F)
    (ha : ∀ t : TState, Holds t.regs F → readValue L g t ty.width a = .ok va)
    (hb : ∀ t : TState, Holds t.regs F → readValue L g t ty.width b = .ok vb)
    (hva : va.bytes = ty.width / 8) (hvb : vb.bytes = ty.width / 8) (hd : ∀ r ∈ F, r.1 ≠ d)
    (hL : NoRuleAt A L g pc (.int ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩))
    (hA : Assumption.SegFreePc A pc)
    (hr : IntInstr.rule ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩ = some .threadMove)
    (hvs : Op.varyingSregs (.int ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩) = []) :
    ∃ n, Seg K A L g n pc F (pc + 1) ((d, if c = true then va else vb) :: F) := by
  refine ⟨1, fun t h => ⟨_, ?_, At.set h hd⟩⟩
  have hrp := holds_mem h.2.2.2.2 hp
  have hx : execLocalA A L g t (.int ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩) =
      .ok (PTX.next (setReg t d (if c = true then va else vb))) := by
    rw [hA.exec h.1, execLocalRule_of_none (hL t h.1), execLocal_selp hr]
    cases c
    · simp [execMove, readReg, hrp, hb t h.2.2.2.2, hvb, bind, Except.bind, pure, Except.pure]
    · simp [execMove, readReg, hrp, ha t h.2.2.2.2, hva, bind, Except.bind, pure, Except.pure]
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, hx, hvs, pure,
    Except.pure]

/-- A `div` with a rule is one local step to its quotient. -/
theorem Seg.div_ok {k : IType} {w pc d a b wa wb : Nat} {x y : BitVec 64}
    {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .int ⟨.div, .int k w, false, [some d], [.reg a, .reg b]⟩⟩)
    (ha : (a, Value.bits wa x) ∈ F) (hb : (b, Value.bits wb y) ∈ F)
    (hok : divOk k w (truncBits w x) (truncBits w y) = true) (hd : ∀ r ∈ F, r.1 ≠ d)
    (hL : NoRuleAt A L g pc (.int ⟨.div, .int k w, false, [some d], [.reg a, .reg b]⟩))
    (hA : Assumption.SegFreePc A pc := by seg_free_pc)
    (hr : IntInstr.rule ⟨.div, .int k w, false, [some d], [.reg a, .reg b]⟩ = some .threadInt :=
      by rfl) :
    ∃ n, Seg K A L g n pc F (pc + 1)
      ((d, .bits w (divQ k w (truncBits w x) (truncBits w y))) :: F) := by
  refine ⟨1, fun t h => ⟨_, ?_, At.set h hd⟩⟩
  have hra := holds_mem h.2.2.2.2 ha
  have hrb := holds_mem h.2.2.2.2 hb
  unfold divOk at hok
  unfold divQ
  split at hok
  · rename_i q hq
    simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, Op.varyingSregs,
      Opnd.varying?, List.filterMap, hA.exec, execLocalRule_of_none (hL t h.1),
      execLocal_int hr, execInt, intResult, DType.width, DType.intLanes?, readReg, hra, hrb,
      readBits, hq, bind, Except.bind, pure, Except.pure]
  · cases hok

/-- Every state at `s` with facts `F` is dead: its local steps reach undefined behaviour. -/
def DeadFrom (K : Kernel) (A : List Assumption) (L : Launch) (g s : Nat)
    (F : List (Nat × Value)) : Prop :=
  ∀ u, At u s F → Machine.Dead (K := K) (A := A) (L := L) (g := g) u

/-- A segment into dead states starts at dead states. -/
theorem DeadFrom.of_seg {s q : Nat} {F H : List (Nat × Value)}
    (h : ∃ n, Seg K A L g n s F q H) (hd : DeadFrom K A L g q H) : DeadFrom K A L g s F := by
  intro u hu
  obtain ⟨n, h⟩ := h
  obtain ⟨t, hr, ht⟩ := h u hu
  obtain ⟨v, f, hv, hf⟩ := hd t ht
  exact ⟨v, f, (run_rtg hr).trans hv, hf⟩

theorem DeadFrom.pred {s p : Nat} {c c' : Bool} {F : List (Nat × Value)}
    (hp : (p, Value.pred c) ∈ F) (hc : c = c') (h : DeadFrom K A L g s ((p, .pred c') :: F)) :
    DeadFrom K A L g s F :=
  fun u hu => h u (At.mono hu ⟨hc ▸ holds_mem hu.2.2.2.2 hp, hu.2.2.2.2⟩)

/-- A local instruction whose step faults from every state with the facts kills the thread:
a floating operation on operands where no assumption gives a rule and Core has none (a NaN half
of `mul.bf16x2`, which has no rounding modifier, say). -/
theorem DeadFrom.local_error {s : Nat} {op : Op} {F : List (Nat × Value)}
    (hc : K.code[s]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ R cf, Holds R F → ∃ f, execLocalA A L g ⟨s, R, cf, 0, [], none⟩ op = .error f) :
    DeadFrom K A L g s F := by
  intro u hu
  obtain ⟨tpc, R, cf, sub, acc, fault⟩ := u
  obtain ⟨h1, h2, h3, h4, h5⟩ := hu
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4
  obtain ⟨f, hf⟩ := hex R cf h5
  exact dead_of_error (f := f) hc hl rfl hf

/-- **A cut at a step the walk cannot compute**: `s`'s instruction is local and writes, from every
state with the facts `F`, the state at `b` with the facts `H`; the role states the step
(`Seg.segStep`'s hypothesis, the values the step writes) because no rule of the assumptions and no
rule of Core evaluates it — a floating `cvt` the walk would have to compute symbolically. If every
state with `H` at `b` is dead, the states at `s` are. -/
theorem DeadFrom.of_step {s b : Nat} {op : Op} {F H : List (Nat × Value)}
    (hc : K.code[s]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hstep : ∀ R cf, Holds R F → ∃ t' : TState,
      execLocalA A L g ⟨s, R, cf, 0, [], none⟩ op = .ok t' ∧ t'.pc = b ∧ t'.sub = 0 ∧
        t'.acc = [] ∧ t'.fault = none ∧ Holds t'.regs H)
    (hd : DeadFrom K A L g b H) : DeadFrom K A L g s F :=
  DeadFrom.of_seg (Seg.segStep hc hl hstep) hd

/-- **A step the walk cannot compute, then a fault**: the form a `cvt` + `mul.bf16x2` sequence takes
in FlashMLA — the `cvt` writes a value that no rule gives (`hstep`), and the `mul` on the pair that
is not finite faults (`hex`, the kernel's `pairValue = none`). -/
theorem DeadFrom.of_step_local_error {s b : Nat} {op op' : Op} {F H : List (Nat × Value)}
    (hc : K.code[s]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hstep : ∀ R cf, Holds R F → ∃ t' : TState,
      execLocalA A L g ⟨s, R, cf, 0, [], none⟩ op = .ok t' ∧ t'.pc = b ∧ t'.sub = 0 ∧
        t'.acc = [] ∧ t'.fault = none ∧ Holds t'.regs H)
    (hc' : K.code[b]? = some ⟨none, op'⟩) (hl' : op'.isLocal = true)
    (hex : ∀ R cf, Holds R H → ∃ f, execLocalA A L g ⟨b, R, cf, 0, [], none⟩ op' = .error f) :
    DeadFrom K A L g s F :=
  DeadFrom.of_step hc hl hstep (DeadFrom.local_error hc' hl' hex)

/-- `sym_fault`: prove `∀ R cf, Holds R F → ∃ f, execLocalA A L g ⟨s, R, cf, 0, [], none⟩ op =
.error f` for the local instruction at `s`, where `seg_sym` proves `DeadFrom` and the walk meets a
floating step that no assumption's rule takes on the facts' values. Kernels extend it with
`macro_rules` (the decline of their rule and Core's missing rule); it fails by default. -/
syntax "sym_fault" : tactic
macro_rules | `(tactic| sym_fault) => `(tactic| fail "sym_fault: no proof")

/-- A `div` without a rule kills the thread. -/
theorem DeadFrom.div {k : IType} {w s d a b wa wb : Nat} {x y : BitVec 64}
    {F : List (Nat × Value)}
    (hc : K.code[s]? = some ⟨none, .int ⟨.div, .int k w, false, [some d], [.reg a, .reg b]⟩⟩)
    (ha : (a, Value.bits wa x) ∈ F) (hb : (b, Value.bits wb y) ∈ F)
    (hok : divOk k w (truncBits w x) (truncBits w y) = false)
    (hL : NoRuleAt A L g s (.int ⟨.div, .int k w, false, [some d], [.reg a, .reg b]⟩))
    (hA : Assumption.SegFreePc A s := by seg_free_pc)
    (hr : IntInstr.rule ⟨.div, .int k w, false, [some d], [.reg a, .reg b]⟩ = some .threadInt :=
      by rfl) : DeadFrom K A L g s F := by
  intro t h
  have hra := holds_mem h.2.2.2.2 ha
  have hrb := holds_mem h.2.2.2.2 hb
  unfold divOk at hok
  split at hok
  · cases hok
  · rename_i f hq
    have he : execLocalA A L g t
        (.int ⟨.div, .int k w, false, [some d], [.reg a, .reg b]⟩) = .error f := by
      simp [hA.exec h.1, execLocalRule_of_none (hL t h.1),
        execLocal_int hr,
        execInt, intResult, DType.width, DType.intLanes?, readReg, hra, hrb, readBits, hq, bind,
        Except.bind, pure, Except.pure]
    refine Machine.dead_of_ub (f := f) ?_
    have hc' : K.code[t.pc]? = some ⟨none, .int ⟨.div, .int k w, false, [some d],
        [.reg a, .reg b]⟩⟩ := by rw [h.1]; exact hc
    have hl : (Op.int ⟨.div, .int k w, false, [some d], [.reg a, .reg b]⟩).isLocal = true := rfl
    simp only [out, h.2.2.2.1, hc', guardHolds, hl, he, ↓reduceIte]
    rfl

theorem DeadFrom.launch {L' : Launch} (hL : L' = L) {s : Nat} {F : List (Nat × Value)}
    (h : DeadFrom K A L' g s F) : DeadFrom K A L g s F :=
  hL ▸ h

theorem not_eq_of {x b : Bool} (h : x = !b) : (!x) = b := by
  rw [h]; cases b <;> rfl

/-- Keys apart from `d`. -/
theorem keys_ne {F : List (Nat × Value)} {d : Nat} (h : (F.map Prod.fst).elem d = false) :
    ∀ r ∈ F, r.1 ≠ d := by
  intro r hr he
  have : (F.map Prod.fst).elem d = true :=
    List.elem_eq_true_of_mem (List.mem_map.mpr ⟨r, hr, he⟩)
  rw [h] at this
  cases this

/-- The writes `(d₁, v₁), …, (dₖ, vₖ)` in this order (the last one written last). -/
def setRegsL (t : TState) : List (Nat × Value) → TState
  | [] => t
  | (d, v) :: rest => setRegsL (setReg t d v) rest

/-- Each written register is apart from the facts and from the writes before it. -/
def freshKeys : List (Nat × Value) → List (Nat × Value) → Bool
  | [], _ => true
  | (d, v) :: rest, F => (F.map Prod.fst).elem d = false && freshKeys rest ((d, v) :: F)

theorem At.setRegsL {t : TState} {pc : Nat} {F : List (Nat × Value)} :
    ∀ {dv : List (Nat × Value)}, At t pc F → freshKeys dv F = true →
      At (PTX.next (setRegsL t dv)) (pc + 1) (dv.reverse ++ F)
  | [], h, _ => At.next h
  | (d, v) :: rest, h, hk => by
    simp only [freshKeys, Bool.and_eq_true] at hk
    have h1 : At (setReg t d v) pc ((d, v) :: F) :=
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, Function.update_self ..,
        holds_update h.2.2.2.2 (keys_ne (of_decide_eq_true hk.1))⟩
    simpa [PTX.Flow.setRegsL] using At.setRegsL (dv := rest) h1 hk.2

/-- **A local step that writes `(d₁, v₁), …, (dₖ, vₖ)` in this order**, as a piece: its step from
every state with the facts `F` (Core's rule, or an assumption's that declines to Core's). -/
theorem Seg.writes {pc : Nat} {op : Op} {F : List (Nat × Value)} {dv : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ R cf, Holds R F → execLocalA A L g ⟨pc, R, cf, 0, [], none⟩ op =
      .ok (PTX.next (setRegsL ⟨pc, R, cf, 0, [], none⟩ dv)))
    (hk : freshKeys dv F = true) :
    ∃ n, Seg K A L g n pc F (pc + 1) (dv.reverse ++ F) := by
  refine ⟨1, fun t h => ⟨_, ?_, At.setRegsL h hk⟩⟩
  obtain ⟨tpc, R, cf, sub, acc, fault⟩ := t
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4
  exact run_local hc hl ⟨rfl, rfl, rfl, rfl, h5⟩ (hex R cf h5)

/-- Where no assumption gives the instruction a rule or takes a segment, its step is Core's. -/
theorem execLocalA_core {pc : Nat} {op : Op} {t : TState} (hL : NoRuleAt A L g pc op)
    (hA : Assumption.SegFreePc A pc) (ht : t.pc = pc) :
    execLocalA A L g t op = execLocal L g t op := by
  rw [hA.exec ht, execLocalRule_of_none (hL t ht)]

/-- **`neg.f32 d, r` of a word that a hypothesis classifies as the finite datum `s`**, as a piece
(Core's rule writes the payload `-s`; no assumption gives `neg` a rule). -/
theorem Seg.negWord {pc d r : Nat} {F : List (Nat × Value)} {x : BitVec 64} {s : ℚ}
    (hc : K.code[pc]? = some ⟨none,
      .float { op := .neg, ty := ⟨.f32, 1⟩, dsts := [some d], srcs := [.reg r] }⟩)
    (hL : NoRuleAt A L g pc
      (.float { op := .neg, ty := ⟨.f32, 1⟩, dsts := [some d], srcs := [.reg r] }))
    (hA : Assumption.SegFreePc A pc) (hrF : (r, .bits 32 x) ∈ F)
    (hx : classify .f32 (.bits 32 x) = .ok (.fin s))
    (hk : freshKeys [(d, .float .f32 ((-s : ℚ) : ℝ))] F = true) :
    ∃ n, Seg K A L g n pc F (pc + 1) ([(d, .float .f32 ((-s : ℚ) : ℝ))].reverse ++ F) :=
  Seg.writes hc rfl (fun R cf hR => by
    rw [execLocalA_core hL hA rfl, execLocal_negWord (holds_mem hR hrF) hx]; rfl) hk

/-- **`abs.f32 d, r` of a word that a hypothesis classifies as the finite datum `s`**, as a
piece. -/
theorem Seg.absWord {pc d r : Nat} {F : List (Nat × Value)} {x : BitVec 64} {s : ℚ}
    (hc : K.code[pc]? = some ⟨none,
      .float { op := .abs, ty := ⟨.f32, 1⟩, dsts := [some d], srcs := [.reg r] }⟩)
    (hL : NoRuleAt A L g pc
      (.float { op := .abs, ty := ⟨.f32, 1⟩, dsts := [some d], srcs := [.reg r] }))
    (hA : Assumption.SegFreePc A pc) (hrF : (r, .bits 32 x) ∈ F)
    (hx : classify .f32 (.bits 32 x) = .ok (.fin s))
    (hk : freshKeys [(d, .float .f32 ((|s| : ℚ) : ℝ))] F = true) :
    ∃ n, Seg K A L g n pc F (pc + 1) ([(d, .float .f32 ((|s| : ℚ) : ℝ))].reverse ++ F) :=
  Seg.writes hc rfl (fun R cf hR => by
    rw [execLocalA_core hL hA rfl, execLocal_absWord (holds_mem hR hrF) hx]; rfl) hk
end

open Lean Meta Elab Tactic

/-- `code_lookup`: close `K.code[i]? = some ?ins` with the generated lookup `Flow.code_<n>` of the
numeral `n` that `i` evaluates to. -/
elab "code_lookup" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, lhs, _) := ty.consumeMData.eq? | throwError "code_lookup: expected K.code[i]? = _"
  unless lhs.isAppOfArity ``GetElem?.getElem? 7 do throwError "code_lookup: expected K.code[i]?"
  let xs := lhs.getArg! 5
  unless xs.isAppOfArity ``PTX.Kernel.code 1 do throwError "code_lookup: expected K.code[i]?"
  let some k := xs.appArg!.getAppFn.constName? |
    throwError "code_lookup: the kernel is not a constant"
  let n ← natValue (lhs.getArg! 6)
  let lemmaName := k.getPrefix ++ `Flow ++ Name.mkSimple s!"code_{n}"
  unless (← getEnv).contains lemmaName do throwError "code_lookup: no lookup {lemmaName}"
  let pf := mkConst lemmaName
  unless ← withAssignableSyntheticOpaque (isDefEq ty (← inferType pf)) do
    throwError "code_lookup: {lemmaName} does not match {ty}"
  goal.assign pf
  replaceMainGoal []

/-- The lengths `n ≤ maxN` of the local paths from `s` to `b`: both branches of a branch are
taken, a guarded event instruction is passed (its guard may be false), and an unguarded event
instruction ends the walk. At most `limit` lengths, the shortest first. -/
meta def segLengths (K code : Expr) (s b maxN limit : Nat) : SegM (Array Nat) := do
  let localAt (pc : Nat) : MetaM Bool := do
    let some ins ← instrAt K code pc | return false
    let ins ← whnfD ins
    unless ins.isAppOfArity ``PTX.Instr.mk 2 do return false
    if (← whnfD (ins.getArg! 0)).isAppOfArity ``Option.some 2 then return true
    let l ← whnfD (← mkAppM ``PTX.Op.isLocal #[ins.getArg! 1])
    return l.isConstOf ``Bool.true
  let mut cur : Array Nat := #[s]
  let mut out := #[]
  let mut locals : Std.HashMap Nat Bool := {}
  for k in [0:maxN + 1] do
    if cur.contains b then
      out := out.push k
      if out.size ≥ limit then break
    let mut nxt := #[]
    for pc in cur do
      let loc ← match locals[pc]? with
        | some l => pure l
        | none => do
          let l ← localAt pc
          locals := locals.insert pc l
          pure l
      unless loc do continue
      if let some i ← segInstrM K code pc then
        for t in i.succ do
          unless nxt.contains t do nxt := nxt.push t
    if nxt.isEmpty then break
    cur := nxt
  return out

/-- `seg_auto using tac`: prove `∃ n, Seg K A L g n s F b G` with `tac` closing `Seg … n …`, for
the lengths `n` of the local paths from `s` to `b`, the shortest first. -/
syntax "seg_auto " "using " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| seg_auto using $tac) => withMainContext do
    let ty ← instantiateMVars (← getMainTarget)
    let some (_, body) := ty.consumeMData.app2? ``Exists |
      throwError "seg_auto: expected ∃ n, Seg …, got {ty}"
    let .lam _ _ seg _ := body.consumeMData | throwError "seg_auto: expected ∃ n, Seg …"
    unless seg.isAppOfArity ``PTX.Flow.Seg 9 do throwError "seg_auto: expected ∃ n, Seg …"
    let K := seg.getArg! 0
    let s ← natValue (seg.getArg! 5)
    if ((seg.getArg! 7).find? fun e => e.isAppOf ``ite || e.isAppOf ``dite).isSome then
      throwError "seg_auto: the end of the segment is an `if`"
    let b ← natValue (seg.getArg! 7)
    let code ← mkAppM ``PTX.Kernel.code #[K]
    let ns ← (segLengths K code s b 1024 4).run' {}
    if ns.isEmpty then throwError "seg_auto: no local path from {s} to {b}"
    let saved ← saveState
    let mut err : Option Exception := none
    for n in ns do
      try
        -- a runtime error of the role's tactic (an evaluation that runs away) is a failure
        tryCatchRuntimeEx
          (evalTactic (← `(tactic| focus
            refine ⟨$(Syntax.mkNumLit (toString n)), ?_⟩
            ($tac)
            done)))
          fun e => throwError "seg_auto: {e.toMessageData}"
        return
      catch e =>
        err := some e
        saved.restore (restoreInfo := true)
    match err with
    | some e => throw e
    | none => throwError "seg_auto: no segment from {s} to {b}"


/-- A line of `seg_sym`'s report, appended to the file `SEG_SYM_LOG` names. -/
meta def symLog (s : String) : IO Unit := do
  if let some path ← IO.getEnv "SEG_SYM_LOG" then
    let now ← IO.monoMsNow
    IO.FS.withFile path .append fun h => h.putStrLn s!"{now} {s}"

/-- A Boolean literal, by evaluation. -/
meta def boolLit? (e : Expr) : MetaM (Option Bool) := do
  let e ← instantiateMVars e
  -- an evaluation that runs away (a comparison of symbolic words) is not a literal
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := 100000 }) <|
      withCurrHeartbeats do
        let e ← whnfD e
        if e.isConstOf ``Bool.true then return some true
        if e.isConstOf ``Bool.false then return some false
        return none)
    (fun _ => pure none)

/-- The Boolean `c` of a predicate value `.pred c`. -/
meta def predBool? (v : Expr) : MetaM (Option Expr) := do
  let v ← whnfD v
  if v.isAppOfArity ``PTX.Value.pred 1 then return some (v.getArg! 0)
  return none

/-- The bits `x` of a value `.bits w x`. -/
meta def valueBits? (v : Expr) : MetaM (Option Expr) := do
  let v ← whnfD v
  if v.isAppOfArity ``PTX.Value.bits 2 then return some (v.getArg! 1)
  return none

/-- The control of the instruction at a program counter, as `seg_sym` walks it. -/
inductive SymCtl where
  /-- An event instruction: the walk ends. -/
  | event
  /-- A branch, guarded by register `p` (taken when it holds `!neg`) or unconditional. -/
  | bra (guard : Option (Nat × Bool)) (target : Nat)
  /-- `selp` of width `w` into `d` of operands `a`, `b` on register `p`. -/
  | selp (d p w : Nat) (a b : Expr)
  /-- A `div` of kind `k` and width `w` into `d` of registers `a`, `b`: it has a rule only for
  some operands. -/
  | div (k : Expr) (w d a b : Nat)
  /-- A local instruction that an assumption gives a rule (`rule_step`), or one on conditional
  values (`condStep`), writing `ds` and reading `srcs`; `ruled`: an assumption may give it a
  rule. -/
  | rule (ds : Array Nat) (srcs : Array Nat) (ruled : Bool)
  /-- `neg.f32 d, r` (`abs` when `abs`) of a word `.bits 32 x` that `h : classify .f32 (.bits 32 x)
  = .ok (.fin s)` classifies as the finite datum `s` (`wordHyp?`; `Seg.negWord`, `Seg.absWord`). -/
  | word (abs : Bool) (d r : Nat) (h s : Expr)
  /-- A step that an assumption takes as a segment (`segmentRule`, THREAD-LOCAL): one local step
  from `pc` to the segment's stop `b`, with the facts `G` there and the premise `hstep` of
  `Seg.segStep` (`segStepHyp`). -/
  | seg (b : Nat) (G : Expr) (hstep : Expr)
  /-- Another local instruction. -/
  | step

/-- The guard of the instruction at `pc`: its predicate register and whether it is negated. -/
meta def instrGuard (K code : Expr) (pc : Nat) : MetaM (Option (Nat × Bool)) := do
  let some ins ← instrAt K code pc | return none
  let ins ← whnfD ins
  unless ins.isAppOfArity ``PTX.Instr.mk 2 do return none
  let guard ← whnfD (ins.getArg! 0)
  unless guard.isAppOfArity ``Option.some 2 do return none
  let pn ← whnfD (guard.getArg! 1)
  let some p := regLit? (← whnfD (pn.getArg! 2)) | return none
  let neg ← whnfD (pn.getArg! 3)
  return some (p, neg.isConstOf ``Bool.true)

/-- The control of the instruction at `pc`. -/
meta def symCtl (K code : Expr) (pc : Nat) : MetaM SymCtl := do
  let some ins ← instrAt K code pc | throwError "seg_sym: no instruction at {pc}"
  let ins ← whnfD ins
  unless ins.isAppOfArity ``PTX.Instr.mk 2 do throwError "seg_sym: instruction {pc} is {ins}"
  let guard ← whnfD (ins.getArg! 0)
  let op ← whnfD (ins.getArg! 1)
  if op.isAppOfArity ``PTX.Op.bra 2 then
    let t ← natValue (op.getArg! 0)
    if guard.isAppOfArity ``Option.some 2 then
      let pn ← whnfD (guard.getArg! 1)
      let some p := regLit? (← whnfD (pn.getArg! 2)) | throwError "seg_sym: guard at {pc}"
      let neg ← whnfD (pn.getArg! 3)
      return .bra (some (p, neg.isConstOf ``Bool.true)) t
    return .bra none t
  let loc ← whnfD (← mkAppM ``PTX.Op.isLocal #[op])
  unless loc.isConstOf ``Bool.true do return .event
  if op.isAppOfArity ``PTX.Op.int 1 then
    let i ← whnfD (op.getArg! 0)
    if i.isAppOfArity ``PTX.IntInstr.mk 5 && (← whnfD (i.getArg! 0)).isConstOf ``PTX.IntOp.selp
    then
      let ds ← whnfD (i.getArg! 3)
      let ss ← whnfD (i.getArg! 4)
      if ds.isAppOfArity ``List.cons 3 && ss.isAppOfArity ``List.cons 3 then
        let d0 ← whnfD (ds.getArg! 1)
        let s1 ← whnfD (ss.getArg! 2)
        let s2 ← whnfD (s1.getArg! 2)
        let pOp ← whnfD (s2.getArg! 1)
        if d0.isAppOfArity ``Option.some 2 && pOp.isAppOfArity ``PTX.Opnd.reg 1 then
          let some d := regLit? (← whnfD (d0.getArg! 1)) | throwError "seg_sym: selp at {pc}"
          let some p := regLit? (← whnfD (pOp.getArg! 0)) | throwError "seg_sym: selp at {pc}"
          let w ← natValue (← mkAppM ``PTX.DType.width #[i.getArg! 1])
          return .selp d p w (ss.getArg! 1) (s1.getArg! 1)
    if i.isAppOfArity ``PTX.IntInstr.mk 5 && (← whnfD (i.getArg! 0)).isConstOf ``PTX.IntOp.div &&
        guard.isAppOfArity ``Option.none 1 then
      let ds ← whnfD (i.getArg! 3)
      let ss ← whnfD (i.getArg! 4)
      if ds.isAppOfArity ``List.cons 3 && ss.isAppOfArity ``List.cons 3 then
        let d0 ← whnfD (ds.getArg! 1)
        let s1 ← whnfD (ss.getArg! 2)
        let ra ← whnfD (ss.getArg! 1)
        let rb ← whnfD (s1.getArg! 1)
        if d0.isAppOfArity ``Option.some 2 && ra.isAppOfArity ``PTX.Opnd.reg 1 &&
            rb.isAppOfArity ``PTX.Opnd.reg 1 then
          let some d := regLit? (← whnfD (d0.getArg! 1)) | throwError "seg_sym: div at {pc}"
          let some a := regLit? (← whnfD (ra.getArg! 0)) | throwError "seg_sym: div at {pc}"
          let some b := regLit? (← whnfD (rb.getArg! 0)) | throwError "seg_sym: div at {pc}"
          let ty ← whnfD (i.getArg! 1)
          if ty.isAppOfArity ``PTX.DType.int 2 then
            return .div (← whnfD (ty.getArg! 0)) (← natValue (ty.getArg! 1)) d a b
  return .step

/-- The segment steps that the local context states, by start `pc`: a hypothesis
`∃ n, Seg K A L g n pc F b G` gives the stop `b`, the facts `G` at it and its proof. Scanned once
per walk (a context scan per step would unfold the hypotheses' types at every instruction). -/
meta def segHyps : MetaM (Std.HashMap Nat (Nat × Expr × Expr)) := do
  let mut out : Std.HashMap Nat (Nat × Expr × Expr) := {}
  for ldecl in (← getLCtx) do
    if !ldecl.isImplementationDetail then
      let ty ← whnfD ldecl.type
      if ty.isAppOfArity ``Exists 2 then
        let pred ← whnfD (ty.getArg! 1)
        if pred.isLambda then
          let body := pred.bindingBody!
          if body.getAppFn.isConstOf ``PTX.Flow.Seg && body.getAppArgs.size == 9 then
            let args := body.getAppArgs
            if let some s := regLit? (← whnfD args[5]!) then
              if let some b := regLit? (← whnfD args[7]!) then
                out := out.insert s (b, args[8]!, mkFVar ldecl.fvarId)
  return out

meta def symStart (s : Nat) (F R cf : Expr) : MetaM Expr := do
  let (ex, tbl) ← splitFacts F
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``PTX.Value]
  let mut cells := ex.toList
  if let some (live, v) := tbl then
    for r in ← regList live do
      cells := cells ++ [← mkAppM ``Prod.mk #[mkNatLit r, ← evalTable (mkApp v (mkNatLit r))]]
  let fexp ← mkListLit pairTy cells
  let regs ← mkAppM ``PTX.Proof.override #[fexp, R]
  let none' ← mkAppOptM ``Option.none #[mkConst ``PTX.Fault]
  let nilV ← mkAppOptM ``List.nil #[mkConst ``PTX.Value]
  return mkAppN (mkConst ``PTX.TState.mk) #[mkNatLit s, regs, cf, mkNatLit 0, nilV, none']

/-- Closed subterms of small types (numbers, Booleans, instruction types) evaluated, and closed
values to their constructors (Core's `-∞` or `+0` result of a constant operand, say): the values
a symbolic run computes, with the instruction fields they read resolved. -/
meta partial def normVal (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if x.hasFVar || x.hasMVar || x.hasLooseBVars || x.isLit then return .done x
    let some c := x.getAppFn.constName? | return .done x
    if (← getEnv).isConstructor c then return .done x
    let ty ← try whnfR (← inferType x) catch _ => return .done x
    if ty.isConstOf ``PTX.Value then
      let x' ← whnfD x
      let env ← getEnv
      let ctor := match x'.getAppFn.constName? with
        | some n => env.isConstructor n
        | none => false
      if ctor && x' != x then return .done (← normVal x')
      return .done x
    unless ty.isConstOf ``Nat || ty.isConstOf ``Bool || ty.isConstOf ``PTX.IType ||
      ty.isConstOf ``PTX.DType do return .done x
    let x' ← whnfD x
    let env ← getEnv
    let isCtor := match x'.getAppFn.constName? with
      | some n => env.isConstructor n
      | none => false
    if x'.isLit || x'.nat?.isSome || isCtor then return .done x'
    return .done x)

/-- A definitional equality check with a small budget: a comparison that runs away counts as
different. -/
meta def cheapDefEq (a b : Expr) : MetaM Bool := withNewMCtxDepth do
  if a == b then return true
  let budget (x : MetaM Bool) : MetaM Bool :=
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000000 })
        (withCurrHeartbeats x))
      (fun _ => pure false)
  if ← budget (withReducible (isDefEq a b)) then return true
  budget (isDefEq a b)

/-- The value a symbolic thread state gives register `r`. -/
meta def stateReg (t : Expr) (r : Nat) : MetaM (Option Expr) := do
  let o ← whnfD (mkApp2 (mkConst ``PTX.TState.regs) t (mkNatLit r))
  if o.isAppOfArity ``Option.some 2 then return some (o.getArg! 1)
  return none

/-- The registers and values of the facts `F` (explicit facts, then the table's live registers).
-/
meta def startCells (F : Expr) : MetaM (Array (Nat × Expr)) := do
  let (ex, tbl) ← splitFacts F
  let mut out := #[]
  for q in ex do
    let q ← whnfD q
    unless q.isAppOfArity ``Prod.mk 4 do continue
    let some r := regLit? (← whnfD (q.getArg! 2)) | continue
    out := out.push (r, q.getArg! 3)
  if let some (live, v) := tbl then
    for r in ← regList live do
      out := out.push (r, ← evalTable (mkApp v (mkNatLit r)))
  return out

/-- The facts of the registers `rs` that a symbolic state gives a value, as an explicit list.
`start`: the start facts' values; a register that still holds its start value keeps it as it is
(`fresh`: the state is the start state, whose registers are not evaluated). -/
meta def stateFacts (t : Expr) (rs : List Nat) (start : Std.HashMap Nat Expr := {})
    (fresh : Bool := false) : MetaM Expr := do
  let tm0 ← IO.monoMsNow
  let r ← stateFactsCore t rs start fresh
  symLog s!"  facts of {rs.length} registers: {(← IO.monoMsNow) - tm0} ms"
  return r
where stateFactsCore (t : Expr) (rs : List Nat) (start : Std.HashMap Nat Expr)
    (fresh : Bool) : MetaM Expr := do
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``PTX.Value]
  let mut cells := #[]
  for r in rs do
    if fresh then
      if let some v := start[r]? then
        cells := cells.push (← mkAppM ``Prod.mk #[mkNatLit r, v])
      continue
    -- a register the start facts do not give (a datum the role does not state) has no fact
    let some v ← stateReg t r | continue
    let v ← if start[r]? == some v then pure v else normVal v
    cells := cells.push (← mkAppM ``Prod.mk #[mkNatLit r, v])
  mkListLit pairTy cells.toList

/-- `sym_decide_rw`: after `sym_decide`'s own alternatives, prove a decision by a rewrite the role
knows — the branch's predicate as the machine states it (`scmpi …`, `skipLoop d`) and the walk's
term (the comparison unfolded by Core's rule) are the same up to the expansion of the machine's
abbreviations, and a hypothesis may only match after that rewrite. Kernels extend it with
`macro_rules` (a `simp only [skipLoop, padded, scmpi, scmp, r32, i32, compare] at *`, say); it
fails by default. -/
syntax "sym_decide_rw" : tactic
macro_rules | `(tactic| sym_decide_rw) => `(tactic| fail "sym_decide_rw: no rewrite")

/-- `sym_decide`: prove a decision `c = true` or `c = false` of a branch that no hypothesis in
context decides. Kernels extend it with `macro_rules` for the facts of their launch (an index
that does not overflow, say); it fails by default. -/
syntax "sym_decide" : tactic
macro_rules | `(tactic| sym_decide) => `(tactic| fail "sym_decide: no decision")
/- The library's rule: a comparison of two recorded reals (`erealCompare` of reals, a
floating `setp` on payloads) decided by the facts about the reals in context (a row sum that a
hypothesis makes zero, say): the comparison as a real inequality, then `linarith`. -/
macro_rules | `(tactic| sym_decide) => `(tactic| first
  | (simp only [PTX.Flow.erealCompare_coe_eq, PTX.Flow.erealCompare_coe_ne,
      PTX.Flow.erealCompare_coe_lt, PTX.Flow.erealCompare_coe_le, PTX.Flow.erealCompare_coe_gt,
      PTX.Flow.erealCompare_coe_ge, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq,
      not_not, not_lt, not_le]
     first | assumption | (symm; assumption) | sym_decide_rw | linarith |
       fail "sym_decide: no real decision")
  | fail "sym_decide: no decision")

/-- `sym_local_none`: prove `NoRuleAt A L g pc op` for an integer instruction of the kernel's
code. Kernels extend it with `macro_rules` for their assumption list; it fails by default. -/
syntax "sym_local_none" : tactic
macro_rules | `(tactic| sym_local_none) => `(tactic| fail "sym_local_none: no proof")

/-- The heartbeats a `sym_decide` attempt may take before it counts as no decision. -/
meta register_option seg_sym.decideHeartbeats : Nat := {
  defValue := 20000
  descr := "heartbeats (in the units of maxHeartbeats) of one sym_decide attempt in seg_sym; \
    an attempt that exceeds them counts as no decision" }

/-- The proof of a decision `c = lit` from a hypothesis in context: `c = lit`, or `¬ c = true`
for `lit = false`, up to evaluation; else by `sym_decide`. -/
meta partial def decideBool (c : Expr) (lit : Bool) : TacticM (Option Expr) := withMainContext do
  let litE := mkConst (if lit then ``Bool.true else ``Bool.false)
  -- a negation: decide its operand
  let c' ← whnfR c
  if c'.isAppOfArity ``not 1 then
    if let some pf ← decideBool (c'.getArg! 0) (!lit) then
      return some (← mkAppOptM ``PTX.Flow.not_eq_of #[none, some litE, some pf])
  -- first a hypothesis whose condition is the predicate up to reducible unfolding (the walk's
  -- term and the role's hypothesis are usually the same term), so that no comparison at default
  -- transparency is run against the other hypotheses first
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if let some (_, a, b) := ty.eq? then
      if (← isDefEq b litE) && (← withNewMCtxDepth (withReducible (isDefEq a c))) then
        symLog s!"decided {lit} by {d.userName}: {← ppExpr ty}"
        return some d.toExpr
    if !lit && ty.isAppOfArity ``Not 1 then
      if let some (_, a, b) := ty.appArg!.consumeMData.eq? then
        if (← isDefEq b (mkConst ``Bool.true)) &&
            (← withNewMCtxDepth (withReducible (isDefEq a c))) then
          let iff ← mkAppOptM ``Bool.eq_false_iff #[some c]
          return some (← mkAppM ``Iff.mpr #[iff, d.toExpr])
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty := ty.consumeMData
    if let some (_, a, b) := ty.eq? then
      if (← isDefEq b litE) && (← cheapDefEq a c) then
        symLog s!"decided {lit} by {d.userName}: {← ppExpr ty}"
        return some d.toExpr
    if !lit && ty.isAppOfArity ``Not 1 then
      if let some (_, a, b) := ty.appArg!.consumeMData.eq? then
        if (← isDefEq b (mkConst ``Bool.true)) && (← cheapDefEq a c) then
          let iff ← mkAppOptM ``Bool.eq_false_iff #[some c]
          return some (← mkAppM ``Iff.mpr #[iff, d.toExpr])
  -- a hypothesis whose condition is the predicate up to unfolding (the role wrote the code's
  -- term through its own abbreviations): a budgeted check at default transparency
  -- (only a hypothesis whose left side has the predicate's head, with a tenth of the budget)
  let budget0 := seg_sym.decideHeartbeats.get (← getOptions) * 100
  let cHead := (← whnfR c).getAppFn
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    let some (_, a, b) := ty.eq? | continue
    unless (← whnfR a).getAppFn == cHead do continue
    unless ← isDefEq b litE do continue
    let s0 ← saveState
    let ok ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxHeartbeats := budget0 }) <|
        withCurrHeartbeats (withTransparency .default (isDefEq a c)))
      (fun _ => pure false)
    if ok then
      symLog s!"decided {lit} by {d.userName} (unfolded): {← ppExpr ty}"
      return some (← mkExpectedTypeHint d.toExpr (← mkEq c litE))
    s0.restore
  let m ← mkFreshExprMVar (← mkEq c litE)
  let saved ← saveState
  let tac ← `(tactic| sym_decide)
  let budget := seg_sym.decideHeartbeats.get (← getOptions) * 1000
  -- a kernel rule whose statement unifies only by running away counts as no decision
  let r ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := budget }) <|
      withCurrHeartbeats do
        let gs ← Tactic.run m.mvarId! (evalTactic tac)
        if gs.isEmpty then return some (← instantiateMVars m) else return none)
    (fun _ => pure none)
  -- keep the state of a decision (its auxiliary declarations); a failed decision, or one whose
  -- proof contains an elaboration error placeholder, counts as none and leaves no trace
  match r with
  | some pf =>
    if pf.hasSorry then
      saved.restore
      return none
    return some pf
  | none =>
    saved.restore
    return none

meta def segGoal (ty : Expr) : MetaM (Expr × Expr × Expr × Nat × Expr × Expr × Expr) := do
  let some (_, body) := ty.consumeMData.app2? ``Exists |
    throwError "seg_sym: expected ∃ n, Seg …, got {ty}"
  let .lam _ _ seg _ := body.consumeMData | throwError "seg_sym: expected ∃ n, Seg …"
  unless seg.isAppOfArity ``PTX.Flow.Seg 9 do throwError "seg_sym: expected ∃ n, Seg …"
  return (seg.getArg! 0, seg.getArg! 1, seg.getArg! 2, ← natValue (seg.getArg! 5),
    seg.getArg! 6, seg.getArg! 7, seg.getArg! 8)

/-- Unfold, once, the definitions applied in `e` whose bodies are an `if` (after their
arguments): the table's abbreviations of conditional values. -/
meta def unfoldIteDefs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    let some c := x.getAppFn.constName? | return .done x
    let env ← getEnv
    if env.isConstructor c || (← isProjectionFn c) then return .done x
    let some (.defnInfo info) := env.find? c | return .done x
    unless (info.value.find? (·.isAppOfArity ``ite 5)).isSome do return .done x
    match ← unfoldDefinition? x with
    | some x' =>
      let x' := x'.headBeta
      if x'.isAppOfArity ``ite 5 then return .done x' else return .done x
    | none => return .done x)

/-- A launch with its parameters or a parameter object written out (`explicitParams`,
`explicitObject` of `Lemmas/Flow/ParamObject.lean`, or one inside the other): a hypothesis
`L' = L` with such an `L'` lets `seg_sym` evaluate under `L'`. -/
meta def isExplicitLaunch (e : Expr) : Bool :=
  e.isAppOfArity ``PTX.Proof.explicitParams 2 || e.isAppOfArity `PTX.Flow.explicitObject 4

/-- One step of `sym_close`, with a bound on the conditions it decides. -/
meta partial def symClose (fuel : Nat) : TacticM Unit := withMainContext do
  -- the stated value read off its table is the computed term: an equation the kernel checks by
  -- unfolding the table once (the elaborator's `rfl` would unfold it at every register)
  let ty0 ← instantiateMVars (← getMainTarget)
  if let some (_, lhs, rhs) := ty0.eq? then
    unless lhs.hasMVar || rhs.hasMVar do
      if lhs == rhs || lhs == (← evalTable rhs) then
        (← getMainGoal).assign (← mkExpectedTypeHint (← mkEqRefl lhs) ty0)
        replaceMainGoal []
        return
  let saved ← saveState
  try
    tryCatchRuntimeEx (evalTactic (← `(tactic| rfl)))
      fun e => throwError "sym_close: {e.toMessageData}"
    return
  catch _ => saved.restore
  if fuel = 0 then throwError "sym_close: too many conditions"
  -- a value read under the launch with explicit parameters (a special register, say): the
  -- launch's, by the hypothesis `explicitParams L ps = L` in context
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dty ← instantiateMVars d.type
    let some (_, l, _) := dty.eq? | continue
    unless isExplicitLaunch l do continue
    unless ((← instantiateMVars (← getMainTarget)).find? (· == l)).isSome do continue
    let s1 ← saveState
    try
      evalTactic (← `(tactic| simp only [$(mkIdent d.userName):ident]))
      if (← getGoals).isEmpty then return
      return ← symClose (fuel - 1)
    catch _ => s1.restore
  let ty ← instantiateMVars (← getMainTarget)
  let some (eqTy, lhs, rhs) := ty.eq? | throwError "sym_close: not an equation"
  -- the stated value as its table writes it, with the role's abbreviations unfolded
  let rhs ← withTransparency .reducible <| Meta.reduce (← evalTable rhs) (skipTypes := true)
  let ty ← mkEq lhs rhs
  let _ := eqTy
  replaceMainGoal [← (← getMainGoal).change ty]
  if rhs.isAppOfArity ``PTX.Value.pred 1 then
    evalTactic (← `(tactic| first
      | exact congrArg PTX.Value.pred (Eq.symm (by assumption))
      | exact congrArg PTX.Value.pred (Eq.symm (Bool.eq_false_iff.mpr (by assumption)))
      | exact congrArg PTX.Value.pred (by assumption)
      | (trace_state; fail "sym_close: no decision of the predicate")))
    return
  -- a definition of the table that hides an `if` (a reciprocal that is one at zero, say) is
  -- unfolded
  let rhs ← if (rhs.find? fun e => e.isAppOfArity ``ite 5 && !e.hasLooseBVars).isSome then
      pure rhs else do
    let rhs' ← unfoldIteDefs rhs
    if rhs' != rhs then
      replaceMainGoal [← (← getMainGoal).change (← mkEq lhs rhs')]
    pure rhs'
  let some it := rhs.find? (fun e => e.isAppOfArity ``ite 5 && !e.hasLooseBVars) |
    throwError m!"sym_close: the values differ: {ty}"
  let tc ← Term.exprToSyntax (it.getArg! 1)
  let hb := mkIdent (← mkFreshUserName `hb)
  evalTactic (← `(tactic| by_cases $hb:ident : $tc))
  let gs ← getGoals
  for (g, pos) in gs.zip [true, false] do
    setGoals [g]
    let s ← saveState
    try
      evalTactic (← if pos then `(tactic| rw [ite_eq_left $hb:ident]) else
        `(tactic| rw [ite_eq_right $hb:ident]))
      if !(← getGoals).isEmpty then symClose (fuel - 1)
    catch _ =>
      s.restore
      evalTactic (← `(tactic| first
        | exact absurd $hb:ident (by assumption)
        | exact absurd $hb:ident (Bool.eq_false_iff.mp (by assumption))
        | exact absurd (by assumption) $hb:ident
        | exact ($hb:ident (by assumption)).elim
        | exact ((by assumption : ¬ _) $hb:ident).elim
        -- a comparison of recorded reals that the facts about them refute (a row sum that a
        -- hypothesis makes zero, say)
        | (exfalso
           revert $hb:ident
           simp only [PTX.Flow.erealCompare_coe_eq, PTX.Flow.erealCompare_coe_ne,
             PTX.Flow.erealCompare_coe_lt, PTX.Flow.erealCompare_coe_le,
             PTX.Flow.erealCompare_coe_gt, PTX.Flow.erealCompare_coe_ge, decide_eq_true_eq,
             decide_eq_false_iff_not, Bool.not_eq_true, ne_eq, not_not, not_lt, not_le]
           first | (intro h; exact h (by linarith)) | (intro; linarith))
        | fail "sym_close: a branch that no hypothesis refutes"))

/-- `sym_close`: close an equation between a computed value and a stated one, by evaluation, or
by deciding the conditions of the `if`s in the stated value with the hypotheses of the case
splits in context (up to evaluation). -/
elab "sym_close" : tactic => symClose 8

/-- A proof of `AllP P l` from a proof of `P x` for each element, as a term (`And.intro` of the
proofs; the kernel checks it against `AllP`). -/
meta def allPProof' (xs : List Nat) (each : Nat → TacticM Expr) : TacticM Expr := do
  let mut acc := mkConst ``True.intro
  let mut accTy := mkConst ``True
  for x in xs.reverse do
    let px ← each x
    let pxTy ← inferType px
    acc := mkApp4 (mkConst ``And.intro) pxTy accTy px acc
    accTy := mkAnd pxTy accTy
  return acc

/-- The elements of a list literal (up to reducible unfolding of its spine). -/
meta partial def listElemsR (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let e ← whnfR e
  if e.isAppOfArity ``List.cons 3 then listElemsR (e.getArg! 2) (acc.push (e.getArg! 1))
  else if e.isAppOfArity ``List.nil 1 then return acc
  else throwError "sym_close: restate: facts not a list {e}"

/-- `∀ R, Holds R E → Holds R G` for an explicit `E` and `G = ex ++ factsFrom live v`: each fact
of `G` from the explicit fact of its register, restated by `sym_close`. -/
meta def restate (E G : Expr) : TacticM Unit := withMainContext do
  let (exG, tblG) ← splitFacts G
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``PTX.Value]
  let tE ← Term.exprToSyntax E
  evalTactic (← `(tactic| intro R hE))
  -- the facts about reals in context, as comparisons of reals: `sym_close` decides the
  -- conditions of the table's values with them
  discard realFacts
  symLog "restate: real facts"
  -- the explicit facts of `G`, then its table
  let exGE ← mkListLit pairTy exG.toList
  let tbl ← match tblG with
    | some (live, v) => mkAppM ``PTX.Flow.factsFrom #[live, v]
    | none => mkListLit pairTy []
  let tExG ← Term.exprToSyntax exGE
  let tTbl ← Term.exprToSyntax tbl
  evalTactic (← `(tactic|
    show PTX.Proof.Holds R ($tExG ++ $tTbl)))
  symLog "restate: shown"
  evalTactic (← `(tactic| refine (PTX.Proof.holds_append _ _ _).mpr ⟨?_, ?_⟩))
  -- explicit facts one by one
  evalTactic (← `(tactic| focus
    repeat' (first
      | exact trivial
      | refine ⟨PTX.Flow.holds_reg_of (E := $tE) hE (by fact_mem) (by sym_close), ?_⟩)))
  symLog "restate: explicit facts"
  -- the table register by register
  -- (built as a term: each register's fact of `E` found by position, its value read off the
  -- table and checked by the kernel when it is the walked term, `sym_close` otherwise)
  if let some (live, v) := tblG then
    let rs ← regList live
    evalTactic (← `(tactic| refine PTX.Flow.holds_factsFrom_of ?_))
    withMainContext do
    let goal ← getMainGoal
    -- the hypothesis `hE : Holds R E` the `intro` above made (its name is hygienic)
    let mut hE? := none
    for d in ← getLCtx do
      let dty ← instantiateMVars d.type
      if dty.isAppOfArity ``PTX.Proof.Holds 2 && dty.getArg! 1 == E then hE? := some d
    let some hE := hE? | throwError "sym_close: restate: no hypothesis Holds R E"
    let Rx := (← instantiateMVars hE.type).getArg! 0
    let es ← listElemsR E
    let mut keys := #[]
    for p in es do
      let p ← whnfR p
      keys := keys.push (regLit? (← whnfD (p.getArg! 2)))
    let each (r : Nat) : TacticM Expr := do
      let some i := keys.idxOf? (some r) | throwError "sym_close: restate: no fact of {r}"
      let pr ← whnfR es[i]!
      let x := pr.getArg! 3
      let vr := (mkApp v (mkNatLit r)).headBeta
      let hm ← memAt pairTy es.toList i
      let eqTy ← mkEq x vr
      let he ← if x == vr || (← projNorm x) == (← projNorm (← evalTable vr)) then
          mkExpectedTypeHint (← mkEqRefl x) eqTy
        else do
          symLog s!"restate: {r} by sym_close"
          let m ← mkFreshExprSyntheticOpaqueMVar eqTy
          let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| sym_close)))
          unless gs.isEmpty do throwError "sym_close: restate: the value of {r}"
          pure m
      return mkAppN (mkConst ``PTX.Flow.holds_reg_of)
        #[Rx, E, pr.getArg! 2, x, vr, hE.toExpr, hm, he]
    let pf ← allPProof' rs.toList each
    goal.assign pf
    replaceMainGoal []
  else
    evalTactic (← `(tactic| exact trivial))

/-- The bits an operand of a `selp` of width `w` reads from facts `F`: an immediate's pattern, or
the bits of a register's `.bits` value. -/
meta def selpOperand (F : Expr) (w : Nat) (o : Expr) : MetaM Expr := do
  let o ← whnfD o
  if o.isAppOfArity ``PTX.Opnd.imm 1 then
    let x ← mkAppM ``BitVec.ofInt #[mkNatLit 64, o.getArg! 0]
    return ← mkAppM ``PTX.truncBits #[mkNatLit w, x]
  if o.isAppOfArity ``PTX.Opnd.reg 1 then
    let some r := regLit? (← whnfD (o.getArg! 0)) | throwError "seg_sym: selp operand {o}"
    let (ex, _) ← splitFacts F
    for q in ex do
      let q ← whnfD q
      if q.isAppOfArity ``Prod.mk 4 && regLit? (← whnfD (q.getArg! 2)) == some r then
        let some x ← valueBits? (q.getArg! 3) |
          throwError "seg_sym: the selp operand {r} is not bits"
        return x
    throwError "seg_sym: no fact of the selp operand {r}"
  throwError "seg_sym: selp operand {o}"

/-- `sym_selp_value`: a role's choice to give a `selp` on values that are not words (a floating
`selp` between a payload and a constant) the conditional value `if c = true then a else b`
instead of a case split. The library's rule fails (split); a role opts in with
`scoped macro_rules | `(tactic| sym_selp_value) => `(tactic| skip)` in its namespace. A rule step
reads such a value as the conditional of the operands' readings (`readEReal_ite`), so a floating
operation on it is one step with no split. -/
syntax "sym_selp_value" : tactic
macro_rules | `(tactic| sym_selp_value) => `(tactic| fail "sym_selp_value: split")

/-- Whether the role opted in to conditional `selp` values. -/
meta def selpValueOptIn : TacticM Bool := do
  let s ← saveState
  let ok ← try evalTactic (← `(tactic| sym_selp_value)); pure true catch _ => pure false
  s.restore
  return ok

/-- The value of register `r` in facts `F`: an explicit fact first, then the table. -/
meta def factValue (F : Expr) (r : Nat) : MetaM (Option Expr) := do
  let (ex, tbl) ← splitFacts F
  for q in ex do
    let q ← whnfD q
    if q.isAppOfArity ``Prod.mk 4 then
      if regLit? (← whnfD (q.getArg! 2)) == some r then return some (q.getArg! 3)
  let some (_, v) := tbl | return none
  return some (← evalTable (mkApp v (mkNatLit r)))

/-- The value an operand of a `selp` of width `w` reads from facts `F`: a register's fact, or
the bits of a constant (a 32-bit constant as its literal pattern). -/
meta def selpValue (L g : Expr) (F : Expr) (w : Nat) (o : Expr) : MetaM Expr := do
  let o ← whnfD o
  if o.isAppOfArity ``PTX.Opnd.reg 1 then
    let some r := regLit? (← whnfD (o.getArg! 0)) | throwError "seg_sym: selp operand {o}"
    let some v ← factValue F r | throwError "seg_sym: no fact of the selp operand {r}"
    return v
  -- a constant: Core's reading at any state
  let noneV ← mkAppOptM ``Option.none #[mkConst ``PTX.Value]
  let regsNone := Expr.lam `r (mkConst ``Nat) noneV .default
  let none' ← mkAppOptM ``Option.none #[mkConst ``PTX.Fault]
  let nilV ← mkAppOptM ``List.nil #[mkConst ``PTX.Value]
  let cfN ← mkAppOptM ``Option.none #[mkConst ``Bool]
  let t0 := mkAppN (mkConst ``PTX.TState.mk) #[mkNatLit 0, regsNone, cfN, mkNatLit 0, nilV, none']
  let r ← whnfD (← mkAppM ``PTX.readValue #[L, g, t0, mkNatLit w, o])
  unless r.isAppOfArity ``Except.ok 3 do throwError "seg_sym: selp operand {o}"
  let v ← whnfD (r.getArg! 2)
  unless v.isAppOfArity ``PTX.Value.bits 2 do throwError "seg_sym: selp operand {o}"
  let n ← natValue (← mkAppM ``BitVec.toNat #[v.getArg! 1])
  return ← mkAppM ``PTX.Value.bits #[mkNatLit w, ← mkAppM ``BitVec.ofNat #[mkNatLit 64,
    mkNatLit n]]

/-- The condition `c` of the first conditional value `if c = true then a else b` in the facts
of the sources `srcs` (at the top of a value or inside it, a pair of them, say). -/
meta def condOperand (F : Expr) (srcs : Array Nat) : MetaM (Option Expr) := do
  for r in srcs do
    let some v ← factValue F r | continue
    let isCond (e : Expr) : Bool := e.isAppOfArity ``ite 5 &&
      (match (e.getArg! 1).eq? with
        | some (_, _, t) => t.isConstOf ``Bool.true
        | none => false)
    let some it := v.find? isCond | continue
    let some (_, c, _) := (it.getArg! 1).eq? | continue
    return some c
  return none

/-- The facts `F` on the side where `c` is `lit`: `c` replaced by the literal and the
conditionals on it reduced (as `simp only [h]` rewrites them). -/
meta def condFacts (F c : Expr) (lit : Bool) : MetaM Expr := do
  let litE := mkConst (if lit then ``Bool.true else ``Bool.false)
  let F' := F.replace fun e => if e == c then some litE else none
  Meta.transform F' (post := fun e => do
    if e.isAppOfArity ``ite 5 then
      if let some (_, l, t) := (e.getArg! 1).eq? then
        if t.isConstOf ``Bool.true then
          if l.isConstOf ``Bool.true then return .visit (e.getArg! 3)
          if l.isConstOf ``Bool.false then return .visit (e.getArg! 4)
    return .done e)

/-- A scalar `ld.param` under a launch `explicitParams L ps` whose list `ps` names the
parameter by a literal: the state after it (`execLocal` would compare the names). -/
meta def paramLoad (L t op : Expr) : MetaM (Option Expr) := do
  unless L.isAppOfArity ``PTX.Proof.explicitParams 2 do return none
  let op ← whnfD op
  unless op.isAppOfArity ``PTX.Op.mem 1 do return none
  let a := op.getArg! 0
  let addr ← whnfD (← mkAppM ``PTX.MemAccess.addr #[a])
  let base ← whnfD (addr.getArg! 0)
  unless base.isAppOfArity ``PTX.AddrBase.param 2 do return none
  unless (← whnfD (base.getArg! 1)).isConstOf ``Bool.false do return none
  let .lit (.strVal name) ← whnfD (base.getArg! 0) | return none
  let regs ← regList (← mkAppM ``PTX.MemAccess.regs #[a])
  let #[d] := regs | return none
  let mut ps ← whnfD (L.getArg! 1)
  while ps.isAppOfArity ``List.cons 3 do
    let pr ← whnfD (ps.getArg! 1)
    -- the entry's name: a literal, or a kernel's `param i`, the name ending in `_param_i`
    let key ← whnfR (pr.getArg! 2)
    let hit := match key with
      | .lit (.strVal n) => n == name
      | _ => match key.getAppArgs.back?.bind (·.nat?) with
        | some i => name.endsWith s!"_param_{i}"
        | none => false
    if hit then
      let w ← mkAppM ``PTX.DType.width #[← mkAppM ``PTX.MemAccess.elem #[a]]
      let x ← mkAppM ``BitVec.ofNat #[mkNatLit 64, pr.getArg! 3]
      let v ← mkAppM ``PTX.MemExt.extendBits #[← mkAppM ``PTX.MemAccess.ext #[a], w, x]
      return some (← mkAppM ``PTX.next #[← mkAppM ``PTX.setReg #[t, mkNatLit d, v]])
    ps ← whnfD (ps.getArg! 2)
  return none

/-- The goals `seg_sym` works on: a segment `∃ n, Seg K A L g n s F b G`, or dead states
`DeadFrom K A L g s F`. -/
structure SymGoal where
  K : Expr
  A : Expr
  L : Expr
  g : Expr
  s : Nat
  F : Expr
  /-- The end and its facts, for a segment. -/
  stop : Option (Expr × Expr)

meta def symGoal (ty : Expr) : MetaM SymGoal := do
  let ty := ty.consumeMData
  if ty.isAppOfArity ``PTX.Flow.DeadFrom 6 then
    return ⟨ty.getArg! 0, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ← natValue (ty.getArg! 4),
      ty.getArg! 5, none⟩
  let some (_, body) := ty.app2? ``Exists |
    throwError "seg_sym: expected ∃ n, Seg … or DeadFrom …, got {ty}"
  let .lam _ _ seg _ := body.consumeMData | throwError "seg_sym: expected ∃ n, Seg …"
  unless seg.isAppOfArity ``PTX.Flow.Seg 9 do throwError "seg_sym: expected ∃ n, Seg …"
  return ⟨seg.getArg! 0, seg.getArg! 1, seg.getArg! 2, seg.getArg! 3, ← natValue (seg.getArg! 5),
    seg.getArg! 6, some (seg.getArg! 7, seg.getArg! 8)⟩

/-- Close `∃ n, Seg … n …` (or `DeadFrom`'s first piece) with the length `n` the walk counted:
one local step per instruction, every round of a local loop included. -/
meta def segLen (n : Nat) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM Unit := do
  symLog s!"piece of {n} steps"
  evalTactic (← `(tactic| focus
    refine ⟨$(Syntax.mkNumLit (toString n)), ?_⟩
    ($tac)
    done))

/-- The proofs of the pieces `seg_sym` has proved in this file, by statement: a later goal with
the same statement (another successor of the same site, whose segment starts with the same
preamble) reuses the proof when its free variables are in scope (`segLenCached`). -/
meta initialize segPieceCache : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef {}

/-- The walks `seg_sym` has made in this file, by start (kernel, assumptions, launch, thread,
program counter, facts, dead mode): the program counters visited and the first symbolic point
with its facts and control, reused by a later walk from the same start whose end was not visited
on the way. -/
meta initialize segWalkCache :
    IO.Ref (Std.HashMap Expr (Array Nat × Nat × Expr × SymCtl × Nat)) ← IO.mkRef {}

/-- Whether every free variable of `e` is in the local context (by `collectFVars`, which visits
a shared subterm once: a proof term is a DAG whose tree is exponentially larger). -/
meta def inScope (e : Expr) : MetaM Bool := do
  unless e.hasFVar do return true
  let lctx ← getLCtx
  let st := Lean.collectFVars {} e
  return st.fvarSet.toList.all lctx.contains

/-- `segLen` through the cache of pieces: a piece whose statement was proved before (with its
free variables in scope) takes that proof; a new proof without metavariables is recorded. -/
meta def segLenCached (n : Nat) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if !ty.hasMVar then
    if let some pf := (← segPieceCache.get)[ty]? then
      if ← inScope pf then
        symLog s!"piece of {n} steps (cached)"
        g.assign pf
        replaceMainGoal []
        return
  segLen n tac
  let pf ← instantiateMVars (mkMVar g)
  if !ty.hasMVar && !pf.hasMVar then
    segPieceCache.modify (·.insert ty pf)

/-- The explicit facts `(dₖ, vₖ) :: … :: (d₁, v₁) :: F` after the writes `(d₁, v₁), …, (dₖ, vₖ)`
in this order (`Seg.writes`). -/
meta def consFacts (dv : Array (Nat × Expr)) (F : Expr) : MetaM Expr :=
  dv.foldlM (fun acc (d, v) => do
    mkAppM ``List.cons #[← mkAppM ``Prod.mk #[mkNatLit d, v], acc]) F

/-- A proof of `l = l'` for two explicit lists of facts with the same cells: `congr` on each cell,
`prove` for a fact that differs; `tail`: a known equation of two tails. -/
meta partial def listEqProof (l l' : Expr) (prove : Expr → Expr → TacticM Expr)
    (tail : Option (Expr × Expr × Expr) := none) : TacticM Expr := do
  if let some (t, t', pf) := tail then
    if l == t && l' == t' then return pf
  if l == l' then return ← mkEqRefl l
  unless l.isAppOfArity ``List.cons 3 && l'.isAppOfArity ``List.cons 3 do
    throwError "seg_sym: the facts {l} and {l'} have different cells"
  let a := l.getArg! 1
  let a' := l'.getArg! 1
  let ha ← if a == a' then mkEqRefl a else prove a a'
  let ht ← listEqProof (l.getArg! 2) (l'.getArg! 2) prove tail
  let cons ← mkAppOptM ``List.cons #[l.getArg! 0]
  mkCongr (← mkCongrArg cons ha) ht

/-- One local step at `q` (instruction `op`, writing the registers `ds`, reading `srcs`) from the
facts `F` whose sources hold conditional values: the values it writes, one per destination, and
the proof of the piece `∃ n, Seg … q F (q + 1) ((dₖ, vₖ) :: … :: (d₁, v₁) :: F)`. The step is the
rule step where an assumption may give a rule (`ruled`) and it evaluates (one destination);
otherwise the case split on the first condition `c` of a source, each side by the same means,
writing `if c = true then v₁ else v₀` into each destination (`v₁` if the sides agree); a side
without conditionals and without a rule step is the instruction's step evaluated on the side's
values (Core's rule on an infinity or a NaN pattern, say, or on the halves of a pair that an
unpack splits; `Seg.writes`). -/
meta partial def condStep (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) (A L gE : Expr)
    (q : Nat) (op : Expr) (ds : Array Nat) (srcs : Array Nat) (ruled : Bool) (F : Expr) :
    TacticM (Array Expr × TacticM Unit) := do
  let tq := Syntax.mkNumLit (toString q)
  if let (#[d], true) := (ds, ruled) then
    let r? ← try some <$> ruleStepProof A L gE q op d F srcs catch _ => pure none
    if let some (v, pf) := r? then
      let tpf ← Term.exprToSyntax pf
      return (#[v], do
        evalTactic (← `(tactic| exact PTX.Flow.Seg.rule1 (pc := $tq)
          (by code_lookup) rfl $tpf (PTX.Flow.keys_ne rfl)))
        symLog s!"rule step at {q}")
  match ← condOperand F srcs with
  | some c =>
    let tc ← Term.exprToSyntax c
    let F1 ← condFacts F c true
    let F0 ← condFacts F c false
    let (v1, p1) ← condStep tac A L gE q op ds srcs ruled F1
    let (v0, p0) ← condStep tac A L gE q op ds srcs ruled F0
    symLog s!"step at {q} into {ds}: conditional on {← ppExpr c}"
    let cE ← mkEq c (mkConst ``Bool.true)
    -- a destination with the same value on both sides holds it (no `if`)
    let vals ← (v1.zip v0).mapM fun (a, b) => if a == b then pure a else mkAppM ``ite #[cE, a, b]
    return (vals, do
      let h := mkIdent (← mkFreshUserName `hs)
      evalTactic (← `(tactic| by_cases $h:ident : $tc = true))
      let hs ← getGoals
      for (gl, lit, Fs, vs, prove) in [(hs[0]!, true, F1, v1, p1), (hs[1]!, false, F0, v0, p0)] do
        setGoals [gl]
        withMainContext do
        -- the side's facts: the facts that differ (those with the condition) by `simp` each,
        -- the others as they are
        let sg ← symGoal (← instantiateMVars (← getMainTarget))
        let some (_, Gg) := sg.stop | throwError "seg_sym: expected a segment"
        let Gs ← consFacts (ds.zip vs) Fs
        let hl ← if lit then `(term| $h) else `(term| Bool.eq_false_iff.mpr $h)
        let proveFact (a a' : Expr) : TacticM Expr := do
          let mv ← mkFreshExprSyntheticOpaqueMVar (← mkEq a a')
          let rest ← Tactic.run mv.mvarId! (evalTactic (← `(tactic|
            simp only [$hl:term, ↓reduceIte, Bool.false_eq_true])))
          unless rest.isEmpty do throwError "seg_sym: the fact {a} is not {a'} on this side"
          instantiateMVars mv
        let tF ← Term.exprToSyntax Fs
        let tG ← Term.exprToSyntax Gs
        try
          let hF ← listEqProof sg.F Fs proveFact
          let hG ← listEqProof Gg Gs proveFact (some (sg.F, Fs, hF))
          let thF ← Term.exprToSyntax hF
          let thG ← Term.exprToSyntax hG
          evalTactic (← `(tactic|
            refine PTX.Flow.Seg.facts_eq (F' := $tF) (G' := $tG) $thF $thG ?_))
        catch _ =>
          -- facts that are not an explicit list (a table): `simp` on the whole lists
          evalTactic (← `(tactic| refine PTX.Flow.Seg.facts_eq (F' := $tF) (G' := $tG)
            (by simp only [$hl:term, ↓reduceIte, Bool.false_eq_true])
            (by simp only [$hl:term, ↓reduceIte, Bool.false_eq_true]) ?_))
        symLog s!"side {lit} at {q} restated"
        prove)
  | none =>
    -- Core's rule on these values
    let regsTy ← mkArrow (mkConst ``Nat) (← mkAppM ``Option #[mkConst ``PTX.Value])
    let cfTy ← mkAppM ``Option #[mkConst ``Bool]
    let vs? ← (← getMainGoal).withContext do
      withLocalDeclD `R regsTy fun R => withLocalDeclD `cf cfTy fun cf => do
        let t ← symStart q F R cf
        let r ← whnfD (mkAppN (mkConst ``PTX.execLocal) #[L, gE, t, op])
        unless r.isAppOfArity ``Except.ok 3 do return none
        let mut vs := #[]
        for d in ds do
          let some v ← stateReg (r.getArg! 2) d | return none
          if v.containsFVar R.fvarId! || v.containsFVar cf.fvarId! then return none
          vs := vs.push (← normVal v)
        return some vs
    let some vs := vs? | throwError "seg_sym: the instruction at {q} has no rule on the values \
      {F}"
    -- the writes in the order of the destinations, as Core's rules make them (an unpack writes
    -- its low half first); by `seg_auto` if that is not the order
    let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``PTX.Value]
    let dvE ← mkListLit pairTy (← (ds.zip vs).toList.mapM fun (d, v) =>
      mkAppM ``Prod.mk #[mkNatLit d, v])
    let tdv ← Term.exprToSyntax dvE
    return (vs, do
      let s0 ← saveState
      try
        -- Core's rule where no assumption gives one, else the assumptions' rules evaluated (an
        -- approximation's rule that declines on a constant operand, say)
        Tactic.withoutRecover <| evalTactic (← `(tactic| exact PTX.Flow.Seg.writes (pc := $tq)
          (dv := $tdv) (by code_lookup) rfl
          (fun R cf hR => by
            rw [← PTX.Proof.override_eq hR]
            first
              | (rw [PTX.Flow.execLocalA_core (pc := $tq) (by sym_local_none) (by sym_seg_free)
                  rfl]; rfl)
              | rfl) rfl))
        symLog s!"core step at {q}"
      catch _ =>
        s0.restore
        evalTactic (← `(tactic| seg_auto using $tac))
        symLog s!"core step at {q} by seg_auto")

/-- A `neg.f32 d, r` or `abs.f32 d, r` (no other modifier) whose source holds `.bits 32 x` in
the symbolic state `t`, and a hypothesis that classifies the word (`wordHyp?`):
`(abs, d, r, h, s)` with `h : classify .f32 (.bits 32 x) = .ok (.fin s)`. -/
meta def wordStep (t op : Expr) : TacticM (Option (Bool × Nat × Nat × Expr × Expr)) := do
  unless op.isAppOfArity ``PTX.Op.float 1 do return none
  let f := op.appArg!
  let fop ← whnfD (← mkAppM ``PTX.FloatInstr.op #[f])
  let ab ← if fop.isConstOf ``PTX.FOp.neg then pure false
    else if fop.isConstOf ``PTX.FOp.abs then pure true else return none
  let ds ← whnfD (← mkAppM ``PTX.FloatInstr.dsts #[f])
  let ss ← whnfD (← mkAppM ``PTX.FloatInstr.srcs #[f])
  unless ds.isAppOfArity ``List.cons 3 && ss.isAppOfArity ``List.cons 3 do return none
  let d0 ← whnfD (ds.getArg! 1)
  let s0 ← whnfD (ss.getArg! 1)
  unless d0.isAppOfArity ``Option.some 2 && s0.isAppOfArity ``PTX.Opnd.reg 1 do return none
  let some d ← (do return (← whnfD (d0.getArg! 1)).rawNatLit?) | return none
  let some r ← (do return (← whnfD s0.appArg!).rawNatLit?) | return none
  -- the instruction is exactly the lemma's: one f32 lane, no other modifier, one source
  unless (← whnfD (ds.getArg! 2)).isAppOfArity ``List.nil 1 &&
      (← whnfD (ss.getArg! 2)).isAppOfArity ``List.nil 1 do return none
  let ty ← whnfD (← mkAppM ``PTX.FloatInstr.ty #[f])
  unless ty.isAppOfArity ``PTX.FTy.mk 2 && (← whnfD (ty.getArg! 0)).isConstOf ``PTX.FloatFmt.f32 &&
      (← whnfD (ty.getArg! 1)).rawNatLit? == some 1 do return none
  for (fld, isNone) in [(``PTX.FloatInstr.srcTys, true), (``PTX.FloatInstr.cmpTy, true),
      (``PTX.FloatInstr.rnd, true)] do
    let v ← whnfD (← mkAppM fld #[f])
    unless isNone && (v.isAppOfArity ``List.nil 1 || v.isAppOfArity ``Option.none 1) do
      return none
  unless (← whnfD (← mkAppM ``PTX.FloatInstr.mode #[f])).isConstOf ``PTX.FMode.ieee do
    return none
  for fld in [``PTX.FloatInstr.ftz, ``PTX.FloatInstr.sat, ``PTX.FloatInstr.relu,
      ``PTX.FloatInstr.oob, ``PTX.FloatInstr.nanMod, ``PTX.FloatInstr.xorsign,
      ``PTX.FloatInstr.absMod] do
    unless (← whnfD (← mkAppM fld #[f])).isConstOf ``Bool.false do return none
  let some v ← stateReg t r | return none
  let v ← whnfR v
  unless v.isAppOfArity ``PTX.Value.bits 2 do return none
  let some (h, sE) ← wordHyp? (v.getArg! 1) | return none
  return some (ab, d, r, h, sE)

/-- `seg_sym` on the main goal. `cut`: the goal's start facts are explicit facts of a cut. -/
meta partial def segSymGo (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) (cut : Bool)
    (splits : List Nat := []) : TacticM Unit := withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let sg ← symGoal ty
  let (K, A, L, gE, s, F) := (sg.K, sg.A, sg.L, sg.g, sg.s, sg.F)
  let dead := sg.stop.isNone
  -- the end, a literal program counter; an `if` is split first
  let mut b := 0
  let mut G := F
  if let some (bE, G') := sg.stop then
    let hasIte := (bE.find? fun e => e.isAppOf ``ite || e.isAppOf ``dite).isSome
    let b? ← if hasIte then pure none else
      tryCatchRuntimeEx
        (withTheReader Core.Context (fun c => { c with maxHeartbeats := 200000 })
          (withCurrHeartbeats (some <$> natValue bE)))
        (fun _ => pure none)
    let some b' := b? | do
      -- split on the condition of the first `if` of the end (`split` does not enter `∃ n`)
      let some it := bE.find? (·.isAppOfArity ``ite 5) |
        throwError "seg_sym: the end of the segment is not a program counter: {bE}"
      let tc ← Term.exprToSyntax (it.getArg! 1)
      let hb := mkIdent (← mkFreshUserName `hb)
      evalTactic (← `(tactic| by_cases $hb:ident : $tc))
      let gs ← getGoals
      for g' in gs do
        setGoals [g']
        evalTactic (← `(tactic| simp only [$hb:ident, ite_true, ite_false, ↓reduceIte,
          Bool.false_eq_true, Bool.true_eq_false, Bool.not_eq_true]))
        segSymGo tac cut splits
      return
    b := b'
    G := G'
  symLog s!"segment {s} → {b} (dead {dead}, cut {cut})"
  let code ← mkAppM ``PTX.Kernel.code #[K]
  -- the segment steps the context states, by start pc (a hypothesis per segment instance)
  let segSteps ← segHyps
  -- the registers live at a program counter, from a table's live function
  let liveSrc := if dead then F else G
  let (_, tbl) ← splitFacts liveSrc
  let liveFn ← match tbl with
    | some (live, _) => pure live.getAppFn
    | none =>
      -- explicit facts only: the live function of the kernel's code
      let some k := K.getAppFn.constName? | throwError "seg_sym: the kernel is not a constant"
      pure (mkConst (k.getPrefix ++ `Flow ++ `live))
  let liveAt (q : Nat) : MetaM (List Nat) := do
    return (← regList (mkApp liveFn (mkNatLit q))).toList
  -- the walk, on a symbolic state
  let g := (← getMainGoal)
  let regsTy ← mkArrow (mkConst ``Nat) (← mkAppM ``Option #[mkConst ``PTX.Value])
  let cfTy ← mkAppM ``Option #[mkConst ``Bool]
  -- a walk from the same start made before, whose end was not on its path, is reused
  let walkKey := mkAppN (mkConst `PTX.Flow.segWalkKey)
    #[K, A, L, gE, mkNatLit s, F, toExpr dead]
  let cachedWalk ← do
    match (← segWalkCache.get)[walkKey]? with
    | some (vis, q, H, ctl, len) =>
      if !vis.contains b && (← inScope H) then
        symLog s!"walk {s} → {q} (cached)"
        pure (some ((some (q, H, ctl, len) : Option (Nat × Expr × SymCtl × Nat)), 0))
      else pure none
    | none => pure none
  let visRef ← IO.mkRef (#[] : Array Nat)
  let result ← if let some r := cachedWalk then pure r else g.withContext do
    withLocalDeclD `R regsTy fun R => withLocalDeclD `cf cfTy fun cf => do
    let mut t ← symStart s F R cf
    -- the first fact of a register is its value (as `override` reads it)
    let start : Std.HashMap Nat Expr :=
      (← startCells F).foldl (fun m (r, v) => m.insertIfNew r v) {}
    -- the state is still the start state (its facts need no evaluation)
    let mut fresh := true
    let mut pc := s
    let mut steps := 0
    while dead || pc != b do
      visRef.modify (·.push pc)
      steps := steps + 1
      if steps > 4096 then throwError "seg_sym: no path from {s} to {b}"
      let ctl ← symCtl K code pc
      if let SymCtl.event := ctl then
        -- a guarded event instruction whose guard the state gives as false is a local skip
        let some (p, neg) ← instrGuard K code pc |
          throwError "seg_sym: event instruction at {pc} before {b}"
        let some v ← stateReg t p |
          throwError "seg_sym: event instruction at {pc} before {b} (guard {p} unknown)"
        let some c ← predBool? v |
          throwError "seg_sym: event instruction at {pc} before {b} (guard {p} holds {v})"
        -- a guard that is not a literal: cut here, as before a branch on it, so that its value
        -- is decided (by a hypothesis, or by cases) in front of the facts
        let some lit ← boolLit? c |
          return (some (pc, ← stateFacts t (← liveAt pc) start fresh,
            SymCtl.bra (some (p, neg)) (pc + 1), steps - 1), 0)
        unless lit == neg do throwError "seg_sym: event instruction at {pc} before {b}"
        symLog s!"skip the event instruction at {pc}: its guard is false"
        t ← mkAppM ``PTX.skip #[t]
        fresh := false
        pc := pc + 1
        continue
      let pred? : Option Nat := match ctl with
        | .bra (some (p, _)) _ => some p
        | .selp _ p _ _ _ => some p
        | _ => none
      if let some p := pred? then
        let some v ← stateReg t p | throwError "seg_sym: predicate {p} has no value at {pc}"
        let some c ← predBool? v | throwError "seg_sym: register {p} holds {v} at {pc}"
        if (← boolLit? c).isNone then
          return (some (pc, ← stateFacts t (← liveAt pc) start fresh, ctl, steps - 1), 0)
      -- one local step: a branch on a literal predicate, else Core's local rule (the
      -- assumptions take no local step on the walk; `seg_fp` checks the pieces with them)
      let _ := A
      match ctl with
      | .bra none tgt =>
        fresh := false
        t ← mkAppM ``PTX.skip #[t]
        t := mkAppN (mkConst ``PTX.TState.mk) #[mkNatLit tgt,
          mkApp (mkConst ``PTX.TState.regs) t, mkApp (mkConst ``PTX.TState.cf) t,
          mkNatLit 0, mkApp (mkConst ``PTX.TState.acc) t, mkApp (mkConst ``PTX.TState.fault) t]
        pc := tgt
      | .bra (some (p, neg)) tgt =>
        let some v ← stateReg t p | throwError "seg_sym: predicate {p} has no value at {pc}"
        let some c ← predBool? v | throwError "seg_sym: register {p} holds {v} at {pc}"
        let some lit ← boolLit? c | throwError "seg_sym: predicate {p} at {pc}"
        fresh := false
        if lit != neg then
          t := mkAppN (mkConst ``PTX.TState.mk) #[mkNatLit tgt,
            mkApp (mkConst ``PTX.TState.regs) t, mkApp (mkConst ``PTX.TState.cf) t,
            mkNatLit 0, mkApp (mkConst ``PTX.TState.acc) t, mkApp (mkConst ``PTX.TState.fault) t]
          pc := tgt
        else
          t ← mkAppM ``PTX.skip #[t]
          pc := pc + 1
      | _ =>
        let some ins ← instrAt K code pc | throwError "seg_sym: no instruction at {pc}"
        let ins ← whnfD ins
        unless (← whnfD (ins.getArg! 0)).isAppOfArity ``Option.none 1 do
          throwError "seg_sym: a guarded local instruction at {pc}"
        -- a segment step that a hypothesis in context states replaces the instruction's rule:
        -- the step is the segment's, from `pc` to its stop (`Seg.segRunStep`, `Seg.segStep`)
        if let some (b, G, hv) := segSteps.get? pc then
          if b == pc then throwError "seg_sym: the segment at {pc} does not advance"
          let H ← stateFacts t (← liveAt pc) start fresh
          return (some (pc, H, SymCtl.seg b G hv, steps - 1), 0)
        if let some t' ← paramLoad L t (ins.getArg! 1) then
          t := t'
          fresh := false
          pc := pc + 1
          continue
        let tm0 ← IO.monoMsNow
        let r ← whnfD (mkAppN (mkConst ``PTX.execLocal) #[L, gE, t, ins.getArg! 1])
        symLog s!"  step {pc}: {(← IO.monoMsNow) - tm0} ms"
        -- a floating instruction or conversion that Core's rule does not evaluate on these
        -- values (exact reals) and an assumption gives a rule: cut, and take the step by the
        -- rule (`rule_step`)
        let opW ← whnfD (ins.getArg! 1)
        if !r.isAppOfArity ``Except.ok 3 &&
            (opW.isAppOfArity ``PTX.Op.float 1 || opW.isAppOfArity ``PTX.Op.cvt 1) then
          if ← hasRule A L gE t (ins.getArg! 1) then
            let ws ← regList (← mkAppM ``PTX.Proof.writesRegs #[ins.getArg! 1])
            let #[d] := ws | throwError "seg_sym: the instruction at {pc} writes {ws}"
            let occs ← regList (← mkAppM ``PTX.Proof.opRegs #[ins.getArg! 1])
            let srcs := occs.foldl (fun acc r => if r == d || acc.contains r then acc
              else acc.push r) #[]
            return (some (pc, ← stateFacts t (← liveAt pc) start fresh,
              SymCtl.rule #[d] srcs true, steps - 1), 0)
        -- a division that does not evaluate on these values: cut, and decide whether it has a
        -- rule
        if let SymCtl.div .. := ctl then
          unless r.isAppOfArity ``Except.ok 3 do
            return (some (pc, ← stateFacts t (← liveAt pc) start fresh, ctl, steps - 1), 0)
        unless r.isAppOfArity ``Except.ok 3 do
          -- a step on a conditional value (`sym_selp_value`), writing one register (a pack, say)
          -- or several (an unpack): cut, and take it on each side of the condition (`condStep`)
          let ws ← regList (← mkAppM ``PTX.Proof.writesRegs #[ins.getArg! 1])
          let occs ← regList (← mkAppM ``PTX.Proof.opRegs #[ins.getArg! 1])
          let mut cond := false
          for r' in occs do
            if let some v ← stateReg t r' then
              if (v.find? (·.isAppOfArity ``ite 5)).isSome then cond := true
          if cond && ws.size ≥ 1 then
            let srcs := occs.foldl (fun acc r => if ws.contains r || acc.contains r then acc
              else acc.push r) #[]
            let ruled ← hasRule A L gE t (ins.getArg! 1)
            return (some (pc, ← stateFacts t (← liveAt pc) start fresh,
              SymCtl.rule ws srcs ruled, steps - 1), 0)
          -- `neg.f32`/`abs.f32` of a word whose number a hypothesis gives (`Seg.negWord`)
          if let some (ab, d, r0, h, sE) ← wordStep t opW then
            return (some (pc, ← stateFacts t (← liveAt pc) start fresh,
              SymCtl.word ab d r0 h sE, steps - 1), 0)
          throwError "seg_sym: the local step at {pc} does not evaluate: {r}"
        t := r.getArg! 2
        fresh := false
        pc ← natValue (mkApp (mkConst ``PTX.TState.pc) t)
    if cut then
      return (some (b, ← stateFacts t (← liveAt b) start fresh, SymCtl.event, steps), steps)
    return (none, steps)
  -- record a walk that stopped at a symbolic point (not at the end), with no hypothesis in it
  if cachedWalk.isNone then
    if let (some (q, H, ctl, len), _) := result then
      let keep := match ctl with
        | .event | .word .. | .seg .. => false
        | _ => true
      if keep && !H.hasMVar then
        let vis ← visRef.get
        segWalkCache.modify (·.insert walkKey (vis, q, H, ctl, len))
  match result with
  | (none, len) => segLen len tac
  | (some (q, H, ctl, len), _) =>
    if let SymCtl.event := ctl then
      -- the end, after a cut: reach `b` with the explicit facts, then restate them
      let tH ← Term.exprToSyntax H
      evalTactic (← `(tactic| refine PTX.Flow.Seg.weaken_end_ex (G := $tH) ?_ ?_))
      let gs ← getGoals
      setGoals [gs[0]!]
      segLen len tac
      setGoals [gs[1]!]
      symLog "restate"
      try restate H G
      catch e => symLog s!"restate failed: {← e.toMessageData.toString}"; throw e
      symLog "restated"
      return
    -- a segment an assumption takes at the cut point: the piece to its stop by `Seg.segStep`
    if let SymCtl.seg bSeg Gs hs := ctl then
      let tH ← Term.exprToSyntax H
      let tGs ← Term.exprToSyntax Gs
      let tq := Syntax.mkNumLit (toString q)
      let tb := Syntax.mkNumLit (toString bSeg)
      let split (q' : Syntax.Term) (H' : Syntax.Term) : TacticM (List MVarId) := do
        evalTactic (← if dead then
          `(tactic| refine PTX.Flow.DeadFrom.of_seg (q := $q') (H := $H') ?_ ?_) else
          `(tactic| refine PTX.Flow.Seg.comp_ex (q := $q') (H := $H') ?_ ?_))
        getGoals
      if q != s then
        let gs ← split tq tH
        setGoals [gs[0]!]
        segLenCached len tac
        setGoals gs.tail
      let Fq := if q != s then H else F
      let gs ← split tb tGs
      setGoals [gs[0]!]
      let ths ← Term.exprToSyntax hs
      let s0 ← saveState
      try
        Tactic.withoutRecover <| evalTactic (← `(tactic| exact $ths))
      catch _ => do
        s0.restore
        let tH ← Term.exprToSyntax Fq
        throwError "seg_sym: the hypothesis for the segment at {q} does not start from the \
          facts the walk has there ({tH})"
      setGoals gs.tail
      segSymGo tac true splits
      return
    -- cut before the point
    let tq := Syntax.mkNumLit (toString q)
    if q != s then
      let tH ← Term.exprToSyntax H
      evalTactic (← if dead then
        `(tactic| refine PTX.Flow.DeadFrom.of_seg (q := $tq) (H := $tH) ?_ ?_) else
        `(tactic| refine PTX.Flow.Seg.comp_ex (q := $tq) (H := $tH) ?_ ?_))
      let gs ← getGoals
      setGoals [gs[0]!]
      segLenCached len tac
      setGoals gs.tail
    -- the facts at the point
    let F ← if q != s then pure H else pure F
    -- a piece `q → q + 1` into `(d₁, v₁) :: … :: F`, then the rest
    let piece (dv : Array (Nat × Expr)) (prove : TacticM Unit) : TacticM Unit := do
      let F' ← consFacts dv F
      let tF' ← Term.exprToSyntax F'
      let tq1 := Syntax.mkNumLit (toString (q + 1))
      evalTactic (← if dead then
        `(tactic| refine PTX.Flow.DeadFrom.of_seg (q := $tq1) (H := $tF') ?_ ?_) else
        `(tactic| refine PTX.Flow.Seg.comp_ex (q := $tq1) (H := $tF') ?_ ?_))
      let gs ← getGoals
      setGoals [gs[0]!]
      prove
      setGoals gs.tail
      segSymGo tac true splits
    let predRule := if dead then ``PTX.Flow.DeadFrom.pred else ``PTX.Flow.Seg.pred_ex
    match ctl with
    | .bra (some (p, _)) _ =>
      let some v ← factValue F p | throwError "seg_sym: no fact of predicate {p}"
      let some c ← predBool? v | throwError "seg_sym: register {p} holds {v}, not a predicate"
      let tc ← Term.exprToSyntax c
      let tp := Syntax.mkNumLit (toString p)
      let rule := mkIdent predRule
      let decided ← match ← decideBool c true with
        | some pf => pure (some (true, pf))
        | none => match ← decideBool c false with
          | some pf => pure (some (false, pf))
          | none => pure none
      symLog s!"branch at {q} on {p}: {decided.map (·.1)}"
      -- a walk that comes back to this branch again and again goes around a loop whose exit
      -- the hypotheses do not decide: stop with the predicate instead of unrolling the loop
      let again := splits.count q
      if (decided.isNone && again ≥ 2) || again ≥ 64 then
        throwError "seg_sym: the walk comes back to the branch at {q} on {p} (a loop): its \
          predicate {← ppExpr c} is not decided by a hypothesis or by `sym_decide`; give \
          `sym_decide` a rule for it"
      match decided with
      | some (lit, pf) =>
        let tpf ← Term.exprToSyntax pf
        let tl := mkIdent (if lit then ``Bool.true else ``Bool.false)
        evalTactic (← `(tactic|
          refine $rule (p := $tp) (c := $tc) (c' := $tl) (by fact_mem) $tpf ?_))
        segSymGo tac true (q :: splits)
      | none =>
        let h := mkIdent (← mkFreshUserName `hc)
        evalTactic (← `(tactic| by_cases $h:ident : $tc = true))
        let gs ← getGoals
        setGoals [gs[0]!]
        evalTactic (← `(tactic|
          refine $rule (p := $tp) (c := $tc) (c' := true) (by fact_mem) $h ?_))
        segSymGo tac true (q :: splits)
        setGoals [gs[1]!]
        evalTactic (← `(tactic|
          refine $rule (p := $tp) (c := $tc) (c' := false) (by fact_mem)
            (Bool.eq_false_iff.mpr $h) ?_))
        segSymGo tac true (q :: splits)
    | .selp d p w a bo =>
      let some v ← factValue F p | throwError "seg_sym: no fact of predicate {p}"
      let some c ← predBool? v | throwError "seg_sym: register {p} holds {v}, not a predicate"
      let tc ← Term.exprToSyntax c
      let tp := Syntax.mkNumLit (toString p)
      let ops? ← try pure (some (← selpOperand F w a, ← selpOperand F w bo)) catch _ => pure none
      let some (x, y) := ops? | do
        -- operands that are not words, and the role opted in: the conditional value
        if ← selpValueOptIn then
          let va ← selpValue L gE F w a
          let vb ← selpValue L gE F w bo
          let val ← mkAppM ``ite #[← mkEq c (mkConst ``Bool.true), va, vb]
          symLog s!"selp at {q} on {p}: conditional value"
          -- an operand's value as Core reads it, from the facts
          let opnd (o : Expr) : TacticM (TSyntax `term) := do
            let o ← whnfD o
            if o.isAppOfArity ``PTX.Opnd.reg 1 then
              let some r := regLit? (← whnfD (o.getArg! 0)) | throwError "seg_sym: selp operand"
              let tr := Syntax.mkNumLit (toString r)
              `(term| fun t h => by
                  simp only [PTX.readValue, PTX.readReg, PTX.Proof.holds_mem (r := $tr) h
                    (by fact_mem)]; rfl)
            else `(term| fun _ _ => rfl)
          let ta ← opnd a
          let tb ← opnd bo
          piece #[(d, val)] do
            let s0 ← saveState
            try
              -- the operands' byte counts: a value an ideal rule wrote by its lemma (whatever
              -- its argument, such as a fold's maximum over conditionals), else by evaluation
              -- on each side of its conditions
              Tactic.withoutRecover <| evalTactic (← `(tactic| exact PTX.Flow.Seg.selpV
                (pc := $tq) (by code_lookup) (by fact_mem) $ta $tb
                (by first
                  | (rw [PTX.Flow.erealValue_f32_bytes]; rfl)
                  | rfl
                  | ((repeat' split) <;> first | rfl | simp [PTX.Flow.erealValue_f32_bytes]))
                (by first
                  | (rw [PTX.Flow.erealValue_f32_bytes]; rfl)
                  | rfl
                  | ((repeat' split) <;> first | rfl | simp [PTX.Flow.erealValue_f32_bytes]))
                (PTX.Flow.keys_ne rfl) (by sym_local_none) (by sym_seg_free) rfl rfl))
              return
            catch _ => s0.restore
            let h := mkIdent (← mkFreshUserName `hs)
            evalTactic (← `(tactic| by_cases $h:ident : $tc = true))
            let hs ← getGoals
            setGoals [hs[0]!]
            evalTactic (← `(tactic| refine PTX.Flow.Seg.selv_pos $h ?_))
            evalTactic (← `(tactic|
              refine PTX.Flow.Seg.pred_ex (p := $tp) (c := $tc) (c' := true) (by fact_mem) $h
                ?_))
            evalTactic (← `(tactic| seg_auto using $tac))
            setGoals [hs[1]!]
            evalTactic (← `(tactic| refine PTX.Flow.Seg.selv_neg $h ?_))
            evalTactic (← `(tactic|
              refine PTX.Flow.Seg.pred_ex (p := $tp) (c := $tc) (c' := false) (by fact_mem)
                (Bool.eq_false_iff.mpr $h) ?_))
            evalTactic (← `(tactic| seg_auto using $tac))
          return
        -- operands that are not words (floating values, say): both values of the predicate in
        -- turn, the walk continuing on each
        symLog s!"selp at {q} on {p}: split"
        let rule := mkIdent predRule
        let h := mkIdent (← mkFreshUserName `hc)
        evalTactic (← `(tactic| by_cases $h:ident : $tc = true))
        let gs ← getGoals
        setGoals [gs[0]!]
        evalTactic (← `(tactic|
          refine $rule (p := $tp) (c := $tc) (c' := true) (by fact_mem) $h ?_))
        segSymGo tac true splits
        setGoals [gs[1]!]
        evalTactic (← `(tactic|
          refine $rule (p := $tp) (c := $tc) (c' := false) (by fact_mem)
            (Bool.eq_false_iff.mpr $h) ?_))
        segSymGo tac true splits
      let ite ← mkAppM ``ite #[← mkEq c (mkConst ``Bool.true), x, y]
      let val ← mkAppM ``PTX.Value.bits #[mkNatLit w, ite]
      piece #[(d, val)] do
        let h := mkIdent (← mkFreshUserName `hs)
        evalTactic (← `(tactic| by_cases $h:ident : $tc = true))
        let hs ← getGoals
        setGoals [hs[0]!]
        evalTactic (← `(tactic| refine PTX.Flow.Seg.sel_pos $h ?_))
        evalTactic (← `(tactic|
          refine PTX.Flow.Seg.pred_ex (p := $tp) (c := $tc) (c' := true) (by fact_mem) $h ?_))
        evalTactic (← `(tactic| seg_auto using $tac))
        setGoals [hs[1]!]
        evalTactic (← `(tactic| refine PTX.Flow.Seg.sel_neg $h ?_))
        evalTactic (← `(tactic|
          refine PTX.Flow.Seg.pred_ex (p := $tp) (c := $tc) (c' := false) (by fact_mem)
            (Bool.eq_false_iff.mpr $h) ?_))
        evalTactic (← `(tactic| seg_auto using $tac))
    | .div k w d a bd =>
      let some va ← factValue F a | throwError "seg_sym: no fact of the dividend {a}"
      let some vb ← factValue F bd | throwError "seg_sym: no fact of the divisor {bd}"
      let some x ← valueBits? va | throwError "seg_sym: the dividend {a} is not bits"
      let some y ← valueBits? vb | throwError "seg_sym: the divisor {bd} is not bits"
      let tx ← mkAppM ``PTX.truncBits #[mkNatLit w, x]
      let ty' ← mkAppM ``PTX.truncBits #[mkNatLit w, y]
      let c ← mkAppM ``PTX.Flow.divOk #[k, mkNatLit w, tx, ty']
      match ← decideBool c true with
      | some pf =>
        let tpf ← Term.exprToSyntax pf
        let val ← mkAppM ``PTX.Value.bits #[mkNatLit w,
          ← mkAppM ``PTX.Flow.divQ #[k, mkNatLit w, tx, ty']]
        piece #[(d, val)] do
          evalTactic (← `(tactic| exact PTX.Flow.Seg.div_ok (pc := $tq) (by code_lookup)
            (by fact_mem) (by fact_mem) $tpf (PTX.Flow.keys_ne rfl) (by sym_local_none)
            (by sym_seg_free)))
      | none =>
        match ← decideBool c false with
        | some pf =>
          unless dead do throwError "seg_sym: the division at {q} has no rule"
          let tpf ← Term.exprToSyntax pf
          evalTactic (← `(tactic| exact PTX.Flow.DeadFrom.div (s := $tq) (by code_lookup)
            (by fact_mem) (by fact_mem) $tpf (by sym_local_none) (by sym_seg_free)))
        | none => throwError "seg_sym: no decision of the division at {q}"
    | .rule ds srcs ruled =>
      let code ← mkAppM ``PTX.Kernel.code #[K]
      let some ins ← instrAt K code q | throwError "seg_sym: no instruction at {q}"
      let ins ← whnfD ins
      let op := ins.getArg! 1
      -- a rule step writes one register; an instruction with several destinations is taken on
      -- conditional operands only
      let r? ← match ds, ruled with
        | #[d], true => try some <$> ((d, ·) <$> ruleStepProof A L gE q op d F srcs) catch ex => do
          -- an operand that is a conditional value (`sym_selp_value`): the step on each side;
          -- in dead states, possibly a fault
          if !dead then
            let some _ ← condOperand F srcs | throw ex
          pure none
        | _, _ => do
          if !dead then
            let some _ ← condOperand F srcs |
              throwError "seg_sym: the step at {q} into {ds} reads no conditional value"
          pure none
      -- the thread faults here (dead states only): the kernel's `sym_fault`
      if r?.isNone && dead then
        let s0 ← saveState
        try
          Tactic.withoutRecover <| evalTactic (← `(tactic| exact PTX.Flow.DeadFrom.local_error
            (s := $tq) (by code_lookup) (by rfl) (by sym_fault)))
          symLog s!"fault at {q}"
          return
        catch _ => s0.restore
      match r? with
      | some (d, v, pf) =>
        symLog s!"rule step at {q} into {d}"
        let tpf ← Term.exprToSyntax pf
        piece #[(d, v)] do
          evalTactic (← `(tactic| exact PTX.Flow.Seg.rule1 (pc := $tq) (by code_lookup) rfl
            $tpf (PTX.Flow.keys_ne rfl)))
      | none =>
        let (vs, prove) ← condStep tac A L gE q op ds srcs ruled F
        piece (ds.zip vs) prove
    | .word ab d _ h sE =>
      let tS ← Term.exprToSyntax sE
      let th ← Term.exprToSyntax h
      let vE ← Term.elabTerm (← if ab then
          `(PTX.Value.float PTX.FloatFmt.f32 (((|$tS| : ℚ)) : ℝ)) else
          `(PTX.Value.float PTX.FloatFmt.f32 (((-$tS : ℚ)) : ℝ))) none
      let vE ← instantiateMVars vE
      piece #[(d, vE)] do
        let lem := mkIdent (if ab then ``PTX.Flow.Seg.absWord else ``PTX.Flow.Seg.negWord)
        evalTactic (← `(tactic| exact $lem (pc := $tq) (by code_lookup) (by sym_local_none)
          (by sym_seg_free) (by fact_mem) $th rfl))
        symLog s!"word step at {q}"
    | _ => throwError "seg_sym: not a symbolic point"

/-- `sym_mark "text"`: a line in the `SEG_SYM_LOG` timing log. -/
elab "sym_mark " s:str : tactic => symLog s.getString

/-- `seg_sym using tac`: prove `∃ n, Seg K A L g n s F b G` through branches and `selp`s on
symbolic predicates, and signed divisions that hypotheses in context show to have a rule, each
piece by `seg_auto using tac`; or prove `DeadFrom K A L g s F` by reaching a division that
hypotheses show to have no rule. A hypothesis `explicitParams L ps = L` or
`explicitObject L name decl fields = L` (or the one inside the other) in context makes the
parameters or a by-value parameter object explicit for the evaluation (an `ld.param` through a
register then evaluates to the object's bytes).

The walk from a start (program counter and facts) to its first symbolic point, and the proof of
that piece, are kept for the file: a later `seg_sym` from the same start (another successor of the
same site) reuses them (`segWalkCache`, `segPieceCache`), so a preamble before the first branch
is walked and proved once per site. -/
syntax "seg_sym " "using " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| seg_sym using $tac) => withMainContext do
    -- a launch with explicit parameters, if the context has one
    let lctx ← getLCtx
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, lhs, _) := ty.eq? then
        if isExplicitLaunch lhs then
          let goal := (← instantiateMVars (← getMainTarget)).consumeMData
          if goal.isAppOfArity ``PTX.Flow.DeadFrom 6 then
            evalTactic (← `(tactic| refine PTX.Flow.DeadFrom.launch $(mkIdent d.userName) ?_))
          else
            evalTactic (← `(tactic| refine PTX.Flow.Seg.launch_ex $(mkIdent d.userName) ?_))
          break
    segSymGo tac false


/-- `seg_cut q H using tac`: a segment cut at `q`, where the facts `H` (a role's table at `q`)
are restated: the piece to `q` and the rest from `H`, each by `seg_sym` (a once-walked preamble:
its computed terms are replaced by the table's at the cut, and the walk after it starts from the
table's terms). `seg_sym` keeps a site's preamble walk and proof across its successors by itself;
the cut is for a preamble whose computed terms the rest cannot decide. -/
macro "seg_cut " q:term:max H:term:max " using " tac:tacticSeq : tactic => `(tactic| (
  refine PTX.Flow.Seg.comp_ex (q := $q) (H := $H) ?_ ?_
  · seg_sym using $tac
  · seg_sym using $tac))

/-- `dead_cut q H using tac`: dead states (`DeadFrom`) through a cut at `q` with the facts `H`
(a role's table there): an ordinary segment to `q`, whose branches the table and the hypotheses
decide, then the death from `q` (a division without a rule after the loop's branches). A dead
segment has no end table to read its branches' predicates from; the cut gives it one. -/
macro "dead_cut " q:term:max H:term:max " using " tac:tacticSeq : tactic => `(tactic| (
  refine PTX.Flow.DeadFrom.of_seg (q := $q) (H := $H) ?_ ?_
  · seg_sym using $tac
  · seg_sym using $tac))

end PTX.Flow
